/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/StrongMason.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `strong_mason_conjecture`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/strong_mason_conjecture.toml`, rev 1, submitter Kim Morrison, status
archived): the definition `independentSetCount` and the statement of `strong_mason_conjecture`,
with the docstrings they had in the former wanted module
`WantedExt/Combinatorics/StrongMasonWanted.lean`, and the title and first two paragraphs of the
module documentation, as they were in that module.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Combinatorics.StrongMasonWanted` namespace. Mathematical statements are unchanged.
Later changes (ATLAS, 2026): the docstrings were restated to match the Lean statements; then the
`theorem_wanted` was proved and the declarations moved from
`WantedExt/Combinatorics/StrongMasonWanted.lean` to this `MathlibExt` module with unchanged
names, statements and docstrings, the imports of `Batteries.Util.ProofWanted` and of all of
Mathlib were replaced by narrower Mathlib imports, and the plain comment that repeated the
docstring of `strong_mason_conjecture` was dropped.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`strong_mason_conjecture`, the private definitions and lemmas it uses, the rest of the module
documentation and the linter options.
-/
module

public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.Set.PowersetCard
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The strong Mason conjecture

For a finite matroid, let `I k` be the number of independent sets of
cardinality `k`. Mason's strongest conjecture says that the normalized
sequence `I k / (n.choose k)` is log-concave, where `n` is the cardinality
of the ground set. Branden and Huh proved this using Lorentzian polynomials;
Anari, Liu, Oveis Gharan, and Vinzant obtained the result independently.

Mathlib supplies the matroid axioms and their independent-set API. The
inequality below clears the binomial denominators, so it can be stated
entirely in `Nat`.

This module proves the conjecture: `strong_mason_conjecture` is the ultra log-concavity of the
numbers `independentSetCount M k` of independent sets of each size `k`.

## Proof outline

We follow the strategy of Anari, Liu, Oveis Gharan and Vinzant. For a matroid `M` on a finite
type `β` with `n` elements, consider the homogenized generating polynomial
`g_M(y, z) = ∑_{I independent} y^(n - |I|) ∏_{i ∈ I} z_i`. A partial derivative of `g_M` is
recorded by a multi-index on `Option β`, where `none` stands for the variable `y`, and its value
at a point is an explicit sum over independent sets; no polynomial ring is used. A symmetric
matrix `H` is called hyperbolic if `(uᵀHu)(vᵀHv) ≤ (uᵀHv)²` whenever `uᵀHu > 0` (equivalently,
`H` has at most one positive eigenvalue, a fact we do not use). Hyperbolicity at a single vector
`x` with `xᵀHx > 0` implies hyperbolicity (as in the proof of Lemma 2.1 of their paper).

* Base case. The Hessian of a derivative of degree two is hyperbolic. Its nonzero part is indexed
  by `y` and the nonloops of a contraction `M ／ S`; hyperbolicity at `y` reduces, through the
  parallel classes of `M ／ S`, to the Cauchy–Schwarz inequality and the bound `n - |S|` on the
  number of classes (Lemma 4.2 of their paper).
* Local-to-global step. Let `f` be a derivative of degree `d ≥ 3`, let `x` be a positive point,
  and let `H` and `H_i` be the Hessians of `f` and of `∂_i f` at `x`. Euler's identity gives
  `(d - 2) H = ∑_i x_i H_i` and `H_i x = (d - 2) H e_i`; if every `H_i` is hyperbolic, this gives
  `vᵀHv ≤ ∑_i x_i (Hv)_i² / (Hx)_i`. With `δ_i = (Hx)_i / x_i`, the ground state identity gives
  `vᵀHv ≤ ∑_i δ_i v_i²`, and every variable that occurs is joined to `y`, as in the proof of
  Theorem 4.1 of their paper. Hence the kernel of `diag δ - H` is spanned by `x` on the support, a
  vector `v` with `xᵀHv = 0` can be written `v = z - δ⁻¹ H z`, and the two inequalities give
  `vᵀHv ≤ 0`. This elementary argument replaces their reduction to quadratics (Theorem 3.2).
* By induction on the degree, the Hessian of every derivative of degree at least two is
  hyperbolic at every positive point. We apply this to `∂_y^(n-k-1) g_M` at `(t, 1, …, 1)` with
  the vectors `(0, 1, …, 1)` and `(1, 0, …, 0)`, and let `t` tend to `0`. The three entries tend
  to `(n-k-1)! (k+1) k I_{k+1}`, `(n-k)! k I_k` and `(n-k+1)! I_{k-1}`, and the resulting
  determinant inequality is the claim (compare Proposition 5.1 of their paper).
* A matroid with a finite ground set is transported to the subtype of its ground set.

## Implementation notes

`independentSetCount` and `strong_mason_conjecture` keep the full names they had in the former
wanted module, so the namespace repeats `Combinatorics`; the `dupNamespace` linter is turned off
for these two declarations only.

## References

* P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Theorem 4.14, https://doi.org/10.4007/annals.2020.192.3.4.
* N. Anari, K. Liu, S. Oveis Gharan and C. Vinzant, *Log-concave polynomials III: Mason's
  ultra-log-concavity conjecture for independent sets of matroids*,
  https://arxiv.org/abs/1811.01600, Lemma 2.1, Theorem 3.2, Theorem 4.1, Lemma 4.2 and
  Proposition 5.1.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.StrongMasonWanted
namespace Combinatorics.StrongMason

set_option linter.dupNamespace false in
/-- **Number of independent sets of a given size.** For a finite matroid $M$ and a natural
number $k$, this is the number of independent sets of $M$ with exactly $k$ elements. -/
noncomputable def independentSetCount {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) : ℕ :=
  {I ∈ Set.powersetCard α k | M.Indep I}.ncard

open Matrix Finset

section Hyperbolic

variable {ι : Type*} [Fintype ι]

/-- The bilinear form `uᵀ H v` of a square matrix. -/
private def bil (H : Matrix ι ι ℝ) (u v : ι → ℝ) : ℝ := u ⬝ᵥ (H *ᵥ v)

/-- A matrix is hyperbolic if `(uᵀHu)(vᵀHv) ≤ (uᵀHv)²` whenever `uᵀHu > 0`; for symmetric
matrices this says that `H` has at most one positive eigenvalue. -/
private def Hyp (H : Matrix ι ι ℝ) : Prop :=
  ∀ u v, 0 < bil H u u → bil H u u * bil H v v ≤ bil H u v ^ 2

/-- The bilinear form of a symmetric matrix is symmetric. -/
private lemma bil_comm {H : Matrix ι ι ℝ} (hH : ∀ a b, H a b = H b a) (u v : ι → ℝ) :
    bil H u v = bil H v u := by
  simp only [bil, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hH]; ring

/-- Linearity of `bil` in the second argument. -/
private lemma bil_sub_smul (H : Matrix ι ι ℝ) (u v w : ι → ℝ) (r s : ℝ) :
    bil H u (r • v - s • w) = r * bil H u v - s * bil H u w := by
  simp [bil, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul]

/-- Linearity of `bil` in the first argument. -/
private lemma sub_smul_bil (H : Matrix ι ι ℝ) (u v w : ι → ℝ) (r s : ℝ) :
    bil H (r • v - s • w) u = r * bil H v u - s * bil H w u := by
  simp [bil, sub_dotProduct, smul_dotProduct]

/-- Hyperbolicity at a single vector `x` with `xᵀHx > 0` implies hyperbolicity: a binary
quadratic form that is positive definite would be positive on the `H`-orthogonal complement
of `x`. -/
private lemma hyp_of_hyp_at {H : Matrix ι ι ℝ} (hH : ∀ a b, H a b = H b a) {x : ι → ℝ}
    (hxx : 0 < bil H x x) (hx : ∀ v, bil H x x * bil H v v ≤ bil H x v ^ 2) : Hyp H := by
  intro u v hu
  set p := bil H x u
  set q := bil H x v
  have hz : bil H x (q • u - p • v) = 0 := by
    rw [bil_sub_smul]; ring
  have hzz := hx (q • u - p • v)
  rw [hz] at hzz
  have hzz' : bil H (q • u - p • v) (q • u - p • v) ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have hexp : bil H (q • u - p • v) (q • u - p • v) =
      q ^ 2 * bil H u u - 2 * p * q * bil H u v + p ^ 2 * bil H v v := by
    rw [bil_sub_smul, sub_smul_bil, sub_smul_bil, bil_comm hH v u]; ring
  have hp : p ≠ 0 := by
    intro hp0
    have := hx u
    rw [show bil H x u = p from rfl, hp0] at this
    nlinarith
  by_contra hcon
  push Not at hcon
  have key : bil H u u * bil H (q • u - p • v) (q • u - p • v) =
      (q * bil H u u - p * bil H u v) ^ 2 + p ^ 2 * (bil H u u * bil H v v - bil H u v ^ 2) := by
    rw [hexp]; ring
  have h1 : bil H u u * bil H (q • u - p • v) (q • u - p • v) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu.le hzz'
  have h2 : 0 < p ^ 2 * (bil H u u * bil H v v - bil H u v ^ 2) :=
    mul_pos (by positivity) (by linarith)
  nlinarith [sq_nonneg (q * bil H u u - p * bil H u v)]

/-- A symmetric linear system `L z = u` is solvable when `u` is orthogonal to the kernel of `L`:
a linear form vanishing on the range of `L` is given by a vector of the kernel. -/
private lemma exists_mulVec_eq {L : Matrix ι ι ℝ} (hL : ∀ a b, L a b = L b a)
    {u : ι → ℝ} (hu : ∀ z, L *ᵥ z = 0 → u ⬝ᵥ z = 0) : ∃ z, L *ᵥ z = u := by
  classical
  by_contra hne
  have hmem : u ∉ LinearMap.range (Matrix.mulVecLin L) := by
    rintro ⟨z, hz⟩
    exact hne ⟨z, hz⟩
  obtain ⟨f, hfu, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmem inferInstance
  set w : ι → ℝ := fun i => f (Pi.single i 1)
  have hfw : ∀ y, f y = w ⬝ᵥ y := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [dotProduct, smul_eq_mul, w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  have hLw : L *ᵥ w = 0 := by
    ext i
    have h1 : f (L *ᵥ Pi.single i 1) = 0 := by
      have hr : L *ᵥ Pi.single i 1 ∈ LinearMap.range (Matrix.mulVecLin L) := ⟨_, rfl⟩
      have := Submodule.mem_map_of_mem (f := f) hr
      rw [hf] at this
      simpa using this
    rw [hfw] at h1
    simp only [mulVec_single] at h1
    simpa [mulVec, dotProduct, hL i, mul_comm] using h1
  apply hfu
  rw [hfw, dotProduct_comm]
  exact hu w hLw


/-- The ground state identity: for a symmetric `H` and a positive vector `x`, with
`δ a = (Hx)_a / x_a`, the form `∑ δ a w_a² - wᵀHw` is a sum of the squares
`(w_a / x_a - w_b / x_b)²` weighted by `H a b x_a x_b / 2`. -/
private lemma ground_state {H : Matrix ι ι ℝ} (hHs : ∀ a b, H a b = H b a) {x : ι → ℝ}
    (hx : ∀ a, 0 < x a) (w : ι → ℝ) :
    2 * (∑ a, (H *ᵥ x) a / x a * w a ^ 2 - bil H w w) =
      ∑ a, ∑ b, H a b * x a * x b * (w a / x a - w b / x b) ^ 2 := by
  have per : ∀ a b, H a b * x a * x b * (w a / x a - w b / x b) ^ 2 =
      H a b * x b * w a ^ 2 / x a - 2 * (w a * (H a b * w b)) + H b a * x a * w b ^ 2 / x b := by
    intro a b
    have ha := (hx a).ne'
    have hb := (hx b).ne'
    rw [hHs b a]
    field_simp
    ring
  have h1 : ∀ a, ∑ b, H a b * x b * w a ^ 2 / x a = (H *ᵥ x) a / x a * w a ^ 2 := by
    intro a
    simp only [mulVec, dotProduct]
    rw [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
  have h2 : ∑ a, ∑ b, H b a * x a * w b ^ 2 / x b = ∑ a, (H *ᵥ x) a / x a * w a ^ 2 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => h1 a
  have h3 : ∑ a, ∑ b, 2 * (w a * (H a b * w b)) = 2 * bil H w w := by
    simp only [bil, dotProduct, mulVec, Finset.mul_sum]
  calc 2 * (∑ a, (H *ᵥ x) a / x a * w a ^ 2 - bil H w w)
      = ∑ a, ∑ b, H a b * x b * w a ^ 2 / x a - ∑ a, ∑ b, 2 * (w a * (H a b * w b)) +
          ∑ a, ∑ b, H b a * x a * w b ^ 2 / x b := by
        rw [h2, h3, Finset.sum_congr rfl fun a _ => h1 a]; ring
    _ = _ := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => (per a b).symm

/-- For a symmetric matrix with nonnegative entries, `wᵀHw ≤ ∑ δ a w_a²`. -/
private lemma bil_le_ground {H : Matrix ι ι ℝ} (hHs : ∀ a b, H a b = H b a) (hH0 : ∀ a b, 0 ≤ H a b)
    {x : ι → ℝ} (hx : ∀ a, 0 < x a) (w : ι → ℝ) :
    bil H w w ≤ ∑ a, (H *ᵥ x) a / x a * w a ^ 2 := by
  have := ground_state hHs hx w
  have hnn : 0 ≤ ∑ a, ∑ b, H a b * x a * x b * (w a / x a - w b / x b) ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (hH0 a b) (hx a).le) (hx b).le) (sq_nonneg _)
  linarith

/-- **Local-to-global step.** Let `H` be symmetric with nonnegative entries, let `x` be positive,
and let the matrices `T i` (the Hessians of the first derivatives) be hyperbolic, nonnegative
and related to `H` by the two Euler identities `∑ x_i T i = c H` and `T i x = c H e_i` for some
`c > 0`. If every index of the support of `H` is joined to the vertex `h`, then `H` is
hyperbolic. -/
private theorem hyp_of_local {H : Matrix ι ι ℝ} {T : ι → Matrix ι ι ℝ} {x : ι → ℝ}
    {c : ℝ} (h : ι)
    (hc : 0 < c) (hx : ∀ a, 0 < x a)
    (hHs : ∀ a b, H a b = H b a) (hH0 : ∀ a b, 0 ≤ H a b)
    (hT0 : ∀ i a b, 0 ≤ T i a b)
    (hE1 : ∀ a b, ∑ i, x i * T i a b = c * H a b)
    (hE2 : ∀ i b, ∑ a, x a * T i a b = c * H i b)
    (hT : ∀ i, Hyp (T i))
    (hconn : ∀ a, a ≠ h → (∃ b, 0 < H a b) → 0 < H h a) : Hyp H := by
  classical
  set y := H *ᵥ x with hy
  have hyn : ∀ a, 0 ≤ y a := fun a =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hH0 a b) (hx b).le
  -- a zero entry of `H x` forces a zero row
  have hrow : ∀ a, y a = 0 → ∀ b, H a b = 0 := by
    intro a ha b
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => mul_nonneg (hH0 a b) (hx b).le)).1 ha b (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_right (hx b).ne'
  have hpos_of : ∀ a b, H a b ≠ 0 → y a ≠ 0 := fun a b hab ha => hab (hrow a ha b)
  -- Step 1: the bound coming from the hyperbolicity of the `T i`
  have hTx : ∀ i w, bil (T i) x w = c * (H *ᵥ w) i := by
    intro i w
    simp only [bil, dotProduct, mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← hE2 i b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => by ring
  have hTzero : ∀ i, y i = 0 → ∀ a b, T i a b = 0 := by
    intro i hi a b
    have h0 : ∑ a, x a * ∑ b, T i a b * x b = 0 := by
      have := hTx i x
      rw [← hy, hi, mul_zero] at this
      simpa [bil, dotProduct, mulVec] using this
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => mul_nonneg (hx a).le
      (Finset.sum_nonneg fun b _ => mul_nonneg (hT0 i a b) (hx b).le))).1 h0 a
      (Finset.mem_univ _)
    have h2 := (mul_eq_zero.1 h1).resolve_left (hx a).ne'
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => mul_nonneg (hT0 i a b) (hx b).le)).1 h2 b (Finset.mem_univ _)
    exact (mul_eq_zero.1 h3).resolve_right (hx b).ne'
  have hbound : ∀ v i, x i * bil (T i) v v ≤ c * (x i * (H *ᵥ v) i ^ 2 / y i) := by
    intro v i
    rcases (hyn i).lt_or_eq with hpos | hzero
    · have hh := hT i x v (by rw [hTx]; positivity)
      rw [hTx, hTx] at hh
      rw [← mul_div_assoc, le_div_iff₀ hpos]
      have hxi := hx i
      have : c * y i * bil (T i) v v ≤ c * (c * (H *ᵥ v) i ^ 2) := by
        rw [hy]; nlinarith
      have h4 : y i * bil (T i) v v ≤ c * (H *ᵥ v) i ^ 2 := by
        rw [mul_assoc] at this
        exact le_of_mul_le_mul_left this hc
      nlinarith
    · have hz := hTzero i hzero.symm
      simp [bil, dotProduct, mulVec, hz, ← hzero]
  have hsum : ∀ v, c * bil H v v = ∑ i, x i * bil (T i) v v := by
    intro v
    calc c * bil H v v = ∑ a, ∑ b, v a * (c * H a b) * v b := by
          simp only [bil, dotProduct, mulVec, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ a, ∑ b, ∑ i, x i * (v a * T i a b * v b) := by
          simp_rw [← hE1, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ a, ∑ i, ∑ b, x i * (v a * T i a b * v b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, x i * (v a * T i a b * v b) := Finset.sum_comm
      _ = ∑ i, x i * bil (T i) v v := by
          simp only [bil, dotProduct, mulVec, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => by ring
  have step1 : ∀ v, bil H v v ≤ ∑ i, x i * (H *ᵥ v) i ^ 2 / y i := by
    intro v
    have h1 : c * bil H v v ≤ c * ∑ i, x i * (H *ᵥ v) i ^ 2 / y i := by
      rw [hsum, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hbound v i
    exact le_of_mul_le_mul_left h1 hc
  -- Step 2: ground state bound, with `δ a = y a / x a`
  set δ : ι → ℝ := fun a => y a / x a with hδ
  have step2 : ∀ w, bil H w w ≤ ∑ a, δ a * w a ^ 2 := bil_le_ground hHs hH0 hx
  -- Step 3: the kernel of `diag δ - H`
  have step3 : ∀ z : ι → ℝ, (∀ a, δ a * z a = (H *ᵥ z) a) →
      ∀ a, y a ≠ 0 → z a = z h / x h * x a := by
    intro z hz a ha
    have hgs := ground_state hHs hx z
    have hzero : ∑ a, δ a * z a ^ 2 - bil H z z = 0 := by
      simp only [bil, dotProduct]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← hz a]; ring
    rw [hzero, mul_zero] at hgs
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (hH0 a b) (hx a).le) (hx b).le) (sq_nonneg _))).1
      hgs.symm
    by_cases hah : a = h
    · subst hah; field_simp [(hx a).ne']
    · have hb : ∃ b, 0 < H a b := by
        by_contra hnb
        push Not at hnb
        exact ha (Finset.sum_eq_zero fun b _ => by
          simp [le_antisymm (hnb b) (hH0 a b)])
      have hha := hconn a hah hb
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
        mul_nonneg (mul_nonneg (mul_nonneg (hH0 h b) (hx h).le) (hx b).le) (sq_nonneg _))).1
        (hterm h (Finset.mem_univ _)) a (Finset.mem_univ _)
      have h2 : (z h / x h - z a / x a) ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h3 | h3
        · exfalso
          have : 0 < H h a * x h * x a := mul_pos (mul_pos hha (hx h)) (hx a)
          linarith
        · exact h3
      have h4 : z h / x h = z a / x a := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
      rw [h4]; field_simp [(hx a).ne']
  -- Step 4: solving `(diag δ - H) z = δ v` when `x ⊥_H v`
  have step4 : ∀ v, bil H x v = 0 → ∃ z : ι → ℝ, ∀ a, δ a * z a - (H *ᵥ z) a = δ a * v a := by
    intro v hv
    have hL : ∀ a b, (diagonal δ - H) a b = (diagonal δ - H) b a := by
      intro a b
      simp only [Matrix.sub_apply, Matrix.diagonal_apply]
      rw [hHs a b]
      by_cases hab : a = b
      · subst hab; rfl
      · simp [hab, Ne.symm hab]
    obtain ⟨z, hz⟩ := exists_mulVec_eq hL (u := fun a => δ a * v a) (by
      intro z hz
      have hz' : ∀ a, δ a * z a = (H *ᵥ z) a := by
        intro a
        have := congrFun hz a
        simp only [sub_mulVec, mulVec_diagonal, Pi.sub_apply, Pi.zero_apply] at this
        linarith
      have hk := step3 z hz'
      have : ∀ a, δ a * v a * z a = z h / x h * (v a * y a) := by
        intro a
        by_cases ha : y a = 0
        · simp [hδ, ha]
        · rw [hk a ha]
          simp only [hδ]
          field_simp [(hx a).ne']
      simp only [dotProduct]
      simp_rw [this, ← Finset.mul_sum]
      have hv' : ∑ a, v a * y a = 0 := by
        rw [← hv, bil_comm hHs]; rfl
      rw [hv', mul_zero])
    refine ⟨z, fun a => ?_⟩
    have := congrFun hz a
    simp only [sub_mulVec, mulVec_diagonal, Pi.sub_apply] at this
    exact this
  -- Step 5: nonpositivity on the `H`-orthogonal complement of `x`
  have step5 : ∀ v, bil H x v = 0 → bil H v v ≤ 0 := by
    intro v hv
    obtain ⟨z, hz⟩ := step4 v hv
    set p : ι → ℝ := fun a => (H *ᵥ z) a / δ a with hp
    have hv' : bil H v v = bil H (z - p) (z - p) := by
      simp only [bil, dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : H a b = 0
      · simp [hab]
      · have hya := hpos_of a b hab
        have hyb := hpos_of b a (by rw [hHs]; exact hab)
        have key : ∀ c, y c ≠ 0 → (z - p) c = v c := by
          intro c hc
          have hδc : δ c ≠ 0 := div_ne_zero hc (hx c).ne'
          have := hz c
          simp only [Pi.sub_apply, hp]
          field_simp
          linarith
        rw [key a hya, key b hyb]
    have hexp : bil H (z - p) (z - p) = bil H z z - 2 * bil H z p + bil H p p := by
      have h1 : z - p = (1 : ℝ) • z - (1 : ℝ) • p := by simp
      rw [h1, bil_sub_smul, sub_smul_bil, sub_smul_bil, bil_comm hHs p z]
      ring
    set R := ∑ a, (H *ᵥ z) a ^ 2 / δ a with hR
    have hzp : bil H z p = R := by
      rw [bil_comm hHs]
      simp only [bil, dotProduct, hp, hR]
      refine Finset.sum_congr rfl fun a _ => by ring
    have hzz : bil H z z ≤ R := by
      refine (step1 z).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
      simp only [hδ]
      by_cases ha : y a = 0
      · simp [ha]
      · field_simp [(hx a).ne']
    have hpp : bil H p p ≤ R := by
      refine (step2 p).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
      simp only [hp]
      by_cases ha : δ a = 0
      · simp [ha]
      · field_simp
    rw [hv', hexp]
    linarith
  -- Step 6: conclusion
  by_cases hxx : bil H x x = 0
  · have hy0 : ∀ a, y a = 0 := by
      intro a
      simp only [bil, dotProduct] at hxx
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => mul_nonneg (hx a).le (hyn a))).1
        hxx a (Finset.mem_univ _)
      exact (mul_eq_zero.1 this).resolve_left (hx a).ne'
    intro u v hu
    exfalso
    have : bil H u u = 0 := by
      simp [bil, dotProduct, mulVec, hrow _ (hy0 _)]
    linarith
  · have hxx' : 0 < bil H x x := by
      refine lt_of_le_of_ne ?_ (Ne.symm hxx)
      exact Finset.sum_nonneg fun a _ => mul_nonneg (hx a).le (hyn a)
    refine hyp_of_hyp_at hHs hxx' fun v => ?_
    set κ := bil H x v / bil H x x
    have hw : bil H x (v - κ • x) = 0 := by
      have : v - κ • x = (1 : ℝ) • v - κ • x := by simp
      rw [this, bil_sub_smul]
      simp only [κ]
      rw [div_mul_cancel₀ _ hxx]
      ring
    have hww := step5 _ hw
    have hexp : bil H v v = bil H (v - κ • x) (v - κ • x) + κ ^ 2 * bil H x x := by
      have : v - κ • x = (1 : ℝ) • v - κ • x := by simp
      rw [this, bil_sub_smul, sub_smul_bil, sub_smul_bil, bil_comm hHs v x]
      have hw' := hw
      rw [this, bil_sub_smul] at hw'
      linear_combination (2 * κ) * hw'
    rw [hexp]
    have : κ ^ 2 * bil H x x * bil H x x = bil H x v ^ 2 := by
      simp only [κ]; field_simp
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hxx'.le hww]

end Hyperbolic

section Derivatives


variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The multi-index `s` uses each variable `z_i` at most once, and only for `i ∈ A`; otherwise the
derivative `∂^s` kills the monomial `y^(n - |A|) z^A`. -/
private def Fits (s : Option β → ℕ) (A : Finset β) : Prop :=
  ∀ i, s (some i) ≤ if i ∈ A then 1 else 0

/-- The value at `x` of `∂^s (y^(n - |A|) z^A)` when `Fits s A`. -/
private noncomputable def termCore (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β) : ℝ :=
  ((Fintype.card β - #A).descFactorial (s none) : ℝ) *
    (∏ i ∈ A, if s (some i) = 0 then x (some i) else 1) *
    x none ^ (Fintype.card β - #A - s none)

open Classical in
/-- The value at `x` of `∂^s (y^(n - |A|) z^A)`. -/
private noncomputable def term (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β) : ℝ :=
  if Fits s A then termCore x s A else 0

/-- Add one derivative in the variable `a`. -/
private def bump (s : Option β → ℕ) (a : Option β) : Option β → ℕ :=
  fun b => s b + if b = a then 1 else 0

omit [Fintype β] in
@[simp] private lemma bump_none_none (s : Option β → ℕ) : bump s none none = s none + 1 := by
  simp [bump]

omit [Fintype β] in
@[simp] private lemma bump_none_some (s : Option β → ℕ) (i : β) :
    bump s none (some i) = s (some i) := by
  simp [bump]

omit [Fintype β] in
@[simp] private lemma bump_some_none (s : Option β → ℕ) (i : β) :
    bump s (some i) none = s none := by
  simp [bump]

omit [Fintype β] in
@[simp] private lemma bump_some_some (s : Option β → ℕ) (i j : β) :
    bump s (some i) (some j) = s (some j) + if j = i then 1 else 0 := by
  simp [bump]

omit [Fintype β] in
private lemma bump_comm (s : Option β → ℕ) (a b : Option β) :
    bump (bump s a) b = bump (bump s b) a := by
  funext c; simp only [bump]; omega

private lemma sum_bump (s : Option β → ℕ) (a : Option β) : ∑ b, bump s a b = ∑ b, s b + 1 := by
  simp [bump, Finset.sum_add_distrib]

omit [Fintype β] in
private lemma fits_bump_none {s : Option β → ℕ} {A : Finset β} :
    Fits (bump s none) A ↔ Fits s A := by
  simp [Fits]

omit [Fintype β] in
private lemma fits_bump_some {s : Option β → ℕ} {A : Finset β} {i : β} :
    Fits (bump s (some i)) A ↔ Fits s A ∧ i ∈ A ∧ s (some i) = 0 := by
  constructor
  · intro h
    have hi := h i
    simp only [bump_some_some, ↓reduceIte] at hi
    refine ⟨fun j => (Nat.le_add_right _ _).trans ((bump_some_some s i j) ▸ h j), ?_, ?_⟩
    · by_contra hA; simp [hA] at hi
    · split_ifs at hi <;> omega
  · rintro ⟨h, hA, hs⟩ j
    simp only [bump_some_some]
    by_cases hj : j = i
    · subst hj; simp [hA, hs]
    · simpa [hj] using h j

/-- Differentiating in `y` lowers the power of `y` and multiplies by its exponent. -/
private lemma termCore_bump_none (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β) :
    x none * termCore x (bump s none) A =
      ((Fintype.card β - #A - s none : ℕ) : ℝ) * termCore x s A := by
  simp only [termCore, bump_none_none, bump_none_some]
  rw [Nat.descFactorial_succ]
  rcases Nat.lt_or_ge (s none) (Fintype.card β - #A) with hjm | hjm
  · have : Fintype.card β - #A - s none = Fintype.card β - #A - (s none + 1) + 1 := by omega
    rw [this, pow_succ]
    push_cast
    ring
  · have : Fintype.card β - #A - s none = 0 := by omega
    simp [this]

/-- Differentiating in `z_i`, for `i ∈ A` not yet used, removes the factor `z_i`. -/
private lemma termCore_bump_some (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β) {i : β}
    (hi : i ∈ A) (hs : s (some i) = 0) :
    x (some i) * termCore x (bump s (some i)) A = termCore x s A := by
  simp only [termCore, bump_some_none, bump_some_some]
  have hprod : x (some i) * ∏ i' ∈ A, (if s (some i') + (if i' = i then 1 else 0) = 0
      then x (some i') else 1) = ∏ i' ∈ A, (if s (some i') = 0 then x (some i') else 1) := by
    rw [← Finset.mul_prod_erase A _ hi, ← Finset.mul_prod_erase A _ hi]
    simp only [hs, ↓reduceIte, zero_add, one_ne_zero, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun i' hi' => ?_
    simp [Finset.ne_of_mem_erase hi']
  rw [← hprod]
  ring

omit [DecidableEq β] in
private lemma termCore_eq_zero (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β)
    (h : Fintype.card β - #A < s none) : termCore x s A = 0 := by
  simp [termCore, Nat.descFactorial_eq_zero_iff_lt.2 h]

/-- Euler's identity for one monomial: `∑_a x_a ∂_a ∂^s m = (n - |s|) ∂^s m` at `x`. -/
private lemma euler_term (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β) :
    ∑ a, x a * term x (bump s a) A =
      ((Fintype.card β - ∑ a, s a : ℕ) : ℝ) * term x s A := by
  classical
  rw [Fintype.sum_option]
  by_cases hF : Fits s A
  swap
  · have h1 : ¬ Fits (bump s none) A := fun h => hF (fits_bump_none.1 h)
    have h2 : ∀ i, ¬ Fits (bump s (some i)) A := fun i h => hF (fits_bump_some.1 h).1
    simp [term, h1, h2, hF]
  have hnone : x none * term x (bump s none) A =
      ((Fintype.card β - #A - s none : ℕ) : ℝ) * termCore x s A := by
    simp only [term, fits_bump_none.2 hF, ↓reduceIte]
    exact termCore_bump_none x s A
  have hsome : ∀ i, x (some i) * term x (bump s (some i)) A =
      if i ∈ A ∧ s (some i) = 0 then termCore x s A else 0 := by
    intro i
    by_cases hc : i ∈ A ∧ s (some i) = 0
    · simp only [hc, and_self, ↓reduceIte, term, fits_bump_some.2 ⟨hF, hc⟩]
      exact termCore_bump_some x s A hc.1 hc.2
    · simp only [hc, ↓reduceIte]
      have : ¬ Fits (bump s (some i)) A := fun h => hc (fits_bump_some.1 h).2
      simp [term, this]
  simp only [hnone, hsome]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [term, hF, ↓reduceIte]
  have hcount : #(Finset.univ.filter fun i => i ∈ A ∧ s (some i) = 0) + ∑ i, s (some i) = #A := by
    have h1 : #(Finset.univ.filter fun i => i ∈ A ∧ s (some i) = 0) =
        ∑ i, if i ∈ A ∧ s (some i) = 0 then 1 else 0 := by
      rw [Finset.sum_boole]; simp
    have hcardA : #A = ∑ i, if i ∈ A then 1 else 0 := by
      rw [Fintype.sum_ite_mem, Finset.card_eq_sum_ones]
    rw [h1, ← Finset.sum_add_distrib, hcardA]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hF i
    by_cases hA : i ∈ A
    · simp only [hA, ↓reduceIte, true_and] at hi ⊢
      by_cases h0 : s (some i) = 0
      · simp [h0]
      · simp [h0]; omega
    · simp only [hA, ↓reduceIte, false_and] at hi ⊢
      omega
  have hsum : ∑ a, s a = s none + ∑ i, s (some i) := by
    rw [Fintype.sum_option]
  have hA : #A ≤ Fintype.card β := Finset.card_le_univ A
  rcases Nat.lt_or_ge (Fintype.card β - #A) (s none) with hmj | hmj
  · simp [termCore_eq_zero x s A hmj]
  · have : Fintype.card β - ∑ a, s a =
        (Fintype.card β - #A - s none) + #(Finset.univ.filter fun i => i ∈ A ∧ s (some i) = 0) := by
      omega
    rw [this]
    push_cast
    ring

open Classical in
/-- The value at `x` of the derivative `∂^s g_M` of the homogenized generating polynomial
`g_M = ∑_{A independent} y^(n - |A|) z^A`. -/
private noncomputable def val (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A : Finset β => M.Indep (A : Set β)), term x s A

/-- Euler's identity for the derivatives of `g_M`, which are homogeneous of degree `n - |s|`. -/
private lemma euler (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ) :
    ∑ a, x a * val M x (bump s a) =
      ((Fintype.card β - ∑ a, s a : ℕ) : ℝ) * val M x s := by
  simp only [val, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun A _ => euler_term x s A


omit [DecidableEq β] in
private lemma termCore_nonneg {x : Option β → ℝ} (hx : ∀ a, 0 ≤ x a) (s : Option β → ℕ)
    (A : Finset β) :
    0 ≤ termCore x s A := by
  unfold termCore
  refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ => ?_))
    (pow_nonneg (hx none) _)
  split_ifs
  · exact hx _
  · exact zero_le_one

private lemma term_nonneg {x : Option β → ℝ} (hx : ∀ a, 0 ≤ x a) (s : Option β → ℕ) (A : Finset β) :
    0 ≤ term x s A := by
  unfold term
  split_ifs
  · exact termCore_nonneg hx s A
  · exact le_rfl

private lemma val_nonneg (M : Matroid β) {x : Option β → ℝ} (hx : ∀ a, 0 ≤ x a) (s : Option β → ℕ) :
    0 ≤ val M x s :=
  Finset.sum_nonneg fun A _ => term_nonneg hx s A

omit [DecidableEq β] in
private lemma termCore_pos {x : Option β → ℝ} (hx : ∀ a, 0 < x a) {s : Option β → ℕ} {A : Finset β}
    (h : s none ≤ Fintype.card β - #A) : 0 < termCore x s A := by
  unfold termCore
  refine mul_pos (mul_pos ?_ (Finset.prod_pos fun i _ => ?_)) (pow_pos (hx none) _)
  · exact_mod_cast Nat.descFactorial_pos.2 h
  · split_ifs
    · exact hx _
    · exact one_pos

/-- At a positive point, `∂^s g_M` is positive exactly when some independent set survives. -/
private lemma val_pos_iff (M : Matroid β) {x : Option β → ℝ} (hx : ∀ a, 0 < x a)
    (s : Option β → ℕ) :
    0 < val M x s ↔
      ∃ A : Finset β, M.Indep (A : Set β) ∧ Fits s A ∧ s none ≤ Fintype.card β - #A := by
  classical
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine (lt_irrefl (0 : ℝ)) (h.trans_le (Finset.sum_nonpos fun A hA => ?_))
    have hA' := (Finset.mem_filter.1 hA).2
    unfold term
    split_ifs with hF
    · by_cases hle : s none ≤ Fintype.card β - #A
      · exact absurd hle (not_le.2 (hne A hA' hF))
      · rw [termCore_eq_zero x s A (not_le.1 hle)]
    · exact le_rfl
  · rintro ⟨A, hA, hF, hle⟩
    have hpos : 0 < term x s A := by
      simp only [term, hF, ↓reduceIte]
      exact termCore_pos hx hle
    exact hpos.trans_le (Finset.single_le_sum (f := fun A => term x s A)
      (fun A _ => term_nonneg (fun a => (hx a).le) s A) (by simpa using hA))

/-- The Hessian at `x` of the derivative `∂^s g_M`. -/
private noncomputable def hess (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ) :
    Matrix (Option β) (Option β) ℝ :=
  fun a b => val M x (bump (bump s a) b)

private lemma hess_symm (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ) (a b : Option β) :
    hess M x s a b = hess M x s b a := by
  simp only [hess, bump_comm]

/-- Every variable occurring in the Hessian is joined to `y`: the support is a star centred at
`y`, as in the proof of Theorem 4.1 of Anari, Liu, Oveis Gharan and Vinzant. -/
private lemma hess_conn (M : Matroid β) {x : Option β → ℝ} (hx : ∀ a, 0 < x a) (s : Option β → ℕ)
    (a : Option β) (ha : a ≠ none) (hb : ∃ b, 0 < hess M x s a b) : 0 < hess M x s none a := by
  obtain ⟨b, hb⟩ := hb
  cases a with
  | none => exact absurd rfl ha
  | some i =>
  cases b with
  | none =>
    rw [hess_symm]
    exact hb
  | some i' =>
    obtain ⟨A, hA, hF, hle⟩ := (val_pos_iff M hx _).1 hb
    obtain ⟨hF1, hi'A, hs'⟩ := fits_bump_some.1 hF
    obtain ⟨hF0, hiA, hs⟩ := fits_bump_some.1 hF1
    simp only [bump_some_some] at hs'
    have hii' : i' ≠ i := by intro h; simp [h] at hs'
    have hs'0 : s (some i') = 0 := by simpa [hii'] using hs'
    simp only [bump_some_none] at hle
    refine (val_pos_iff M hx _).2 ⟨A.erase i', hA.subset (by simp [Set.sdiff_subset]), ?_, ?_⟩
    · refine fits_bump_some.2 ⟨fits_bump_none.2 fun j => ?_, Finset.mem_erase.2 ⟨hii'.symm, hiA⟩,
        by simpa using hs⟩
      by_cases hj : j = i'
      · subst hj; simp [hs'0]
      · simpa [Finset.mem_erase, hj] using hF0 j
    · have h1 := Finset.card_erase_of_mem hi'A
      have h2 : #A ≤ Fintype.card β := Finset.card_le_univ A
      have h3 : 0 < #A := Finset.card_pos.2 ⟨i', hi'A⟩
      simp only [bump_some_none, bump_none_none]
      omega

/-- A derivative of top order `n` is the constant `(s none)!` on the monomial it selects. -/
private lemma term_top (x : Option β → ℝ) (s : Option β → ℕ) (A : Finset β)
    (hs : ∑ a, s a = Fintype.card β) :
    term x s A = if ∀ i, s (some i) = if i ∈ A then 1 else 0 then ((s none).factorial : ℝ)
      else 0 := by
  classical
  have hcardA : #A = ∑ i, if i ∈ A then 1 else 0 := by
    rw [Fintype.sum_ite_mem, Finset.card_eq_sum_ones]
  rw [Fintype.sum_option] at hs
  by_cases hc : ∀ i, s (some i) = if i ∈ A then 1 else 0
  · have hF : Fits s A := fun i => (hc i).le
    have hsum : ∑ i, s (some i) = #A := by
      rw [hcardA]; exact Finset.sum_congr rfl fun i _ => hc i
    have hnone : s none = Fintype.card β - #A := by omega
    rw [ite_eq_left hc]
    simp only [term, hF, ↓reduceIte, termCore]
    rw [Finset.prod_eq_one (fun i hi => by simp [hc i, hi]), ← hnone, Nat.descFactorial_self,
      Nat.sub_self, pow_zero, mul_one, mul_one]
  · simp only [hc, ↓reduceIte]
    unfold term
    split_ifs with hF
    · apply termCore_eq_zero
      have hlt : ∑ i, s (some i) < ∑ i, (if i ∈ A then 1 else 0) := by
        push Not at hc
        obtain ⟨i, hi⟩ := hc
        exact Finset.sum_lt_sum (fun i _ => hF i) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hF i) hi⟩
      rw [← hcardA] at hlt
      have := Finset.card_le_univ A
      omega
    · rfl

open Classical in
/-- A derivative of top order `n` of `g_M` is `(s none)!` if the variables `z_i` it uses form an
independent set, each used once, and zero otherwise. -/
private lemma val_top (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ)
    (hs : ∑ a, s a = Fintype.card β) :
    val M x s = if (∀ i, s (some i) ≤ 1) ∧
        M.Indep ((Finset.univ.filter fun i => s (some i) = 1 : Finset β) : Set β) then
      ((s none).factorial : ℝ) else 0 := by
  classical
  have hiff : ∀ A : Finset β, (∀ i, s (some i) = if i ∈ A then 1 else 0) ↔
      (∀ i, s (some i) ≤ 1) ∧ (Finset.univ.filter fun i => s (some i) = 1) = A := by
    intro A
    constructor
    · intro h
      refine ⟨fun i => by rw [h i]; split_ifs <;> omega, ?_⟩
      ext i
      rw [Finset.mem_filter, h i]
      split_ifs with hi <;> simp [hi]
    · rintro ⟨h1, rfl⟩ i
      have := h1 i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with hi
      · exact hi
      · omega
  simp only [val, term_top x s _ hs]
  simp_rw [hiff]
  by_cases h1 : ∀ i, s (some i) ≤ 1
  · simp only [h1, implies_true, true_and]
    rw [Finset.sum_ite_eq]
    simp
  · simp only [h1, false_and, ↓reduceIte]
    simp

end Derivatives

section BaseCase

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The zero matrix is hyperbolic. -/
private lemma hyp_of_zero {ι : Type*} [Fintype ι] {H : Matrix ι ι ℝ} (h : ∀ a b, H a b = 0) :
    Hyp H := by
  intro u v hu
  exfalso
  have : bil H u u = 0 := by simp [bil, dotProduct, mulVec, h]
  linarith

/-- `∂^s g_M` vanishes when no independent set fits `s`. -/
private lemma val_eq_zero (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ)
    (h : ∀ A : Finset β, M.Indep (A : Set β) → ¬ Fits s A) : val M x s = 0 := by
  classical
  refine Finset.sum_eq_zero fun A hA => ?_
  simp [term, h A (Finset.mem_filter.1 hA).2]

omit [Fintype β] [DecidableEq β] in
/-- Two nonloops `i`, `i'` of `M ／ S` are independent together exactly when they lie in
different parallel classes, that is when the closures of `S ∪ {i}` and `S ∪ {i'}` differ. -/
private lemma pair_iff_closure (M : Matroid β) (S : Set β) {i i' : β}
    (hi : i ∉ S ∧ M.Indep (insert i S)) (hi' : i' ∉ S ∧ M.Indep (insert i' S)) :
    (i ≠ i' ∧ M.Indep (insert i (insert i' S))) ↔
      M.closure (insert i S) ≠ M.closure (insert i' S) := by
  constructor
  · rintro ⟨hne, hind⟩ heq
    have h1 : i ∈ M.closure (insert i S) :=
      M.subset_closure _ hi.2.subset_ground (Set.mem_insert _ _)
    rw [heq] at h1
    rcases (hi'.2.mem_closure_iff).1 h1 with hdep | hmem
    · exact hdep.not_indep hind
    · rcases hmem with h | h
      · exact hne h
      · exact hi.1 h
  · intro hne
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    by_contra hind
    have hE : insert i (insert i' S) ⊆ M.E :=
      Set.insert_subset (hi.2.subset_ground (Set.mem_insert _ _)) hi'.2.subset_ground
    have hdep : M.Dep (insert i (insert i' S)) := (M.not_indep_iff hE).1 hind
    have h1 : i ∈ M.closure (insert i' S) := hi'.2.mem_closure_iff.2 (Or.inl hdep)
    have hdep' : M.Dep (insert i' (insert i S)) := by rwa [Set.insert_comm]
    have h2 : i' ∈ M.closure (insert i S) := hi.2.mem_closure_iff.2 (Or.inl hdep')
    apply hne
    apply subset_antisymm
    · apply M.closure_subset_closure_of_subset_closure
      exact Set.insert_subset h1
        ((Set.subset_insert _ _).trans (M.subset_closure _ hi'.2.subset_ground))
    · apply M.closure_subset_closure_of_subset_closure
      exact Set.insert_subset h2
        ((Set.subset_insert _ _).trans (M.subset_closure _ hi.2.subset_ground))

open Classical in
/-- The inequality behind the base case: by Cauchy–Schwarz over the parallel classes of
`M ／ S`, of which there are at most `n - |S| = j + 2`, the pairs of nonloops that are
independent in `M ／ S` satisfy `(j + 2) ∑ w_i w_i' ≤ (j + 1) (∑ w_i)²`. -/
private lemma comb_ineq (M : Matroid β) (S : Finset β) (j : ℕ) (hj : #S + j + 2 = Fintype.card β)
    (w : β → ℝ) :
    (j + 2 : ℝ) * ∑ i, ∑ i', (if i ≠ i' ∧ i ∉ S ∧ i' ∉ S ∧
        M.Indep (insert i (insert i' (S : Set β))) then w i * w i' else 0) ≤
      (j + 1 : ℝ) * (∑ i, if i ∉ S ∧ M.Indep (insert i (S : Set β)) then w i else 0) ^ 2 := by
  set NL : Finset β := Finset.univ.filter fun i => i ∉ S ∧ M.Indep (insert i (S : Set β))
  set c : β → Set β := fun i => M.closure (insert i (S : Set β))
  have hterm : ∀ i i', (if i ≠ i' ∧ i ∉ S ∧ i' ∉ S ∧ M.Indep (insert i (insert i' (S : Set β)))
      then w i * w i' else 0) = if i ∈ NL then (if i' ∈ NL then
        (w i * w i' - if c i = c i' then w i * w i' else 0) else 0) else 0 := by
    intro i i'
    by_cases hi : i ∈ NL
    · by_cases hi' : i' ∈ NL
      · have h1 := (Finset.mem_filter.1 hi).2
        have h2 := (Finset.mem_filter.1 hi').2
        have key := pair_iff_closure M (S : Set β) h1 h2
        simp only [hi, hi', ↓reduceIte]
        by_cases hcc : c i = c i'
        · have : ¬ (i ≠ i' ∧ M.Indep (insert i (insert i' (S : Set β)))) :=
            fun h => key.1 h hcc
          rw [ite_eq_right (by tauto), ite_eq_left hcc, sub_self]
        · have : i ≠ i' ∧ M.Indep (insert i (insert i' (S : Set β))) := key.2 hcc
          rw [ite_eq_left ⟨this.1, h1.1, h2.1, this.2⟩, ite_eq_right hcc, sub_zero]
      · simp only [hi, hi', ↓reduceIte]
        refine ite_eq_right fun h => hi' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2.2.1,
          h.2.2.2.subset (Set.subset_insert _ _)⟩)
    · simp only [hi, ↓reduceIte]
      refine ite_eq_right fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2.1,
        h.2.2.2.subset (by
          rw [Set.insert_comm]; exact Set.subset_insert _ _)⟩)
  simp_rw [hterm]
  have hdouble : ∀ G : β → β → ℝ, (∑ i, ∑ i', if i ∈ NL then (if i' ∈ NL then G i i' else 0)
      else 0) = ∑ i ∈ NL, ∑ i' ∈ NL, G i i' := by
    intro G
    rw [← Fintype.sum_ite_mem NL (fun i => ∑ i' ∈ NL, G i i')]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ NL
    · simp only [hi, ↓reduceIte]; rw [Fintype.sum_ite_mem]
    · simp [hi]
  rw [hdouble]
  have hsigma : (∑ i, if i ∉ S ∧ M.Indep (insert i (S : Set β)) then w i else 0) =
      ∑ i ∈ NL, w i := by
    rw [← Fintype.sum_ite_mem NL w]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [NL]
  rw [hsigma]
  simp_rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul_sum, ← sq]
  set Q := ∑ i ∈ NL, ∑ i' ∈ NL, if c i = c i' then w i * w i' else 0
  set σ : Set β → ℝ := fun κ => ∑ i ∈ NL with c i = κ, w i
  have hmaps : ∀ i ∈ NL, c i ∈ NL.image c := fun i hi => Finset.mem_image_of_mem c hi
  have hSig : ∑ i ∈ NL, w i = ∑ κ ∈ NL.image c, σ κ :=
    (Finset.sum_fiberwise_of_maps_to hmaps w).symm
  have hQ : Q = ∑ κ ∈ NL.image c, σ κ ^ 2 := by
    have h1 : Q = ∑ i ∈ NL, w i * σ (c i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [σ]
      rw [Finset.mul_sum, Finset.sum_filter (s := NL)]
      refine Finset.sum_congr rfl fun i' _ => ?_
      by_cases h : c i = c i'
      · simp [h]
      · simp [h, Ne.symm h]
    rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2, mul_comm]
  have hcs := sq_sum_le_card_mul_sum_sq (s := NL.image c) (f := σ)
  rw [← hSig, ← hQ] at hcs
  have hcard : (#(NL.image c) : ℝ) ≤ j + 2 := by
    have h1 : #(NL.image c) ≤ #NL := Finset.card_image_le
    have h2 : #NL ≤ #(Finset.univ \ S) := Finset.card_le_card fun i hi => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.1 hi).2.1
    have h3 : #(Finset.univ \ S) = Fintype.card β - #S := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
    have : #(NL.image c) ≤ j + 2 := by omega
    exact_mod_cast this
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg fun κ _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hcard hQ0]

/-- **Base case.** The Hessian of a derivative of `g_M` of degree two is hyperbolic (Lemma 4.2
of Anari, Liu, Oveis Gharan and Vinzant). -/
private theorem hyp_base (M : Matroid β) (x : Option β → ℝ) (s : Option β → ℕ)
    (hs : ∑ a, s a + 2 = Fintype.card β) : Hyp (hess M x s) := by
  classical
  by_cases h2 : ∃ i, 2 ≤ s (some i)
  · obtain ⟨i, hi⟩ := h2
    refine hyp_of_zero fun a b => val_eq_zero M x _ fun A _ hF => ?_
    have h := hF i
    have hge : s (some i) ≤ bump (bump s a) b (some i) := by simp only [bump]; omega
    split_ifs at h <;> omega
  push Not at h2
  set S : Finset β := Finset.univ.filter fun i => s (some i) = 1 with hSdef
  have hsS : ∀ i, s (some i) = if i ∈ S then 1 else 0 := by
    intro i
    have := h2 i
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  have hcardS : ∑ i, s (some i) = #S := by
    rw [Finset.sum_congr rfl fun i _ => hsS i, Fintype.sum_ite_mem, Finset.card_eq_sum_ones]
  have hjS : #S + s none + 2 = Fintype.card β := by
    rw [Fintype.sum_option] at hs; omega
  by_cases hSi : M.Indep (S : Set β)
  swap
  · refine hyp_of_zero fun a b => val_eq_zero M x _ fun A hA hF => hSi (hA.subset ?_)
    intro i hi
    have h1 : s (some i) = 1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have h := hF i
    have hge : s (some i) ≤ bump (bump s a) b (some i) := by simp only [bump]; omega
    by_contra hiA
    rw [ite_eq_right (by simpa using hiA)] at h
    omega
  set j := s none with hj
  have hsum2 : ∀ a b, ∑ c, bump (bump s a) b c = Fintype.card β := by
    intro a b; rw [sum_bump, sum_bump]; omega
  have hNN : hess M x s none none = ((j + 2).factorial : ℝ) := by
    rw [hess, val_top M x _ (hsum2 none none)]
    have hfilt : (Finset.univ.filter fun i => bump (bump s none) none (some i) = 1) = S := by
      ext i; simp [hSdef]
    rw [hfilt, ite_eq_left ⟨fun i => by simpa using h2 i, hSi⟩]
    simp [hj]
  have hNS : ∀ i, hess M x s none (some i) =
      if i ∉ S ∧ M.Indep (insert i (S : Set β)) then ((j + 1).factorial : ℝ) else 0 := by
    intro i
    rw [hess, val_top M x _ (hsum2 none (some i))]
    by_cases hiS : i ∈ S
    · have : ¬ ∀ i', bump (bump s none) (some i) (some i') ≤ 1 := by
        intro h; have := h i; simp [hsS, hiS] at this
      rw [ite_eq_right (fun h => this h.1), ite_eq_right (fun h => h.1 hiS)]
    · have hcond : ∀ i', bump (bump s none) (some i) (some i') ≤ 1 := by
        intro i'
        simp only [bump_some_some, bump_none_some, hsS]
        by_cases h : i' = i
        · subst h; simp [hiS]
        · simp only [h, ↓reduceIte, add_zero]; split_ifs <;> omega
      have hfilt : (Finset.univ.filter fun i' => bump (bump s none) (some i) (some i') = 1) =
          insert i S := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          bump_some_some, bump_none_some, hsS]
        by_cases h : i' = i
        · subst h; simp [hiS]
        · simp [h]
      rw [hfilt]
      by_cases hind : M.Indep (insert i (S : Set β))
      · rw [ite_eq_left ⟨hcond, by simpa using hind⟩, ite_eq_left ⟨hiS, hind⟩]
        simp [hj]
      · rw [ite_eq_right (fun h => hind (by simpa using h.2)), ite_eq_right (fun h => hind h.2)]
  have hSS : ∀ i i', hess M x s (some i) (some i') =
      if i ≠ i' ∧ i ∉ S ∧ i' ∉ S ∧ M.Indep (insert i (insert i' (S : Set β))) then
        (j.factorial : ℝ) else 0 := by
    intro i i'
    rw [hess, val_top M x _ (hsum2 (some i) (some i'))]
    by_cases hc : i ≠ i' ∧ i ∉ S ∧ i' ∉ S
    · obtain ⟨hne, hiS, hi'S⟩ := hc
      have hcond : ∀ i'', bump (bump s (some i)) (some i') (some i'') ≤ 1 := by
        intro i''
        simp only [bump_some_some, hsS]
        by_cases h : i'' = i
        · subst h; simp [hiS, hne]
        · by_cases h' : i'' = i'
          · subst h'; simp [hi'S, h]
          · simp only [h, h', ↓reduceIte, add_zero]; split_ifs <;> omega
      have hfilt : (Finset.univ.filter fun i'' =>
          bump (bump s (some i)) (some i') (some i'') = 1) = insert i (insert i' S) := by
        ext i''
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          bump_some_some, hsS]
        by_cases h : i'' = i
        · subst h; simp [hiS, hne]
        · by_cases h' : i'' = i'
          · subst h'; simp [hi'S, h]
          · simp [h, h']
      rw [hfilt]
      by_cases hind : M.Indep (insert i (insert i' (S : Set β)))
      · rw [ite_eq_left ⟨hcond, by simpa using hind⟩, ite_eq_left ⟨hne, hiS, hi'S, hind⟩]
        simp [hj]
      · rw [ite_eq_right (fun h => hind (by simpa using h.2)),
          ite_eq_right (fun h => hind h.2.2.2)]
    · have : ¬ ∀ i'', bump (bump s (some i)) (some i') (some i'') ≤ 1 := by
        intro h
        apply hc
        refine ⟨fun hii => ?_, fun hiS => ?_, fun hi'S => ?_⟩
        · have := h i; subst hii; simp at this
        · have := h i
          simp [hsS, hiS] at this
          split_ifs at this <;> omega
        · have := h i'
          simp [hsS, hi'S] at this
      rw [ite_eq_right (fun h => this h.1), ite_eq_right (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩)]
  -- hyperbolicity at the vertex `none`
  set e0 : Option β → ℝ := fun a => if a = none then 1 else 0 with he0
  set H := hess M x s with hH
  have hbil0 : ∀ v, bil H e0 v = H none none * v none + ∑ i, H none (some i) * v (some i) := by
    intro v
    simp [bil, dotProduct, mulVec, Fintype.sum_option, he0]
  have hbilv : ∀ v, bil H v v = v none * (H none none * v none +
      ∑ i, H none (some i) * v (some i)) + ∑ i, v (some i) * (H none (some i) * v none +
        ∑ i', H (some i) (some i') * v (some i')) := by
    intro v
    simp only [bil, dotProduct, mulVec, Fintype.sum_option]
    congr 1
  refine hyp_of_hyp_at (hess_symm M x s) (x := e0) ?_ fun v => ?_
  · rw [hbil0]
    simp only [he0, ↓reduceIte, reduceCtorEq, mul_zero, Finset.sum_const_zero, add_zero, mul_one,
      hNN]
    positivity
  have h00 : bil H e0 e0 = ((j + 2).factorial : ℝ) := by
    rw [hbil0]
    simp only [he0, ↓reduceIte, reduceCtorEq, mul_zero, Finset.sum_const_zero, add_zero, mul_one,
      hNN]
  set Sig := ∑ i, if i ∉ S ∧ M.Indep (insert i (S : Set β)) then v (some i) else 0 with hSig
  set Adj := ∑ i, ∑ i', (if i ≠ i' ∧ i ∉ S ∧ i' ∉ S ∧
        M.Indep (insert i (insert i' (S : Set β))) then v (some i) * v (some i') else 0) with hAdj
  have hcomb := comb_ineq M S j hjS (fun i => v (some i))
  rw [← hSig, ← hAdj] at hcomb
  have hS1 : ∑ i, H none (some i) * v (some i) = ((j + 1).factorial : ℝ) * Sig := by
    rw [hSig, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hNS i]
    split_ifs <;> simp
  have hS2 : ∑ i, v (some i) * (H none (some i) * v none +
      ∑ i', H (some i) (some i') * v (some i')) =
        v none * ((j + 1).factorial : ℝ) * Sig + (j.factorial : ℝ) * Adj := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [mul_assoc, ← hS1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    · rw [hAdj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hSS i i']
      split_ifs <;> ring
  rw [h00, hbilv, hbil0, hS1, hS2]
  have hF : ((j + 2).factorial : ℝ) = (j + 2) * (j + 1).factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hG : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hK : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [hNN] at *
  rw [hF, hG]
  have hGK : (0 : ℝ) ≤ (j + 1) * j.factorial * j.factorial := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcomb hGK]

end BaseCase

section Induction

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [Fintype β] in
private lemma bump_three (s : Option β → ℕ) (a b c : Option β) :
    bump (bump (bump s a) b) c = bump (bump (bump s b) c) a := by
  funext e; simp only [bump]; omega

/-- At a positive point, the Hessian of every derivative of `g_M` of degree at least two is
hyperbolic. -/
private theorem hyp_hess (M : Matroid β) (x : Option β → ℝ) (hx : ∀ a, 0 < x a) :
    ∀ d, 2 ≤ d → ∀ s : Option β → ℕ, ∑ a, s a + d = Fintype.card β → Hyp (hess M x s) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact fun s hs => hyp_base M x s hs
  | succ d hd ih =>
    intro s hs
    have hpos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 1)
    have hx0 : ∀ a, 0 ≤ x a := fun a => (hx a).le
    have hdeg : ∀ a b, Fintype.card β - ∑ c, bump (bump s a) b c = d - 1 := by
      intro a b; rw [sum_bump, sum_bump]; omega
    refine hyp_of_local (T := fun i => hess M x (bump s i)) (c := ((d - 1 : ℕ) : ℝ)) none hpos hx
      (hess_symm M x s) (fun a b => val_nonneg M hx0 _)
      (fun i a b => val_nonneg M hx0 _)
      ?_ ?_ (fun i => ih (bump s i) (by rw [sum_bump]; omega)) (hess_conn M hx s)
    · intro a b
      have h := euler M x (bump (bump s a) b)
      rw [hdeg] at h
      simp only [hess]
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bump_three]
    · intro i b
      have h := euler M x (bump (bump s i) b)
      rw [hdeg] at h
      simp only [hess]
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [bump_comm (bump s i) a b]

end Induction

section Limit

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The point with `y = t` and `z_i = 1`. -/
private def pt (t : ℝ) : Option β → ℝ := fun a => if a = none then t else 1

omit [Fintype β] [DecidableEq β] in
@[simp] private lemma pt_none (t : ℝ) : pt (β := β) t none = t := by simp [pt]

omit [Fintype β] [DecidableEq β] in
@[simp] private lemma pt_some (t : ℝ) (i : β) : pt t (some i) = 1 := by simp [pt]

omit [Fintype β] [DecidableEq β] in
private lemma prod_pt (t : ℝ) (s : Option β → ℕ) (A : Finset β) :
    (∏ i ∈ A, if s (some i) = 0 then pt t (some i) else 1 : ℝ) = 1 :=
  Finset.prod_eq_one fun i _ => by simp

open Classical in
/-- At `y = 0` only the monomials of degree `s none` in `y` survive. -/
private lemma term_pt_zero (s : Option β → ℕ) (A : Finset β) :
    term (pt 0) s A = if Fits s A ∧ #A + s none = Fintype.card β then
      ((s none).factorial : ℝ) else 0 := by
  classical
  unfold term termCore
  by_cases hF : Fits s A
  · simp only [hF, true_and, ↓reduceIte, prod_pt, mul_one, pt_none]
    have hA := Finset.card_le_univ A
    rcases lt_trichotomy (#A + s none) (Fintype.card β) with h | h | h
    · rw [ite_eq_right h.ne, zero_pow (by omega), mul_zero]
    · rw [ite_eq_left h, show Fintype.card β - #A = s none by omega, Nat.descFactorial_self,
        Nat.sub_self, pow_zero, mul_one]
    · rw [ite_eq_right h.ne', Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
      simp
  · simp [hF]

private lemma sum_ite_mem_const (A : Finset β) (c : ℝ) :
    (∑ i, if i ∈ A then c else 0) = (#A : ℝ) * c := by
  classical
  rw [Fintype.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]

/-- The number of ordered pairs of distinct elements of `A`. -/
private lemma sum_pairs (A : Finset β) (c : ℝ) :
    (∑ i, ∑ i', if i ∈ A ∧ i' ∈ A ∧ i' ≠ i then c else 0) = (#A : ℝ) * (#A - 1) * c := by
  have h : ∀ i, (∑ i', if i ∈ A ∧ i' ∈ A ∧ i' ≠ i then c else 0) =
      if i ∈ A then ((#A : ℝ) - 1) * c else 0 := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, true_and, ↓reduceIte]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.univ.filter fun i' => i' ∈ A ∧ i' ≠ i) = A.erase i := by
        ext i'; simp [and_comm]
      rw [this, Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      push_cast [Nat.cast_sub this]
      ring
    · simp [hi]
  simp_rw [h]
  rw [sum_ite_mem_const]
  ring

/-- The derivatives of `g_M` along the points `(t, 1, …, 1)` are continuous in `t`. -/
private lemma continuous_val_pt (M : Matroid β) (s : Option β → ℕ) :
    Continuous fun t => val M (pt t) s := by
  unfold val
  refine continuous_finsetSum _ fun A _ => ?_
  unfold term
  split_ifs
  · unfold termCore
    simp only [prod_pt, pt_none, mul_one]
    fun_prop
  · exact continuous_const

private lemma continuous_bil_pt (M : Matroid β) (s : Option β → ℕ) (u v : Option β → ℝ) :
    Continuous fun t => bil (hess M (pt t) s) u v := by
  simp only [bil, dotProduct, mulVec]
  refine continuous_finsetSum _ fun a _ => ?_
  refine continuous_const.mul (continuous_finsetSum _ fun b _ => ?_)
  exact (continuous_val_pt M _).mul continuous_const

omit [DecidableEq β] in
open Classical in
/-- Ultra log-concavity of the independent set numbers of a matroid on a finite type, over the
reals: the hyperbolic Hessian of `∂_y^(n-k-1) g_M` at `(t, 1, …, 1)`, as `t` tends to `0`. -/
private theorem ulc_real (M : Matroid β) (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card β) :
    let I : ℕ → ℝ := fun j =>
      ∑ A ∈ Finset.univ.filter (fun A : Finset β => M.Indep (A : Set β)), if #A = j then 1 else 0
    ((k + 1) * (Fintype.card β - k + 1) * I (k - 1) * I (k + 1) : ℝ) ≤
      k * (Fintype.card β - k) * I k ^ 2 := by
  classical
  intro I
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card β = m + k + 1 := ⟨Fintype.card β - k - 1, by omega⟩
  set s : Option β → ℕ := fun a => if a = none then m else 0 with hsdef
  have hs : ∑ a, s a + (k + 1) = Fintype.card β := by
    simp [hsdef]; omega
  set u : Option β → ℝ := fun a => if a = none then 0 else 1 with hu
  set v : Option β → ℝ := fun a => if a = none then 1 else 0 with hv
  set F : ℝ → ℝ := fun t => bil (hess M (pt t) s) u v ^ 2 -
    bil (hess M (pt t) s) u u * bil (hess M (pt t) s) v v with hFdef
  have hFpos : ∀ t, 0 < t → 0 ≤ F t := by
    intro t ht
    have hx : ∀ a : Option β, 0 < pt t a := by intro a; cases a <;> simp [ht]
    have hH := hyp_hess M (pt t) hx (k + 1) (by omega) s hs
    have huu : 0 ≤ bil (hess M (pt t) s) u u := by
      simp only [bil, dotProduct, mulVec]
      refine Finset.sum_nonneg fun a _ => mul_nonneg (by simp [hu]; split_ifs <;> norm_num)
        (Finset.sum_nonneg fun b _ => mul_nonneg (val_nonneg M (fun a => (hx a).le) _)
          (by simp [hu]; split_ifs <;> norm_num))
    rcases huu.lt_or_eq with h | h
    · have := hH u v h
      simp only [hFdef]
      linarith
    · simp only [hFdef]
      rw [← h, zero_mul, sub_zero]
      exact sq_nonneg _
  have hFcont : Continuous F :=
    ((continuous_bil_pt M s u v).pow 2).sub
      ((continuous_bil_pt M s u u).mul (continuous_bil_pt M s v v))
  have hF0 : 0 ≤ F 0 := by
    have h1 : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)) :=
      (hFcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun t ht => hFpos t ht)
  -- evaluation at `t = 0`
  have hval0 : ∀ s' : Option β → ℕ, val M (pt 0) s' =
      ∑ A ∈ Finset.univ.filter (fun A : Finset β => M.Indep (A : Set β)),
        if Fits s' A ∧ #A + s' none = Fintype.card β then ((s' none).factorial : ℝ) else 0 := by
    intro s'; simp only [val, term_pt_zero]
  have hs_some : ∀ i, s (some i) = 0 := by intro i; simp [hsdef]
  have hs_none : s none = m := by simp [hsdef]
  have hfits0 : ∀ A, Fits s A := fun A i => by simp [hs_some]
  have hvv : bil (hess M (pt 0) s) v v = ((m + 2).factorial : ℝ) * I (k - 1) := by
    have : bil (hess M (pt 0) s) v v = hess M (pt 0) s none none := by
      simp [bil, dotProduct, mulVec, hv]
    rw [this, hess, hval0]
    simp only [I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    simp only [fits_bump_none, hfits0, true_and, bump_none_none, hs_none]
    by_cases h : #A = k - 1
    · rw [ite_eq_left (by omega), ite_eq_left h]; ring
    · rw [ite_eq_right (by omega), ite_eq_right h]; ring
  have huv : bil (hess M (pt 0) s) u v = ((m + 1).factorial : ℝ) * k * I k := by
    have : bil (hess M (pt 0) s) u v = ∑ i, hess M (pt 0) s (some i) none := by
      simp [bil, dotProduct, mulVec, Fintype.sum_option, hu, hv]
    rw [this]
    simp only [hess, hval0]
    rw [Finset.sum_comm]
    simp only [I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    have hFi : ∀ i, Fits (bump (bump s (some i)) none) A ↔ i ∈ A := by
      intro i; rw [fits_bump_none, fits_bump_some]; simp [hfits0, hs_some]
    simp only [hFi, bump_none_none, bump_some_none, hs_none]
    by_cases h : #A = k
    · have h' : k + (m + 1) = Fintype.card β := by omega
      simp only [h, h', and_true, ↓reduceIte]
      rw [sum_ite_mem_const, h]
      ring
    · have : ¬ (#A + (m + 1) = Fintype.card β) := by omega
      simp [this, h]
  have huu : bil (hess M (pt 0) s) u u = (m.factorial : ℝ) * ((k + 1) * k) * I (k + 1) := by
    have : bil (hess M (pt 0) s) u u = ∑ i, ∑ i', hess M (pt 0) s (some i) (some i') := by
      simp [bil, dotProduct, mulVec, Fintype.sum_option, hu, Finset.mul_sum]
    rw [this]
    simp only [hess, hval0]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    simp only [I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    have hFi : ∀ i i', Fits (bump (bump s (some i)) (some i')) A ↔ i ∈ A ∧ i' ∈ A ∧ i' ≠ i := by
      intro i i'
      rw [fits_bump_some, fits_bump_some]
      simp [hfits0, hs_some]
    simp only [hFi, bump_some_none, hs_none]
    by_cases h : #A = k + 1
    · have h' : k + 1 + m = Fintype.card β := by omega
      simp only [h, h', and_true, ↓reduceIte]
      rw [sum_pairs, h]
      push_cast
      ring
    · have : ¬ (#A + m = Fintype.card β) := by omega
      simp [this, h]
  simp only [hFdef] at hF0
  rw [hvv, huv, huu] at hF0
  have hm2 : ((m + 2).factorial : ℝ) = (m + 2) * (m + 1) * m.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hm1 : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
    push_cast [Nat.factorial_succ]; ring
  rw [hm1, hm2] at hF0
  have hN : (Fintype.card β : ℝ) = m + k + 1 := by exact_mod_cast hm
  rw [hN]
  have hpos : (0 : ℝ) < (m.factorial : ℝ) ^ 2 * (m + 1) * k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have key : (m.factorial : ℝ) ^ 2 * (m + 1) * k *
      ((m + 1) * k * I k ^ 2 - (k + 1) * (m + 2) * I (k - 1) * I (k + 1)) ≥ 0 := by
    linear_combination hF0
  have := le_of_mul_le_mul_left (by linarith : (m.factorial : ℝ) ^ 2 * (m + 1) * k * 0 ≤
    (m.factorial : ℝ) ^ 2 * (m + 1) * k *
      ((m + 1) * k * I k ^ 2 - (k + 1) * (m + 2) * I (k - 1) * I (k + 1))) hpos
  nlinarith [this]

end Limit

open Classical in
/-- `independentSetCount` counts the independent finsets of the restriction to the ground set. -/
private lemma independentSetCount_eq {α : Type*} (M : Matroid α) [M.Finite] [Fintype M.E] (j : ℕ) :
    independentSetCount M j = #(Finset.univ.filter fun A : Finset M.E =>
      (M.restrictSubtype M.E).Indep (A : Set M.E) ∧ #A = j) := by
  have hset : {I ∈ Set.powersetCard α j | M.Indep I} =
      (fun A : Finset M.E => A.map (Function.Embedding.subtype _)) ''
        ↑(Finset.univ.filter fun A : Finset M.E =>
          (M.restrictSubtype M.E).Indep (A : Set M.E) ∧ #A = j) := by
    ext I
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
      Matroid.restrictSubtype_indep_iff]
    constructor
    · rintro ⟨hcard, hI⟩
      refine ⟨I.subtype (· ∈ M.E), ⟨?_, ?_⟩, ?_⟩
      · convert hI
        ext x
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_subtype]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx; exact ⟨⟨x, hI.subset_ground hx⟩, hx, rfl⟩
      · rw [← Finset.card_map (Function.Embedding.subtype _),
          Finset.subtype_map_of_mem fun x hx => hI.subset_ground hx]
        exact hcard
      · exact Finset.subtype_map_of_mem fun x hx => hI.subset_ground hx
    · rintro ⟨A, ⟨hA, hcard⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change #(A.map _) = j
        rw [Finset.card_map]
        exact hcard
      · simpa [Finset.coe_map] using hA
  unfold independentSetCount
  rw [hset, Set.ncard_image_of_injective _ (Finset.map_injective _), Set.ncard_coe_finset]

set_option linter.dupNamespace false in
/-- **The strong Mason conjecture.** Let $M$ be a finite matroid whose ground set has $n$
elements, and for each $j$ let $I_j$ be the number of independent sets of $M$ with $j$ elements.
Then for every natural number $k$ with $0 < k < n$,
$$I_{k-1} \, I_{k+1} \, (k+1) \, (n-k+1) \le I_k^2 \, k \, (n-k).$$

Equivalently, the sequence $I_k / \binom{n}{k}$ is log-concave for $0 \le k \le n$.

Source: P. Branden and J. Huh, 'Lorentzian polynomials', Ann. of Math. 192 (2020), 821-891, Theorem
4.14, https://doi.org/10.4007/annals.2020.192.3.4; independently N. Anari, K. Liu, S. Oveis Gharan,
and C. Vinzant, 'Log-concave polynomials III: Mason's ultra-log-concavity conjecture for independent
sets of matroids', https://arxiv.org/abs/1811.01600. Via leanprover/lean-eval@38361be, problem
`strong_mason_conjecture`. -/
theorem strong_mason_conjecture {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) *
          (k + 1) * (M.E.ncard - k + 1) ≤
      independentSetCount M k ^ 2 * k * (M.E.ncard - k) := by
  classical
  let _ : Fintype M.E := M.ground_finite.fintype
  have hcard : Fintype.card M.E = M.E.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcount : ∀ j, (independentSetCount M j : ℝ) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset M.E => (M.restrictSubtype M.E).Indep (A : Set M.E)),
        if #A = j then 1 else 0 := by
    intro j
    rw [Finset.sum_boole, Finset.filter_filter, independentSetCount_eq]
  have h := ulc_real (M.restrictSubtype M.E) k hk (by omega)
  simp only [← hcount, hcard] at h
  have hle : k ≤ M.E.ncard := hkn.le
  have : ((independentSetCount M (k - 1) * independentSetCount M (k + 1) *
          (k + 1) * (M.E.ncard - k + 1) : ℕ) : ℝ) ≤
      ((independentSetCount M k ^ 2 * k * (M.E.ncard - k) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle]
    linarith [h]
  exact_mod_cast this

end Combinatorics.StrongMason

end MathlibExt.Combinatorics.StrongMasonWanted
