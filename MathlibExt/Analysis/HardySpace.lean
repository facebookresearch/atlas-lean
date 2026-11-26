/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/HardySpace.lean` (leanprover/lean-eval, https://github.com/leanprover/lean-eval),
problem `H1_not_closedComplemented`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/H1_not_closedComplemented.toml`, rev 1, submitter Yongxi Lin, status
archived): the definition `H1` and the statement of `H1_not_closedComplemented`, with the
docstrings and comments they had in the former wanted module
`WantedExt/Analysis/HardySpaceWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Yongxi Lin
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
`MathlibExt.Analysis.HardySpaceWanted` namespace. Mathematical statements are unchanged. Source:
D. J. Newman, 'The nonexistence of projections from L^1 to H^1', Proc. Amer. Math. Soc.;
W. Rudin, Fourier Analysis on Groups; Yongxi Lin, Hardy Space and Hartogs Triangle, Theorem 2.8.
Later change (ATLAS, 2026): the `theorem_wanted` was proved, and it and the definition `H1` moved
from `WantedExt/Analysis/HardySpaceWanted.lean` to this `MathlibExt` module with unchanged names,
statements and docstrings; the import of `Batteries.Util.ProofWanted` was dropped.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`H1_not_closedComplemented`, the private lemmas and definitions it uses, the module
documentation and the linter options.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.Analysis.Fourier.AddCircle.FejerKernel

/-!
# Nonexistence of bounded projections from `L^1` onto `H^1`

The Hardy space `H^1` consists of those `L^1` functions on the unit circle whose
negative Fourier coefficients vanish. D. J. Newman showed that there is no bounded
linear projection from `L^1` onto `H^1`. The theorem below phrases the result
using `Submodule.ClosedComplemented`.

The main result is `H1_not_closedComplemented`: for the circle `ℝ/ℤ` with its Haar probability
measure, no continuous `ℂ`-linear map from `L¹` to the subspace `H1` restricts to the identity
on `H1`.

## Proof outline

Suppose that `P : L¹ → H1` is continuous, linear and the identity on `H1`. Write `e n` for the
character `fourier n` and `ĝ n` for the `n`-th Fourier coefficient of `g`.

* *Averaging over rotations.* Let `f = ∑ i, c i • e (m i)` be a trigonometric polynomial and
  `h` a measurable function with `|h| ≤ B`. For a rotation `t`, pair `P (f (· + t))` with
  `conj (h (· + t))`; this is at most `B * ‖P‖ * ‖f‖₁` in absolute value, since rotations
  preserve the `L¹` norm. As `f (· + t) = ∑ i, (c i * e (m i) t) • e (m i)`, Fubini's theorem
  and the invariance of the Haar measure turn the average over `t` into the sum over `i` of
  `c i * a i * conj (ĥ (m i))`, where `a i` is the `m i`-th Fourier coefficient of
  `P (e (m i))`. As `P` fixes `e n` for `n ≥ 0` and maps `e n` into `H1` for `n < 0`, `a i` is
  `1` when `m i ≥ 0` and `0` otherwise: the rotation average of `P` acts on trigonometric
  polynomials as the projection onto the nonnegative frequencies. Hence
  `‖∑_{m i ≥ 0} c i * conj (ĥ (m i))‖ ≤ B * ‖P‖ * ‖f‖₁`.
* *Test functions.* Take `f = ∑_{j, k < N} e (j - k) = |∑_{j < N} e j|²`, which is `N` times a
  Fejér kernel and has `L¹` norm `N`, and the sawtooth `h`, equal to `x` on `[0, 1)`, with
  `|h| ≤ 1` and `ĥ n = i / (2πn)` for `n ≠ 0`. The imaginary part of the sum above is
  `-(2π)⁻¹ ∑_{j < N} H_j`, where `H_j = ∑_{d = 1}^{j} 1 / d`, so `∑_{j < N} H_j ≤ 2π ‖P‖ N`.
* *Conclusion.* Since `H_j ≥ log (j + 1)`, taking `N = 2E + 1` gives `log (E + 1) ≤ 4π ‖P‖` for
  every `E`, which fails for large `E`.

## Implementation notes

The definition `H1` and the statement keep the full names they had in the former wanted module,
so the namespace still reads `HardySpaceWanted` and repeats `Analysis`; the `dupNamespace`
linter is turned off for these two declarations only.

## References

* D. J. Newman, *The nonexistence of projections from L¹ to H¹*, Proc. Amer. Math. Soc. 12
  (1961), 98–99.

Problem `H1_not_closedComplemented` of the lean-eval benchmark (leanprover/lean-eval), from which
the definition and the statement are taken, also cites W. Rudin, *Fourier Analysis on Groups*,
and Yongxi Lin, *Hardy Space and Hartogs Triangle*, Theorem 2.8.
-/

@[expose] public section

namespace MathlibExt.Analysis.HardySpaceWanted
namespace Analysis

open MeasureTheory Submodule

set_option linter.dupNamespace false in
/-- **The boundary Hardy space H¹.** Let $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ carry its Haar
measure normalized to total mass $1$. The Hardy space $H^1$ is the complex linear subspace of
$L^1(\mathbb{T})$ consisting of those $f$ whose Fourier coefficients
$\hat f(n) = \int_{\mathbb{T}} f(t) e^{-2\pi i n t} dt$ vanish for all integers $n < 0$. -/
def H1 : Submodule ℂ (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1))) where
  carrier := {f | ∀ n : ℤ, n < 0 → fourierCoeff f n = 0}
  zero_mem' := by simp [fourierCoeff]
  add_mem' := by
    intro f g hf hg n hn
    rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),
      fourierCoeff.add (L1.integrable_coeFn f) (L1.integrable_coeFn g)]
    simp_all
  smul_mem' := by
    intro c f n hn
    rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f), fourierCoeff.const_smul]
    simp_all

open AddCircle Complex Finset
open scoped ComplexConjugate Real

/-! ### Characters on the circle -/

private lemma fourier_apply_add (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

private lemma fourier_apply_sub (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourier n (x - y) = fourier n x * fourier (-n) y := by
  rw [sub_eq_add_neg, fourier_apply_add, fourier_neg]
  congr 1
  simp only [fourier_apply, smul_neg, toCircle_neg, Circle.coe_inv_eq_conj]

private lemma norm_fourier_apply (n : ℤ) (x : AddCircle (1 : ℝ)) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The `L¹` class of the character `fourier n` has Fourier coefficients `Pi.single n 1`. -/
private lemma fourierCoeff_fourierLp (n k : ℤ) :
    fourierCoeff (fourierLp (T := 1) 1 n : AddCircle (1 : ℝ) → ℂ) k =
      (Pi.single n 1 : ℤ → ℂ) k := by
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 1 n), fourierCoeff_fourier]

private lemma fourierLp_mem_H1 {n : ℤ} (hn : 0 ≤ n) : fourierLp (T := 1) 1 n ∈ H1 := by
  intro k hk
  rw [fourierCoeff_fourierLp, Pi.single_apply, ite_eq_right (by omega)]

/-- A projection onto `H1` fixes the characters of nonnegative frequency and sends the others
into `H1`, so the `n`-th coefficient of the image of `fourier n` is `1` or `0`. -/
private lemma fourierCoeff_proj {P : Lp ℂ 1 (haarAddCircle (T := 1)) →L[ℂ] H1}
    (hP : ∀ x : H1, P x = x) (n : ℤ) :
    fourierCoeff ((P (fourierLp 1 n) : Lp ℂ 1 (haarAddCircle (T := 1))) :
      AddCircle (1 : ℝ) → ℂ) n = if 0 ≤ n then 1 else 0 := by
  split_ifs with hn
  · have h := hP ⟨fourierLp (T := 1) 1 n, fourierLp_mem_H1 hn⟩
    have h' : P (fourierLp (T := 1) 1 n) = ⟨fourierLp (T := 1) 1 n, fourierLp_mem_H1 hn⟩ := h
    rw [h']
    exact (fourierCoeff_fourierLp n n).trans (Pi.single_eq_same _ _)
  · exact (P (fourierLp (T := 1) 1 n)).2 n (by omega)

/-! ### Averaging over rotations -/

section Pairing

variable {h : AddCircle (1 : ℝ) → ℂ} (hh : Measurable h) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
include hh hB

private lemma integrable_mul_conj_translate (t : AddCircle (1 : ℝ)) {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Integrable g haarAddCircle) :
    Integrable (fun y => g y * conj (h (y + t))) haarAddCircle :=
  hg.mul_bdd
    (continuous_conj.measurable.comp (hh.comp (measurable_add_const t))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hB (y + t))

/-- Pairing of an `L¹` function against the conjugate of the translate `h (· + t)`. -/
private noncomputable def pairing (t : AddCircle (1 : ℝ)) :
    Lp ℂ 1 (haarAddCircle (T := 1)) →ₗ[ℂ] ℂ where
  toFun u := ∫ y, u y * conj (h (y + t)) ∂haarAddCircle
  map_add' u v := by
    rw [← integral_add (integrable_mul_conj_translate hh hB t (L1.integrable_coeFn u))
      (integrable_mul_conj_translate hh hB t (L1.integrable_coeFn v))]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add u v] with y hy
    rw [hy, Pi.add_apply, add_mul]
  map_smul' c u := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c u] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_assoc]

private lemma pairing_apply (t : AddCircle (1 : ℝ)) (u : Lp ℂ 1 (haarAddCircle (T := 1))) :
    pairing hh hB t u = ∫ y, u y * conj (h (y + t)) ∂haarAddCircle :=
  rfl

private lemma norm_pairing_le (t : AddCircle (1 : ℝ)) (u : Lp ℂ 1 (haarAddCircle (T := 1))) :
    ‖pairing hh hB t u‖ ≤ B * ‖u‖ := by
  rw [pairing_apply, L1.norm_eq_integral_norm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn u).norm.const_mul B)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, RCLike.norm_conj, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

private lemma integrable_prod_pairing {g : AddCircle (1 : ℝ) → ℂ} (hg : Integrable g haarAddCircle)
    (m : ℤ) :
    Integrable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      fourier m p.1 * (g p.2 * conj (h (p.2 + p.1))))
      ((haarAddCircle (T := 1)).prod haarAddCircle) := by
  have hg2 : Integrable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => g p.2)
      ((haarAddCircle (T := 1)).prod haarAddCircle) :=
    hg.comp_snd haarAddCircle
  have hmeas : AEStronglyMeasurable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      fourier m p.1 * conj (h (p.2 + p.1))) ((haarAddCircle (T := 1)).prod haarAddCircle) :=
    ((fourier m).continuous.comp continuous_fst).aestronglyMeasurable.mul
      (continuous_conj.measurable.comp
        (hh.comp (measurable_snd.add measurable_fst))).aestronglyMeasurable
  refine (hg2.bdd_mul hmeas (c := B) (Filter.Eventually.of_forall fun p => ?_)).congr
    (Filter.Eventually.of_forall fun p => ?_)
  · rw [norm_mul, norm_fourier_apply, one_mul, RCLike.norm_conj]
    exact hB _
  · dsimp only
    ring

private lemma integrable_fourier_mul_pairing {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Integrable g haarAddCircle) (m : ℤ) :
    Integrable (fun t => fourier m t * ∫ y, g y * conj (h (y + t)) ∂haarAddCircle)
      haarAddCircle := by
  refine ((integrable_prod_pairing hh hB hg m).integral_prod_left).congr
    (Filter.Eventually.of_forall fun t => ?_)
  exact integral_const_mul (fourier m t) _

/-- **Averaging identity.** Averaging the pairing of `g` against the rotated function
`h (· + t)`, weighted by the character `fourier m t`, gives `ĝ(m) * conj (ĥ(m))`. -/
private lemma integral_fourier_mul_pairing {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Integrable g haarAddCircle) (m : ℤ) :
    ∫ t, fourier m t * (∫ y, g y * conj (h (y + t)) ∂haarAddCircle) ∂haarAddCircle =
      fourierCoeff g m * conj (fourierCoeff h m) := by
  have hinner : ∀ y, ∫ t, fourier m t * (g y * conj (h (y + t))) ∂haarAddCircle =
      fourier (-m) y * g y * conj (fourierCoeff h m) := by
    intro y
    have h1 := integral_add_left_eq_self (μ := haarAddCircle)
      (fun s => fourier m (s - y) * (g y * conj (h s))) y
    simp only [add_sub_cancel_left] at h1
    rw [h1]
    have h2 : ∀ s, fourier m (s - y) * (g y * conj (h s)) =
        (fourier (-m) y * g y) * conj (fourier (-m) s • h s) := by
      intro s
      rw [fourier_apply_sub, smul_eq_mul, map_mul, fourier_neg (n := m) (x := s), conj_conj]
      ring
    simp_rw [h2]
    rw [integral_const_mul, integral_conj, fourierCoeff]
  calc ∫ t, fourier m t * (∫ y, g y * conj (h (y + t)) ∂haarAddCircle) ∂haarAddCircle
      = ∫ t, ∫ y, fourier m t * (g y * conj (h (y + t))) ∂haarAddCircle ∂haarAddCircle := by
        simp_rw [integral_const_mul]
    _ = ∫ y, ∫ t, fourier m t * (g y * conj (h (y + t))) ∂haarAddCircle ∂haarAddCircle :=
        integral_integral_swap (integrable_prod_pairing hh hB hg m)
    _ = ∫ y, fourier (-m) y * g y * conj (fourierCoeff h m) ∂haarAddCircle := by
        simp_rw [hinner]
    _ = fourierCoeff g m * conj (fourierCoeff h m) := by
        rw [integral_mul_const]
        rfl

/-- **Key estimate.** If `P` is a bounded projection of `L¹` onto `H1` and `h` is bounded by `B`,
then for every trigonometric polynomial `f = ∑ c i * fourier (m i)` the sum of
`c i * conj (ĥ (m i))` over the indices with `0 ≤ m i` is at most `B * ‖P‖ * ‖f‖₁`. The proof
averages `P` over the rotations of the circle, which turns it into the Riesz projection on
trigonometric polynomials. -/
private lemma norm_sum_le_of_proj {P : Lp ℂ 1 (haarAddCircle (T := 1)) →L[ℂ] H1}
    (hP : ∀ x : H1, P x = x) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → ℤ) :
    ‖∑ i ∈ s, if 0 ≤ m i then c i * conj (fourierCoeff h (m i)) else 0‖ ≤
      B * ‖P‖ * ∫ y : AddCircle (1 : ℝ), ‖∑ i ∈ s, c i * fourier (m i) y‖ ∂haarAddCircle := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set g : ι → Lp ℂ 1 (haarAddCircle (T := 1)) :=
    fun i => (P (fourierLp 1 (m i)) : Lp ℂ 1 (haarAddCircle (T := 1))) with hg
  set N := ∫ y : AddCircle (1 : ℝ), ‖∑ i ∈ s, c i * fourier (m i) y‖ ∂haarAddCircle
  set Φ : AddCircle (1 : ℝ) → ℂ := fun t =>
    ∑ i ∈ s, c i * (fourier (m i) t * ∫ y, g i y * conj (h (y + t)) ∂haarAddCircle)
  have hint : ∫ t, Φ t ∂haarAddCircle =
      ∑ i ∈ s, if 0 ≤ m i then c i * conj (fourierCoeff h (m i)) else 0 := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_fourier_mul_pairing hh hB (L1.integrable_coeFn _),
        hg, fourierCoeff_proj hP]
      split_ifs <;> simp
    · intro i _
      exact (integrable_fourier_mul_pairing hh hB (L1.integrable_coeFn _) (m i)).const_mul (c i)
  have hbound : ∀ t, ‖Φ t‖ ≤ B * ‖P‖ * N := by
    intro t
    set F : C(AddCircle (1 : ℝ), ℂ) := ∑ i ∈ s, (c i * fourier (m i) t) • fourier (m i) with hF
    set u : Lp ℂ 1 (haarAddCircle (T := 1)) := ContinuousMap.toLp 1 haarAddCircle ℂ F with hu
    have hPu : (P u : Lp ℂ 1 (haarAddCircle (T := 1))) =
        ∑ i ∈ s, (c i * fourier (m i) t) • g i := by
      simp only [hu, hF, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hg]
    have hΦt : Φ t = pairing hh hB t (P u) := by
      rw [hPu, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, pairing_apply]
      ring
    have hnorm : ‖u‖ = N := by
      have hae : (fun y => ‖(u : AddCircle (1 : ℝ) → ℂ) y‖) =ᵐ[haarAddCircle]
          fun y => ‖F y‖ := by
        filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (μ := haarAddCircle) (𝕜 := ℂ) F]
          with y hy
        rw [hu, hy]
      rw [L1.norm_eq_integral_norm, integral_congr_ae hae]
      have hFy : ∀ y, F y = ∑ i ∈ s, c i * fourier (m i) (y + t) := by
        intro y
        simp only [hF, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
          Pi.smul_apply, smul_eq_mul, fourier_apply_add]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      simp only [hFy]
      exact integral_add_right_eq_self (fun y => ‖∑ i ∈ s, c i * fourier (m i) y‖) t
    rw [hΦt]
    calc ‖pairing hh hB t (P u)‖ ≤ B * ‖(P u : Lp ℂ 1 (haarAddCircle (T := 1)))‖ :=
          norm_pairing_le hh hB t _
      _ = B * ‖P u‖ := rfl
      _ ≤ B * (‖P‖ * ‖u‖) := mul_le_mul_of_nonneg_left (P.le_opNorm u) hB0
      _ = B * ‖P‖ * N := by rw [hnorm, mul_assoc]
  rw [← hint]
  calc ‖∫ t, Φ t ∂haarAddCircle‖ ≤ B * ‖P‖ * N * (haarAddCircle (T := 1)).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)
    _ = B * ‖P‖ * N := by simp

end Pairing

/-! ### The sawtooth function -/

/-- The sawtooth function `x ↦ x` on `[0, 1)`, as a function on the circle. -/
private noncomputable def saw : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIco (1 : ℝ) 0 (fun x : ℝ => (x : ℂ))

private lemma measurable_saw : Measurable saw :=
  (Complex.measurable_ofReal.comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private lemma norm_saw_le (x : AddCircle (1 : ℝ)) : ‖saw x‖ ≤ 1 := by
  have hx := (AddCircle.equivIco 1 0 x).2
  change ‖(((AddCircle.equivIco 1 0 x : ℝ)) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
  linarith [hx.2]

private lemma fourierCoeff_saw {n : ℤ} (hn : n ≠ 0) :
    fourierCoeff saw n = ((2 * π * n)⁻¹ : ℝ) * I := by
  have hab : (0 : ℝ) < 0 + 1 := by norm_num
  rw [saw, fourierCoeff_liftIco_eq]
  have hconst : fourierCoeffOn hab (fun _ : ℝ => (1 : ℂ)) n = 0 := by
    rw [fourierCoeffOn_of_hasDerivAt hab hn (f' := fun _ => 0)
      (fun x _ => hasDerivAt_const x (1 : ℂ)) intervalIntegrable_const]
    simp [fourierCoeffOn_eq_integral]
  rw [fourierCoeffOn_of_hasDerivAt hab hn (f' := fun _ => (1 : ℂ))
    (fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp) intervalIntegrable_const, hconst]
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [ofReal_zero, sub_zero, zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero,
    ofReal_one, mul_one, mul_zero]
  push_cast
  field_simp
  rw [I_sq]

private lemma im_fourierCoeff_saw_zero : (fourierCoeff saw 0).im = 0 := by
  have h : fourierCoeff saw 0 =
      ((∫ x, (AddCircle.equivIco 1 0 x : ℝ) ∂haarAddCircle : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, fourierCoeff]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [neg_zero, fourier_zero, one_smul]
    rfl
  rw [h, ofReal_im]

/-! ### The Fejér kernel and the harmonic numbers -/

/-- The sum of the characters `fourier (j - k)` over `0 ≤ j, k < N` is `|∑_{j < N} fourier j|²`. -/
private lemma sum_fourier_sub_eq (N : ℕ) (y : AddCircle (1 : ℝ)) :
    ∑ p ∈ range N ×ˢ range N, fourier ((p.1 : ℤ) - p.2) y =
      ((‖∑ j ∈ range N, fourier (j : ℤ) y‖ ^ 2 : ℝ) : ℂ) := by
  rw [← normSq_eq_norm_sq, ← mul_conj, map_sum, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

private lemma integral_norm_sum_fourier_sub (N : ℕ) :
    ∫ y : AddCircle (1 : ℝ), ‖∑ p ∈ range N ×ˢ range N, fourier ((p.1 : ℤ) - p.2) y‖
      ∂haarAddCircle = N := by
  simp_rw [sum_fourier_sub_eq, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm]
  have h : ((∫ y : AddCircle (1 : ℝ), ‖∑ j ∈ range N, fourier (j : ℤ) y‖ ^ 2 ∂haarAddCircle :
      ℝ) : ℂ) = N := by
    rw [← integral_complex_ofReal]
    simp_rw [← sum_fourier_sub_eq]
    rw [integral_finsetSum _ fun p _ => AddCircle.fourier_integrable _]
    simp_rw [AddCircle.integral_fourier, sub_eq_zero, Nat.cast_inj]
    rw [Finset.sum_product]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_ite_of_true fun j hj => Finset.mem_range.mp hj]
    simp
  exact_mod_cast h

private lemma sum_ite_lt_eq_harmonic {N j : ℕ} (hj : j ∈ range N) :
    ∑ k ∈ range N, (if k < j then ((j : ℝ) - k)⁻¹ else 0) = harmonic j := by
  rw [mem_range] at hj
  rw [← Finset.sum_filter, show (range N).filter (· < j) = range j by ext k; simp; omega,
    harmonic, Rat.cast_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  have hcast : ((j - 1 - k : ℕ) : ℝ) = (j : ℝ) - 1 - k := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]
  push_cast
  ring_nf

/-- The imaginary part of the pairing of the Fejér-type sum with the sawtooth. -/
private lemma im_sum_saw (N : ℕ) :
    (∑ p ∈ range N ×ˢ range N, if 0 ≤ (p.1 : ℤ) - p.2 then
      (1 : ℂ) * conj (fourierCoeff saw ((p.1 : ℤ) - p.2)) else 0).im =
      -((2 * π)⁻¹ * ∑ j ∈ range N, (harmonic j : ℝ)) := by
  rw [im_sum, Finset.sum_product, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← sum_ite_lt_eq_harmonic hj, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · have h0 : 0 ≤ (j : ℤ) - k := by omega
    have hne : (j : ℤ) - k ≠ 0 := by omega
    rw [ite_eq_left h0, ite_eq_left hkj, one_mul, fourierCoeff_saw hne, map_mul, conj_ofReal,
      conj_I, Complex.im_ofReal_mul, neg_im, I_im]
    push_cast
    rw [mul_inv]
    ring
  · simp [im_fourierCoeff_saw_zero]
  · have h0 : ¬ (0 ≤ (j : ℤ) - k) := by omega
    rw [ite_eq_right h0, ite_eq_right (by omega : ¬ k < j)]
    simp

/- There is no bounded projection from `L^1` onto `H^1`. In the language of
topological vector spaces, `H^1` has no topological complement in `L^1`. -/
set_option linter.dupNamespace false in
/-- **Newman's theorem: no bounded projection onto the Hardy space.** Let $L^1(\mathbb{T})$ be
the space of integrable complex functions on the circle $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ with
its normalized Haar measure, and let $H^1 \subseteq L^1(\mathbb{T})$ be the boundary Hardy space.
There is no continuous $\mathbb{C}$-linear map $\pi : L^1(\mathbb{T}) \to H^1$ with $\pi(f) = f$
for every $f \in H^1$.

Source: D. J. Newman, 'The nonexistence of projections from L^1 to H^1', Proc. Amer. Math. Soc.;
W. Rudin, Fourier Analysis on Groups; Yongxi Lin, Hardy Space and Hartogs Triangle, Theorem 2.8. Via
leanprover/lean-eval@38361be, problem `H1_not_closedComplemented`. -/
public theorem H1_not_closedComplemented :
    ¬ H1.ClosedComplemented := by
  rintro ⟨P, hP⟩
  have hH : ∀ j : ℕ, Real.log ((j : ℝ) + 1) ≤ harmonic j := fun j => by
    simpa using log_add_one_le_harmonic j
  have hH0 : ∀ j : ℕ, (0 : ℝ) ≤ harmonic j := fun j =>
    (Real.log_nonneg (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])).trans (hH j)
  -- For every `N`, the Fejér sum of order `N` against the sawtooth gives a harmonic lower bound.
  have hest : ∀ N : ℕ, ∑ j ∈ range N, (harmonic j : ℝ) ≤ 2 * π * ‖P‖ * N := by
    intro N
    have h1 := norm_sum_le_of_proj measurable_saw norm_saw_le hP (range N ×ˢ range N)
      (fun _ => 1) (fun p => (p.1 : ℤ) - p.2)
    simp only [one_mul] at h1
    rw [integral_norm_sum_fourier_sub] at h1
    have h2 := Complex.abs_im_le_norm (∑ p ∈ range N ×ˢ range N, if 0 ≤ (p.1 : ℤ) - p.2 then
      (1 : ℂ) * conj (fourierCoeff saw ((p.1 : ℤ) - p.2)) else 0)
    rw [im_sum_saw, abs_neg, abs_of_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => hH0 j))] at h2
    simp only [one_mul] at h2
    have h3 := h2.trans h1
    rw [inv_mul_le_iff₀ (by positivity)] at h3
    linarith
  -- Choose `E` with `log (E + 1) > 4 π ‖P‖`.
  set E : ℕ := ⌈Real.exp (4 * π * ‖P‖)⌉₊
  have hlog : 4 * π * ‖P‖ < Real.log ((E : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact (Nat.le_ceil _).trans_lt (by linarith)
  have hsum : ((E : ℝ) + 1) * Real.log ((E : ℝ) + 1) ≤
      ∑ j ∈ range (2 * E + 1), (harmonic j : ℝ) := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : E ≤ 2 * E + 1)]
    have h1 : 0 ≤ ∑ j ∈ range E, (harmonic j : ℝ) := Finset.sum_nonneg fun j _ => hH0 j
    have h2 := Finset.card_nsmul_le_sum (Ico E (2 * E + 1)) (fun j => (harmonic j : ℝ))
      (Real.log ((E : ℝ) + 1)) fun j hj => by
        rw [Finset.mem_Ico] at hj
        refine (Real.log_le_log (by positivity) ?_).trans (hH j)
        exact_mod_cast Nat.succ_le_succ hj.1
    rw [Nat.card_Ico, nsmul_eq_mul, show 2 * E + 1 - E = E + 1 by omega] at h2
    push_cast at h2
    linarith
  have h := hest (2 * E + 1)
  push_cast at h
  nlinarith [mul_lt_mul_of_pos_left hlog (by positivity : (0 : ℝ) < E + 1),
    mul_nonneg Real.pi_pos.le (norm_nonneg P)]

end Analysis

end MathlibExt.Analysis.HardySpaceWanted
