/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonnegative matrix factorization

Nonnegative matrix factorization (NMF; Paatero and Tapper 1994; Lee and Seung 1999) approximates
a data matrix `X : Matrix m n ℝ` by a product `W * H` of an `m × k` matrix `W` and a `k × n`
matrix `H` with nonnegative entries, by minimizing the squared Frobenius distance
`objective X W H = ∑ i j, (X i j - (W * H) i j) ^ 2` over `W, H ≥ 0` (entrywise). The index
types `m`, `n`, `k` are arbitrary finite types; `k` plays the role of the rank `r`.

## Main results

* `exists_minimizer`: a minimizer over `W, H ≥ 0` exists, for every real `X` (nonnegativity of
  `X` is not needed). The proof normalizes the columns of `W` to sum to `1` (rescaling the rows
  of `H`, which leaves `W * H` unchanged), which confines a minimizing pair to a compact set.
* Lee–Seung multiplicative updates (Lee and Seung 2001, Theorem 1):
  `updateH`: `H ← H ⊙ (Wᵀ X) ⊘ (Wᵀ W H)` and `updateW`: `W ← W ⊙ (X Hᵀ) ⊘ (W H Hᵀ)`, entrywise.
  `objective_updateH_le` and `objective_updateW_le`: each update does not increase the objective
  (auxiliary-function argument), for `W, H ≥ 0`; `objective_sweep_le`: one full sweep (`sweep`:
  first `H`, then `W`) does not either, for `X, W, H ≥ 0`, and `objective_sweep_iterate_antitone`:
  the objective is non-increasing along the iterates. Lean's `x / 0 = 0` makes the updates total:
  an entry whose denominator vanishes is set to `0`. For `W, H ≥ 0` this happens only where the
  numerator's factor `H a j` is `0` or the column `a` of `W` is `0` (then `H a j` does not affect
  `W * H`), so the monotonicity theorems hold with this convention, with no positivity hypothesis.
* Stationarity (`gradH`, `gradW` are the partial gradients, `hasDerivAt_objective_H`,
  `hasDerivAt_objective_W`): at a fixed point of an update, complementary slackness holds
  (`mul_gradH_eq_zero_of_updateH_eq`), and the gradient vanishes at every positive entry; a fixed
  point of `sweep` with all entries of `W` and `H` positive satisfies the Karush–Kuhn–Tucker
  conditions of the problem (`isKKTPoint_of_sweep_eq`). Fixed points with zero entries need not
  (the test file has a `1 × 1` example with a negative gradient), and no convergence of the
  iterates to a stationary point is claimed.
* Identifiability (`eq_of_isSeparable`): if `X = W * H` where every factor has a pure row of
  `W` and a pure column of `H` (`IsSeparable Wᵀ` and `IsSeparable H`: a row of `W`, resp. a
  column of `H`, that is a positive multiple of a unit vector), then every nonnegative
  factorization `X = W' * H'` of the same inner dimension equals `(W, H)` up to a permutation and
  a positive diagonal scaling of the factors. Pure rows of the basis are the separability
  condition of Donoho and Stodden 2004 and the anchor condition of Arora, Ge, Kannan and Moitra
  2012; pure columns of `H` are the same condition for the transposed factorization
  `Xᵀ = Hᵀ Wᵀ` (pure samples). The key step is the classical fact that a nonnegative matrix
  with a nonnegative inverse is monomial (`exists_perm_of_mul_eq_one`). Weaker sufficient
  conditions (sufficiently scattered factors; Gillis 2020) are not covered.
* Nonnegative rank (`nonnegRank`, the least inner dimension of a nonnegative factorization; Cohen
  and Rothblum 1993): `rank_le_nonnegRank` for `X ≥ 0`. The test file has a `4 × 4` matrix with
  rank at most `3` and nonnegative rank `4`.
* Applications. In mutational-signature analysis (Alexandrov et al. 2013) the mutation-count
  matrix (mutation types × samples) is factored as signatures × exposures; with signatures
  normalized to probability vectors, the total count of a sample is the sum of its exposures
  (`sum_mul_apply_of_sum_eq_one`). In gene-expression deconvolution the bulk matrix
  (genes × samples) is cell-type profiles × proportions; with proportions summing to `1`, the
  bulk value of a gene lies between its lowest and highest cell-type values
  (`mul_apply_mem_Icc`). NMF provides a factorization only: without further assumptions (such as
  separability above) the factors are not unique, and nothing here gives a factor a causal or
  biological identity.

## References

* P. Paatero and U. Tapper, *Positive matrix factorization: a non-negative factor model with
  optimal utilization of error estimates of data values*, Environmetrics 5 (1994), 111–126.
* D. D. Lee and H. S. Seung, *Learning the parts of objects by non-negative matrix
  factorization*, Nature 401 (1999), 788–791.
* D. D. Lee and H. S. Seung, *Algorithms for non-negative matrix factorization*, Advances in
  Neural Information Processing Systems 13 (2001), 556–562.
* D. Donoho and V. Stodden, *When does non-negative matrix factorization give a correct
  decomposition into parts?*, Advances in Neural Information Processing Systems 16 (2004).
* S. Arora, R. Ge, R. Kannan and A. Moitra, *Computing a nonnegative matrix factorization —
  provably*, STOC 2012.
* J. E. Cohen and U. G. Rothblum, *Nonnegative ranks, decompositions, and factorizations of
  nonnegative matrices*, Linear Algebra Appl. 190 (1993), 149–168.
* N. Gillis, *Nonnegative Matrix Factorization*, SIAM, 2020.
* L. B. Alexandrov et al., *Signatures of mutational processes in human cancer*, Nature 500
  (2013), 415–421.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.NMF

open Matrix Finset

variable {m n k : Type*}

/-- The NMF objective: the squared Frobenius distance `‖X - W H‖_F² = ∑ i j, (X i j - (W H) i j)²`
between the data `X` and the product `W * H`. -/
def objective [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) : ℝ :=
  ∑ i, ∑ j, (X i j - (W * H) i j) ^ 2

/-- Entrywise nonnegativity is preserved by matrix products. -/
private lemma mul_nonneg_of_nonneg {l o p : Type*} [Fintype o] {A : Matrix l o ℝ}
    {B : Matrix o p ℝ} (hA : ∀ i a, 0 ≤ A i a) (hB : ∀ a j, 0 ≤ B a j) (i : l) (j : p) :
    0 ≤ (A * B) i j :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hA i a) (hB a j)

/-- The objective is nonnegative. -/
theorem objective_nonneg [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) :
    0 ≤ objective X W H :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- Transposing exchanges the roles of `W` and `H`: `‖Xᵀ - Hᵀ Wᵀ‖² = ‖X - W H‖²`. -/
theorem objective_transpose [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) :
    objective Xᵀ Hᵀ Wᵀ = objective X W H := by
  unfold objective
  rw [Finset.sum_comm]
  simp only [← transpose_mul, transpose_apply]

/-- **Existence of a minimizer.** For every real matrix `X` and every finite inner index type
`k`, the objective attains its infimum over pairs `W, H ≥ 0` (entrywise). -/
theorem exists_minimizer [Fintype m] [Fintype n] [Fintype k] (X : Matrix m n ℝ) :
    ∃ W : Matrix m k ℝ, ∃ H : Matrix k n ℝ, (∀ i a, 0 ≤ W i a) ∧ (∀ a j, 0 ≤ H a j) ∧
      ∀ (W' : Matrix m k ℝ) (H' : Matrix k n ℝ), (∀ i a, 0 ≤ W' i a) → (∀ a j, 0 ≤ H' a j) →
        objective X W H ≤ objective X W' H' := by
  classical
  set F0 := objective X (0 : Matrix m k ℝ) (0 : Matrix k n ℝ) with hF0
  have hF0nn : 0 ≤ F0 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set B : ℝ := ∑ i, (∑ j, |X i j| + F0 + 1) with hB
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun i _ => by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (X i j)
    linarith
  let K : Set ((m → k → ℝ) × (k → n → ℝ)) :=
    (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 1) ×ˢ
      (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 B)
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
  have hmemK : ∀ q : (m → k → ℝ) × (k → n → ℝ), q ∈ K ↔
      (∀ i a, q.1 i a ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ a j, q.2 a j ∈ Set.Icc (0 : ℝ) B := by
    intro q
    simp only [K, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_const]
  let φ : (m → k → ℝ) × (k → n → ℝ) → ℝ := fun q => objective X (Matrix.of q.1) (Matrix.of q.2)
  have hcont : Continuous φ := by
    simp only [φ, objective, mul_apply, of_apply]
    fun_prop
  have h0K : ((0 : m → k → ℝ), (0 : k → n → ℝ)) ∈ K :=
    (hmemK _).2 ⟨fun i a => by simp, fun a j => ⟨le_refl 0, by simpa using hBnn⟩⟩
  obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn ⟨_, h0K⟩ hcont.continuousOn
  have hmin : ∀ q ∈ K, φ p ≤ φ q := fun q hq => hpmin hq
  have hpK' := (hmemK p).1 hpK
  refine ⟨Matrix.of p.1, Matrix.of p.2, fun i a => (hpK'.1 i a).1, fun a j => (hpK'.2 a j).1,
    fun W' H' hW' hH' => ?_⟩
  by_cases hbig : F0 < objective X W' H'
  · exact (hmin _ h0K).trans hbig.le
  · have hle : objective X W' H' ≤ F0 := not_lt.mp hbig
    let s : k → ℝ := fun a => ∑ i, W' i a
    have hs0 : ∀ a, 0 ≤ s a := fun a => Finset.sum_nonneg fun i _ => hW' i a
    let Wf : m → k → ℝ := fun i a => if s a = 0 then 0 else W' i a / s a
    let Hf : k → n → ℝ := fun a j => s a * H' a j
    have hprod : Matrix.of Wf * Matrix.of Hf = W' * H' := by
      ext i j
      simp only [mul_apply, Wf, Hf, of_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hs : s a = 0
      · have : W' i a = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hW' i a)).mp hs i (Finset.mem_univ i)
        simp [hs, this]
      · simp only [hs, ite_false]
        field_simp
    have hobj : φ (Wf, Hf) = objective X W' H' := by
      simp only [φ, objective, hprod]
    have hentry : ∀ i j, (W' * H') i j ≤ |X i j| + F0 + 1 := by
      intro i j
      have hsq : (X i j - (W' * H') i j) ^ 2 ≤ objective X W' H' := by
        unfold objective
        refine (Finset.single_le_sum (f := fun j => (X i j - (W' * H') i j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ j)).trans ?_
        exact Finset.single_le_sum (f := fun i => ∑ j, (X i j - (W' * H') i j) ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have h1 : (W' * H') i j - X i j ≤ (X i j - (W' * H') i j) ^ 2 + 1 := by
        nlinarith [sq_nonneg (X i j - (W' * H') i j + 1 / 2)]
      have h2 : X i j ≤ |X i j| := le_abs_self _
      linarith
    have hK'' : (Wf, Hf) ∈ K := by
      refine (hmemK _).2 ⟨fun i a => ?_, fun a j => ?_⟩
      · simp only [Wf]
        split_ifs with hs
        · simp
        · have hpos : 0 < s a := lt_of_le_of_ne (hs0 a) (Ne.symm hs)
          refine ⟨div_nonneg (hW' i a) hpos.le, (div_le_one hpos).mpr ?_⟩
          exact Finset.single_le_sum (f := fun i => W' i a) (fun i _ => hW' i a)
            (Finset.mem_univ i)
      · simp only [Hf]
        refine ⟨mul_nonneg (hs0 a) (hH' a j), ?_⟩
        calc s a * H' a j = ∑ i, W' i a * H' a j := by rw [Finset.sum_mul]
          _ ≤ ∑ i, (W' * H') i j := Finset.sum_le_sum fun i _ =>
              Finset.single_le_sum (f := fun b => W' i b * H' b j)
                (fun b _ => mul_nonneg (hW' i b) (hH' b j)) (Finset.mem_univ a)
          _ ≤ ∑ i, (|X i j| + F0 + 1) := Finset.sum_le_sum fun i _ => hentry i j
          _ ≤ ∑ i, (∑ j, |X i j| + F0 + 1) := Finset.sum_le_sum fun i _ => by
              have := Finset.single_le_sum (f := fun j => |X i j|) (fun j _ => abs_nonneg _)
                (Finset.mem_univ j)
              linarith
          _ = B := hB.symm
    exact (hmin (Wf, Hf) hK'').trans_eq hobj

/-! ### Lee–Seung multiplicative updates -/

/-- The Lee–Seung multiplicative update of `H` (Lee and Seung 2001, Theorem 1):
`H a j ← H a j * (Wᵀ X) a j / (Wᵀ W H) a j`. An entry with a zero denominator becomes `0`
(Lean's `x / 0 = 0`). -/
noncomputable def updateH [Fintype m] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) : Matrix k n ℝ :=
  Matrix.of fun a j => H a j * (Wᵀ * X) a j / (Wᵀ * W * H) a j

/-- The Lee–Seung multiplicative update of `W` (Lee and Seung 2001, Theorem 1):
`W i a ← W i a * (X Hᵀ) i a / (W H Hᵀ) i a`. An entry with a zero denominator becomes `0`. -/
noncomputable def updateW [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) : Matrix m k ℝ :=
  Matrix.of fun i a => W i a * (X * Hᵀ) i a / (W * H * Hᵀ) i a

/-- One sweep of the Lee–Seung algorithm: update `H`, then update `W` using the new `H`. -/
noncomputable def sweep [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (p : Matrix m k ℝ × Matrix k n ℝ) : Matrix m k ℝ × Matrix k n ℝ :=
  (updateW X p.1 (updateH X p.1 p.2), updateH X p.1 p.2)

/-- The `W` update is the `H` update of the transposed problem. -/
theorem updateW_eq_transpose [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) :
    updateW X W H = (updateH Xᵀ Hᵀ Wᵀ)ᵀ := by
  have h1 : H * Xᵀ = (X * Hᵀ)ᵀ := by rw [transpose_mul, transpose_transpose]
  have h2 : H * Hᵀ * Wᵀ = (W * H * Hᵀ)ᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  ext i a
  simp only [updateW, updateH, of_apply, transpose_apply, transpose_transpose, h1, h2]

/-- The `H` update keeps `H` nonnegative when `X`, `W`, `H` are nonnegative. -/
theorem updateH_nonneg [Fintype m] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ} {H : Matrix k n ℝ}
    (hX : ∀ i j, 0 ≤ X i j) (hW : ∀ i a, 0 ≤ W i a) (hH : ∀ a j, 0 ≤ H a j) (a : k) (j : n) :
    0 ≤ updateH X W H a j := by
  have hWX : ∀ a j, 0 ≤ (Wᵀ * X) a j := mul_nonneg_of_nonneg (fun a i => hW i a) hX
  have hD : ∀ a j, 0 ≤ (Wᵀ * W * H) a j :=
    mul_nonneg_of_nonneg (mul_nonneg_of_nonneg (fun a i => hW i a) hW) hH
  exact div_nonneg (mul_nonneg (hH a j) (hWX a j)) (hD a j)

/-- The `W` update keeps `W` nonnegative when `X`, `W`, `H` are nonnegative. -/
theorem updateW_nonneg [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ} {H : Matrix k n ℝ}
    (hX : ∀ i j, 0 ≤ X i j) (hW : ∀ i a, 0 ≤ W i a) (hH : ∀ a j, 0 ≤ H a j) (i : m) (a : k) :
    0 ≤ updateW X W H i a := by
  have hXH : ∀ i a, 0 ≤ (X * Hᵀ) i a := mul_nonneg_of_nonneg hX (fun j a => hH a j)
  have hD : ∀ i a, 0 ≤ (W * H * Hᵀ) i a :=
    mul_nonneg_of_nonneg (mul_nonneg_of_nonneg hW hH) (fun j a => hH a j)
  exact div_nonneg (mul_nonneg (hW i a) (hXH i a)) (hD i a)

/-- Reordering a triple sum. -/
private lemma sum_comm₃ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) : ∑ i, ∑ j, ∑ a, f i j a = ∑ a, ∑ j, ∑ i, f i j a := by
  calc ∑ i, ∑ j, ∑ a, f i j a = ∑ i, ∑ a, ∑ j, f i j a :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, f i j a := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, f i j a := Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- `∑ i j, A i j (W δ) i j = ∑ a j, (Wᵀ A) a j δ a j`. -/
private lemma sum_mul_mul_apply {l o p : Type*} [Fintype l] [Fintype o] [Fintype p]
    (A : Matrix l p ℝ) (W : Matrix l o ℝ) (δ : Matrix o p ℝ) :
    ∑ i, ∑ j, A i j * (W * δ) i j = ∑ a, ∑ j, (Wᵀ * A) a j * δ a j := by
  simp only [mul_apply, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm₃]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

/-- **Lee–Seung, `H` step** (Lee and Seung 2001, Theorem 1): for `W, H ≥ 0`, the multiplicative
update of `H` does not increase `‖X - W H‖_F²`. The proof is the auxiliary-function argument:
the quadratic term of the exact expansion is bounded by Lee and Seung's diagonal majorant
(here through a weighted Cauchy–Schwarz inequality), and the update minimizes the majorant.
`X` may have any sign. -/
theorem objective_updateH_le [Fintype m] [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ} {H : Matrix k n ℝ}
    (hW : ∀ i a, 0 ≤ W i a) (hH : ∀ a j, 0 ≤ H a j) :
    objective X W (updateH X W H) ≤ objective X W H := by
  set D := Wᵀ * W * H with hD
  set g := Wᵀ * X with hg
  let u : Matrix k n ℝ := Matrix.of fun a j => g a j / D a j - 1
  let δ : Matrix k n ℝ := Matrix.of fun a j => H a j * u a j
  have hH' : updateH X W H = H + δ := by
    ext a j
    simp only [updateH, of_apply, Matrix.add_apply, δ, u]
    rw [← hD, ← hg]
    ring
  have hDi : ∀ a j, D a j = ∑ i, W i a * (W * H) i j := by
    intro a j; rw [hD, Matrix.mul_assoc, mul_apply]; rfl
  -- exact expansion of the objective
  have hexp : objective X W (H + δ) = objective X W H +
      ∑ a, ∑ j, 2 * (D a j - g a j) * δ a j + ∑ i, ∑ j, ((W * δ) i j) ^ 2 := by
    have h1 : objective X W (H + δ) = objective X W H +
        ∑ i, ∑ j, 2 * ((W * H) i j - X i j) * (W * δ) i j + ∑ i, ∑ j, ((W * δ) i j) ^ 2 := by
      simp only [objective, Matrix.mul_add, Matrix.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    congr 2
    have h2 := sum_mul_mul_apply (Matrix.of fun i j => 2 * ((W * H) i j - X i j)) W δ
    simp only [of_apply] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hDi, hg, mul_apply, mul_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [transpose_apply, of_apply]
    ring
  -- the quadratic term is bounded by the auxiliary-function term (Cauchy–Schwarz)
  have hquad : ∑ i, ∑ j, ((W * δ) i j) ^ 2 ≤ ∑ a, ∑ j, D a j * H a j * u a j ^ 2 := by
    have hcs : ∀ i j, ((W * δ) i j) ^ 2 ≤ (W * H) i j * ∑ a, W i a * H a j * u a j ^ 2 := by
      intro i j
      rw [mul_apply, mul_apply]
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
        (fun a _ => mul_nonneg (hW i a) (hH a j))
        (fun a _ => mul_nonneg (mul_nonneg (hW i a) (hH a j)) (sq_nonneg _))
        (fun a _ => le_of_eq (by simp only [δ, of_apply]; ring))
    calc ∑ i, ∑ j, ((W * δ) i j) ^ 2
        ≤ ∑ i, ∑ j, (W * H) i j * ∑ a, W i a * H a j * u a j ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcs i j
      _ = ∑ a, ∑ j, D a j * H a j * u a j ^ 2 := by
          simp only [hDi, Finset.mul_sum, Finset.sum_mul]
          rw [sum_comm₃]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun i _ => by ring
  -- each auxiliary term is nonpositive
  have hterm : ∀ a j, 2 * (D a j - g a j) * δ a j + D a j * H a j * u a j ^ 2 ≤ 0 := by
    intro a j
    simp only [δ, u, of_apply]
    by_cases hDz : D a j = 0
    · -- column `a` of `W` vanishes where `H a j > 0`
      rw [hDz, div_zero]
      rcases (hH a j).lt_or_eq with hpos | hzero
      · have hcol : ∀ i, W i a = 0 := by
          have hle : (∑ i, W i a ^ 2) * H a j ≤ D a j := by
            rw [hDi, Finset.sum_mul]
            refine Finset.sum_le_sum fun i _ => ?_
            have : W i a * H a j ≤ (W * H) i j :=
              Finset.single_le_sum (f := fun b => W i b * H b j)
                (fun b _ => mul_nonneg (hW i b) (hH b j)) (Finset.mem_univ a)
            nlinarith [mul_le_mul_of_nonneg_left this (hW i a)]
          rw [hDz] at hle
          have hsum : ∑ i, W i a ^ 2 = 0 := le_antisymm
            (nonpos_of_mul_nonpos_left hle hpos) (Finset.sum_nonneg fun i _ => sq_nonneg _)
          intro i
          exact pow_eq_zero_iff (two_ne_zero) |>.mp ((Finset.sum_eq_zero_iff_of_nonneg
            (fun i _ => sq_nonneg (W i a))).mp hsum i (Finset.mem_univ i))
        have : g a j = 0 := by
          rw [hg, mul_apply]; simp [hcol]
        rw [this]; simp
      · rw [← hzero]; simp
    · have hDpos : 0 < D a j := lt_of_le_of_ne (by
        rw [hDi]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hW i a)
          (Finset.sum_nonneg fun b _ => mul_nonneg (hW i b) (hH b j))) (Ne.symm hDz)
      have e : g a j / D a j - 1 = (g a j - D a j) / D a j := by field_simp
      rw [e]
      have : 2 * (D a j - g a j) * (H a j * ((g a j - D a j) / D a j)) +
          D a j * H a j * ((g a j - D a j) / D a j) ^ 2 =
          -(H a j * (g a j - D a j) ^ 2 / D a j) := by
        field_simp; ring
      rw [this, neg_nonpos]
      exact div_nonneg (mul_nonneg (hH a j) (sq_nonneg _)) hDpos.le
  rw [hH', hexp]
  have : ∑ a, ∑ j, 2 * (D a j - g a j) * δ a j + ∑ i, ∑ j, ((W * δ) i j) ^ 2 ≤ 0 := by
    calc _ ≤ ∑ a, ∑ j, 2 * (D a j - g a j) * δ a j + ∑ a, ∑ j, D a j * H a j * u a j ^ 2 :=
          by linarith
      _ = ∑ a, ∑ j, (2 * (D a j - g a j) * δ a j + D a j * H a j * u a j ^ 2) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ 0 := Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun j _ => hterm a j
  linarith

/-- **Lee–Seung, `W` step**: for `W, H ≥ 0`, the multiplicative update of `W` does not increase
`‖X - W H‖_F²`. -/
theorem objective_updateW_le [Fintype m] [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ} {H : Matrix k n ℝ}
    (hW : ∀ i a, 0 ≤ W i a) (hH : ∀ a j, 0 ≤ H a j) :
    objective X (updateW X W H) H ≤ objective X W H := by
  rw [updateW_eq_transpose, ← objective_transpose X, ← objective_transpose X W H,
    transpose_transpose]
  exact objective_updateH_le (fun j a => hH a j) (fun a i => hW i a)

/-- One sweep keeps both factors nonnegative when `X ≥ 0`. -/
theorem sweep_nonneg [Fintype m] [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {p : Matrix m k ℝ × Matrix k n ℝ}
    (hX : ∀ i j, 0 ≤ X i j) (hW : ∀ i a, 0 ≤ p.1 i a) (hH : ∀ a j, 0 ≤ p.2 a j) :
    (∀ i a, 0 ≤ (sweep X p).1 i a) ∧ ∀ a j, 0 ≤ (sweep X p).2 a j := by
  have hH' := updateH_nonneg hX hW hH
  exact ⟨updateW_nonneg hX hW hH', hH'⟩

/-- **One Lee–Seung sweep does not increase the objective**, for `X, W, H ≥ 0`. -/
theorem objective_sweep_le [Fintype m] [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {p : Matrix m k ℝ × Matrix k n ℝ}
    (hX : ∀ i j, 0 ≤ X i j) (hW : ∀ i a, 0 ≤ p.1 i a) (hH : ∀ a j, 0 ≤ p.2 a j) :
    objective X (sweep X p).1 (sweep X p).2 ≤ objective X p.1 p.2 := by
  exact (objective_updateW_le hW (updateH_nonneg hX hW hH)).trans (objective_updateH_le hW hH)

/-- **The objective is non-increasing along the Lee–Seung iterates** started from `W, H ≥ 0`,
for `X ≥ 0`. -/
theorem objective_sweep_iterate_antitone [Fintype m] [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {p : Matrix m k ℝ × Matrix k n ℝ}
    (hX : ∀ i j, 0 ≤ X i j) (hW : ∀ i a, 0 ≤ p.1 i a) (hH : ∀ a j, 0 ≤ p.2 a j) :
    Antitone fun t : ℕ => objective X ((sweep X)^[t] p).1 ((sweep X)^[t] p).2 := by
  have hnn : ∀ t : ℕ, (∀ i a, 0 ≤ ((sweep X)^[t] p).1 i a) ∧
      ∀ a j, 0 ≤ ((sweep X)^[t] p).2 a j := by
    intro t
    induction t with
    | zero => exact ⟨hW, hH⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact sweep_nonneg hX ih.1 ih.2
  refine antitone_nat_of_succ_le fun t => ?_
  rw [Function.iterate_succ_apply']
  exact objective_sweep_le hX (hnn t).1 (hnn t).2

/-! ### Stationarity at fixed points -/

/-- The gradient of the objective with respect to `H`: `2 (Wᵀ W H - Wᵀ X)`. -/
def gradH [Fintype m] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) : Matrix k n ℝ :=
  (2 : ℝ) • (Wᵀ * W * H - Wᵀ * X)

/-- The gradient of the objective with respect to `W`: `2 (W H Hᵀ - X Hᵀ)`. -/
def gradW [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) : Matrix m k ℝ :=
  (2 : ℝ) • (W * H * Hᵀ - X * Hᵀ)

/-- `gradH X W H a j` is the partial derivative of the objective in the entry `H a j`. -/
theorem hasDerivAt_objective_H [Fintype m] [Fintype n] [Fintype k] [DecidableEq k] [DecidableEq n]
    (X : Matrix m n ℝ)
    (W : Matrix m k ℝ) (H : Matrix k n ℝ) (a : k) (j : n) :
    HasDerivAt (fun t : ℝ => objective X W (H + Matrix.single a j t)) (gradH X W H a j) 0 := by
  have hu : ∀ (t : ℝ) i j', (W * (H + Matrix.single a j t)) i j' =
      (W * H) i j' + (if j' = j then W i a else 0) * t := by
    intro t i j'
    rw [Matrix.mul_add, Matrix.add_apply]
    by_cases h : j' = j
    · subst h; simp
    · simp [h]
  have hf : (fun t : ℝ => objective X W (H + Matrix.single a j t)) = fun t =>
      ∑ i, ∑ j', (X i j' - (W * H) i j' - (if j' = j then W i a else 0) * t) ^ 2 := by
    funext t; unfold objective; simp only [hu]; congr 1; ext i; congr 1; ext j'; ring
  rw [hf]
  have hd : ∀ i j', HasDerivAt
      (fun t : ℝ => (X i j' - (W * H) i j' - (if j' = j then W i a else 0) * t) ^ 2)
      (2 * (X i j' - (W * H) i j') * (-(if j' = j then W i a else 0))) 0 := by
    intro i j'
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (if j' = j then W i a else 0)).const_sub
      (X i j' - (W * H) i j')).pow 2
    convert this using 1
    · funext t; simp
    · simp
  convert HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j' _ => hd i j')) using 1
  simp only [mul_neg, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    Finset.sum_neg_distrib]
  change (2 : ℝ) * ((Wᵀ * W * H) a j - (Wᵀ * X) a j) = _
  rw [Matrix.mul_assoc]
  simp only [mul_apply, transpose_apply]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_true]
  ring

/-- `gradW X W H i a` is the partial derivative of the objective in the entry `W i a`. -/
theorem hasDerivAt_objective_W [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]
    (X : Matrix m n ℝ)
    (W : Matrix m k ℝ) (H : Matrix k n ℝ) (i : m) (a : k) :
    HasDerivAt (fun t : ℝ => objective X (W + Matrix.single i a t) H) (gradW X W H i a) 0 := by
  have e1 : (fun t : ℝ => objective X (W + Matrix.single i a t) H) =
      fun t => objective Xᵀ Hᵀ (Wᵀ + Matrix.single a i t) := by
    funext t
    rw [← objective_transpose, transpose_add, transpose_single]
  have e2 : gradW X W H i a = gradH Xᵀ Hᵀ Wᵀ a i := by
    change (2 : ℝ) * ((W * H * Hᵀ) i a - (X * Hᵀ) i a) =
      2 * ((Hᵀᵀ * Hᵀ * Wᵀ) a i - (Hᵀᵀ * Xᵀ) a i)
    have h1 : H * Hᵀ * Wᵀ = (W * H * Hᵀ)ᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    have h2 : H * Xᵀ = (X * Hᵀ)ᵀ := by rw [transpose_mul, transpose_transpose]
    rw [transpose_transpose, h1, h2]
    rfl
  rw [e1, e2]
  exact hasDerivAt_objective_H Xᵀ Hᵀ Wᵀ a i

/-- **Complementary slackness at a fixed point of the `H` update**: if `updateH X W H = H`,
then `H a j * gradH X W H a j = 0` for every entry. -/
theorem mul_gradH_eq_zero_of_updateH_eq [Fintype m] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ}
    {H : Matrix k n ℝ} (hfix : updateH X W H = H) (a : k) (j : n) :
    H a j * gradH X W H a j = 0 := by
  have h := congrFun (congrFun hfix a) j
  simp only [updateH, of_apply] at h
  change H a j * (2 * ((Wᵀ * W * H) a j - (Wᵀ * X) a j)) = 0
  by_cases hD : (Wᵀ * W * H) a j = 0
  · rw [hD, div_zero] at h
    rw [← h, zero_mul]
  · have h' := (div_eq_iff hD).mp h
    linear_combination (-2) * h'

/-- **Complementary slackness at a fixed point of the `W` update**. -/
theorem mul_gradW_eq_zero_of_updateW_eq [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ}
    {H : Matrix k n ℝ} (hfix : updateW X W H = W) (i : m) (a : k) :
    W i a * gradW X W H i a = 0 := by
  have h := congrFun (congrFun hfix i) a
  simp only [updateW, of_apply] at h
  change W i a * (2 * ((W * H * Hᵀ) i a - (X * Hᵀ) i a)) = 0
  by_cases hD : (W * H * Hᵀ) i a = 0
  · rw [hD, div_zero] at h
    rw [← h, zero_mul]
  · have h' := (div_eq_iff hD).mp h
    linear_combination (-2) * h'

/-- The Karush–Kuhn–Tucker conditions of `min ‖X - W H‖_F²` subject to `W, H ≥ 0`: primal
feasibility, dual feasibility (nonnegative gradients) and complementary slackness. -/
structure IsKKTPoint [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix m n ℝ) (W : Matrix m k ℝ) (H : Matrix k n ℝ) : Prop where
  /-- `W` is nonnegative. -/
  W_nonneg : ∀ i a, 0 ≤ W i a
  /-- `H` is nonnegative. -/
  H_nonneg : ∀ a j, 0 ≤ H a j
  /-- The gradient in `W` is nonnegative. -/
  gradW_nonneg : ∀ i a, 0 ≤ gradW X W H i a
  /-- The gradient in `H` is nonnegative. -/
  gradH_nonneg : ∀ a j, 0 ≤ gradH X W H a j
  /-- Complementary slackness in `W`. -/
  W_mul_gradW : ∀ i a, W i a * gradW X W H i a = 0
  /-- Complementary slackness in `H`. -/
  H_mul_gradH : ∀ a j, H a j * gradH X W H a j = 0

/-- **Positive fixed points are KKT points**: a fixed point of the Lee–Seung sweep with all
entries of `W` and `H` positive has both gradients zero, so it satisfies the KKT conditions. -/
theorem isKKTPoint_of_sweep_eq [Fintype m] [Fintype n] [Fintype k]
    {X : Matrix m n ℝ} {W : Matrix m k ℝ} {H : Matrix k n ℝ}
    (hfix : sweep X (W, H) = (W, H)) (hW : ∀ i a, 0 < W i a) (hH : ∀ a j, 0 < H a j) :
    IsKKTPoint X W H ∧ gradW X W H = 0 ∧ gradH X W H = 0 := by
  simp only [sweep, Prod.mk.injEq] at hfix
  obtain ⟨hfW, hfH⟩ := hfix
  rw [hfH] at hfW
  have gW : gradW X W H = 0 := by
    ext i a
    exact (mul_eq_zero.mp (mul_gradW_eq_zero_of_updateW_eq hfW i a)).resolve_left (hW i a).ne'
  have gH : gradH X W H = 0 := by
    ext a j
    exact (mul_eq_zero.mp (mul_gradH_eq_zero_of_updateH_eq hfH a j)).resolve_left (hH a j).ne'
  refine ⟨⟨fun i a => (hW i a).le, fun a j => (hH a j).le, ?_, ?_, ?_, ?_⟩, gW, gH⟩ <;>
    simp [gW, gH]

/-! ### Identifiability under separability -/

/-- `H` is separable: every factor `a` has a pure column, a column `j` of `H` equal to a
positive multiple of the unit vector `e_a`. For `X = W * H` this makes column `j` of `X` a
positive multiple of column `a` of `W` (a sample containing only factor `a`). Applied to `Wᵀ`
it says that every factor has a pure row of `W` (an "anchor" feature of factor `a` alone). -/
def IsSeparable [DecidableEq k] (H : Matrix k n ℝ) : Prop :=
  ∀ a, ∃ j, ∃ c : ℝ, 0 < c ∧ ∀ b, H b j = if b = a then c else 0

/-- **A nonnegative matrix with a nonnegative inverse is monomial**: if `G * K = 1` with `G` and
`K` entrywise nonnegative, then there are a permutation `σ` and positive weights `d` with
`G a b = d b` if `a = σ b` and `0` otherwise. -/
theorem exists_perm_of_mul_eq_one [Fintype k] [DecidableEq k] {G K : Matrix k k ℝ}
    (hG : ∀ a b, 0 ≤ G a b) (hK : ∀ a b, 0 ≤ K a b) (hGK : G * K = 1) :
    ∃ σ : k ≃ k, ∃ d : k → ℝ, (∀ b, 0 < d b) ∧ ∀ a b, G a b = if a = σ b then d b else 0 := by
  have hKG : K * G = 1 := mul_eq_one_comm.mp hGK
  have hpos : ∀ b, ∃ a, 0 < G a b ∧ 0 < K b a := by
    intro b
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have h1 : (K * G) b b = 1 := by rw [hKG, one_apply_eq]
    rw [mul_apply] at h1
    have : ∑ a, K b a * G a b ≤ 0 := Finset.sum_nonpos fun a _ => by
      rcases (hG a b).lt_or_eq with hp | hz
      · nlinarith [h a hp, hK b a]
      · rw [← hz, mul_zero]
    linarith
  choose τ hτ using hpos
  have hzero : ∀ {A B : Matrix k k ℝ}, (∀ a b, 0 ≤ A a b) → (∀ a b, 0 ≤ B a b) → A * B = 1 →
      ∀ a a' c, a ≠ a' → A a c * B c a' = 0 := by
    intro A B hA hB hAB a a' c hne
    have h0 : (A * B) a a' = 0 := by rw [hAB, one_apply_ne hne]
    rw [mul_apply] at h0
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hA a c) (hB c a'))).mp h0 c
      (Finset.mem_univ c)
  have huniq : ∀ a b, 0 < G a b → a = τ b := by
    intro a b hab
    by_contra hne
    have := hzero hG hK hGK a (τ b) b hne
    nlinarith [mul_pos hab (hτ b).2]
  have hinj : Function.Injective τ := by
    intro b b' hbb
    by_contra hne
    have := hzero hK hG hKG b b' (τ b) hne
    have h2 : 0 < G (τ b) b' := by rw [hbb]; exact (hτ b').1
    nlinarith [mul_pos (hτ b).2 h2]
  refine ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj), fun b => G (τ b) b,
    fun b => (hτ b).1, fun a b => ?_⟩
  simp only [Equiv.ofBijective_apply]
  split_ifs with h
  · rw [h]
  · exact le_antisymm (not_lt.mp fun hp => h (huniq a b hp)) (hG a b)

/-- **Essential uniqueness of NMF when both factors are separable.** Suppose `X = W * H`, where
`W` has a pure row for every factor (`IsSeparable Wᵀ`: for each `a` a row `i` with
`W i · = e • e_a`, `e > 0`) and `H` has a pure column for every factor (`IsSeparable H`). Then
every factorization `X = W' * H'` with `W', H' ≥ 0` and the same inner dimension agrees with
`(W, H)` up to a permutation `σ` and positive scalings `d` of the factors:
`W' · a = d a • W · (σ a)` and `H' a · = (d a)⁻¹ • H (σ a) ·`. The signs of `W` and `H` are not
used. Proof: the anchor rows and columns of `X` form a positive diagonal block, so the matching
block of `W'` is a nonnegative matrix with a nonnegative inverse, hence monomial
(`exists_perm_of_mul_eq_one`). -/
theorem eq_of_isSeparable [Fintype k] [DecidableEq k] {X : Matrix m n ℝ}
    {W W' : Matrix m k ℝ} {H H' : Matrix k n ℝ} (hX : X = W * H) (hX' : X = W' * H')
    (hW' : ∀ i a, 0 ≤ W' i a) (hH' : ∀ a j, 0 ≤ H' a j) (hsW : IsSeparable Wᵀ)
    (hsH : IsSeparable H) :
    ∃ σ : k ≃ k, ∃ d : k → ℝ, (∀ a, 0 < d a) ∧ (∀ i a, W' i a = d a * W i (σ a)) ∧
      ∀ a j, H' a j = (d a)⁻¹ * H (σ a) j := by
  choose i e he hi using hsW
  choose j c hc hj using hsH
  simp only [transpose_apply] at hi
  -- a pure row of `W` reads off a row of `H`, a pure column of `H` a column of `W`
  have hrow : ∀ a jj, X (i a) jj = e a * H a jj := by
    intro a jj
    rw [hX, mul_apply, Finset.sum_eq_single a]
    · rw [hi, ite_eq_left rfl]
    · intro b _ hb; rw [hi, ite_eq_right hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hcol : ∀ ii a, X ii (j a) = W ii a * c a := by
    intro ii a
    rw [hX, mul_apply, Finset.sum_eq_single a]
    · rw [hj, ite_eq_left rfl]
    · intro b _ hb; rw [hj, ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  -- the anchor block of the second factorization is a positive diagonal matrix
  let A : Matrix k k ℝ := Matrix.of fun a b => W' (i a) b
  let B : Matrix k k ℝ := Matrix.of fun b a => H' b (j a) * (e a * c a)⁻¹
  have hAB : A * B = 1 := by
    ext a a'
    have h := hrow a (j a')
    rw [hj, hX', mul_apply] at h
    simp only [A, B, of_apply, mul_apply, ← mul_assoc]
    rw [← Finset.sum_mul, h, one_apply]
    split_ifs with haa
    · subst haa
      exact mul_inv_cancel₀ (mul_pos (he a) (hc a)).ne'
    · rw [mul_zero, zero_mul]
  obtain ⟨σ, δ, hδ, hA⟩ := exists_perm_of_mul_eq_one (G := A) (K := B)
    (fun a b => hW' _ _)
    (fun b a => mul_nonneg (hH' _ _) (inv_nonneg.mpr (mul_pos (he a) (hc a)).le)) hAB
  -- the rows of `H'` are scaled rows of `H`
  have hH'eq : ∀ b jj, H' b jj = (e (σ b) / δ b) * H (σ b) jj := by
    intro b jj
    have h := hrow (σ b) jj
    rw [hX', mul_apply, Finset.sum_eq_single b] at h
    · have hAσ : W' (i (σ b)) b = δ b := by
        have := hA (σ b) b
        simp only [A, of_apply] at this
        rw [this, ite_true]
      rw [hAσ] at h
      field_simp [(hδ b).ne']
      linarith
    · intro b' _ hb'
      have := hA (σ b) b'
      simp only [A, of_apply] at this
      rw [this, ite_eq_right (fun h => hb' (σ.injective h).symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ b) h
  refine ⟨σ, fun b => δ b / e (σ b), fun b => div_pos (hδ b) (he _), fun ii b => ?_,
    fun b jj => ?_⟩
  · have h := hcol ii (σ b)
    rw [hX', mul_apply, Finset.sum_eq_single b] at h
    · rw [hH'eq, hj, ite_eq_left rfl] at h
      have hcpos := hc (σ b)
      have hepos := he (σ b)
      have hδpos := hδ b
      field_simp at h ⊢
      nlinarith [h]
    · intro b' _ hb'
      rw [hH'eq, hj, ite_eq_right (fun h => hb' (σ.injective h)), mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  · rw [hH'eq, inv_div]

/-! ### Nonnegative rank -/

/-- The nonnegative rank of `X`: the least `r` such that `X = W * H` with `W : m × r` and
`H : r × n` entrywise nonnegative (Cohen and Rothblum 1993). If `X` has a negative entry no
such factorization exists and the value is the junk value `sInf ∅ = 0`. -/
noncomputable def nonnegRank (X : Matrix m n ℝ) : ℕ :=
  sInf {r | ∃ (W : Matrix m (Fin r) ℝ) (H : Matrix (Fin r) n ℝ),
    (∀ i a, 0 ≤ W i a) ∧ (∀ a j, 0 ≤ H a j) ∧ W * H = X}

/-- The trivial factorization `X = X * 1` (after reindexing the columns by `Fin (card n)`). -/
private lemma exists_mul_eq_card [Fintype n] {X : Matrix m n ℝ} (hX : ∀ i j, 0 ≤ X i j) :
    ∃ (W : Matrix m (Fin (Fintype.card n)) ℝ) (H : Matrix (Fin (Fintype.card n)) n ℝ),
      (∀ i a, 0 ≤ W i a) ∧ (∀ a j, 0 ≤ H a j) ∧ W * H = X := by
  classical
  let e := Fintype.equivFin n
  refine ⟨Matrix.of fun i a => X i (e.symm a), Matrix.of fun a j => if e j = a then 1 else 0,
    fun i a => hX _ _, fun a j => by simp only [of_apply]; split_ifs <;> norm_num, ?_⟩
  ext i j
  simp [mul_apply]

/-- A nonnegative factorization with inner dimension `r` bounds the nonnegative rank by `r`. -/
theorem nonnegRank_le_of_mul_eq {r : ℕ} {X : Matrix m n ℝ} (W : Matrix m (Fin r) ℝ)
    (H : Matrix (Fin r) n ℝ) (hW : ∀ i a, 0 ≤ W i a) (hH : ∀ a j, 0 ≤ H a j) (hX : W * H = X) :
    nonnegRank X ≤ r := by
  exact Nat.sInf_le ⟨W, H, hW, hH, hX⟩

/-- A nonnegative matrix has a nonnegative factorization of inner dimension `nonnegRank X`. -/
theorem exists_mul_eq_nonnegRank [Finite n] {X : Matrix m n ℝ} (hX : ∀ i j, 0 ≤ X i j) :
    ∃ (W : Matrix m (Fin (nonnegRank X)) ℝ) (H : Matrix (Fin (nonnegRank X)) n ℝ),
      (∀ i a, 0 ≤ W i a) ∧ (∀ a j, 0 ≤ H a j) ∧ W * H = X := by
  have := Fintype.ofFinite n
  let S : Set ℕ := {r | ∃ (W : Matrix m (Fin r) ℝ) (H : Matrix (Fin r) n ℝ),
    (∀ i a, 0 ≤ W i a) ∧ (∀ a j, 0 ≤ H a j) ∧ W * H = X}
  have hS : S.Nonempty := ⟨Fintype.card n, exists_mul_eq_card hX⟩
  exact Nat.sInf_mem hS

/-- The nonnegative rank of a nonnegative matrix is at most its number of columns. -/
theorem nonnegRank_le_card_width [Fintype n] {X : Matrix m n ℝ} (hX : ∀ i j, 0 ≤ X i j) :
    nonnegRank X ≤ Fintype.card n := by
  obtain ⟨W, H, hW, hH, hX'⟩ := exists_mul_eq_card hX
  exact nonnegRank_le_of_mul_eq W H hW hH hX'

/-- **The nonnegative rank of a nonnegative matrix is at least its rank.** -/
theorem rank_le_nonnegRank [Fintype n] {X : Matrix m n ℝ} (hX : ∀ i j, 0 ≤ X i j) :
    X.rank ≤ nonnegRank X := by
  obtain ⟨W, H, -, -, hX'⟩ := exists_mul_eq_nonnegRank hX
  have h := (rank_mul_le_left W H).trans ((rank_le_card_width W).trans_eq (Fintype.card_fin _))
  rwa [hX'] at h

/-! ### Applications -/

/-- Column sums of a product: `∑ i, (W H) i j = ∑ a, (∑ i, W i a) H a j`. -/
theorem sum_mul_apply [Fintype m] [Fintype k] (W : Matrix m k ℝ) (H : Matrix k n ℝ) (j : n) :
    ∑ i, (W * H) i j = ∑ a, (∑ i, W i a) * H a j := by
  simp only [mul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- **Mutational signatures** (Alexandrov et al. 2013). Write the mutation-count matrix
(mutation types × samples) as `W * H`, signatures (columns of `W`) times exposures `H`. If every
signature is a probability vector over mutation types, the total mutation count of sample `j`
equals the sum of its exposures. -/
theorem sum_mul_apply_of_sum_eq_one [Fintype m] [Fintype k]
    {W : Matrix m k ℝ} (hW : ∀ a, ∑ i, W i a = 1)
    (H : Matrix k n ℝ) (j : n) : ∑ i, (W * H) i j = ∑ a, H a j := by
  simp [sum_mul_apply, hW]

/-- **Gene-expression deconvolution.** Write the bulk matrix (genes × samples) as `C * P`, the
cell-type profiles `C` times the cell-type proportions `P`. If the proportions of sample `j` are
nonnegative and sum to `1` and every cell type expresses gene `g` at a level in `[lo, hi]`, then
the bulk level of `g` in sample `j` lies in `[lo, hi]`. -/
theorem mul_apply_mem_Icc [Fintype k]
    {C : Matrix m k ℝ} {P : Matrix k n ℝ} {g : m} {j : n} {lo hi : ℝ}
    (hP : ∀ a, 0 ≤ P a j) (hsum : ∑ a, P a j = 1) (hC : ∀ a, C g a ∈ Set.Icc lo hi) :
    (C * P) g j ∈ Set.Icc lo hi := by
  rw [mul_apply]
  constructor
  · calc lo = ∑ a, lo * P a j := by rw [← Finset.mul_sum, hsum, mul_one]
      _ ≤ ∑ a, C g a * P a j :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hC a).1 (hP a)
  · calc ∑ a, C g a * P a j ≤ ∑ a, hi * P a j :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hC a).2 (hP a)
      _ = hi := by rw [← Finset.mul_sum, hsum, mul_one]

end Cslib.MachineLearning.NMF
