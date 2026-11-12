/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.SubstitutionModels
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Identifiability of the general time-reversible substitution model

The GTR model (Tavaré 1986; `SubstitutionModels.gtrRate`) has base frequencies `π` and symmetric
exchangeabilities `s`. On the **GTR domain** `IsGTRParam π s` (`π i > 0`, `∑ i, π i = 1`,
`s i j = s j i`, `s i j > 0` for `i ≠ j`) we show which parameters the model determines and
which symmetries are permitted.

**Identifiability** here means injectivity of the map from parameters to the law, modulo the
listed symmetries. It is a property of the model, not of a procedure; consistency of any
estimator (that a statistic converges to the parameters as data accumulate) is a separate
statement and is not claimed here.

## Permitted symmetries

1. **The diagonal of `s`** is not used by `gtrRate` (`gtrRate_congr_offDiag`); only the
   off-diagonal exchangeabilities are identified.
2. **Rate/time scaling.** At a single branch, `(s, t)` and `(c • s, t / c)` give the same
   transition matrix and pair-site law (`ctmcTransition_gtrRate_smul`, `gtrPairLaw_smul`), so
   one branch identifies only the products `t * s i j`. Fixing the branch length (or the overall
   rate) removes this symmetry.
3. **State relabeling.** Relabeling states by a permutation `σ` maps `(π, s)` to
   `(π ∘ σ, s.submatrix σ σ)` and relabels the rate matrix and pair-site law
   (`gtrRate_comp_perm`, `gtrPairLaw_comp_perm`). With observed labels this symmetry is
   absent; with unobserved labels the parameters are determined up to the same `σ`.

Apart from these, the parameters are determined.

## Main results

* `gtrRate_eq_iff`: on the GTR domain, `gtrRate π s = gtrRate π' s'` iff `π = π'` and `s = s'`
  off the diagonal. (`eq_of_gtrRate_eq` needs only that `π'` sums to `1` and `s'` is
  symmetric.)
* `eq_and_offDiag_eq_of_ctmcTransition_eq`: the transition function `t ↦ exp (t • Q)` on
  `t ≥ 0` determines `π` and the off-diagonal `s` (`eq_of_ctmcTransition_eq`: it determines
  the generator).
* `gtrPairLaw_eq_iff`: **one branch.** For `t, t' > 0` the pair-site laws
  `π i * P t i j` agree iff `π = π'` and `t * s i j = t' * s' i j` off the diagonal.
  The key step, `eq_of_exp_eq_of_isDetailedBalance`, is uniqueness of the matrix logarithm
  for generators reversible with respect to a positive `π`: conjugation by `diag (√π)` makes
  them symmetric, and on symmetric real matrices the exponential is inverted by the real
  logarithm of the continuous functional calculus.
* `eq_and_offDiag_eq_of_gtrPairLaw_eq`: with known branch length, exact identification.
* `eq_comp_perm_of_gtrRate_submatrix_eq`, `eq_comp_perm_of_gtrPairLaw_eq`: identification up to
  an unknown relabeling of the states.
* `k80Rate_injective`: the K80 matrix determines `κ`.

## Implementation notes

The Kimura (K80) facts used are those of the merged `SubstitutionModels.k80Rate`; nothing is
imported from the unmerged Kimura development.

## References

* S. Tavaré, *Some probabilistic and statistical problems in the analysis of DNA sequences*,
  Lectures on Mathematics in the Life Sciences 17 (1986), 57–86.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 13.
* J. T. Chang, *Full reconstruction of Markov models on evolutionary trees: identifiability
  and consistency*, Math. Biosci. 137 (1996), 51–73.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory

namespace MathlibExt.Biology.Phylogenetics.GTRIdentifiability

open SubstitutionModels

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **GTR parameter domain**: base frequencies `π` form a strictly positive probability
vector and the exchangeabilities `s` are symmetric with strictly positive off-diagonal entries.
The diagonal of `s` is unconstrained (it is not used by `gtrRate`). -/
structure IsGTRParam (π : ι → ℝ) (s : Matrix ι ι ℝ) : Prop where
  /-- Every base frequency is strictly positive. -/
  pos : ∀ i, 0 < π i
  /-- The base frequencies sum to `1`. -/
  sum_eq_one : ∑ i, π i = 1
  /-- The exchangeabilities are symmetric. -/
  symm : ∀ i j, s i j = s j i
  /-- The off-diagonal exchangeabilities are strictly positive. -/
  offDiag_pos : ∀ i j, i ≠ j → 0 < s i j

/-- Off the diagonal the GTR rate is `s i j * π j`. -/
theorem gtrRate_apply_of_ne (π : ι → ℝ) (s : Matrix ι ι ℝ) {i j : ι} (h : i ≠ j) :
    gtrRate π s i j = s i j * π j := by
  simp [gtrRate, h]

/-- **Symmetry: the diagonal of `s` is not identified.** Exchangeabilities that agree off the
diagonal give the same GTR rate matrix. -/
theorem gtrRate_congr_offDiag (π : ι → ℝ) {s s' : Matrix ι ι ℝ}
    (h : ∀ i j, i ≠ j → s i j = s' i j) : gtrRate π s = gtrRate π s' := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [gtrRate, of_apply, ite_true]
    exact congrArg Neg.neg (sum_congr rfl fun k hk => by rw [h i k (ne_of_mem_erase hk).symm])
  · rw [gtrRate_apply_of_ne _ _ hij, gtrRate_apply_of_ne _ _ hij, h i j hij]

/-- **The GTR rate matrix determines its base frequencies.** If `(π, s)` lies in the GTR
domain, `π'` sums to `1` and `s'` is symmetric, then equal rate matrices force `π = π'`. No
positivity of `(π', s')` is needed. -/
theorem eq_of_gtrRate_eq {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ} (hp : IsGTRParam π s)
    (hπ' : ∑ i, π' i = 1) (hs' : ∀ i j, s' i j = s' j i)
    (hQ : gtrRate π s = gtrRate π' s') : π = π' := by
  -- Cross-ratio identity `π i π' j = π' i π j` for every pair of states.
  have key : ∀ i j, π i * π' j = π' i * π j := by
    intro i j
    by_cases hij : i = j
    · subst hij; ring
    have h1 := congrFun (congrFun hQ i) j
    have h2 := congrFun (congrFun hQ j) i
    rw [gtrRate_apply_of_ne _ _ hij, gtrRate_apply_of_ne _ _ hij] at h1
    rw [gtrRate_apply_of_ne _ _ (Ne.symm hij), gtrRate_apply_of_ne _ _ (Ne.symm hij),
      hp.symm j i, hs' j i] at h2
    have hq : 0 < s i j * π j := mul_pos (hp.offDiag_pos i j hij) (hp.pos j)
    -- `h1 : s i j π j = s' i j π' j`, `h2 : s i j π i = s' i j π' i`.
    have : s i j * π j * (π i * π' j - π' i * π j) = 0 := by
      linear_combination π' j * π j * h2 - π' i * π j * h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hq.ne'
    · linarith
  funext i
  have := Finset.sum_congr rfl fun j (_ : j ∈ univ) => key i j
  rw [← mul_sum, ← mul_sum, hπ', hp.sum_eq_one] at this
  linarith

/-- **GTR identifiability from the rate matrix.** Under the hypotheses of
`eq_of_gtrRate_eq`, equal rate matrices force equal base frequencies and equal off-diagonal
exchangeabilities. -/
theorem eq_and_offDiag_eq_of_gtrRate_eq {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ}
    (hp : IsGTRParam π s) (hπ' : ∑ i, π' i = 1) (hs' : ∀ i j, s' i j = s' j i)
    (hQ : gtrRate π s = gtrRate π' s') : π = π' ∧ ∀ i j, i ≠ j → s i j = s' i j := by
  obtain rfl := eq_of_gtrRate_eq hp hπ' hs' hQ
  refine ⟨rfl, fun i j hij => ?_⟩
  have h1 := congrFun (congrFun hQ i) j
  rw [gtrRate_apply_of_ne _ _ hij, gtrRate_apply_of_ne _ _ hij] at h1
  exact mul_right_cancel₀ (hp.pos j).ne' h1

/-- **GTR identifiability, exact form.** On the GTR domain the rate matrix determines the
parameters exactly up to the diagonal of `s`, which it does not see:
`gtrRate π s = gtrRate π' s' ↔ π = π' ∧ s = s'` off the diagonal. -/
theorem gtrRate_eq_iff {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ} (hp : IsGTRParam π s)
    (hp' : IsGTRParam π' s') :
    gtrRate π s = gtrRate π' s' ↔ π = π' ∧ ∀ i j, i ≠ j → s i j = s' i j := by
  refine ⟨eq_and_offDiag_eq_of_gtrRate_eq hp hp'.sum_eq_one hp'.symm, ?_⟩
  rintro ⟨rfl, h⟩
  exact gtrRate_congr_offDiag π h

/-! ## State relabeling -/

omit [DecidableEq ι] in
private lemma sum_erase_eq_sub_apply (f : ι → ℝ) [DecidableEq ι] (i : ι) :
    ∑ k ∈ univ.erase i, f k = ∑ k, f k - f i := by
  rw [← add_sum_erase _ _ (mem_univ i)]
  ring

/-- **Relabeling equivariance.** Relabeling the states by a permutation `σ` relabels the GTR
rate matrix: the parameters `(π ∘ σ, s.submatrix σ σ)` give `(gtrRate π s).submatrix σ σ`. -/
theorem gtrRate_comp_perm (π : ι → ℝ) (s : Matrix ι ι ℝ) (σ : Equiv.Perm ι) :
    gtrRate (π ∘ σ) (s.submatrix σ σ) = (gtrRate π s).submatrix σ σ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [gtrRate, submatrix_apply, of_apply, ite_true, Function.comp_apply]
    rw [sum_erase_eq_sub_apply, sum_erase_eq_sub_apply,
      Equiv.sum_comp σ (fun k => s (σ i) k * π k)]
  · rw [submatrix_apply, gtrRate_apply_of_ne _ _ hij,
      gtrRate_apply_of_ne _ _ (σ.injective.ne hij)]
    rfl

omit [DecidableEq ι] in
/-- The GTR domain is preserved by relabeling the states. -/
theorem IsGTRParam.comp_perm {π : ι → ℝ} {s : Matrix ι ι ℝ} (hp : IsGTRParam π s)
    (σ : Equiv.Perm ι) : IsGTRParam (π ∘ σ) (s.submatrix σ σ) where
  pos i := hp.pos (σ i)
  sum_eq_one := by rw [← hp.sum_eq_one]; exact Equiv.sum_comp σ π
  symm i j := hp.symm (σ i) (σ j)
  offDiag_pos i j h := hp.offDiag_pos (σ i) (σ j) (σ.injective.ne h)

/-- **Identifiability up to relabeling.** If the rate matrix of `(π, s)` is observed only up to
an unknown relabeling `σ` of the states, the parameters are determined up to the same
relabeling: `π' = π ∘ σ` and `s' = s.submatrix σ σ` off the diagonal. When the state labels
are observed (`σ = 1`) this is `gtrRate_eq_iff`. -/
theorem eq_comp_perm_of_gtrRate_submatrix_eq {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ}
    (hp : IsGTRParam π s) (hp' : IsGTRParam π' s') (σ : Equiv.Perm ι)
    (hQ : (gtrRate π s).submatrix σ σ = gtrRate π' s') :
    π' = π ∘ σ ∧ ∀ i j, i ≠ j → s' i j = s (σ i) (σ j) := by
  rw [← gtrRate_comp_perm] at hQ
  obtain ⟨h1, h2⟩ := (gtrRate_eq_iff (hp.comp_perm σ) hp').1 hQ
  exact ⟨h1.symm, fun i j h => (h2 i j h).symm⟩

/-! ## Rate/time scaling -/

/-- Scaling all exchangeabilities by `c` scales the GTR rate matrix by `c`. -/
theorem gtrRate_smul (π : ι → ℝ) (s : Matrix ι ι ℝ) (c : ℝ) :
    gtrRate π (c • s) = c • gtrRate π s := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [gtrRate, of_apply, ite_true, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
    ring
  · simp only [Matrix.smul_apply, smul_eq_mul, gtrRate_apply_of_ne _ _ hij]
    ring

omit [DecidableEq ι] in
/-- The GTR domain is preserved by a positive rescaling of the exchangeabilities. -/
theorem IsGTRParam.smul {π : ι → ℝ} {s : Matrix ι ι ℝ} (hp : IsGTRParam π s) {c : ℝ}
    (hc : 0 < c) : IsGTRParam π (c • s) where
  pos := hp.pos
  sum_eq_one := hp.sum_eq_one
  symm i j := by simp [hp.symm i j]
  offDiag_pos i j h := by simpa using mul_pos hc (hp.offDiag_pos i j h)

/-- **Symmetry: rate and time are confounded at a single branch.** Exchangeabilities `c • s`
over time `t` give the same transition matrix as `s` over time `c * t`. So a transition matrix
observed at one unknown branch length can identify at most the products `t * s i j`. -/
theorem ctmcTransition_gtrRate_smul (π : ι → ℝ) (s : Matrix ι ι ℝ) (c t : ℝ) :
    ctmcTransition (gtrRate π (c • s)) t = ctmcTransition (gtrRate π s) (c * t) := by
  rw [gtrRate_smul, ctmcTransition_smul]

/-! ## Identifiability from the transition function -/

private lemma hasDerivAt_ctmcTransition_apply (Q : Matrix ι ι ℝ) (i j : ι) (t : ℝ) :
    HasDerivAt (fun u => ctmcTransition Q u i j) ((Q * ctmcTransition Q t) i j) t := by
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_ctmcTransition_backward Q t
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j

/-- **The transition function determines the generator.** If two generators give the same
transition matrices at all times `t ≥ 0`, they are equal (`Q` is the right derivative of
`t ↦ exp (t • Q)` at `0`). -/
theorem eq_of_ctmcTransition_eq {Q Q' : Matrix ι ι ℝ}
    (h : ∀ t, 0 ≤ t → ctmcTransition Q t = ctmcTransition Q' t) : Q = Q' := by
  ext i j
  have h1 := (hasDerivAt_ctmcTransition_apply Q i j 0).hasDerivWithinAt (s := Set.Ici 0)
  have h2 := (hasDerivAt_ctmcTransition_apply Q' i j 0).hasDerivWithinAt (s := Set.Ici 0)
  have h2' : HasDerivWithinAt (fun u => ctmcTransition Q u i j)
      ((Q' * ctmcTransition Q' 0) i j) (Set.Ici 0) 0 :=
    h2.congr (fun u hu => by rw [h u hu]) (by rw [h 0 le_rfl])
  have := (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv _ h1 h2'
  simpa using this

/-- **GTR identifiability from the transition function.** If `(π, s)` and `(π', s')` lie in the
GTR domain and give the same transition matrices `exp (t • Q)` at every time `t ≥ 0`, then
`π = π'` and `s = s'` off the diagonal. -/
theorem eq_and_offDiag_eq_of_ctmcTransition_eq {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ}
    (hp : IsGTRParam π s) (hp' : IsGTRParam π' s')
    (h : ∀ t, 0 ≤ t → ctmcTransition (gtrRate π s) t = ctmcTransition (gtrRate π' s') t) :
    π = π' ∧ ∀ i j, i ≠ j → s i j = s' i j :=
  (gtrRate_eq_iff hp hp').1 (eq_of_ctmcTransition_eq h)

/-! ## The pair-site law of one branch -/

/-- The **pair-site law** of a GTR branch of length `t`: the joint probability
`π i * P t i j` that a site is in state `i` at one end of the branch (drawn from the stationary
base frequencies) and in state `j` at the other end. This is the law of an aligned site
pattern for two taxa joined by a branch of length `t`. -/
noncomputable def gtrPairLaw (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) (i j : ι) : ℝ :=
  π i * ctmcTransition (gtrRate π s) t i j

/-- The row marginal of the pair-site law is the base-frequency vector. -/
theorem sum_gtrPairLaw_right {π : ι → ℝ} {s : Matrix ι ι ℝ} (hp : IsGTRParam π s) (t : ℝ)
    (i : ι) : ∑ j, gtrPairLaw π s t i j = π i := by
  simp only [gtrPairLaw, ← mul_sum,
    (isRateMatrix_gtrRate (fun k => (hp.pos k).le) fun a b h => (hp.offDiag_pos a b h).le)
      |>.sum_ctmcTransition, mul_one]

/-- The pair-site law is a probability distribution on pairs of states. -/
theorem sum_sum_gtrPairLaw {π : ι → ℝ} {s : Matrix ι ι ℝ} (hp : IsGTRParam π s) (t : ℝ) :
    ∑ i, ∑ j, gtrPairLaw π s t i j = 1 := by
  simp only [sum_gtrPairLaw_right hp, hp.sum_eq_one]

/-- The pair-site law is nonnegative for branch lengths `t ≥ 0`. -/
theorem gtrPairLaw_nonneg {π : ι → ℝ} {s : Matrix ι ι ℝ} (hp : IsGTRParam π s) {t : ℝ}
    (ht : 0 ≤ t) (i j : ι) : 0 ≤ gtrPairLaw π s t i j :=
  mul_nonneg (hp.pos i).le <| (isRateMatrix_gtrRate (fun k => (hp.pos k).le)
    fun a b h => (hp.offDiag_pos a b h).le).ctmcTransition_nonneg ht i j

/-- **Symmetry: rate and time are confounded in the pair-site law.** For every `c`,
`(π, c • s, t)` and `(π, s, c * t)` have the same pair-site law. -/
theorem gtrPairLaw_smul (π : ι → ℝ) (s : Matrix ι ι ℝ) (c t : ℝ) :
    gtrPairLaw π (c • s) t = gtrPairLaw π s (c * t) := by
  funext i j
  simp only [gtrPairLaw, ctmcTransition_gtrRate_smul]

/-! ## Identifiability from a single branch -/

open scoped Matrix.Norms.L2Operator in
/-- The real matrix exponential is injective on symmetric matrices (via the real logarithm of
the continuous functional calculus). -/
private lemma eq_of_exp_eq_of_isSymm {A B : Matrix ι ι ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  have hA' : IsSelfAdjoint A := by
    simpa [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      hA.eq
  have hB' : IsSelfAdjoint B := by
    simpa [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      hB.eq
  rw [← CFC.log_exp A hA', ← CFC.log_exp B hB', h]

/-- A generator in detailed balance with a positive vector `π` becomes symmetric after
conjugation by `diag (√π)`. -/
private lemma isSymm_conj_sqrt {π : ι → ℝ} (hπ : ∀ i, 0 < π i) {Q : Matrix ι ι ℝ}
    (hQ : IsDetailedBalance π Q) :
    (diagonal (fun i => √(π i)) * Q * diagonal (fun i => (√(π i))⁻¹)).IsSymm := by
  refine IsSymm.ext fun i j => ?_
  simp only [mul_diagonal, diagonal_mul]
  have hi := Real.sqrt_pos.2 (hπ i)
  have hj := Real.sqrt_pos.2 (hπ j)
  have h := hQ i j
  rw [← Real.mul_self_sqrt (hπ i).le, ← Real.mul_self_sqrt (hπ j).le] at h
  field_simp
  linear_combination (-1 : ℝ) * h

/-- **Reversible generators are determined by one transition matrix.** Two generators in
detailed balance with the same strictly positive vector `π` and with equal exponentials are
equal. (For non-reversible generators this fails: the matrix logarithm need not be unique.) -/
theorem eq_of_exp_eq_of_isDetailedBalance {π : ι → ℝ} (hπ : ∀ i, 0 < π i)
    {Q Q' : Matrix ι ι ℝ} (hQ : IsDetailedBalance π Q) (hQ' : IsDetailedBalance π Q')
    (h : NormedSpace.exp Q = NormedSpace.exp Q') : Q = Q' := by
  set D : Matrix ι ι ℝ := diagonal fun i => √(π i)
  set E : Matrix ι ι ℝ := diagonal fun i => (√(π i))⁻¹
  have hDE : D * E = 1 := by
    simp only [D, E, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 (hπ i)).ne'
  have hED : E * D = 1 := mul_eq_one_comm.1 hDE
  have hE : D⁻¹ = E := inv_eq_right_inv hDE
  have hU : IsUnit D := (isUnit_iff_isUnit_det D).2 (isUnit_det_of_right_inverse hDE)
  have hexp : NormedSpace.exp (D * Q * E) = NormedSpace.exp (D * Q' * E) := by
    rw [← hE, exp_conj _ _ hU, exp_conj _ _ hU, h]
  have hsym := eq_of_exp_eq_of_isSymm (isSymm_conj_sqrt hπ hQ) (isSymm_conj_sqrt hπ hQ') hexp
  have hcancel (M : Matrix ι ι ℝ) : E * (D * M * E) * D = M := by
    rw [show E * (D * M * E) * D = (E * D) * M * (E * D) by simp only [Matrix.mul_assoc], hED,
      Matrix.one_mul, Matrix.mul_one]
  rw [← hcancel Q, hsym, hcancel]

/-- The pair-site law at branch length `t` is the stationary joint law of the generator
`gtrRate π (t • s)` at unit time. -/
private lemma gtrPairLaw_eq_exp (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    gtrPairLaw π s t i j = π i * NormedSpace.exp (gtrRate π (t • s)) i j := by
  rw [gtrPairLaw, gtrRate_smul]
  rfl

/-- **GTR identifiability from a single branch, up to rate/time scaling.** Let `(π, s)` and
`(π', s')` lie in the GTR domain and `t, t' > 0` be branch lengths. Their pair-site laws agree
if and only if `π = π'` and the branch-scaled exchangeabilities agree off the diagonal,
`t * s i j = t' * s' i j`. Thus one branch identifies the base frequencies and the products
`t * s i j`, and nothing more: the only permitted symmetries are the rate/time scaling
`(s, t) ↦ (c • s, t / c)` (`gtrPairLaw_smul`) and the unused diagonal of `s`. This is a statement
about the law; it says nothing about estimators. -/
theorem gtrPairLaw_eq_iff {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ} {t t' : ℝ}
    (hp : IsGTRParam π s) (hp' : IsGTRParam π' s') (ht : 0 < t) (ht' : 0 < t') :
    gtrPairLaw π s t = gtrPairLaw π' s' t' ↔
      π = π' ∧ ∀ i j, i ≠ j → t * s i j = t' * s' i j := by
  constructor
  · intro h
    obtain rfl : π = π' := funext fun i => by
      rw [← sum_gtrPairLaw_right hp t i, ← sum_gtrPairLaw_right hp' t' i, h]
    have hexp : NormedSpace.exp (gtrRate π (t • s)) = NormedSpace.exp (gtrRate π (t' • s')) := by
      ext i j
      have := congrFun (congrFun h i) j
      rw [gtrPairLaw_eq_exp, gtrPairLaw_eq_exp] at this
      exact mul_left_cancel₀ (hp.pos i).ne' this
    have hQ := eq_of_exp_eq_of_isDetailedBalance hp.pos
      (isDetailedBalance_gtrRate π (hp.smul ht).symm)
      (isDetailedBalance_gtrRate π (hp'.smul ht').symm) hexp
    obtain ⟨-, h2⟩ := (gtrRate_eq_iff (hp.smul ht) (hp'.smul ht')).1 hQ
    exact ⟨rfl, fun i j hij => by simpa using h2 i j hij⟩
  · rintro ⟨rfl, h⟩
    have hQ : gtrRate π (t • s) = gtrRate π (t' • s') :=
      gtrRate_congr_offDiag π fun i j hij => by simpa using h i j hij
    funext i j
    rw [gtrPairLaw_eq_exp, gtrPairLaw_eq_exp, hQ]

/-- **GTR identifiability from a single branch of known length.** If the branch length
`t > 0` is fixed (for example by normalizing the expected substitution rate), the pair-site law
determines `π` and the off-diagonal exchangeabilities exactly. -/
theorem eq_and_offDiag_eq_of_gtrPairLaw_eq {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ} {t : ℝ}
    (hp : IsGTRParam π s) (hp' : IsGTRParam π' s') (ht : 0 < t)
    (h : gtrPairLaw π s t = gtrPairLaw π' s' t) :
    π = π' ∧ ∀ i j, i ≠ j → s i j = s' i j := by
  obtain ⟨h1, h2⟩ := (gtrPairLaw_eq_iff hp hp' ht ht).1 h
  exact ⟨h1, fun i j hij => mul_left_cancel₀ ht.ne' (h2 i j hij)⟩

/-! ## Relabeling the states in the pair-site law -/

/-- The matrix exponential commutes with relabeling the states by a permutation (conjugation by
the permutation matrix). -/
private lemma exp_submatrix_perm (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) :
    NormedSpace.exp (A.submatrix σ σ) = (NormedSpace.exp A).submatrix σ σ := by
  set U : Matrix ι ι ℝ := (σ : ι ≃ ι).toPEquiv.toMatrix
  set V : Matrix ι ι ℝ := (σ.symm : ι ≃ ι).toPEquiv.toMatrix
  have hconj (M : Matrix ι ι ℝ) : U * M * V = M.submatrix σ σ := by
    simp only [U, V, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have hUV : U * V = 1 := by
    have := hconj 1
    rwa [Matrix.mul_one, submatrix_one_equiv] at this
  have hV : U⁻¹ = V := inv_eq_right_inv hUV
  have hU : IsUnit U := (isUnit_iff_isUnit_det U).2 (isUnit_det_of_right_inverse hUV)
  rw [← hconj, ← hconj, ← hV, exp_conj _ _ hU]

/-- **Relabeling equivariance of the pair-site law.** Relabeling the states by `σ` relabels the
pair-site law. -/
theorem gtrPairLaw_comp_perm (π : ι → ℝ) (s : Matrix ι ι ℝ) (t : ℝ) (σ : Equiv.Perm ι)
    (i j : ι) : gtrPairLaw (π ∘ σ) (s.submatrix σ σ) t i j = gtrPairLaw π s t (σ i) (σ j) := by
  have hs : t • s.submatrix σ σ = (t • s).submatrix σ σ := rfl
  rw [gtrPairLaw_eq_exp, gtrPairLaw_eq_exp, hs, gtrRate_comp_perm, exp_submatrix_perm]
  rfl

/-- **Single-branch identifiability up to relabeling and rate/time scaling.** If the pair-site
law of `(π, s, t)` is observed only up to an unknown relabeling `σ` of the states, then any
`(π', s', t')` in the GTR domain with that law satisfies `π' = π ∘ σ` and
`t' * s' i j = t * s (σ i) (σ j)` off the diagonal. -/
theorem eq_comp_perm_of_gtrPairLaw_eq {π π' : ι → ℝ} {s s' : Matrix ι ι ℝ} {t t' : ℝ}
    (hp : IsGTRParam π s) (hp' : IsGTRParam π' s') (ht : 0 < t) (ht' : 0 < t')
    (σ : Equiv.Perm ι) (h : ∀ i j, gtrPairLaw π s t (σ i) (σ j) = gtrPairLaw π' s' t' i j) :
    π' = π ∘ σ ∧ ∀ i j, i ≠ j → t' * s' i j = t * s (σ i) (σ j) := by
  have h' : gtrPairLaw (π ∘ σ) (s.submatrix σ σ) t = gtrPairLaw π' s' t' := by
    funext i j
    rw [gtrPairLaw_comp_perm, h]
  obtain ⟨h1, h2⟩ := (gtrPairLaw_eq_iff (hp.comp_perm σ) hp' ht ht').1 h'
  exact ⟨h1.symm, fun i j hij => (h2 i j hij).symm⟩

/-! ## A submodel: K80 -/

/-- **K80 identifiability.** The K80 rate matrix (merged `SubstitutionModels.k80Rate`, with
transversion exchangeability fixed at `1`) determines the transition/transversion ratio `κ`. -/
theorem k80Rate_injective : Function.Injective k80Rate := by
  intro κ κ' h
  have := congrFun (congrFun h 0) 2
  simp [k80Rate, hkyRate, gtrRate, hkyExchangeability] at this
  linarith

end MathlibExt.Biology.Phylogenetics.GTRIdentifiability
