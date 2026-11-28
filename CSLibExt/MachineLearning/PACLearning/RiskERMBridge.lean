/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.RiskBridge
public import MathlibExt.Probability.Statistics.Learning.FiniteRisk

/-!
# Empirical risk minimization and the 0-1 bridges

The generalization-bound files measure a predictor by the loss-generic expected risk
`risk L ν h = ∫ L h z dν` and empirical risk `empiricalRisk L S h = (1/n) ∑ᵢ L h (Sᵢ)`
(F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Definitions 2.1 and 2.2).
CSLib's PAC library measures a hypothesis by the 0-1 `error` and `empiricalError`. This file adds
the empirical risk minimization rule over a class (S. Shalev-Shwartz and S. Ben-David,
*Understanding Machine Learning*, Cambridge University Press (2014), Section 2.3) and connects it
to both sides.

## Main definitions

- `IsERM L C S h`: `h ∈ C` minimizes the empirical risk `empiricalRisk L S` over `C`.
- `IsERMLearner L C A`: the learner `A` returns an empirical risk minimizer over `C` on every
  labelled sample (the rule `ERM_H` of Shalev-Shwartz and Ben-David, Section 2.3).

## Main results

- `empiricalRisk_zeroOneLoss_eq_toReal_empiricalError`: when singletons are measurable, the
  empirical 0-1 risk is CSLib's empirical error.
- `isERM_iff_isMinOn`: `IsERM L C S h` is `h ∈ C` with Mathlib's `IsMinOn` for the empirical risk.
- `exists_isERM_of_finite`, `exists_isERMLearner_of_finite`: a nonempty finite class has an
  empirical risk minimizer on every sample, hence an ERM learner.
- `isERM_zeroOneLoss_iff_mem_versionSpace`: on a realizable sample, the 0-1 empirical risk
  minimizers are exactly the version space.
- `isConsistent_iff_forall_realizable_isERM`, `IsERMLearner.isConsistent`: a learner is consistent
  exactly when it is a 0-1 empirical risk minimizer on every realizable sample; in particular
  every 0-1 ERM learner is consistent (Shalev-Shwartz and Ben-David, Section 2.3.1).
- `empiricalRisk_eq_inv_mul_sum`, `isERM_ermIdx`: the empirical risk is the inverse-size sample
  sum that `ProbabilityTheory.ermIdx` minimizes, so for a finite family `h : Fin M → H` the member
  `h (ermIdx (fun j => L (h j)) S)` is an empirical risk minimizer over `Set.range h`.
-/

@[expose] public section

namespace CSLibExt.MachineLearning.GeneralizationBounds

/-- **The empirical risk is the inverse-size sample sum.** On a nonempty sample `S`, the empirical
risk of `h` is `(n : ℝ)⁻¹ * ∑ i, L h (S i)`, the form of the empirical means that
`ProbabilityTheory.ermIdx_spec` compares. -/
theorem empiricalRisk_eq_inv_mul_sum {H Z : Type*} {n : ℕ} [NeZero n] (L : H → Z → ℝ)
    (S : Fin n → Z) (h : H) :
    empiricalRisk L S h = (n : ℝ)⁻¹ * ∑ i, L h (S i) := by
  unfold empiricalRisk
  rw [one_div]

end CSLibExt.MachineLearning.GeneralizationBounds

namespace Cslib.MachineLearning.PACLearning

open CSLibExt.MachineLearning.GeneralizationBounds (empiricalRisk empiricalRisk_eq_inv_mul_sum)

/-! ### The empirical 0-1 risk is CSLib's empirical error -/

/-- **The empirical 0-1 risk is CSLib's empirical error.** When singletons are measurable in `X`
and `Y`, on a nonempty labelled sample `S` the empirical risk of the 0-1 loss is the real value of
`empiricalError h S`, the mass that the empirical distribution of `S` puts on the disagreement set
of `h`. -/
theorem empiricalRisk_zeroOneLoss_eq_toReal_empiricalError {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    {n : ℕ} [NeZero n] (S : LabeledSample X Y n) (h : X → Y) :
    empiricalRisk zeroOneLoss S h = (empiricalError h S).toReal := by
  classical
  rw [empiricalRisk_zeroOneLoss_eq_miscount_div,
    empiricalError_eq_div (NeZero.pos n) h S, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-! ### Empirical risk minimization -/

/-- **Empirical risk minimizer.** For a real-valued loss `L h z`, a class `C` and a nonempty
sample `S`, the predictor `h` is an empirical risk minimizer over `C` on `S` if `h ∈ C` and no
member of `C` has smaller empirical risk on `S` (Shalev-Shwartz and Ben-David, *Understanding
Machine Learning*, 2014, Section 2.3: `ERM_H(S) ∈ argmin_{h ∈ H} L_S(h)`, with the empirical risk
`L_S(h) = (1/m) ∑ᵢ ℓ(h, zᵢ)` of a general loss from equation (3.4) in Section 3.2.2, where the
loss is nonnegative). Ties are allowed, so a sample can have several minimizers; over an empty
class there is none. -/
def IsERM {H Z : Type*} {n : ℕ} [NeZero n] (L : H → Z → ℝ) (C : Set H) (S : Fin n → Z)
    (h : H) : Prop :=
  h ∈ C ∧ ∀ h' ∈ C, empiricalRisk L S h ≤ empiricalRisk L S h'

/-- **An empirical risk minimizer minimizes the empirical risk on the class.** `IsERM L C S h`
holds exactly when `h ∈ C` and `IsMinOn (empiricalRisk L S) C h`, that is,
`empiricalRisk L S h ≤ empiricalRisk L S h'` for every `h' ∈ C`. -/
theorem isERM_iff_isMinOn {H Z : Type*} {n : ℕ} [NeZero n] {L : H → Z → ℝ} {C : Set H}
    {S : Fin n → Z} {h : H} :
    IsERM L C S h ↔ h ∈ C ∧ IsMinOn (empiricalRisk L S) C h :=
  Iff.rfl

/-- **ERM learner.** A learner `A` on samples of size `m ≥ 1` follows the empirical risk
minimization rule for the loss `L` over the class `C` if, on every labelled sample `S`, its output
`A S` is an empirical risk minimizer over `C` (the rule `ERM_H` of Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, Section 2.3, with the general-loss empirical risk of
equation (3.4)). No ERM learner exists over a class on which some sample has no minimizer; when
`X` and `Y` are nonempty, that includes the empty class. When `X` or `Y` is empty there is no
labelled sample, so every learner is vacuously an ERM learner. -/
def IsERMLearner {X Y : Type*} {m : ℕ} [NeZero m] (L : (X → Y) → X × Y → ℝ)
    (C : ConceptClass X Y) (A : Learner X Y m) : Prop :=
  ∀ S : LabeledSample X Y m, IsERM L C S (A S)

/-- **A nonempty finite class has an empirical risk minimizer** on every nonempty sample. -/
theorem exists_isERM_of_finite {H Z : Type*} {n : ℕ} [NeZero n] (L : H → Z → ℝ) {C : Set H}
    (hC : C.Finite) (hne : C.Nonempty) (S : Fin n → Z) :
    ∃ h, IsERM L C S h := by
  obtain ⟨h, hm, hmin⟩ := Set.exists_min_image C (empiricalRisk L S) hC hne
  exact ⟨h, hm, hmin⟩

/-- **A nonempty finite class has an ERM learner** for every loss and every sample size
`m ≥ 1`. -/
theorem exists_isERMLearner_of_finite {X Y : Type*} {m : ℕ} [NeZero m]
    (L : (X → Y) → X × Y → ℝ) {C : ConceptClass X Y} (hC : C.Finite) (hne : C.Nonempty) :
    ∃ A : Learner X Y m, IsERMLearner L C A := by
  have hchoice : ∀ S : LabeledSample X Y m, ∃ h, IsERM L C S h :=
    fun S => exists_isERM_of_finite L hC hne S
  choose A hA using hchoice
  exact ⟨A, hA⟩

/-! ### Realizable samples: 0-1 empirical risk minimizers are consistent hypotheses -/

/-- **On a realizable sample, the 0-1 empirical risk minimizers are the version space.** If some
concept of `C` labels the nonempty sample `S` correctly, then `h` minimizes the empirical 0-1 risk
over `C` exactly when `h ∈ C` agrees with every point of `S` (Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, Section 2.3.1). -/
theorem isERM_zeroOneLoss_iff_mem_versionSpace {X Y : Type*} {m : ℕ} [NeZero m]
    {C : ConceptClass X Y} {S : LabeledSample X Y m} (hS : Realizable C S) {h : X → Y} :
    IsERM zeroOneLoss C S h ↔ h ∈ VersionSpace C S := by
  classical
  obtain ⟨c, hcC, hcS⟩ := hS
  have hcV : c ∈ VersionSpace C S := mem_versionSpace_of_realizable hcC S hcS
  have hc0 : empiricalMiscount c S = 0 :=
    (mem_versionSpace_iff_empiricalMiscount_zero.mp hcV).2
  have hmc : ∀ g : X → Y, empiricalRisk zeroOneLoss S g = (empiricalMiscount g S : ℝ) / m :=
    fun g => empiricalRisk_zeroOneLoss_eq_miscount_div S g
  have hnn : ∀ g : X → Y, 0 ≤ empiricalRisk zeroOneLoss S g := by
    intro g
    rw [hmc g]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcz : empiricalRisk zeroOneLoss S c = 0 := by
    rw [hmc c, hc0, Nat.cast_zero, zero_div]
  constructor
  · intro hmin
    have hle : empiricalRisk zeroOneLoss S h ≤ 0 := by
      have h1 := hmin.2 c hcC
      rw [hcz] at h1
      exact h1
    have heq : empiricalRisk zeroOneLoss S h = 0 := le_antisymm hle (hnn h)
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    have hdiv : (empiricalMiscount h S : ℝ) / m = 0 := by
      rw [← hmc h]
      exact heq
    have hk0 : (empiricalMiscount h S : ℝ) = 0 :=
      (div_eq_zero_iff.mp hdiv).resolve_right (ne_of_gt hmpos)
    have hm0 : empiricalMiscount h S = 0 := by exact_mod_cast hk0
    exact mem_versionSpace_iff_empiricalMiscount_zero.mpr ⟨hmin.1, hm0⟩
  · intro hmem
    obtain ⟨hmC, hm0⟩ := mem_versionSpace_iff_empiricalMiscount_zero.mp hmem
    have heq : empiricalRisk zeroOneLoss S h = 0 := by
      rw [hmc h, hm0, Nat.cast_zero, zero_div]
    refine ⟨hmC, fun h' _ => ?_⟩
    rw [heq]
    exact hnn h'

/-- **Consistency is 0-1 empirical risk minimization on realizable samples.** A learner on samples
of size `m ≥ 1` is consistent with `C` exactly when, on every sample realizable by `C`, its output
minimizes the empirical 0-1 risk over `C`. -/
theorem isConsistent_iff_forall_realizable_isERM {X Y : Type*} {m : ℕ} [NeZero m]
    {C : ConceptClass X Y} {A : Learner X Y m} :
    IsConsistent A C ↔ ∀ S : LabeledSample X Y m, Realizable C S → IsERM zeroOneLoss C S (A S) := by
  constructor
  · intro hA S hS
    exact (isERM_zeroOneLoss_iff_mem_versionSpace hS).mpr (hA S hS)
  · intro hA S hS
    exact (isERM_zeroOneLoss_iff_mem_versionSpace hS).mp (hA S hS)

/-- **Every 0-1 ERM learner is consistent** with its class (Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, Section 2.3.1). -/
theorem IsERMLearner.isConsistent {X Y : Type*} {m : ℕ} [NeZero m] {C : ConceptClass X Y}
    {A : Learner X Y m} (hA : IsERMLearner zeroOneLoss C A) : IsConsistent A C := by
  rw [isConsistent_iff_forall_realizable_isERM]
  exact fun S _ => hA S

/-! ### Finite families: identification with `ProbabilityTheory.ermIdx` -/

/-- **The finite-family minimizer is an empirical risk minimizer.** For a nonempty finite family
`h : Fin M → H` and a nonempty sample `S`, the member selected by `ProbabilityTheory.ermIdx` for the
losses `f j := L (h j)` minimizes the empirical risk over `Set.range h`. -/
theorem isERM_ermIdx {H Z : Type*} [MeasurableSpace Z] {M n : ℕ} [NeZero M] [NeZero n]
    (L : H → Z → ℝ) (h : Fin M → H) (S : Fin n → Z) :
    IsERM L (Set.range h) S (h (ProbabilityTheory.ermIdx (fun j => L (h j)) S)) := by
  refine ⟨Set.mem_range_self _, fun h' hh' => ?_⟩
  obtain ⟨j, rfl⟩ := hh'
  rw [empiricalRisk_eq_inv_mul_sum, empiricalRisk_eq_inv_mul_sum]
  exact ProbabilityTheory.ermIdx_spec (fun j => L (h j)) S j

end Cslib.MachineLearning.PACLearning
