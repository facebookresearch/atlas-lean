/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The two-groups model: local and tail false discovery rates, Storey's pFDR

The *two-groups model* of Efron, Tibshirani, Storey and Tusher (2001): each case is null with
prior probability `π₀ ∈ [0, 1]`; its z-value has density `f₀` if it is null and `f₁` if not, so
that the z-values have the mixture density `f = π₀ f₀ + (1 - π₀) f₁`. The joint law of the
pair (null indicator, z-value) is `TwoGroupsModel.jointLaw` on `Bool × ℝ`, with `true` meaning
"the null hypothesis holds".

* `TwoGroupsModel.localFdr`: Efron's local false discovery rate `fdr(z) = π₀ f₀(z) / f(z)`.
* `TwoGroupsModel.tailFdr`: the tail-area false discovery rate of a region `Γ`,
  `Fdr(Γ) = π₀ P₀(Γ) / P(Γ)`; Efron's `Fdr(z)` is `tailFdr (Set.Iic z)`, and Storey's
  Bayesian `pFDR(Γ)` is the same quantity.
* `positiveFDR q m`: Storey's positive false discovery rate `E[V / R | R > 0]` for `m` tests
  whose (null, rejected) indicator pairs are i.i.d. with law `q`.
* `storeyPi0 t p`: Storey's estimator `π̂₀(t) = #{i | pᵢ > t} / (m (1 - t))`.
* `qValue pfdr t`: Storey's q-value `inf_{s ≥ t} pFDR(Γ_s)` for a nested family of
  rejection regions.

## Main results

* `localFdr_mul_mixtureDensity`: `fdr(z) f(z) = π₀ f₀(z)` for every `z`.
* `jointLaw_null_prod_eq_lintegral_localFdr`: `P(H = 0, Z ∈ A) = ∫_A fdr dP_Z`, i.e. `fdr(Z)` is
  a version of the posterior null probability `P(H = 0 | Z)` (Efron et al. 2001).
* `condExp_null_eq_localFdr`: the same statement as a conditional expectation,
  `E[1{H = 0} | Z] = fdr(Z)` almost surely.
* `cond_null_eq_tailFdr`: `P(H = 0 | Z ∈ Γ) = Fdr(Γ)` (the right-hand equality of
  Storey 2002, Theorem 1; Efron 2010, ch. 2).
* `tailFdr_eq_setIntegral_localFdr`: `Fdr(Γ) = E[fdr(Z) | Z ∈ Γ]` (Efron 2010, ch. 5).
* `positiveFDR_eq`: `pFDR = P(H = 0 | T ∈ Γ)` for i.i.d. tests (Storey 2002, Theorem 1), and
  `positiveFDR_pairLaw_eq_tailFdr` in the two-groups model.
* `le_integral_storeyPi0`: `E[π̂₀(t)] ≥ m₀ / m` for valid null p-values, `0 ≤ t < 1`, with
  no independence assumption (Storey's estimator is from Storey 2002).
* `qValue_le`, `monotone_qValue`, `qValue_eq_of_monotone`.

## References

* B. Efron, R. Tibshirani, J. D. Storey and V. Tusher, *Empirical Bayes analysis of a
  microarray experiment*, J. Amer. Statist. Assoc. 96 (2001), 1151–1160.
* B. Efron, *Large-Scale Inference*, Cambridge University Press (2010), ch. 2 and 5.
* J. D. Storey, *A direct approach to false discovery rates*, J. R. Stat. Soc. B 64 (2002),
  479–498.
* J. D. Storey, *The positive false discovery rate: a Bayesian interpretation and the
  q-value*, Ann. Statist. 31 (2003), 2013–2035.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.TwoGroupsTesting

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.MultipleTesting

/-! ### The two-groups model -/

/-- The two-groups model of Efron et al. (2001): prior null probability `π₀ ∈ [0, 1]`, null
density `f₀` and non-null density `f₁` of the z-value (probability densities on `ℝ`). -/
structure TwoGroupsModel where
  /-- Prior probability that a case is null. -/
  π₀ : ℝ
  /-- Density of the z-value of a null case. -/
  f₀ : ℝ → ℝ
  /-- Density of the z-value of a non-null case. -/
  f₁ : ℝ → ℝ
  /-- The prior null probability is nonnegative. -/
  π₀_nonneg : 0 ≤ π₀
  /-- The prior null probability is at most one. -/
  π₀_le_one : π₀ ≤ 1
  /-- The null density is nonnegative. -/
  f₀_nonneg : ∀ z, 0 ≤ f₀ z
  /-- The non-null density is nonnegative. -/
  f₁_nonneg : ∀ z, 0 ≤ f₁ z
  /-- The null density is measurable. -/
  measurable_f₀ : Measurable f₀
  /-- The non-null density is measurable. -/
  measurable_f₁ : Measurable f₁
  /-- The null density is integrable. -/
  integrable_f₀ : Integrable f₀
  /-- The non-null density is integrable. -/
  integrable_f₁ : Integrable f₁
  /-- The null density integrates to one. -/
  integral_f₀ : ∫ z, f₀ z = 1
  /-- The non-null density integrates to one. -/
  integral_f₁ : ∫ z, f₁ z = 1

namespace TwoGroupsModel

variable (M : TwoGroupsModel)

/-- The mixture density `f = π₀ f₀ + (1 - π₀) f₁` of the z-values. -/
noncomputable def mixtureDensity (z : ℝ) : ℝ := M.π₀ * M.f₀ z + (1 - M.π₀) * M.f₁ z

/-- The law `P₀` of a null z-value. -/
noncomputable def nullLaw : Measure ℝ := volume.withDensity fun z => ENNReal.ofReal (M.f₀ z)

/-- The law `P₁` of a non-null z-value. -/
noncomputable def altLaw : Measure ℝ := volume.withDensity fun z => ENNReal.ofReal (M.f₁ z)

/-- Joint law of (null indicator, z-value) on `Bool × ℝ`; `true` means the case is null. -/
noncomputable def jointLaw : Measure (Bool × ℝ) :=
  ENNReal.ofReal M.π₀ • (Measure.dirac true).prod M.nullLaw +
    ENNReal.ofReal (1 - M.π₀) • (Measure.dirac false).prod M.altLaw

/-- Efron's local false discovery rate `fdr(z) = π₀ f₀(z) / f(z)` (zero where `f(z) = 0`). -/
noncomputable def localFdr (z : ℝ) : ℝ := M.π₀ * M.f₀ z / M.mixtureDensity z

/-- The tail-area false discovery rate of a region `Γ`: `Fdr(Γ) = π₀ P₀(Γ) / P(Γ)`, written with
the densities. Efron's `Fdr(z)` is `tailFdr (Set.Iic z)`. It is `0` when `P(Γ) = 0`. -/
noncomputable def tailFdr (Γ : Set ℝ) : ℝ :=
  M.π₀ * (∫ z in Γ, M.f₀ z) / ∫ z in Γ, M.mixtureDensity z

/-- The mixture density is nonnegative. -/
theorem mixtureDensity_nonneg (z : ℝ) : 0 ≤ M.mixtureDensity z := by
  have := M.π₀_le_one
  have := M.π₀_nonneg
  have := M.f₀_nonneg z
  have := M.f₁_nonneg z
  unfold mixtureDensity
  nlinarith

/-- The null part of the mixture is dominated by the mixture: `π₀ f₀ ≤ f`. -/
theorem mul_f₀_le_mixtureDensity (z : ℝ) : M.π₀ * M.f₀ z ≤ M.mixtureDensity z := by
  have := M.π₀_le_one
  have := M.f₁_nonneg z
  unfold mixtureDensity
  nlinarith

/-- The mixture density is measurable. -/
theorem measurable_mixtureDensity : Measurable M.mixtureDensity :=
  (M.measurable_f₀.const_mul _).add (M.measurable_f₁.const_mul _)

/-- The mixture density is integrable. -/
theorem integrable_mixtureDensity : Integrable M.mixtureDensity :=
  (M.integrable_f₀.const_mul _).add (M.integrable_f₁.const_mul _)

/-- The local false discovery rate is measurable. -/
theorem measurable_localFdr : Measurable M.localFdr :=
  (M.measurable_f₀.const_mul _).div M.measurable_mixtureDensity

/-- The basic identity `fdr(z) f(z) = π₀ f₀(z)`, for every `z` (where `f(z) = 0` both sides
vanish because `π₀ f₀ ≤ f`). -/
theorem localFdr_mul_mixtureDensity (z : ℝ) :
    M.localFdr z * M.mixtureDensity z = M.π₀ * M.f₀ z := by
  unfold localFdr
  rcases eq_or_ne (M.mixtureDensity z) 0 with h | h
  · have h1 := M.mul_f₀_le_mixtureDensity z
    have h2 : 0 ≤ M.π₀ * M.f₀ z := mul_nonneg M.π₀_nonneg (M.f₀_nonneg z)
    rw [h] at h1 ⊢
    simp [le_antisymm h1 h2]
  · exact div_mul_cancel₀ _ h

/-- The local false discovery rate is nonnegative. -/
theorem localFdr_nonneg (z : ℝ) : 0 ≤ M.localFdr z :=
  div_nonneg (mul_nonneg M.π₀_nonneg (M.f₀_nonneg z)) (M.mixtureDensity_nonneg z)

/-- The local false discovery rate is at most one. -/
theorem localFdr_le_one (z : ℝ) : M.localFdr z ≤ 1 :=
  div_le_one_of_le₀ (M.mul_f₀_le_mixtureDensity z) (M.mixtureDensity_nonneg z)

private theorem withDensity_ofReal_apply {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z)
    {A : Set ℝ} (hA : MeasurableSet A) :
    volume.withDensity (fun z => ENNReal.ofReal (f z)) A = ENNReal.ofReal (∫ z in A, f z) := by
  rw [withDensity_apply _ hA, ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (Filter.Eventually.of_forall fun z => hf0 z)]

/-- `P₀(A) = ∫_A f₀`. -/
theorem nullLaw_apply {A : Set ℝ} (hA : MeasurableSet A) :
    M.nullLaw A = ENNReal.ofReal (∫ z in A, M.f₀ z) :=
  withDensity_ofReal_apply M.integrable_f₀ M.f₀_nonneg hA

/-- `P₁(A) = ∫_A f₁`. -/
theorem altLaw_apply {A : Set ℝ} (hA : MeasurableSet A) :
    M.altLaw A = ENNReal.ofReal (∫ z in A, M.f₁ z) :=
  withDensity_ofReal_apply M.integrable_f₁ M.f₁_nonneg hA

/-- The null law is a probability measure. -/
instance : IsProbabilityMeasure M.nullLaw :=
  ⟨by rw [nullLaw_apply M MeasurableSet.univ, Measure.restrict_univ, M.integral_f₀]; simp⟩

/-- The non-null law is a probability measure. -/
instance : IsProbabilityMeasure M.altLaw :=
  ⟨by rw [altLaw_apply M MeasurableSet.univ, Measure.restrict_univ, M.integral_f₁]; simp⟩

/-- `P(H = 0, Z ∈ A) = π₀ P₀(A)`. -/
theorem jointLaw_null_prod {A : Set ℝ} (hA : MeasurableSet A) :
    M.jointLaw ({true} ×ˢ A) = ENNReal.ofReal (M.π₀ * ∫ z in A, M.f₀ z) := by
  simp [jointLaw, Measure.prod_prod, M.nullLaw_apply hA,
    ENNReal.ofReal_mul M.π₀_nonneg]

/-- `P(H = 1, Z ∈ A) = (1 - π₀) P₁(A)`. -/
theorem jointLaw_alt_prod {A : Set ℝ} (hA : MeasurableSet A) :
    M.jointLaw ({false} ×ˢ A) = ENNReal.ofReal ((1 - M.π₀) * ∫ z in A, M.f₁ z) := by
  simp [jointLaw, Measure.prod_prod, M.altLaw_apply hA,
    ENNReal.ofReal_mul (sub_nonneg.2 M.π₀_le_one)]

/-- The z-value has the mixture law: `P(Z ∈ A) = ∫_A f`. -/
theorem jointLaw_univ_prod {A : Set ℝ} (hA : MeasurableSet A) :
    M.jointLaw (Set.univ ×ˢ A) = ENNReal.ofReal (∫ z in A, M.mixtureDensity z) := by
  have hu : (Set.univ : Set Bool) ×ˢ A = {true} ×ˢ A ∪ {false} ×ˢ A := by
    ext ⟨b, z⟩; cases b <;> simp
  rw [hu, measure_union _ ((measurableSet_singleton false).prod hA), M.jointLaw_null_prod hA,
    M.jointLaw_alt_prod hA, ← ENNReal.ofReal_add
      (mul_nonneg M.π₀_nonneg (setIntegral_nonneg hA fun z _ => M.f₀_nonneg z))
      (mul_nonneg (sub_nonneg.2 M.π₀_le_one) (setIntegral_nonneg hA fun z _ => M.f₁_nonneg z))]
  · unfold mixtureDensity
    rw [integral_add (M.integrable_f₀.const_mul _).integrableOn
      (M.integrable_f₁.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
  · rw [Set.disjoint_left]
    rintro ⟨b, z⟩ h1 h2
    simp_all

/-- The joint law is a probability measure. -/
instance : IsProbabilityMeasure M.jointLaw :=
  ⟨by
    rw [← Set.univ_prod_univ, M.jointLaw_univ_prod MeasurableSet.univ, Measure.restrict_univ]
    unfold mixtureDensity
    rw [integral_add (M.integrable_f₀.const_mul _) (M.integrable_f₁.const_mul _),
      integral_const_mul, integral_const_mul, M.integral_f₀, M.integral_f₁]
    simp⟩

/-- The law of the z-value under the joint law is the mixture `f · Lebesgue`. -/
theorem map_snd_jointLaw :
    M.jointLaw.map Prod.snd =
      volume.withDensity fun z => ENNReal.ofReal (M.mixtureDensity z) := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, ← Set.univ_prod, M.jointLaw_univ_prod hA,
    withDensity_ofReal_apply M.integrable_mixtureDensity M.mixtureDensity_nonneg hA]

/-- Efron et al. (2001): `P(H = 0, Z ∈ A) = ∫_A fdr(z) dP_Z(z)` for every measurable `A`, so
`fdr(Z)` is a version of the posterior null probability `P(H = 0 | Z)`. -/
theorem jointLaw_null_prod_eq_lintegral_localFdr {A : Set ℝ} (hA : MeasurableSet A) :
    M.jointLaw ({true} ×ˢ A) =
      ∫⁻ z in A, ENNReal.ofReal (M.localFdr z) ∂(M.jointLaw.map Prod.snd) := by
  rw [map_snd_jointLaw, setLIntegral_withDensity_eq_setLIntegral_mul _
    (M.measurable_mixtureDensity.ennreal_ofReal) M.measurable_localFdr.ennreal_ofReal hA,
    M.jointLaw_null_prod hA]
  simp only [Pi.mul_apply]
  simp_rw [← ENNReal.ofReal_mul (M.mixtureDensity_nonneg _), mul_comm (M.mixtureDensity _),
    M.localFdr_mul_mixtureDensity]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (M.integrable_f₀.const_mul _).integrableOn
    (Filter.Eventually.of_forall fun z => mul_nonneg M.π₀_nonneg (M.f₀_nonneg z)),
    integral_const_mul]

/-- Efron et al. (2001): `fdr(Z) = P(H = 0 | Z)` almost surely, as a conditional expectation
of the null indicator given the z-value. -/
theorem condExp_null_eq_localFdr :
    M.jointLaw[{p : Bool × ℝ | p.1 = true}.indicator 1 |
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[M.jointLaw] fun p => M.localFdr p.2 := by
  have hm : MeasurableSpace.comap (Prod.snd : Bool × ℝ → ℝ) inferInstance ≤
      (inferInstance : MeasurableSpace (Bool × ℝ)) :=
    measurable_snd.comap_le
  have hnull : MeasurableSet {p : Bool × ℝ | p.1 = true} :=
    measurable_fst (measurableSet_singleton true)
  have hg : Measurable fun p : Bool × ℝ => M.localFdr p.2 :=
    M.measurable_localFdr.comp measurable_snd
  have hgi : Integrable (fun p : Bool × ℝ => M.localFdr p.2) M.jointLaw :=
    Integrable.mono' (integrable_const 1) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (M.localFdr_nonneg _)]; exact M.localFdr_le_one _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    (by exact (integrable_const (1 : ℝ)).indicator hnull) (fun s _ _ => hgi.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨A, hA, rfl⟩ := hs
    have hset : Prod.snd ⁻¹' A ∩ {p : Bool × ℝ | p.1 = true} = {true} ×ˢ A := by
      ext ⟨b, z⟩; simp [and_comm]
    rw [integral_indicator_one hnull, Measure.real, Measure.restrict_apply hnull, Set.inter_comm,
      hset, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun p => M.localFdr_nonneg _) hg.aestronglyMeasurable,
      ← setLIntegral_map hA M.measurable_localFdr.ennreal_ofReal measurable_snd,
      ← M.jointLaw_null_prod_eq_lintegral_localFdr hA]
  · exact (M.measurable_localFdr.comp (comap_measurable Prod.snd)).aestronglyMeasurable

/-- `P(H = 0 | Z ∈ Γ) = Fdr(Γ)`: the tail-area false discovery rate is the posterior null
probability given `Z ∈ Γ` (Storey 2002, Theorem 1; Efron 2010, ch. 2). Both sides are `0` when
`P(Z ∈ Γ) = 0`. -/
theorem cond_null_eq_tailFdr {Γ : Set ℝ} (hΓ : MeasurableSet Γ) :
    (M.jointLaw[{p | p.1 = true} | Prod.snd ⁻¹' Γ]).toReal = M.tailFdr Γ := by
  have hs : Prod.snd ⁻¹' Γ ∩ {p : Bool × ℝ | p.1 = true} = {true} ×ˢ Γ := by
    ext ⟨b, z⟩; simp [and_comm]
  rw [cond_apply (measurable_snd hΓ), hs, ← Set.univ_prod, M.jointLaw_univ_prod hΓ,
    M.jointLaw_null_prod hΓ, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (setIntegral_nonneg hΓ fun z _ => M.mixtureDensity_nonneg z),
    ENNReal.toReal_ofReal (mul_nonneg M.π₀_nonneg
      (setIntegral_nonneg hΓ fun z _ => M.f₀_nonneg z)), tailFdr, inv_mul_eq_div]

/-- `E[fdr(Z) | Z ∈ Γ] = Fdr(Γ)`, written with densities: the tail-area false discovery rate is
the `f`-weighted average of the local false discovery rate over `Γ` (Efron 2010, ch. 5). -/
theorem tailFdr_eq_setIntegral_localFdr (Γ : Set ℝ) :
    M.tailFdr Γ =
      (∫ z in Γ, M.localFdr z * M.mixtureDensity z) / ∫ z in Γ, M.mixtureDensity z := by
  simp_rw [M.localFdr_mul_mixtureDensity, integral_const_mul, tailFdr]

end TwoGroupsModel

/-! ### Storey's positive false discovery rate for i.i.d. tests -/

variable {m : ℕ}

/-- The true-null set of an outcome vector `x : Fin m → Bool × Bool`, where `(x i).1` records
that hypothesis `i` is null and `(x i).2` that it is rejected. -/
def nullSet (x : Fin m → Bool × Bool) : Finset (Fin m) := univ.filter fun i => (x i).1 = true

/-- The rejection set of an outcome vector. -/
def rejectedSet (x : Fin m → Bool × Bool) : Finset (Fin m) :=
  univ.filter fun i => (x i).2 = true

/-- The probability `∏ᵢ q(xᵢ)` of an outcome vector when the `m` (null, rejected) pairs are
i.i.d. with law `q`. -/
def outcomeWeight (q : Bool × Bool → ℝ) (x : Fin m → Bool × Bool) : ℝ := ∏ i, q (x i)

/-- Storey's positive false discovery rate `pFDR = E[V / R | R > 0]` for `m` tests whose
(null, rejected) indicator pairs are i.i.d. with law `q`: `V / R` is the false discovery
proportion. -/
noncomputable def positiveFDR (q : Bool × Bool → ℝ) (m : ℕ) : ℝ :=
  (∑ x : Fin m → Bool × Bool, outcomeWeight q x *
      falseDiscoveryProportion (nullSet x) (rejectedSet x)) /
    ∑ x : Fin m → Bool × Bool, if (rejectedSet x).Nonempty then outcomeWeight q x else 0

private def swapTF : Bool × Bool → Bool × Bool
  | (b, true) => (!b, true)
  | u => u

private theorem swapTF_swapTF (u : Bool × Bool) : swapTF (swapTF u) = u := by
  rcases u with ⟨_ | _, _ | _⟩ <;> rfl

private theorem swapTF_snd (u : Bool × Bool) : (swapTF u).2 = u.2 := by
  rcases u with ⟨_ | _, _ | _⟩ <;> rfl

private theorem swapTF_eq_TT_iff (u : Bool × Bool) :
    swapTF u = (true, true) ↔ u = (false, true) := by
  rcases u with ⟨_ | _, _ | _⟩ <;> decide

private def flipAt (i : Fin m) (x : Fin m → Bool × Bool) : Fin m → Bool × Bool :=
  Function.update x i (swapTF (x i))

private theorem flipAt_involutive (i : Fin m) : Function.Involutive (flipAt i) := by
  intro x
  ext1 j
  by_cases hj : j = i
  · subst hj; simp [flipAt, swapTF_swapTF]
  · simp [flipAt, Function.update_of_ne hj]

private theorem rejectedSet_flipAt (i : Fin m) (x : Fin m → Bool × Bool) :
    rejectedSet (flipAt i x) = rejectedSet x := by
  unfold rejectedSet
  refine Finset.filter_congr fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp [flipAt, swapTF_snd]
  · simp [flipAt, Function.update_of_ne hj]

private theorem outcomeWeight_eq_mul (q : Bool × Bool → ℝ) (i : Fin m)
    (x : Fin m → Bool × Bool) :
    outcomeWeight q x = q (x i) * ∏ j ∈ ({i}ᶜ : Finset (Fin m)), q (x j) :=
  Fintype.prod_eq_mul_prod_compl i _

private theorem outcomeWeight_flipAt (q : Bool × Bool → ℝ) (i : Fin m)
    (x : Fin m → Bool × Bool) (hx : x i = (true, true)) :
    q (true, true) * outcomeWeight q (flipAt i x) = q (false, true) * outcomeWeight q x := by
  rw [outcomeWeight_eq_mul q i x, outcomeWeight_eq_mul q i (flipAt i x)]
  have h1 : flipAt i x i = (false, true) := by simp [flipAt, hx, swapTF]
  have h2 : ∏ j ∈ ({i}ᶜ : Finset (Fin m)), q (flipAt i x j) =
      ∏ j ∈ ({i}ᶜ : Finset (Fin m)), q (x j) :=
    Finset.prod_congr rfl fun j hj => by
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      simp [flipAt, Function.update_of_ne hj]
  rw [h1, h2, hx]
  ring

private noncomputable def denom (x : Fin m → Bool × Bool) : ℝ :=
  max ((rejectedSet x).card : ℝ) 1

private theorem key_i (q : Bool × Bool → ℝ) (i : Fin m) :
    q (false, true) * ∑ x : Fin m → Bool × Bool,
        (if x i = (true, true) then outcomeWeight q x / denom x else 0) =
      q (true, true) * ∑ x : Fin m → Bool × Bool,
        (if x i = (false, true) then outcomeWeight q x / denom x else 0) := by
  rw [← Equiv.sum_comp (flipAt_involutive i).toPerm]
  simp only [Function.Involutive.coe_toPerm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hfi : flipAt i x i = swapTF (x i) := by simp [flipAt]
  simp only [hfi]
  by_cases hx : x i = (false, true)
  · have hy : flipAt i x i = (true, true) := by simp [flipAt, hx, swapTF]
    have h := outcomeWeight_flipAt q i (flipAt i x) hy
    rw [flipAt_involutive i x] at h
    rw [ite_eq_left ((swapTF_eq_TT_iff _).2 hx), ite_eq_left hx, denom, denom,
      rejectedSet_flipAt, mul_div_assoc', mul_div_assoc', h]
  · rw [ite_eq_right (fun h => hx ((swapTF_eq_TT_iff _).1 h)), ite_eq_right hx]
    simp

private theorem rej_split (u : Bool × Bool) :
    (if u.2 = true then (1 : ℝ) else 0) =
      (if u = (true, true) then 1 else 0) + (if u = (false, true) then 1 else 0) := by
  rcases u with ⟨_ | _, _ | _⟩ <;> norm_num

private theorem card_inter_eq (x : Fin m → Bool × Bool) :
    ((rejectedSet x ∩ nullSet x).card : ℝ) = ∑ i, if x i = (true, true) then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 2
  ext i
  rcases hxi : x i with ⟨_ | _, _ | _⟩ <;> simp [rejectedSet, nullSet, hxi]

private theorem card_rej_eq (x : Fin m → Bool × Bool) :
    ((rejectedSet x).card : ℝ) = ∑ i, if (x i).2 = true then 1 else 0 := by
  rw [Finset.sum_boole]
  rfl

private theorem key (q : Bool × Bool → ℝ) :
    (q (true, true) + q (false, true)) * ∑ x : Fin m → Bool × Bool, outcomeWeight q x *
        falseDiscoveryProportion (nullSet x) (rejectedSet x) =
      q (true, true) * ∑ x : Fin m → Bool × Bool,
        outcomeWeight q x * ((rejectedSet x).card : ℝ) / denom x := by
  have hN : ∑ x : Fin m → Bool × Bool, outcomeWeight q x *
      falseDiscoveryProportion (nullSet x) (rejectedSet x) =
      ∑ i, ∑ x : Fin m → Bool × Bool,
        (if x i = (true, true) then outcomeWeight q x / denom x else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [falseDiscoveryProportion, card_inter_eq, ← denom]
    rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hR : ∑ x : Fin m → Bool × Bool,
      outcomeWeight q x * ((rejectedSet x).card : ℝ) / denom x =
      ∑ i, (∑ x : Fin m → Bool × Bool,
        (if x i = (true, true) then outcomeWeight q x / denom x else 0) +
        ∑ x : Fin m → Bool × Bool,
        (if x i = (false, true) then outcomeWeight q x / denom x else 0)) := by
    simp_rw [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [card_rej_eq, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rej_split (x i)]
    split_ifs <;> ring
  rw [hN, hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_add, ← key_i q i]
  ring

/-- Storey (2002), Theorem 1: for `m ≥ 1` i.i.d. tests, `pFDR = P(H = 0 | T ∈ Γ)`, where
`q (true, true) = P(H = 0, T ∈ Γ)` and `q (false, true) = P(H = 1, T ∈ Γ)`. The identity is
homogeneous in `q`, so only `q ≥ 0` is assumed; when `P(T ∈ Γ) = 0` both sides are `0`. -/
theorem positiveFDR_eq (q : Bool × Bool → ℝ) (hq : ∀ b, 0 ≤ q b) (hm : 0 < m) :
    positiveFDR q m = q (true, true) / (q (true, true) + q (false, true)) := by
  have hW : ∀ x : Fin m → Bool × Bool, 0 ≤ outcomeWeight q x :=
    fun x => Finset.prod_nonneg fun i _ => hq _
  have hD : ∑ x : Fin m → Bool × Bool,
      outcomeWeight q x * ((rejectedSet x).card : ℝ) / denom x =
      ∑ x : Fin m → Bool × Bool, if (rejectedSet x).Nonempty then outcomeWeight q x else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · have h1 : (1 : ℝ) ≤ (rejectedSet x).card := by exact_mod_cast h.card_pos
      rw [denom, max_eq_left h1, mul_div_assoc, div_self (by linarith), mul_one]
    · simp [Finset.not_nonempty_iff_eq_empty.1 h]
  have hk := key (m := m) q
  rw [hD] at hk
  unfold positiveFDR
  rcases (add_nonneg (hq (true, true)) (hq (false, true))).eq_or_lt with hab | hab
  · have ha : q (true, true) = 0 := by linarith [hq (true, true), hq (false, true)]
    rw [← hab, div_zero]
    have hN : ∑ x : Fin m → Bool × Bool, outcomeWeight q x *
        falseDiscoveryProportion (nullSet x) (rejectedSet x) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : ∃ i, x i = (true, true)
      · obtain ⟨i, hi⟩ := hx
        rw [outcomeWeight_eq_mul q i, hi, ha]
        simp
      · push Not at hx
        have : rejectedSet x ∩ nullSet x = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun i hi => hx i ?_
          simp only [rejectedSet, nullSet, Finset.mem_inter, Finset.mem_filter_univ] at hi
          exact Prod.ext hi.2 hi.1
        simp [falseDiscoveryProportion, this]
    rw [hN, zero_div]
  · have hDpos : 0 < ∑ x : Fin m → Bool × Bool,
        if (rejectedSet x).Nonempty then outcomeWeight q x else 0 := by
      set u : Bool × Bool := if 0 < q (true, true) then (true, true) else (false, true)
      have hu : 0 < q u := by
        simp only [u]
        split_ifs with h
        · exact h
        · linarith [hq (true, true)]
      have hu2 : u.2 = true := by simp only [u]; split_ifs <;> rfl
      have hne : (rejectedSet fun _ : Fin m => u).Nonempty :=
        ⟨⟨0, hm⟩, by simp [rejectedSet, hu2]⟩
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun x : Fin m → Bool × Bool =>
        if (rejectedSet x).Nonempty then outcomeWeight q x else 0)
        (fun x _ => by split_ifs <;> simp [hW x]) (Finset.mem_univ fun _ => u))
      rw [ite_eq_left hne]
      exact Finset.prod_pos fun _ _ => hu
    rw [div_eq_div_iff hDpos.ne' hab.ne']
    linarith

namespace TwoGroupsModel

variable (M : TwoGroupsModel)

/-- The law of one test's (null, rejected) pair in the two-groups model when the test rejects
iff its z-value lies in `Γ`. -/
noncomputable def pairLaw (Γ : Set ℝ) (b : Bool × Bool) : ℝ :=
  (M.jointLaw ({b.1} ×ˢ if b.2 then Γ else Γᶜ)).toReal

/-- Storey (2002), Theorem 1, in the two-groups model: for `m ≥ 1` i.i.d. tests rejecting on
`Γ`, `pFDR(Γ) = π₀ P₀(Γ) / P(Γ) = Fdr(Γ)`. -/
theorem positiveFDR_pairLaw_eq_tailFdr {Γ : Set ℝ} (hΓ : MeasurableSet Γ) (hm : 0 < m) :
    positiveFDR (M.pairLaw Γ) m = M.tailFdr Γ := by
  rw [positiveFDR_eq (M.pairLaw Γ) (fun b => ENNReal.toReal_nonneg) hm]
  simp only [pairLaw, ite_true]
  rw [M.jointLaw_null_prod hΓ, M.jointLaw_alt_prod hΓ,
    ENNReal.toReal_ofReal (mul_nonneg M.π₀_nonneg
      (setIntegral_nonneg hΓ fun z _ => M.f₀_nonneg z)),
    ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.2 M.π₀_le_one)
      (setIntegral_nonneg hΓ fun z _ => M.f₁_nonneg z)), tailFdr]
  congr 1
  unfold mixtureDensity
  rw [integral_add (M.integrable_f₀.const_mul _).integrableOn
    (M.integrable_f₁.const_mul _).integrableOn, integral_const_mul, integral_const_mul]

end TwoGroupsModel

/-! ### Storey's estimator of the null proportion -/

/-- Storey's estimator `π̂₀(t) = #{i | pᵢ > t} / (m (1 - t))` of the proportion of true nulls,
for a tuning parameter `t ∈ [0, 1)`. -/
noncomputable def storeyPi0 (t : ℝ) (p : Fin m → ℝ) : ℝ :=
  ((univ.filter fun i => t < p i).card : ℝ) / (m * (1 - t))

/-- Conservative bias of Storey's (2002) estimator for a fixed set `H0` of true nulls: if their
p-values are valid, then `E[π̂₀(t)] ≥ m₀ / m` for every `t ∈ [0, 1)`. No independence is
assumed; the non-null p-values are arbitrary measurable functions. -/
theorem le_integral_storeyPi0 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i))
    {H0 : Finset (Fin m)} (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    (H0.card : ℝ) / m ≤ ∫ ω, storeyPi0 t (fun i => p i ω) ∂μ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [storeyPi0]
  have hc : 0 < (m : ℝ) * (1 - t) := mul_pos (by exact_mod_cast hm) (by linarith)
  have hmeas : ∀ i, MeasurableSet {ω | t < p i ω} :=
    fun i => measurableSet_lt measurable_const (hp i)
  have key : ∀ ω, storeyPi0 t (fun i => p i ω) =
      (∑ i, Set.indicator {ω | t < p i ω} (1 : Ω → ℝ) ω) / (m * (1 - t)) := by
    intro ω
    simp [storeyPi0, Set.indicator_apply, Finset.sum_boole]
  simp_rw [key]
  rw [integral_div, integral_finsetSum _ fun i _ => by
    exact (integrable_const (1 : ℝ)).indicator (hmeas i)]
  simp_rw [integral_indicator_one (hmeas _)]
  rw [div_le_div_iff₀ (by exact_mod_cast hm) hc]
  have hi : ∀ i ∈ H0, 1 - t ≤ μ.real {ω | t < p i ω} := by
    intro i hi
    have h := hnull i hi t ⟨ht0, ht1.le⟩
    have h' : μ.real {ω | p i ω ≤ t} ≤ t := ENNReal.toReal_le_of_le_ofReal ht0 h
    have hcomp : {ω | t < p i ω} = {ω | p i ω ≤ t}ᶜ := by ext ω; simp
    rw [hcomp, probReal_compl_eq_one_sub (measurableSet_le (hp i) measurable_const)]
    linarith
  calc (H0.card : ℝ) * (m * (1 - t)) = (m : ℝ) * ∑ i ∈ H0, (1 - t) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (m : ℝ) * ∑ i ∈ H0, μ.real {ω | t < p i ω} :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hi) (Nat.cast_nonneg _)
    _ ≤ (m : ℝ) * ∑ i, μ.real {ω | t < p i ω} :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => measureReal_nonneg) (Nat.cast_nonneg _)
    _ = (∑ i, μ.real {ω | t < p i ω}) * m := mul_comm _ _

/-! ### Storey's q-value -/

/-- Storey's (2003) q-value for a nested family of rejection regions `Γ_s = {T ≤ s}` with
`pFDR(Γ_s) = pfdr s`: `q(t) = inf_{s ≥ t} pfdr s`, the smallest pFDR over the regions that
contain the observed statistic `t`. -/
noncomputable def qValue (pfdr : ℝ → ℝ) (t : ℝ) : ℝ := ⨅ s : Set.Ici t, pfdr s

private theorem bddBelow_range_Ici {pfdr : ℝ → ℝ} (h0 : ∀ s, 0 ≤ pfdr s) (t : ℝ) :
    BddBelow (Set.range fun s : Set.Ici t => pfdr s) :=
  ⟨0, by rintro _ ⟨s, rfl⟩; exact h0 s⟩

/-- The q-value is at most the pFDR of the smallest region containing the statistic. -/
theorem qValue_le {pfdr : ℝ → ℝ} (h0 : ∀ s, 0 ≤ pfdr s) (t : ℝ) : qValue pfdr t ≤ pfdr t :=
  ciInf_le (bddBelow_range_Ici h0 t) (⟨t, le_rfl⟩ : Set.Ici t)

/-- The q-value is monotone in the statistic. -/
theorem monotone_qValue {pfdr : ℝ → ℝ} (h0 : ∀ s, 0 ≤ pfdr s) : Monotone (qValue pfdr) := by
  intro t₁ t₂ h
  refine le_ciInf fun s => ?_
  exact ciInf_le (bddBelow_range_Ici h0 t₁) (⟨s, h.trans s.2⟩ : Set.Ici t₁)

/-- When the pFDR is nondecreasing along the nested regions, the q-value is the pFDR. -/
theorem qValue_eq_of_monotone {pfdr : ℝ → ℝ} (h : Monotone pfdr) (t : ℝ) :
    qValue pfdr t = pfdr t := by
  have hb : BddBelow (Set.range fun s : Set.Ici t => pfdr s) :=
    ⟨pfdr t, by rintro _ ⟨s, rfl⟩; exact h s.2⟩
  exact le_antisymm (ciInf_le hb (⟨t, le_rfl⟩ : Set.Ici t)) (le_ciInf fun s => h s.2)

end MathlibExt.Probability.Statistics.TwoGroupsTesting
