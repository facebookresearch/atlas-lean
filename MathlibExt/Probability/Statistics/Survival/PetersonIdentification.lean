/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.IdentifiableHazardContinuous

/-!
# Identification under an unknown censoring law (Peterson's argument)

`IdentifiableHazardContinuous` shows that, for a **fixed** censoring law `G`, the law of the
right-censored observation `(X, δ) = (T ∧ C, 1{T ≤ C})` determines the failure-time law `F` on
`{s | G[s, ∞) ≠ 0}`. Here the censoring law is unknown and may vary with the parameter: two pairs
`(F, G)` and `(F', G')` with `G ≠ G'` are allowed to produce the same observed-data law. Peterson's
argument shows that the failure-time law is still identified, on the set of times at which a
subject is at risk with positive probability:

1. Both the observed-failure sub-distribution `P(X ∈ ds, δ = 1) = G[s, ∞) dF(s)` and the at-risk
   mass `P(X ≥ s) = F[s, ∞) G[s, ∞)` are functionals of the observed-data law alone.
2. Their ratio is the hazard `dΛ = dF / F[s, ∞)`, whatever the censoring law: the hazard is an
   explicit functional of the observed-data law on `{s | P(X ≥ s) > 0}`.
3. The hazard determines the law: if two laws have the same hazard on `(-∞, h]` and
   `F[h, ∞) ≠ 0`, then `S(t) = 1 - ∫_{(-∞, t)} S dΛ` has a unique solution on `(-∞, h]`
   (a Gronwall-type argument valid for hazards with atoms), so the two laws agree on
   `(-∞, h]`.

## Definitions

* `obsAtRisk P s = P([s, ∞) × Bool)`: the at-risk mass `P(X ≥ s)` of an observed-data law.
* `obsFailMeasure P`: the observed-failure sub-distribution `A ↦ P(X ∈ A, δ = 1)`.
* `atRiskSet P = {s | P(X ≥ s) ≠ 0}`, a down-set (`atRiskSet_downward`).

## Main results

* `censoredObsLaw_apply_Ici_prod_univ`: `P(X ≥ s) = F[s, ∞) G[s, ∞)`.
* `obsFailMeasure_censoredObsLaw`: `P(X ∈ ds, δ = 1) = G[s, ∞) dF(s)`.
* `hazardMeasure_restrict_Iic_eq_peterson`: **Peterson representation**: if `P(X ≥ h) ≠ 0`, then
  on `(-∞, h]` the hazard of `F` is `obsFailMeasure P / obsAtRisk P`, a functional of the
  observed-data law `P = censoredObsLaw F G` that does not involve `G`.
* `hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk`: two pairs `(F, G)`, `(F', G')`
  with the same observed-data law have the same hazard on `(-∞, h]` when `P(X ≥ h) ≠ 0`.
* `setLIntegral_measure_Ici_hazardMeasure`: `F A = ∫_A F[s, ∞) dΛ(s)`.
* `eq_zero_of_le_setLIntegral_Iio`: Gronwall-type uniqueness for `e(t) ≤ ∫_{(-∞, t)} e dΛ` with a
  finite measure `Λ` (atoms allowed).
* `restrict_Iic_eq_of_hazardMeasure_restrict_Iic_eq`: **the hazard determines the law**: laws
  with the same hazard on `(-∞, h]` agree on `(-∞, h]` when `F[h, ∞) ≠ 0`.
* `restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk`: **identification with an unknown censoring
  law**: if `censoredObsLaw F G = censoredObsLaw F' G'` and `P(X ≥ h) ≠ 0`, then `F` and `F'`
  agree on `(-∞, h]`; `measure_Ici_eq_of_censoredObsLaw_eq_of_atRisk` is the survival function.
* `restrict_atRiskSet_eq_of_censoredObsLaw_eq`: `F` and `F'` agree on the whole at-risk set.
* `parameter_eq_of_censoredObsLaw_eq`: **parametric identification with a parameter-varying,
  unknown censoring law**: for failure laws `F θ` and censoring laws `G θ η` (depending on the
  parameter `θ` and a nuisance `η` in an arbitrary way), if `θ ↦ (F θ)|_{(-∞, h]}` is injective
  and every model has `P(X ≥ h) ≠ 0`, then the observed-data law determines `θ`.

## Scope

Single-subject observed-data law under independent censoring (`T ⊥ C`, as in
`IdentifiableHazardContinuous`); `F, F'` are arbitrary Borel probability laws on `ℝ` (atoms
allowed), `G, G'` arbitrary finite Borel measures, ties count as failures. The censoring laws
themselves are not shown to be identified. Peterson's closed-form expression of the survival
function as a product integral of the sub-survival functions is not formalized; identification
is obtained from the hazard representation and the uniqueness of the solution of the Volterra
equation `S(t) = 1 - ∫_{(-∞, t)} S dΛ` instead.

## Reused API (source receipts)

* `censoredObsLaw`, `censoredObsMap`, `measurable_censoredObsMap`,
  `censoredObsLaw_apply_prod_true` (`IdentifiableHazardContinuous.lean`): reused; the
  fixed-`G` theorems of that file are special cases of the results here and are not re-proved.
* `hazardMeasure`, `measurable_measure_Ici`, `ae_measure_Ici_ne_zero` (`CountingProcess.lean`).
* `MeasureTheory.withDensity_mul`, `restrict_withDensity`, `withDensity_congr_ae`,
  `setLIntegral_withDensity_eq_setLIntegral_mul` (`Mathlib/MeasureTheory/Measure/WithDensity.lean`);
  `MeasureTheory.Measure.ext_of_Iic` (`Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`);
  `MeasureTheory.lintegral_sub_le` (`Mathlib/MeasureTheory/Integral/Lebesgue/Sub.lean`);
  `MeasureTheory.tendsto_measure_iInter_atTop` (`Mathlib/MeasureTheory/Measure/Continuity.lean`);
  `MeasureTheory.Measure.restrict_iUnion_congr` (`Mathlib/MeasureTheory/Measure/Restrict.lean`).

## References

* A. V. Peterson, *Expressing the Kaplan-Meier estimator as a function of empirical subsurvival
  functions*, J. Amer. Statist. Assoc. 72 (1977), 854–858 (the survival function is a functional
  of the observable sub-survival functions, without reference to the censoring law).
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section III.2.2 (the hazard is identified on `{s : P(X ≥ s) > 0}`)
  and Section II.6 (product integrals and the Volterra equation for the survival function).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-! ### Observed-data functionals -/

/-- The **at-risk mass** `P(X ≥ s)` of an observed-data law `P` on `ℝ × Bool`. -/
noncomputable def obsAtRisk (P : Measure (ℝ × Bool)) (s : ℝ) : ℝ≥0∞ := P (Ici s ×ˢ univ)

/-- The **observed-failure sub-distribution** `A ↦ P(X ∈ A, δ = 1)` of an observed-data law. -/
noncomputable def obsFailMeasure (P : Measure (ℝ × Bool)) : Measure ℝ :=
  (P.restrict (univ ×ˢ {true})).map Prod.fst

/-- The **at-risk set** `{s | P(X ≥ s) ≠ 0}` of an observed-data law. -/
def atRiskSet (P : Measure (ℝ × Bool)) : Set ℝ := {s | obsAtRisk P s ≠ 0}

/-- The at-risk mass is antitone in `s`, hence measurable. -/
theorem measurable_obsAtRisk (P : Measure (ℝ × Bool)) : Measurable (obsAtRisk P) :=
  Antitone.measurable fun _ _ h => measure_mono (prod_mono (Ici_subset_Ici.2 h) subset_rfl)

/-- The at-risk set is a down-set. -/
theorem atRiskSet_downward {P : Measure (ℝ × Bool)} {s s' : ℝ} (hs : s ∈ atRiskSet P)
    (hs' : s' ≤ s) : s' ∈ atRiskSet P :=
  fun h0 => hs (measure_mono_null (prod_mono (Ici_subset_Ici.2 hs') subset_rfl) h0)

/-- `obsFailMeasure P A = P(A × {true})`. -/
theorem obsFailMeasure_apply (P : Measure (ℝ × Bool)) {A : Set ℝ} (hA : MeasurableSet A) :
    obsFailMeasure P A = P (A ×ˢ {true}) := by
  rw [obsFailMeasure, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext ⟨t, b⟩
  simp

/-- **At-risk mass under independent censoring**: `P(X ≥ s) = F[s, ∞) G[s, ∞)`. -/
theorem censoredObsLaw_apply_Ici_prod_univ (F G : Measure ℝ) [SFinite F] [SFinite G] (s : ℝ) :
    censoredObsLaw F G (Ici s ×ˢ univ) = F (Ici s) * G (Ici s) := by
  have hpre : censoredObsMap ⁻¹' (Ici s ×ˢ univ) = Ici s ×ˢ Ici s := by
    ext ⟨t, c⟩
    simp only [censoredObsMap, obsTime, mem_preimage, mem_prod, mem_Ici, mem_univ, and_true,
      le_min_iff]
  rw [censoredObsLaw, Measure.map_apply measurable_censoredObsMap
    (measurableSet_Ici.prod MeasurableSet.univ), hpre, Measure.prod_prod]

/-- **Observed failures under independent censoring**: `P(X ∈ ds, δ = 1) = G[s, ∞) dF(s)`. -/
theorem obsFailMeasure_censoredObsLaw (F G : Measure ℝ) [SFinite G] :
    obsFailMeasure (censoredObsLaw F G) = F.withDensity fun t => G (Ici t) := by
  ext A hA
  rw [obsFailMeasure_apply _ hA, censoredObsLaw_apply_prod_true F G hA, withDensity_apply _ hA]

/-! ### The Peterson representation of the hazard -/

/-- `a⁻¹ = b (a b)⁻¹` for nonzero finite `a, b`. -/
private lemma inv_eq_mul_inv_mul {a b : ℝ≥0∞} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hat : a ≠ ∞)
    (hbt : b ≠ ∞) : a⁻¹ = b * (a * b)⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl hat), mul_comm b, mul_assoc,
    ENNReal.inv_mul_cancel hb0 hbt, mul_one]

variable {F F' G G' : Measure ℝ}

/-- **Peterson representation of the hazard.** If the observed-data law `P = censoredObsLaw F G`
has `P(X ≥ h) ≠ 0`, then on `(-∞, h]` the hazard of `F` is the observed-failure
sub-distribution divided by the at-risk mass: `dΛ(s) = P(X ∈ ds, δ = 1) / P(X ≥ s)`. The right
side is a functional of `P` alone; the censoring law `G` does not enter. -/
theorem hazardMeasure_restrict_Iic_eq_peterson [IsFiniteMeasure F] [IsFiniteMeasure G] {h : ℝ}
    (hh : obsAtRisk (censoredObsLaw F G) h ≠ 0) :
    (hazardMeasure F).restrict (Iic h) =
      ((obsFailMeasure (censoredObsLaw F G)).restrict (Iic h)).withDensity
        fun s => (obsAtRisk (censoredObsLaw F G) s)⁻¹ := by
  set P := censoredObsLaw F G
  have hH : ∀ s, obsAtRisk P s = F (Ici s) * G (Ici s) := fun s =>
    censoredObsLaw_apply_Ici_prod_univ F G s
  rw [hazardMeasure, restrict_withDensity measurableSet_Iic, obsFailMeasure_censoredObsLaw,
    restrict_withDensity measurableSet_Iic,
    ← withDensity_mul _ (f := fun t => G (Ici t)) (g := fun s => (obsAtRisk P s)⁻¹)
      (measurable_measure_Ici G) (measurable_obsAtRisk P).inv]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Iic).2
    (Eventually.of_forall fun s hs => ?_))
  have hpos : obsAtRisk P s ≠ 0 := atRiskSet_downward hh hs
  rw [hH] at hpos
  change (F (Ici s))⁻¹ = G (Ici s) * (obsAtRisk P s)⁻¹
  rw [hH s]
  obtain ⟨hF0, hG0⟩ := mul_ne_zero_iff.1 hpos
  exact inv_eq_mul_inv_mul hF0 hG0 (measure_ne_top _ _) (measure_ne_top _ _)

/-- **The hazard is identified under an unknown censoring law.** Two pairs `(F, G)` and
`(F', G')` with the same observed-data law `P` have the same hazard on `(-∞, h]` whenever
`P(X ≥ h) ≠ 0`. -/
theorem hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk [IsFiniteMeasure F]
    [IsFiniteMeasure F'] [IsFiniteMeasure G] [IsFiniteMeasure G']
    (heq : censoredObsLaw F G = censoredObsLaw F' G') {h : ℝ}
    (hh : obsAtRisk (censoredObsLaw F G) h ≠ 0) :
    (hazardMeasure F).restrict (Iic h) = (hazardMeasure F').restrict (Iic h) := by
  rw [hazardMeasure_restrict_Iic_eq_peterson hh,
    hazardMeasure_restrict_Iic_eq_peterson (heq ▸ hh), heq]

/-! ### The hazard determines the law -/

/-- `F A = ∫_A F[s, ∞) dΛ(s)`: a law is recovered from its hazard and its survival function. -/
theorem setLIntegral_measure_Ici_hazardMeasure (F : Measure ℝ) [IsFiniteMeasure F] {A : Set ℝ}
    (hA : MeasurableSet A) : ∫⁻ s in A, F (Ici s) ∂(hazardMeasure F) = F A := by
  rw [hazardMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _
    (f := fun s => (F (Ici s))⁻¹) (g := fun s => F (Ici s))
    (measurable_measure_Ici F).inv (measurable_measure_Ici F) hA]
  calc ∫⁻ s in A, ((fun s => (F (Ici s))⁻¹) * fun s => F (Ici s)) s ∂F
      = ∫⁻ _ in A, 1 ∂F := by
        refine setLIntegral_congr_fun_ae hA ?_
        filter_upwards [ae_measure_Ici_ne_zero F] with s hs _
        exact ENNReal.inv_mul_cancel hs (measure_ne_top _ _)
    _ = F A := by rw [setLIntegral_const, one_mul]

/-- The hazard of `(-∞, t₁]` is at most `F(-∞, t₁] / F[t₁, ∞)`, finite when `F[t₁, ∞) ≠ 0`. -/
theorem hazardMeasure_Iic_lt_top (F : Measure ℝ) [IsFiniteMeasure F] {t₁ : ℝ}
    (hF : F (Ici t₁) ≠ 0) : hazardMeasure F (Iic t₁) < ∞ := by
  rw [hazardMeasure, withDensity_apply _ measurableSet_Iic]
  calc ∫⁻ s in Iic t₁, (F (Ici s))⁻¹ ∂F
      ≤ ∫⁻ _ in Iic t₁, (F (Ici t₁))⁻¹ ∂F :=
        setLIntegral_mono measurable_const fun s hs =>
          ENNReal.inv_le_inv.2 (measure_mono (Ici_subset_Ici.2 hs))
    _ = (F (Ici t₁))⁻¹ * F (Iic t₁) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hF))
        (measure_lt_top _ _)

/-- One contraction step: if `e ≤ B < ∞`, `Λ E < 1` and `e t ≤ ∫_E e dΛ` on a set `T ⊇ E`,
then `e = 0` on `T`. -/
private lemma eq_zero_of_le_setLIntegral_of_lt_one {Λ : Measure ℝ} {e : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    {E T : Set ℝ} (hB : ∀ t, e t ≤ B) (hBt : B ≠ ∞) (hEΛ : Λ E < 1)
    (hET : E ⊆ T) (hle : ∀ t ∈ T, e t ≤ ∫⁻ s in E, e s ∂Λ) : ∀ t ∈ T, e t = 0 := by
  set m := ∫⁻ s in E, e s ∂Λ
  have hmfin : m ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hBt (ne_top_of_lt hEΛ)) ?_
    calc m ≤ ∫⁻ _ in E, B ∂Λ := lintegral_mono fun s => hB s
      _ = B * Λ E := setLIntegral_const _ _
  have hmle : m ≤ m * Λ E :=
    calc m ≤ ∫⁻ _ in E, m ∂Λ := setLIntegral_mono measurable_const fun s hs => hle s (hET hs)
      _ = m * Λ E := setLIntegral_const _ _
  have hm0 : m = 0 := by
    by_contra hm
    have hlt : Λ E * m < 1 * m := ENNReal.mul_lt_mul_left hm hmfin hEΛ
    rw [one_mul, mul_comm] at hlt
    exact absurd hmle (not_le.2 hlt)
  intro t ht
  exact le_antisymm ((hle t ht).trans hm0.le) bot_le

/-- **Gronwall-type uniqueness for the Volterra inequality** `e(t) ≤ ∫_{(-∞, t)} e dΛ`. For a
finite measure `Λ` (atoms allowed) and a bounded `e ≥ 0`, the inequality on `(-∞, t₁]` forces
`e = 0` on `(-∞, t₁]`. The integral is over the open half-line `(-∞, t)`: at the first point `a`
where `e` could fail to vanish the inequality gives `e a = 0`, and just after `a` the measure
`Λ (a, b)` is small, which propagates `e = 0` past `a`. -/
theorem eq_zero_of_le_setLIntegral_Iio {Λ : Measure ℝ} [IsFiniteMeasure Λ] {e : ℝ → ℝ≥0∞}
    {B : ℝ≥0∞} {t₁ : ℝ} (hB : ∀ t, e t ≤ B) (hBt : B ≠ ∞)
    (hle : ∀ t ≤ t₁, e t ≤ ∫⁻ s in Iio t, e s ∂Λ) : ∀ t ≤ t₁, e t = 0 := by
  -- `A` is the set of `x` such that `e` vanishes on `(-∞, x)`
  set A : Set ℝ := {x | ∀ t < x, e t = 0}
  have hint0 : ∀ x ∈ A, ∫⁻ s in Iio x, e s ∂Λ = 0 := fun x hx => by
    rw [setLIntegral_congr_fun measurableSet_Iio (fun s hs => hx s hs)]
    simp
  -- far to the left, `Λ (-∞, x₀) < 1`, so `e` vanishes there
  obtain ⟨x₀, hx₀A⟩ : ∃ x₀, x₀ ∈ A := by
    have htend : Tendsto (Λ ∘ fun n : ℕ => Iio (-(n : ℝ))) atTop
        (nhds (Λ (⋂ n : ℕ, Iio (-(n : ℝ))))) :=
      tendsto_measure_iInter_atTop (fun _ => measurableSet_Iio.nullMeasurableSet)
        (fun m n hmn => Iio_subset_Iio (neg_le_neg (Nat.cast_le.2 hmn)))
        ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, Iio (-(n : ℝ))) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Iio, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge (-x)
      exact ⟨n, by linarith⟩
    rw [hempty, measure_empty] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨min (-(n : ℝ)) t₁, ?_⟩
    have hE : Λ (Iio (min (-(n : ℝ)) t₁)) < 1 :=
      (measure_mono (Iio_subset_Iio (min_le_left _ _))).trans_lt hn
    exact eq_zero_of_le_setLIntegral_of_lt_one hB hBt hE subset_rfl
      fun t ht => (hle t ((le_of_lt (mem_Iio.1 ht)).trans (min_le_right _ _))).trans
        (lintegral_mono_set (Iio_subset_Iio (le_of_lt (mem_Iio.1 ht))))
  by_contra hne
  push Not at hne
  obtain ⟨t, ht₁, het⟩ := hne
  have hAbdd : BddAbove A := ⟨t, fun x hx => by
    by_contra hxt
    exact het (hx t (not_le.1 hxt))⟩
  set a := sSup A
  have haA : a ∈ A := fun t' ht' => by
    obtain ⟨x, hxA, hx⟩ := exists_lt_of_lt_csSup ⟨x₀, hx₀A⟩ ht'
    exact hxA t' hx
  have hat : a ≤ t := csSup_le ⟨x₀, hx₀A⟩ fun x hx => by
    by_contra hxt
    exact het (hx t (not_le.1 hxt))
  have hea : e a = 0 := le_antisymm ((hle a (hat.trans ht₁)).trans (hint0 a haA).le) bot_le
  have hat' : a < t := lt_of_le_of_ne hat fun h => het (h ▸ hea)
  have hIic0 : ∫⁻ s in Iic a, e s ∂Λ = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0) fun s hs =>
      (lt_or_eq_of_le (mem_Iic.1 hs)).elim (haA s) fun h => h ▸ hea]
    simp
  -- just after `a`, `Λ (a, b) < 1`, so `e` vanishes up to `b > a`: contradiction
  have htend : Tendsto (Λ ∘ fun n : ℕ => Ioo a (a + 1 / ((n : ℝ) + 1))) atTop
      (nhds (Λ (⋂ n : ℕ, Ioo a (a + 1 / ((n : ℝ) + 1))))) := by
    refine tendsto_measure_iInter_atTop (fun _ => measurableSet_Ioo.nullMeasurableSet)
      (fun m n hmn => Ioo_subset_Ioo_right ?_) ⟨0, measure_ne_top _ _⟩
    gcongr
  have hinter : (⋂ n : ℕ, Ioo a (a + 1 / ((n : ℝ) + 1))) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioo, mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hx 0).1)
    linarith [(hx n).2]
  rw [hinter, measure_empty] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds zero_lt_one)).exists
  set b := min (a + 1 / ((n : ℝ) + 1)) t₁
  have hab : a < b := lt_min (lt_add_of_pos_right _ Nat.one_div_pos_of_nat) (hat'.trans_le ht₁)
  have hE : Λ (Ioo a b) < 1 := (measure_mono (Ioo_subset_Ioo_right (min_le_left _ _))).trans_lt hn
  have hbA : b ∈ A := by
    refine eq_zero_of_le_setLIntegral_of_lt_one hB hBt hE
      (fun s hs => hs.2) fun t' ht' => ?_
    calc e t' ≤ ∫⁻ s in Iio t', e s ∂Λ := hle t' ((le_of_lt ht').trans (min_le_right _ _))
      _ ≤ ∫⁻ s in Iio b, e s ∂Λ := lintegral_mono_set (Iio_subset_Iio (le_of_lt ht'))
      _ = ∫⁻ s in Iic a, e s ∂Λ + ∫⁻ s in Ioo a b, e s ∂Λ := by
        rw [← Iic_union_Ioo_eq_Iio hab, lintegral_union measurableSet_Ioo
          ((Iic_disjoint_Ioi le_rfl).mono_right Ioo_subset_Ioi_self)]
      _ = ∫⁻ s in Ioo a b, e s ∂Λ := by rw [hIic0, zero_add]
  exact absurd (le_csSup hAbdd hbA) (not_le.2 hab)

/-- **The hazard determines the law.** If two probability laws have the same hazard on
`(-∞, t₁]` and `F[t₁, ∞) ≠ 0`, they agree on `(-∞, t₁]`. Together with
`hazardMeasure_restrict_Iic_eq_of_restrict_Iic_eq` this is an equivalence. -/
theorem restrict_Iic_eq_of_hazardMeasure_restrict_Iic_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] {t₁ : ℝ} (hF : F (Ici t₁) ≠ 0)
    (hΛ : (hazardMeasure F).restrict (Iic t₁) = (hazardMeasure F').restrict (Iic t₁)) :
    F.restrict (Iic t₁) = F'.restrict (Iic t₁) := by
  set Λ := (hazardMeasure F).restrict (Iic t₁)
  have : IsFiniteMeasure Λ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hazardMeasure_Iic_lt_top F hF⟩
  set S : ℝ → ℝ≥0∞ := fun s => F (Ici s)
  set S' : ℝ → ℝ≥0∞ := fun s => F' (Ici s)
  have hSm : Measurable S := measurable_measure_Ici F
  have hS'm : Measurable S' := measurable_measure_Ici F'
  -- integrals over subsets of `(-∞, t₁]` against `Λ` and against either hazard agree
  have hsub : ∀ {A : Set ℝ}, MeasurableSet A → A ⊆ Iic t₁ → ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ s in A, f s ∂Λ = ∫⁻ s in A, f s ∂(hazardMeasure F)) ∧
        (∫⁻ s in A, f s ∂Λ = ∫⁻ s in A, f s ∂(hazardMeasure F')) := by
    intro A hA hAt f
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_restrict hA, inter_eq_left.2 hAt]
    · rw [hΛ, Measure.restrict_restrict hA, inter_eq_left.2 hAt]
  -- the survival functions agree on `(-∞, t₁]`
  set e : ℝ → ℝ≥0∞ := fun s => (S s - S' s) + (S' s - S s)
  have hB : ∀ t, e t ≤ 2 := fun t => by
    rw [← one_add_one_eq_two]
    exact add_le_add (tsub_le_self.trans prob_le_one) (tsub_le_self.trans prob_le_one)
  have hIio : ∀ t ≤ t₁, F (Iio t) = ∫⁻ s in Iio t, S s ∂Λ ∧ F' (Iio t) = ∫⁻ s in Iio t, S' s ∂Λ :=
    fun t ht => by
      have hAt : Iio t ⊆ Iic t₁ := Iio_subset_Iic_self.trans (Iic_subset_Iic.2 ht)
      exact ⟨by rw [(hsub measurableSet_Iio hAt S).1,
          setLIntegral_measure_Ici_hazardMeasure F measurableSet_Iio],
        by rw [(hsub measurableSet_Iio hAt S').2,
          setLIntegral_measure_Ici_hazardMeasure F' measurableSet_Iio]⟩
  have hS_eq : ∀ t, S t = 1 - F (Iio t) := fun t => by
    rw [← prob_compl_eq_one_sub measurableSet_Iio, compl_Iio]
  have hS'_eq : ∀ t, S' t = 1 - F' (Iio t) := fun t => by
    rw [← prob_compl_eq_one_sub measurableSet_Iio, compl_Iio]
  have hle : ∀ t ≤ t₁, e t ≤ ∫⁻ s in Iio t, e s ∂Λ := fun t ht => by
    obtain ⟨hF1, hF2⟩ := hIio t ht
    have h1 : S t - S' t = F' (Iio t) - F (Iio t) := by
      rw [hS_eq, hS'_eq, AddLECancellable.tsub_tsub_tsub_cancel_left
        (ENNReal.cancel_of_ne (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)) prob_le_one]
    have h2 : S' t - S t = F (Iio t) - F' (Iio t) := by
      rw [hS_eq, hS'_eq, AddLECancellable.tsub_tsub_tsub_cancel_left
        (ENNReal.cancel_of_ne (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)) prob_le_one]
    calc e t = (F' (Iio t) - F (Iio t)) + (F (Iio t) - F' (Iio t)) := by
          simp only [e, h1, h2]
      _ ≤ ∫⁻ s in Iio t, (S' s - S s) ∂Λ + ∫⁻ s in Iio t, (S s - S' s) ∂Λ := by
          rw [hF1, hF2]
          exact add_le_add (lintegral_sub_le _ _ hSm) (lintegral_sub_le _ _ hS'm)
      _ = ∫⁻ s in Iio t, e s ∂Λ := by
          rw [add_comm, ← lintegral_add_left (f := fun s => S s - S' s) (hSm.sub hS'm)]
  have he0 := eq_zero_of_le_setLIntegral_Iio hB ENNReal.ofNat_ne_top hle
  have hSS' : ∀ t ≤ t₁, S t = S' t := fun t ht => by
    obtain ⟨h1, h2⟩ := add_eq_zero.1 (he0 t ht)
    exact le_antisymm (tsub_eq_zero_iff_le.1 h1) (tsub_eq_zero_iff_le.1 h2)
  -- hence the laws agree on every `(-∞, c]`, `c ≤ t₁`
  have hIic : ∀ c ≤ t₁, F (Iic c) = F' (Iic c) := fun c hc => by
    have hAt : Iic c ⊆ Iic t₁ := Iic_subset_Iic.2 hc
    rw [← setLIntegral_measure_Ici_hazardMeasure F measurableSet_Iic,
      ← setLIntegral_measure_Ici_hazardMeasure F' measurableSet_Iic,
      ← (hsub measurableSet_Iic hAt S).1, ← (hsub measurableSet_Iic hAt S').2]
    exact setLIntegral_congr_fun measurableSet_Iic fun s hs => hSS' s (hs.trans hc)
  refine Measure.ext_of_Iic _ _ fun c => ?_
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    Iic_inter_Iic]
  exact hIic _ (min_le_right _ _)

/-! ### Identification of the failure-time law -/

/-- **Identification under an unknown censoring law.** If `(F, G)` and `(F', G')` give the same
observed-data law `P` and `P(X ≥ h) ≠ 0`, then `F` and `F'` agree on `(-∞, h]`. The censoring
laws `G` and `G'` may differ. -/
theorem restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G] [IsFiniteMeasure G']
    (heq : censoredObsLaw F G = censoredObsLaw F' G') {h : ℝ}
    (hh : obsAtRisk (censoredObsLaw F G) h ≠ 0) :
    F.restrict (Iic h) = F'.restrict (Iic h) := by
  have hF : F (Ici h) ≠ 0 := by
    have := hh
    rw [obsAtRisk, censoredObsLaw_apply_Ici_prod_univ] at this
    exact left_ne_zero_of_mul this
  exact restrict_Iic_eq_of_hazardMeasure_restrict_Iic_eq hF
    (hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk heq hh)

/-- **The survival function is identified under an unknown censoring law**:
`F[h, ∞) = F'[h, ∞)` whenever `P(X ≥ h) ≠ 0`. -/
theorem measure_Ici_eq_of_censoredObsLaw_eq_of_atRisk [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G] [IsFiniteMeasure G']
    (heq : censoredObsLaw F G = censoredObsLaw F' G') {h : ℝ}
    (hh : obsAtRisk (censoredObsLaw F G) h ≠ 0) :
    F (Ici h) = F' (Ici h) := by
  have hr := restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk heq hh
  have hIio : F (Iio h) = F' (Iio h) := by
    rw [← Measure.restrict_eq_self F Iio_subset_Iic_self,
      ← Measure.restrict_eq_self F' Iio_subset_Iic_self, hr]
  rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio,
    prob_compl_eq_one_sub measurableSet_Iio, hIio]

/-- **Identification on the whole at-risk set**: under an unknown censoring law the
observed-data law `P` determines `F` on `{s | P(X ≥ s) ≠ 0}`. -/
theorem restrict_atRiskSet_eq_of_censoredObsLaw_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G] [IsFiniteMeasure G']
    (heq : censoredObsLaw F G = censoredObsLaw F' G') :
    F.restrict (atRiskSet (censoredObsLaw F G)) =
      F'.restrict (atRiskSet (censoredObsLaw F G)) := by
  set U := atRiskSet (censoredObsLaw F G)
  have hIic : ∀ h ∈ U, F.restrict (Iic h) = F'.restrict (Iic h) := fun h hh =>
    restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk heq hh
  rcases U.eq_empty_or_nonempty with hU | hU
  · rw [hU, Measure.restrict_empty, Measure.restrict_empty]
  by_cases hbdd : BddAbove U
  · by_cases hmax : sSup U ∈ U
    · have hUeq : U = Iic (sSup U) := Subset.antisymm (fun s hs => le_csSup hbdd hs)
        fun s hs => atRiskSet_downward hmax hs
      rw [hUeq]
      exact hIic _ hmax
    · -- `U = (-∞, sup U)`, a countable union of `(-∞, u n]` with `u n ∈ U`
      obtain ⟨u, -, hu_tend, huU⟩ := exists_seq_tendsto_sSup hU hbdd
      have hUeq : U = ⋃ n, Iic (u n) := by
        refine Subset.antisymm (fun s hs => ?_) (iUnion_subset fun n s hs =>
          atRiskSet_downward (huU n) hs)
        have hlt : s < sSup U := lt_of_le_of_ne (le_csSup hbdd hs) fun h => hmax (h ▸ hs)
        obtain ⟨n, hn⟩ := (hu_tend.eventually (lt_mem_nhds hlt)).exists
        exact mem_iUnion.2 ⟨n, hn.le⟩
      rw [hUeq, Measure.restrict_iUnion_congr]
      exact fun n => hIic _ (huU n)
  · -- unbounded above: `U = ℝ = ⋃ (-∞, n]`
    have hn : ∀ n : ℕ, (n : ℝ) ∈ U := fun n => by
      obtain ⟨s, hs, hns⟩ := not_bddAbove_iff.1 hbdd n
      exact atRiskSet_downward hs hns.le
    have hUeq : U = ⋃ n : ℕ, Iic (n : ℝ) := by
      refine Subset.antisymm (fun s _ => ?_) (iUnion_subset fun n s hs =>
        atRiskSet_downward (hn n) hs)
      obtain ⟨n, hn⟩ := exists_nat_ge s
      exact mem_iUnion.2 ⟨n, hn⟩
    rw [hUeq, Measure.restrict_iUnion_congr]
    exact fun n => hIic _ (hn n)

/-- **Parametric identification with a parameter-varying, unknown censoring law.** Let the
failure-time law `F θ` depend on a parameter `θ`, and the censoring law `G θ η` depend on `θ` and
a nuisance `η` in an arbitrary way. If `θ` is determined by the failure-time law on `(-∞, h]`
and every model has `P(X ≥ h) ≠ 0`, then the observed-data law determines `θ`. -/
theorem parameter_eq_of_censoredObsLaw_eq {Θ H : Type*} (F : Θ → Measure ℝ)
    (G : Θ → H → Measure ℝ) [∀ θ, IsProbabilityMeasure (F θ)]
    [∀ θ η, IsFiniteMeasure (G θ η)] {h : ℝ}
    (hinj : Function.Injective fun θ => (F θ).restrict (Iic h))
    (hrisk : ∀ θ η, obsAtRisk (censoredObsLaw (F θ) (G θ η)) h ≠ 0) {θ θ' : Θ} {η η' : H}
    (heq : censoredObsLaw (F θ) (G θ η) = censoredObsLaw (F θ') (G θ' η')) : θ = θ' :=
  hinj (restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk heq (hrisk θ η))

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
