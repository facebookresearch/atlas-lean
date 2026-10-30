/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.StochasticOrder.Strassen
import MathlibExt.Probability.StrassenCoupling

/-!
# Strassen's theorem for configurations on a finite set

For finite `E`, two probability measures `μ ≼ ν` on `ConfigSpace E` (stochastic domination with
respect to increasing events) have a monotone coupling: a measure on pairs `(ω, ω')` with
marginals `μ` and `ν` concentrated on `ω ≤ ω'`. Together with
`StatMech.MonotoneCoupling.stochasticallyDominated` this characterizes stochastic domination.

The finite-poset step reuses
`MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling`.
The complement of an upper set is a down-set, so down-set domination and equality of total mass
give the theorem's upper-set inequality. Its nonnegative matrix coupling is then restricted to
the ordered pairs `x ≤ y`; the support condition recovers the same row and column marginals.

## Main definitions

* `StatMech.Transport.IsDown D`: `D` is a down-set of the finite poset `P`.
* `StatMech.Transport.OrderPairs P`: the ordered pairs `x ≤ y` of `P`.
* `StatMech.kappaOfVec c`: the measure on pairs of configurations with weights `c`.

## Main results

* `StatMech.Transport.exists_coupling_vec`: Strassen's theorem on a finite poset, for
  nonnegative vectors.
* `StatMech.exists_monotoneCoupling_of_stochasticallyDominated`: Strassen's theorem on
  `ConfigSpace E`.

## References

* V. Strassen, *The existence of probability measures with given marginals*, Ann. Math.
  Statist. 36 (1965), 423–439.
* T. Lindvall, *Lectures on the Coupling Method*, Wiley, 1992, Chapter IV.
-/

@[expose] public section

open MeasureTheory Finset


namespace StatMech

namespace Transport

variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]

/-- `D` is a down-set of `P`: `x ≤ y` and `y ∈ D` imply `x ∈ D`. -/
def IsDown (D : Finset P) : Prop := ∀ x y, x ≤ y → y ∈ D → x ∈ D

/-- The ordered pairs `(x, y)` with `x ≤ y`; couplings supported on the order are vectors indexed
by `OrderPairs P`. -/
abbrev OrderPairs (P : Type*) [PartialOrder P] := {p : P × P // p.1 ≤ p.2}

variable [DecidableRel ((· ≤ ·) : P → P → Prop)]

/-- **Strassen's theorem** on a finite poset `P`, for nonnegative vectors: if `μ` and `ν` have
equal total mass and `ν(D) ≤ μ(D)` for every down-set `D`, there is a nonnegative `c` on the
ordered pairs `x ≤ y` with first marginal `μ` and second marginal `ν`. This is the ordered-pair
vector form of
`MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling`. -/
theorem exists_coupling_vec (μ ν : P → ℝ)
    (hμpos : ∀ x, 0 ≤ μ x) (hνpos : ∀ x, 0 ≤ ν x)
    (hTOT : ∑ x, μ x = ∑ x, ν x)
    (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x) :
    ∃ c : OrderPairs P → ℝ, (∀ q, 0 ≤ c q) ∧
      (∀ x, (∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0) = μ x) ∧
      (∀ y, (∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0) = ν y) := by
  classical
  have hUpper : ∀ U : Finset P,
      MathlibExt.Probability.StrassenCouplingWanted.IsUpperSet U →
        ∑ x ∈ U, μ x ≤ ∑ x ∈ U, ν x := by
    intro U hU
    let D := Finset.univ \ U
    have hD : IsDown D := by
      intro x y hxy hy
      simp only [D, Finset.mem_sdiff, Finset.mem_univ, true_and] at hy ⊢
      intro hx
      exact hy (hU hx hxy)
    have hdom := hDOM D hD
    have hμsplit := Finset.sum_sdiff (f := μ) (Finset.subset_univ U)
    have hνsplit := Finset.sum_sdiff (f := ν) (Finset.subset_univ U)
    dsimp [D] at hdom
    linarith [hμsplit, hνsplit, hTOT]
  obtain ⟨π, hπpos, hrow, hcol, hsupp⟩ :=
    (MathlibExt.Probability.StrassenCouplingWanted.forall_isUpperSet_sum_le_iff_exists_coupling
      μ ν hμpos hνpos hTOT).mp hUpper
  refine ⟨fun q => π q.1.1 q.1.2, fun q => hπpos _ _, ?_, ?_⟩
  · intro x
    change (∑ q : {q : P × P // q.1 ≤ q.2},
      if q.1.1 = x then π q.1.1 q.1.2 else 0) = μ x
    rw [← Finset.sum_subtype
      (p := fun q : P × P => q.1 ≤ q.2)
      (s := Finset.univ.filter (fun q : P × P => q.1 ≤ q.2))
      (by intro q; simp) (fun q => if q.1 = x then π q.1 q.2 else 0)]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · calc
        (∑ y : P, if x ≤ y then (if x = x then π x y else 0) else 0)
            = ∑ y : P, π x y := by
                apply Finset.sum_congr rfl
                intro y _
                by_cases hxy : x ≤ y
                · simp [hxy]
                · simp [hxy, hsupp x y hxy]
        _ = μ x := hrow x
    · intro a _ hax
      apply Finset.sum_eq_zero
      intro b _
      simp [hax]
    · simp
  · intro y
    change (∑ q : {q : P × P // q.1 ≤ q.2},
      if q.1.2 = y then π q.1.1 q.1.2 else 0) = ν y
    rw [← Finset.sum_subtype
      (p := fun q : P × P => q.1 ≤ q.2)
      (s := Finset.univ.filter (fun q : P × P => q.1 ≤ q.2))
      (by intro q; simp) (fun q => if q.2 = y then π q.1 q.2 else 0)]
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
    rw [Finset.sum_eq_single y]
    · calc
        (∑ x : P, if x ≤ y then (if y = y then π x y else 0) else 0)
            = ∑ x : P, π x y := by
                apply Finset.sum_congr rfl
                intro x _
                by_cases hxy : x ≤ y
                · simp [hxy]
                · simp [hxy, hsupp x y hxy]
        _ = ν y := hcol y
    · intro b _ hby
      apply Finset.sum_eq_zero
      intro a _
      simp [hby]
    · simp

end Transport

section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport

/-- The coordinatewise order on configurations of a finite set is decidable. -/
instance : DecidableRel ((· ≤ ·) : ConfigSpace E → ConfigSpace E → Prop) :=
  fun _ _ => Fintype.decidableForallFintype

/-- The mass `μ {ω}` of a configuration, as a real number. -/
private noncomputable def mass (μ : Measure (ConfigSpace E)) (ω : ConfigSpace E) : ℝ :=
  (μ {ω}).toReal

omit [Fintype E] [DecidableEq E] in
private theorem mass_nonneg (μ : Measure (ConfigSpace E)) (ω : ConfigSpace E) :
    0 ≤ mass μ ω := ENNReal.toReal_nonneg

omit [Fintype E] [DecidableEq E] in
private theorem measureReal_finset_eq_sum_mass [Finite E] (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (A : Finset (ConfigSpace E)) :
    μ.real (A : Set (ConfigSpace E)) = ∑ ω ∈ A, mass μ ω := by
  classical
  simp only [mass, measureReal_def]
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  congr 1
  rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
        (fun ω _ => measurableSet_singleton ω)]
  congr 1; ext ω; simp

private theorem sum_mass_eq_one (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] :
    ∑ ω : ConfigSpace E, mass μ ω = 1 := by
  simp only [mass]
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  rw [show (∑ ω : ConfigSpace E, μ {ω}) = μ Set.univ by
    rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
          (fun ω _ => measurableSet_singleton ω)]
    congr 1; ext ω; simp]
  simp

omit [Fintype E] [DecidableEq E] in
private theorem measure_singleton_eq_ofReal_mass (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (ω : ConfigSpace E) : μ {ω} = ENNReal.ofReal (mass μ ω) := by
  classical
  rw [mass, ENNReal.ofReal_toReal (measure_ne_top μ _)]

omit [Fintype E] [DecidableEq E] in
private theorem mass_down_dom [Finite E] (μ ν : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hdom : μ ≼ ν)
    (D : Finset (ConfigSpace E)) (hD : Transport.IsDown D) :
    ∑ ω ∈ D, mass ν ω ≤ ∑ ω ∈ D, mass μ ω := by
  classical
  have hDc_inc : IsIncreasing ((↑D)ᶜ : Set (ConfigSpace E)) := by
    apply IsLowerSet.compl
    intro a b hab hb
    simp only [Finset.mem_coe] at *
    exact hD b a hab hb
  have hmeas : MeasurableSet ((↑D)ᶜ : Set (ConfigSpace E)) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hle := hdom _ hmeas hDc_inc
  have hsplit : ∀ (ρ : Measure (ConfigSpace E)) [IsProbabilityMeasure ρ],
      ρ.real ((↑D)ᶜ : Set (ConfigSpace E)) = 1 - ∑ ω ∈ D, mass ρ ω := by
    intro ρ _
    have h1 := probReal_add_probReal_compl (μ := ρ) (s := (↑D : Set (ConfigSpace E)))
        (DiscreteMeasurableSpace.forall_measurableSet _)
    rw [measureReal_finset_eq_sum_mass ρ D] at h1
    linarith
  rw [hsplit μ, hsplit ν] at hle
  linarith

/-- The measure on pairs of configurations that puts mass `c q` on each ordered pair `q`. -/
noncomputable def kappaOfVec
    (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ) :
    Measure (ConfigSpace E × ConfigSpace E) :=
  ∑ q : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2},
    (ENNReal.ofReal (c q)) • Measure.dirac (q : ConfigSpace E × ConfigSpace E)

open scoped Classical in
private theorem kappaOfVec_apply
    (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ)
    (A : Set (ConfigSpace E × ConfigSpace E)) :
    kappaOfVec c A
      = ∑ q : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2},
          if (q : ConfigSpace E × ConfigSpace E) ∈ A then ENNReal.ofReal (c q) else 0 := by
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  unfold kappaOfVec
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases hq : (q : ConfigSpace E × ConfigSpace E) ∈ A <;> simp [hq]

/-- `kappaOfVec c` is a finite measure. -/
instance (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ) :
    IsFiniteMeasure (kappaOfVec c) := by
  refine ⟨?_⟩
  rw [kappaOfVec_apply]
  simp only [Set.mem_univ, ite_true]
  exact ENNReal.sum_lt_top.2 (fun q _ => ENNReal.ofReal_lt_top)

omit [Fintype E] [DecidableEq E] in
/-- **Strassen's theorem** for configurations on a finite set: if `μ ≼ ν` are probability
measures on `ConfigSpace E`, there is a finite monotone coupling of `μ` and `ν`
(V. Strassen, *The existence of probability measures with given marginals*, 1965). The converse
is `StatMech.MonotoneCoupling.stochasticallyDominated`. -/
theorem exists_monotoneCoupling_of_stochasticallyDominated
    [Finite E] (μ ν : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : μ ≼ ν) :
    ∃ κ : Measure (ConfigSpace E × ConfigSpace E),
      IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ := by
  classical
  have := Fintype.ofFinite E
  obtain ⟨c, hcpos, hrow, hcol⟩ :=
    Transport.exists_coupling_vec (P := ConfigSpace E) (mass μ) (mass ν)
      (mass_nonneg μ) (mass_nonneg ν)
      (by rw [sum_mass_eq_one μ, sum_mass_eq_one ν])
      (fun D hD => mass_down_dom μ ν hdom D hD)
  refine ⟨kappaOfVec c, inferInstance, ?_, ?_, ?_⟩
  · apply Measure.ext_of_singleton
    intro ω
    rw [Measure.fst_apply (measurableSet_singleton ω), kappaOfVec_apply,
      measure_singleton_eq_ofReal_mass μ ω, ← hrow ω,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => by split_ifs <;> [exact hcpos q; exact le_refl 0])]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (q : ConfigSpace E × ConfigSpace E).1 = ω
    · rw [ite_eq_left (show (q : ConfigSpace E × ConfigSpace E) ∈ Prod.fst ⁻¹' {ω} from hq),
        ite_eq_left hq]
    · rw [ite_eq_right (show (q : ConfigSpace E × ConfigSpace E) ∉ Prod.fst ⁻¹' {ω} from hq),
        ite_eq_right hq, ENNReal.ofReal_zero]
  · apply Measure.ext_of_singleton
    intro ω
    rw [Measure.snd_apply (measurableSet_singleton ω), kappaOfVec_apply,
      measure_singleton_eq_ofReal_mass ν ω, ← hcol ω,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => by split_ifs <;> [exact hcpos q; exact le_refl 0])]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (q : ConfigSpace E × ConfigSpace E).2 = ω
    · rw [ite_eq_left (show (q : ConfigSpace E × ConfigSpace E) ∈ Prod.snd ⁻¹' {ω} from hq),
        ite_eq_left hq]
    · rw [ite_eq_right (show (q : ConfigSpace E × ConfigSpace E) ∉ Prod.snd ⁻¹' {ω} from hq),
        ite_eq_right hq, ENNReal.ofReal_zero]
  · rw [kappaOfVec_apply]
    apply Finset.sum_eq_zero
    intro q _
    rw [ite_eq_right]
    intro hmem
    exact hmem q.2

end ConfigSpace

end StatMech
