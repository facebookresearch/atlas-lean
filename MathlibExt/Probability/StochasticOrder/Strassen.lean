/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.StochasticOrder.StochasticDomination

/-!
# Monotone couplings and stochastic domination

A monotone coupling of two measures `μ` and `ν` on `ConfigSpace E` is a measure on pairs of
configurations with marginals `μ` and `ν` that is concentrated on `{(ω, ω') | ω ≤ ω'}`. If one
exists, `μ` is stochastically dominated by `ν`; this is the easy half of Strassen's theorem. The
converse for finite `E` is `StatMech.exists_monotoneCoupling_of_stochasticallyDominated` in
`MathlibExt.Probability.StochasticOrder.StrassenFull`.

## Main definitions

* `StatMech.orderSet E`: the set of ordered pairs `ω ≤ ω'` of configurations.
* `StatMech.MonotoneCoupling μ ν κ`: `κ` is a monotone coupling of `μ` and `ν`.

## Main results

* `StatMech.MonotoneCoupling.stochasticallyDominated`: a monotone coupling with finite mass
  gives `μ ≼ ν` (finite `E`).

## References

* V. Strassen, *The existence of probability measures with given marginals*, Ann. Math.
  Statist. 36 (1965), 423–439.
-/

@[expose] public section

open MeasureTheory

namespace StatMech

variable {E : Type*}

/-- The set of ordered pairs `(ω, ω')` of configurations with `ω ≤ ω'` coordinatewise. -/
def orderSet (E : Type*) : Set (ConfigSpace E × ConfigSpace E) := {p | p.1 ≤ p.2}

/-- `κ` is a monotone coupling of `μ` and `ν`: a measure on pairs of configurations with first
marginal `μ`, second marginal `ν`, and no mass off the ordered pairs `ω ≤ ω'`. -/
structure MonotoneCoupling (μ ν : Measure (ConfigSpace E))
    (κ : Measure (ConfigSpace E × ConfigSpace E)) : Prop where
  /-- The first marginal of `κ` is `μ`. -/
  fst_eq : κ.fst = μ
  /-- The second marginal of `κ` is `ν`. -/
  snd_eq : κ.snd = ν
  /-- `κ` is concentrated on the ordered pairs. -/
  supported : κ (orderSet E)ᶜ = 0

namespace MonotoneCoupling

variable {μ ν : Measure (ConfigSpace E)}
  {κ : Measure (ConfigSpace E × ConfigSpace E)}

/-- The two marginals of a coupling have the same total mass. -/
theorem total_mass_eq (h : MonotoneCoupling μ ν κ) : μ Set.univ = ν Set.univ := by
  rw [← h.fst_eq, ← h.snd_eq, Measure.fst_univ, Measure.snd_univ]

theorem isFiniteMeasure_left (h : MonotoneCoupling μ ν κ) [IsFiniteMeasure κ] :
    IsFiniteMeasure μ := by
  rw [← h.fst_eq]; infer_instance

theorem isFiniteMeasure_right (h : MonotoneCoupling μ ν κ) [IsFiniteMeasure κ] :
    IsFiniteMeasure ν := by
  rw [← h.snd_eq]; infer_instance

theorem isProbabilityMeasure_left (h : MonotoneCoupling μ ν κ)
    [IsProbabilityMeasure κ] : IsProbabilityMeasure μ := by
  rw [← h.fst_eq]; infer_instance

theorem isProbabilityMeasure_right (h : MonotoneCoupling μ ν κ)
    [IsProbabilityMeasure κ] : IsProbabilityMeasure ν := by
  rw [← h.snd_eq]; infer_instance

end MonotoneCoupling

section Finite

variable [Finite E]

theorem measurableSet_orderSet : MeasurableSet (orderSet E) :=
  DiscreteMeasurableSpace.forall_measurableSet _

namespace MonotoneCoupling

variable {μ ν : Measure (ConfigSpace E)}
  {κ : Measure (ConfigSpace E × ConfigSpace E)}

/-- A finite monotone coupling of `μ` and `ν` shows `μ ≼ ν`: the easy direction of Strassen's
theorem. -/
theorem stochasticallyDominated (h : MonotoneCoupling μ ν κ)
    [IsFiniteMeasure κ] : μ ≼ ν := by
  have hνfin : IsFiniteMeasure ν := h.isFiniteMeasure_right
  intro A _ hAinc
  have hmA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  have key : μ A ≤ ν A := by
    rw [← h.fst_eq, ← h.snd_eq, Measure.fst_apply hmA, Measure.snd_apply hmA]
    have hsub : Prod.fst ⁻¹' A ⊆ (Prod.snd ⁻¹' A) ∪ (orderSet E)ᶜ := by
      rintro p hp
      by_cases hle : p.1 ≤ p.2
      · exact Or.inl (hAinc hle hp)
      · exact Or.inr hle
    calc κ (Prod.fst ⁻¹' A)
        ≤ κ ((Prod.snd ⁻¹' A) ∪ (orderSet E)ᶜ) := measure_mono hsub
      _ ≤ κ (Prod.snd ⁻¹' A) + κ (orderSet E)ᶜ := measure_union_le _ _
      _ = κ (Prod.snd ⁻¹' A) := by rw [h.supported, add_zero]
  unfold Measure.real
  gcongr
  exact measure_ne_top ν A

end MonotoneCoupling

/-- If a finite monotone coupling of `μ` and `ν` exists, then `μ ≼ ν`. -/
theorem stochasticallyDominated_of_exists_monotoneCoupling
    {μ ν : Measure (ConfigSpace E)}
    (h : ∃ κ : Measure (ConfigSpace E × ConfigSpace E),
          IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ) :
    μ ≼ ν := by
  obtain ⟨κ, hκfin, hκ⟩ := h
  exact hκ.stochasticallyDominated

end Finite

end StatMech
