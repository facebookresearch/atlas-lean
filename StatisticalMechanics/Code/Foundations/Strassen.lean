/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Code.Foundations.StochasticDomination

open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace StatMech



variable {E : Type*}



def orderSet (E : Type*) : Set (ConfigSpace E × ConfigSpace E) := {p | p.1 ≤ p.2}






structure MonotoneCoupling (μ ν : Measure (ConfigSpace E))
    (κ : Measure (ConfigSpace E × ConfigSpace E)) : Prop where
  
  fst_eq : κ.fst = μ
  
  snd_eq : κ.snd = ν
  
  supported : κ (orderSet E)ᶜ = 0

namespace MonotoneCoupling

variable {μ ν : Measure (ConfigSpace E)}
  {κ : Measure (ConfigSpace E × ConfigSpace E)}


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

variable [Fintype E] [DecidableEq E]

omit [DecidableEq E] in


theorem measurableSet_orderSet : MeasurableSet (orderSet E) :=
  DiscreteMeasurableSpace.forall_measurableSet _

namespace MonotoneCoupling

variable {μ ν : Measure (ConfigSpace E)}
  {κ : Measure (ConfigSpace E × ConfigSpace E)}

omit [DecidableEq E] in










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

omit [DecidableEq E] in




theorem stochasticallyDominated_of_exists_monotoneCoupling
    {μ ν : Measure (ConfigSpace E)}
    (h : ∃ κ : Measure (ConfigSpace E × ConfigSpace E),
          IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ) :
    μ ≼ ν := by
  obtain ⟨κ, hκfin, hκ⟩ := h
  exact hκ.stochasticallyDominated

end Finite

end StatMech
