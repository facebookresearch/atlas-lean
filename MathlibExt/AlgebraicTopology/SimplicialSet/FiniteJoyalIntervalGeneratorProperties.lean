/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGenerators
public import MathlibExt.AlgebraicTopology.ModelCategory.PresheafCylinderCorners
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.Basic.Countable.Basic

/-!
# A countable finite presentation of the auxiliary family

The actual inner horns and finite-interval endpoint corners admit a
countable index in the simplicial value universe. Their morphism class
is exactly `ofHoms` of the indexed arrows. Every map is monic and both
its source and target have finitely many nondegenerate simplices.

Only the generator family is counted. Attaching maps into an arbitrary
object are not asserted countable. No model structure or small object
argument is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- Dimension and interior-horn indices, or dimension and an endpoint,
lifted to the value universe. The maps keep their actual chosen sources. -/
abbrev AuxiliaryGeneratorIndex : Type u := ULift.{u}
  ((Σ n : ℕ, {k : Fin (n + 3) // 0 < k ∧ k < Fin.last (n + 2)}) ⊕ (ℕ × Fin 2))

/-- The actual arrow at each countable index. No isomorphic representative
is substituted for a specified pushout corner. -/
def auxiliaryGeneratorArrow (i : AuxiliaryGeneratorIndex.{u}) : Arrow SSet.{u} :=
  match i.down with
  | .inl ⟨n, k⟩ => Arrow.mk (horn.{u} (n + 2) k.1).ι
  | .inr (n, ε) => Arrow.mk (productPrecylinder.{u}.endpointCorner (boundary.{u} n).ι ε)

@[simp]
lemma auxiliaryGeneratorArrow_inner (n : ℕ) (k : Fin (n + 3))
    (h0 : 0 < k) (hn : k < Fin.last (n + 2)) :
    auxiliaryGeneratorArrow.{u} ⟨.inl ⟨n, ⟨k, h0, hn⟩⟩⟩ =
      Arrow.mk (horn.{u} (n + 2) k).ι := rfl

@[simp]
lemma auxiliaryGeneratorArrow_endpoint (n : ℕ) (ε : Fin 2) :
    auxiliaryGeneratorArrow.{u} ⟨.inr (n, ε)⟩ =
      Arrow.mk (productPrecylinder.{u}.endpointCorner (boundary.{u} n).ι ε) := rfl

/-- The explicit index is countable, including both zero-dimensional corners. -/
instance : Countable AuxiliaryGeneratorIndex.{u} := inferInstance

/-- The explicit arrows present exactly the original literal family. -/
theorem auxiliaryGenerators_eq_ofHoms :
    auxiliaryGenerators.{u} = MorphismProperty.ofHoms
      (fun i : AuxiliaryGeneratorIndex.{u} ↦ (auxiliaryGeneratorArrow i).hom) := by
  apply le_antisymm
  · rw [auxiliaryGenerators, sup_le_iff]
    constructor
    · rw [innerHornInclusions_eq_iSup, iSup_le_iff]
      intro n
      rw [MorphismProperty.ofHoms_le_iff]
      intro k
      exact MorphismProperty.ofHoms.mk (⟨.inl ⟨n, k⟩⟩ : AuxiliaryGeneratorIndex.{u})
    · rw [MorphismProperty.ofHoms_le_iff]
      intro i
      exact MorphismProperty.ofHoms.mk (⟨.inr i⟩ : AuxiliaryGeneratorIndex.{u})
  · rw [MorphismProperty.ofHoms_le_iff]
    rintro ⟨⟨n, ⟨k, h0, hn⟩⟩ | ⟨n, ε⟩⟩
    · exact auxiliaryGenerators.horn_ι_mem h0 hn
    · exact auxiliaryGenerators.endpointCorner_mem n ε

/-- Every explicit indexed generator is monic. -/
theorem mono_auxiliaryGeneratorArrow (i : AuxiliaryGeneratorIndex.{u}) :
    Mono (auxiliaryGeneratorArrow i).hom := by
  rcases i with ⟨⟨n, ⟨k, h0, hn⟩⟩ | ⟨n, ε⟩⟩
  · change Mono (horn.{u} (n + 2) k).ι
    infer_instance
  · change Mono (productPrecylinder.{u}.endpointCorner (boundary.{u} n).ι ε)
    infer_instance

/-- Each target is a finite standard simplex or a finite product with the interval. -/
theorem finite_auxiliaryGeneratorArrow_target (i : AuxiliaryGeneratorIndex.{u}) :
    SSet.Finite (auxiliaryGeneratorArrow i).right := by
  rcases i with ⟨⟨n, k⟩ | ⟨n, ε⟩⟩
  · change SSet.Finite (Δ[n + 2] : SSet.{u})
    infer_instance
  · change SSet.Finite (joyalInterval.{u} ⊗ (Δ[n] : SSet.{u}))
    infer_instance

/-- Each actual source is finite, as a subobject of its finite target. -/
theorem finite_auxiliaryGeneratorArrow_source (i : AuxiliaryGeneratorIndex.{u}) :
    SSet.Finite (auxiliaryGeneratorArrow i).left := by
  have : SSet.Finite (auxiliaryGeneratorArrow i).right :=
    finite_auxiliaryGeneratorArrow_target i
  have : Mono (auxiliaryGeneratorArrow i).hom := mono_auxiliaryGeneratorArrow i
  exact SSet.finite_of_mono (auxiliaryGeneratorArrow i).hom

/-- The actual family is small in the value universe. -/
instance auxiliaryGenerators.isSmall : MorphismProperty.IsSmall.{u} auxiliaryGenerators.{u} := by
  rw [auxiliaryGenerators_eq_ofHoms]
  exact MorphismProperty.isSmall_ofHoms.{u}
    (fun i : AuxiliaryGeneratorIndex.{u} ↦ (auxiliaryGeneratorArrow i).hom)

/-- Monicity is available for any actual family member. -/
theorem auxiliaryGenerators_le_monomorphisms :
    auxiliaryGenerators.{u} ≤ MorphismProperty.monomorphisms SSet := by
  rw [auxiliaryGenerators_eq_ofHoms, MorphismProperty.ofHoms_le_iff]
  intro i
  have : Mono (auxiliaryGeneratorArrow i).hom := mono_auxiliaryGeneratorArrow i
  exact MorphismProperty.monomorphisms.infer_property _

/-- Every actual generator has finite source and target. -/
theorem auxiliaryGenerators.finite {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : auxiliaryGenerators f) : X.Finite ∧ Y.Finite := by
  rw [auxiliaryGenerators_eq_ofHoms] at hf
  cases hf with
  | mk i => exact ⟨finite_auxiliaryGeneratorArrow_source i, finite_auxiliaryGeneratorArrow_target i⟩

/-- The complete countable presentation, with the exact arrow family and
monicity and finite nondegenerate source and target at every index. -/
theorem auxiliaryGenerators.exists_countable_finite_generators :
    ∃ (ι : Type u) (_ : Countable ι) (F : ι → Arrow SSet.{u}),
      auxiliaryGenerators.{u} = MorphismProperty.ofHoms (fun i ↦ (F i).hom) ∧
        ∀ i, Mono (F i).hom ∧ SSet.Finite (F i).left ∧ SSet.Finite (F i).right :=
  ⟨AuxiliaryGeneratorIndex.{u}, inferInstance, auxiliaryGeneratorArrow,
    auxiliaryGenerators_eq_ofHoms, fun i ↦ ⟨mono_auxiliaryGeneratorArrow i,
      finite_auxiliaryGeneratorArrow_source i, finite_auxiliaryGeneratorArrow_target i⟩⟩

end SSet.joyalInterval
