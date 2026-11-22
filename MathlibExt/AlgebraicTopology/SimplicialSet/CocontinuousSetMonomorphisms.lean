/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplexCategory.MappedBoundaryColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The original one-boundary test for Set-valued cocontinuous functors

Joyal D.0.28 reduces monomorphism preservation to the original boundary of
the one-simplex. The finite mapped-boundary construction supplies all other
boundary images. The native relative boundary-cell complex of each original
monomorphism supplies the natural-number composition used in D.0.12.

Colimit preservation is stated at the source coefficient universe. The target
is an independent universe of types; its actual image colimits are provided
by the given functor's preservation property.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet

private def monoInverseImage (F : SSet.{u} ⥤ Type v) : MorphismProperty SSet.{u} :=
  (monomorphisms (Type v)).inverseImage F

private theorem monoInverseImage_coproducts (F : SSet.{u} ⥤ Type v)
    [PreservesColimitsOfSize.{u, u} F] :
    IsStableUnderCoproducts.{u} (monoInverseImage F) where
  isStableUnderCoproductsOfShape J :=
    { condition := by
        intro X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ
        let hM : (monomorphisms (Type v)).IsStableUnderCoproductsOfShape J := inferInstance
        exact hM.condition
          (X₁ ⋙ F) (X₂ ⋙ F) (F.mapCocone c₁) (F.mapCocone c₂)
          (isColimitOfPreserves F h₁) (isColimitOfPreserves F h₂)
          (Functor.whiskerRight f F) hf (F.map φ) (fun j ↦ by
            change F.map (c₁.ι.app j) ≫ F.map φ = F.map (f.app j) ≫ F.map (c₂.ι.app j)
            rw [← F.map_comp, ← F.map_comp]
            exact F.congr_map (hφ j)) }

private theorem monoInverseImage_cobase (F : SSet.{u} ⥤ Type v)
    [PreservesColimitsOfSize.{u, u} F] : (monoInverseImage F).IsStableUnderCobaseChange := by
  let : PreservesColimitsOfSize.{0, 0} F := preservesSmallestColimits_of_preservesColimits F
  exact { of_isPushout := fun sq hf ↦
    IsStableUnderCobaseChange.of_isPushout (P := monomorphisms (Type v)) (sq.map F) hf }

private theorem monoInverseImage_infinite (F : SSet.{u} ⥤ Type v)
    [PreservesColimitsOfSize.{u, u} F] : (monoInverseImage F).IsStableUnderInfiniteComposition := by
  let : PreservesColimitsOfSize.{0, 0} F := preservesSmallestColimits_of_preservesColimits F
  let : PreservesWellOrderContinuousOfShape ℕ F :=
    { preservesColimitsOfShape _ _ := inferInstance }
  constructor
  rintro X Y f ⟨h⟩
  exact (monomorphisms (Type v)).transfiniteCompositionsOfShape_le ℕ (F.map f)
    ⟨MorphismProperty.TransfiniteCompositionOfShape.map (F := F) h⟩

private theorem boundaryImageMono (F : SSet.{u} ⥤ Type v)
    [PreservesColimitsOfSize.{u, u} F]
    (h1 : Mono (F.map ((boundary.{u} 1).ι))) (n : ℕ) :
    Mono (F.map ((boundary.{u} n).ι)) := by
  let : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  cases n with
  | zero =>
    apply (mono_iff_injective _).2
    intro a b _
    exact PEmpty.elim ((mappedBoundaryZeroIsInitial F).to (PEmpty : Type v) a)
  | succ n =>
    cases n with
    | zero => exact h1
    | succ n => exact mappedBoundaryComparison_isMono F n

/-- Source-sized cocontinuity and the original one-boundary test preserve every original Mono. -/
theorem cocontinuous_preservesMonomorphisms_of_boundaryOne
    (F : SSet.{u} ⥤ Type v) [PreservesColimitsOfSize.{u, u} F]
    (h1 : Mono (F.map ((boundary.{u} 1).ι))) : F.PreservesMonomorphisms := by
  let μ := monoInverseImage F
  let : IsStableUnderCoproducts.{u} μ := monoInverseImage_coproducts F
  let : μ.IsStableUnderCobaseChange := monoInverseImage_cobase F
  let : μ.IsStableUnderInfiniteComposition := monoInverseImage_infinite F
  let : μ.IsStableUnderRetracts := inferInstanceAs
    (((monomorphisms (Type v)).inverseImage F).IsStableUnderRetracts)
  have hI : modelCategoryQuillen.I.{u} ≤ μ := by
    rintro X Y f ⟨n⟩
    exact boundaryImageMono F h1 n
  have hCells : (coproducts.{u} modelCategoryQuillen.I.{u}).pushouts ≤ μ := by
    calc
      (coproducts.{u} modelCategoryQuillen.I.{u}).pushouts ≤ (coproducts.{u} μ).pushouts :=
        pushouts_monotone (coproducts_monotone hI)
      _ ≤ μ.pushouts := pushouts_monotone (coproducts_le (W := μ))
      _ ≤ μ := pushouts_le (P := μ)
  constructor
  intro X Y f hf
  have h : (transfiniteCompositionsOfShape
      (coproducts.{u} modelCategoryQuillen.I.{u}).pushouts ℕ) f :=
    ⟨(relativeCellComplexOfMono f).transfiniteCompositionOfShape' (fun _ ↦ ⟨_⟩)⟩
  exact μ.transfiniteCompositionsOfShape_le ℕ f
    (transfiniteCompositionsOfShape_monotone ℕ hCells f h)

/-- A Set-valued source-sized cocontinuous functor preserves Mono exactly when its original
one-boundary image is Mono. -/
theorem cocontinuous_preservesMonomorphisms_iff_boundaryOne
    (F : SSet.{u} ⥤ Type v) [PreservesColimitsOfSize.{u, u} F] :
    F.PreservesMonomorphisms ↔ Mono (F.map ((boundary.{u} 1).ι)) := by
  constructor
  · intro h
    exact h.preserves ((boundary.{u} 1).ι)
  · exact cocontinuous_preservesMonomorphisms_of_boundaryOne F

end SSet
