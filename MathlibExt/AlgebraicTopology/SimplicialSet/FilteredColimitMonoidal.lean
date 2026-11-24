/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Actual Cartesian monoidality of filtered simplicial-set colimits

Filtered colimits preserve finite limits at every original scalar
evaluation. The resulting monoidal colimit functor and its actual stage
injections preserve the tensor and unit. The indexing object and Hom
universes are independent, with the genuine small-object indexing bound.
-/

noncomputable section
universe u v w
open CategoryTheory Limits Opposite MonoidalCategory

namespace SSet.FilteredColimit

variable (J : Type v) [Category.{w} J] [IsFiltered J] [Small.{u} J]

/-- Actual filtered colimits of simplicial sets preserve finite limits, including the empty limit. -/
instance preservesFiniteLimits : PreservesFiniteLimits (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  apply preservesFiniteLimits_of_evaluation
  intro q
  let E : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj q
  let R : (J ⥤ SSet.{u}) ⥤ (J ⥤ Type u) :=
    (Functor.whiskeringRight J SSet.{u} (Type u)).obj E
  let _ : PreservesFiniteLimits E := by dsimp [E]; infer_instance
  let _ : PreservesFiniteLimits R := by
    apply preservesFiniteLimits_of_evaluation
    intro j
    change PreservesFiniteLimits ((evaluation J SSet.{u}).obj j ⋙ E)
    infer_instance
  let _ : PreservesFiniteLimits (R ⋙ (colim : (J ⥤ Type u) ⥤ Type u)) := inferInstance
  exact preservesFiniteLimits_of_natIso (preservesColimitNatIso E).symm

/-- The actual Cartesian monoidal structure on the scalar colimit functor. -/
instance colimMonoidal : (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The actual Cartesian monoidal evaluation at an individual original indexing object. -/
instance evaluationMonoidal (j : J) : ((evaluation J SSet.{u}).obj j).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The genuine original stage injection, natural in the whole simplicial-set diagram. -/
def injection (j : J) : (evaluation J SSet.{u}).obj j ⟶ colim where
  app X := colimit.ι X j
  naturality _X _Y f := (colimit.ι_map f j).symm

omit [IsFiltered J] in
/-- The whole original stage-injection component is the actual scalar colimit injection. -/
@[simp]
theorem injection_app (j : J) (X : J ⥤ SSet.{u}) : (injection J j).app X = colimit.ι X j := rfl

/-- Cartesian finite-product uniqueness proves the actual stage injection is monoidal. -/
instance injectionMonoidal (j : J) : NatTrans.IsMonoidal (injection J j) := inferInstance

omit [IsFiltered J] [Small.{u} J] in
/-- Evaluation has the literal identity unit map in the pointwise Cartesian structure. -/
theorem evaluation_unit (j : J) :
    Functor.LaxMonoidal.ε ((evaluation J SSet.{u}).obj j) = 𝟙 (𝟙_ SSet.{u}) :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

omit [IsFiltered J] [Small.{u} J] in
/-- Evaluation has the literal identity tensorator on the same original pointwise tensor objects. -/
theorem evaluation_tensor (j : J) (X Y : J ⥤ SSet.{u}) :
    Functor.LaxMonoidal.μ ((evaluation J SSet.{u}).obj j) X Y = 𝟙 (X.obj j ⊗ Y.obj j) := by
  let E := (evaluation J SSet.{u}).obj j
  have hδ : (Functor.Monoidal.μIso E X Y).inv = 𝟙 (X.obj j ⊗ Y.obj j) := by
    change Functor.OplaxMonoidal.δ E X Y = 𝟙 (X.obj j ⊗ Y.obj j)
    rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    apply CartesianMonoidalCategory.hom_ext
    · exact (CartesianMonoidalCategory.prodComparison_fst E X Y).trans
        (Category.id_comp _).symm
    · exact (CartesianMonoidalCategory.prodComparison_snd E X Y).trans
        (Category.id_comp _).symm
  have h := (Functor.Monoidal.μIso E X Y).inv_hom_id
  rw [hδ] at h
  change 𝟙 (X.obj j ⊗ Y.obj j) ≫ Functor.LaxMonoidal.μ E X Y = 𝟙 (X.obj j ⊗ Y.obj j) at h
  exact (Category.id_comp _).symm.trans h

/-- The genuine monoidal colimit unit is the same injection from every original stage unit. -/
theorem injection_unit (j : J) :
    colimit.ι (𝟙_ (J ⥤ SSet.{u})) j =
      Functor.LaxMonoidal.ε (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  have h := NatTrans.IsMonoidal.unit (τ := injection J j)
  rw [evaluation_unit] at h
  change 𝟙 (𝟙_ SSet.{u}) ≫ colimit.ι (𝟙_ (J ⥤ SSet.{u})) j =
    Functor.LaxMonoidal.ε (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) at h
  exact (Category.id_comp _).symm.trans h

/-- Two original same-stage tensor factors inject by the actual colimit tensorator. -/
theorem injection_tensor (j : J) (X Y : J ⥤ SSet.{u}) :
    (colimit.ι X j ⊗ₘ colimit.ι Y j) ≫
      Functor.LaxMonoidal.μ (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) X Y =
        colimit.ι (X ⊗ Y) j := by
  have h := NatTrans.IsMonoidal.tensor (τ := injection J j) X Y
  rw [evaluation_tensor] at h
  change 𝟙 (X.obj j ⊗ Y.obj j) ≫ colimit.ι (X ⊗ Y) j =
    (colimit.ι X j ⊗ₘ colimit.ι Y j) ≫
      Functor.LaxMonoidal.μ (colim : (J ⥤ SSet.{u}) ⥤ SSet.{u}) X Y at h
  exact h.symm.trans (Category.id_comp _)

end SSet.FilteredColimit
