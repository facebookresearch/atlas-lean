/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

/-!
# Original finite-action evaluation and free R-modules

Each degree category is the actual functor category on the usual symmetric group.
Restriction along its original finite-alphabet action is right adjoint to left Kan
extension; composition with the existing Day equivalence and free module
adjunction gives the free/evaluation pair on the existing module carrier.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.PositiveLevelModel

/-- The genuine Sigma_n indexing category, with the usual permutation composition. -/
abbrev degreeActionIndex (n : ℕ) := SingleObj (Equiv.Perm (Fin n))

/-- The original action of Sigma_n on the selected finite alphabet of cardinality n. -/
def degreeActionInclusion (n : ℕ) : degreeActionIndex n ⥤ CategoryTheory.Operad.SmallFinBijGroupoid
    :=
  SingleObj.functor (Aut.toEnd.comp (finAutEquiv (card n)).symm.toMonoidHom)

/-- The inclusion sends each permutation to its actual original finite-bijection map. -/
theorem degreeActionInclusion_map (n : ℕ) {a b : degreeActionIndex n} (σ : a ⟶ b) :
    (degreeActionInclusion n).map σ = ((finAutEquiv (card n)).symm σ).asIso.hom := rfl

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) [MonObj R]

/-- The actual category of Sigma_n objects in the base. -/
abbrev degreeActionCategory (n : ℕ) := degreeActionIndex n ⥤ C

/-- Original evaluation retains the full Sigma_n action of the original R-module. -/
def degreeActionEvaluation (n : ℕ) :
    CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R ⥤
        degreeActionCategory (C := C) n :=
  CategoryTheory.Mod.forget R ⋙
      (DayFunctor.equiv CategoryTheory.Operad.SmallFinBijGroupoid C).symm.inverse ⋙
    (Functor.whiskeringLeft (degreeActionIndex n) CategoryTheory.Operad.SmallFinBijGroupoid C).obj
      (degreeActionInclusion n)

/-- Free finite-action input at the original degree, followed by the existing free R-module functor.
-/
def degreeActionFreeAt (n : ℕ) :
    degreeActionCategory (C := C) n ⥤ CategoryTheory.Mod
        (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R :=
  (degreeActionInclusion n).lan ⋙
      (DayFunctor.equiv CategoryTheory.Operad.SmallFinBijGroupoid C).symm.functor ⋙
    CategoryTheory.Mod.free R

/-- The complete actual finite-action free/evaluation adjunction. -/
def degreeActionAdjunction (n : ℕ) : degreeActionFreeAt R n ⊣ degreeActionEvaluation R n :=
  (((degreeActionInclusion n).lanAdjunction C).comp
    (DayFunctor.equiv CategoryTheory.Operad.SmallFinBijGroupoid C).symm.toAdjunction).comp
      (CategoryTheory.Mod.freeForgetAdjunction R)

/-- Forgetting only the finite action recovers the same complete original module evaluation functor.
-/
theorem degreeActionEvaluation_underlying (n : ℕ) :
    degreeActionEvaluation R n ⋙ (CategoryTheory.evaluation (degreeActionIndex n) C).obj
      (SingleObj.star (Equiv.Perm (Fin n))) = CategoryTheory.Mod.dayEvaluation R (card n) := rfl

/-- Every original finite-action evaluation object has the original R-module degree as its carrier.
-/
theorem degreeActionEvaluation_obj (n : ℕ)
    (M : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :
    ((degreeActionEvaluation R n).obj M).obj (SingleObj.star (Equiv.Perm (Fin n))) =
      M.X.functor.obj (card n) := rfl

/-- Every original module map remains the exact same underlying finite-action component map. -/
theorem degreeActionEvaluation_map (n : ℕ)
    {M N : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R}
        (f : M ⟶ N) :
    ((degreeActionEvaluation R n).map f).app (SingleObj.star (Equiv.Perm (Fin n))) =
      f.hom.natTrans.app (card n) := rfl

/-- The complete free finite-action composite is left adjoint to the original ordinary degree
evaluation. -/
def degreeFreeCompositeAdjunction (n : ℕ) :
    CategoryTheory.evaluationLeftAdjoint C (SingleObj.star (Equiv.Perm (Fin n))) ⋙
        degreeActionFreeAt R n ⊣
      CategoryTheory.Mod.dayEvaluation R (card n) :=
  (CategoryTheory.evaluationAdjunctionRight C (SingleObj.star (Equiv.Perm (Fin n)))).comp
    (degreeActionAdjunction R n)

/-- The actual original base free R-module is the free finite-action composite, including every map.
-/
def degreeFreeCompositeIso (n : ℕ) :
    CategoryTheory.evaluationLeftAdjoint C (SingleObj.star (Equiv.Perm (Fin n))) ⋙
        degreeActionFreeAt R n ≅
      CategoryTheory.Mod.dayFreeAt R (card n) :=
  Adjunction.leftAdjointUniq (degreeFreeCompositeAdjunction R n)
    (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (card n))

/-- The complete original unit is retained through the actual free-composite comparison. -/
theorem degreeFreeCompositeIso_unit (n : ℕ) (X : C) :
    (degreeFreeCompositeAdjunction R n).unit.app X ≫
      (CategoryTheory.Mod.dayEvaluation R (card n)).map ((degreeFreeCompositeIso R n).hom.app X) =
        (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (card n)).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The full original module action counit is retained through the actual free-composite comparison.
-/
theorem degreeFreeCompositeIso_counit (n : ℕ)
    (M : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :
    (degreeFreeCompositeIso R n).hom.app ((CategoryTheory.Mod.dayEvaluation R (card n)).obj M) ≫
      (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (card n)).counit.app M =
        (degreeFreeCompositeAdjunction R n).counit.app M :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ M

/-- The genuine finite-action generator family, retaining the original degree and action-arrow
label. -/
def actionGenerators (positive : Bool)
    (K : ∀ n, MorphismProperty (degreeActionCategory (C := C) n)) :
    MorphismProperty
        (CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R) :=
  ofHoms (fun q : Σ n : {n : ℕ // positive = true → 0 < n}, (K n.1).toSet =>
    (degreeActionFreeAt R q.1.1).map q.2.1.hom)

/-- The exact right lifting class is tested at each retained original finite-action degree. -/
theorem actionGenerators_rlp_iff (positive : Bool)
    (K : ∀ n, MorphismProperty (degreeActionCategory (C := C) n))
    {M N : CategoryTheory.Mod (DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid C) R}
        (f : M ⟶ N) :
    (actionGenerators R positive K).rlp f ↔
      ∀ n : ℕ, (positive = true → 0 < n) → (K n).rlp ((degreeActionEvaluation R n).map f) := by
  constructor
  · intro h n hn A B g hg
    apply (Adjunction.hasLiftingProperty_iff (degreeActionAdjunction R n) g f).mp
    exact h _ (ofHoms.mk (f := fun q : Σ n : {n : ℕ // positive = true → 0 < n}, (K n.1).toSet =>
      (degreeActionFreeAt R q.1.1).map q.2.1.hom) ⟨⟨n, hn⟩, ⟨Arrow.mk g, hg⟩⟩)
  · intro h A B g hg
    obtain ⟨q⟩ := hg
    exact (Adjunction.hasLiftingProperty_iff (degreeActionAdjunction R q.1.1) q.2.1.hom f).mpr
      (h q.1.1 q.1.2 _ q.2.2)

end HomotopicalAlgebra.PositiveLevelModel
