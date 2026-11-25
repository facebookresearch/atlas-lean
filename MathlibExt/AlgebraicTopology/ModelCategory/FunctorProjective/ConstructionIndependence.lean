/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.SourceConstruction

/-!
# Independence of projective model constructions

Two cofibrant-generation and small-index witnesses for the same coefficient
model define the same projective model structure on the functor category,
even when their working universes and chosen small index categories differ.
For each arrow, lifting gives comparison maps between the two factorization
objects that preserve both triangles. These maps are objectwise weak
equivalences, and the corresponding arrow maps have identity endpoints.
The comparison maps are chosen separately for each arrow.
-/

set_option autoImplicit false
noncomputable section

universe w w' uD vD uC vC uK vK

namespace HomotopicalAlgebra.FunctorProjective

open CategoryTheory CategoryTheory.MorphismProperty

private theorem modelCategory_eq_of_classes {K : Type uK} [Category.{vK} K]
    (M N : ModelCategory K)
    (hF : M.categoryWithFibrations.fibrations = N.categoryWithFibrations.fibrations)
    (hC : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations)
    (hW : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) : M = N := by
  have hF' : M.categoryWithFibrations = N.categoryWithFibrations :=
    congrArg (fun P : MorphismProperty K => (⟨P⟩ : CategoryWithFibrations K)) hF
  have hC' : M.categoryWithCofibrations = N.categoryWithCofibrations :=
    congrArg (fun P : MorphismProperty K => (⟨P⟩ : CategoryWithCofibrations K)) hC
  have hW' : M.categoryWithWeakEquivalences = N.categoryWithWeakEquivalences :=
    congrArg (fun P : MorphismProperty K => (⟨P⟩ : CategoryWithWeakEquivalences K)) hW
  cases M
  cases N
  cases hF'
  cases hC'
  cases hW'
  rfl

private def factorComparisonLift {K : Type uK} [Category.{vK} K]
    (Q : MorphismProperty K) (a b : FunctorialFactorizationData Q.llp Q) (f : Arrow K) :
    (CommSq.mk (b.fac_app.trans a.fac_app.symm) :
      CommSq (b.i.app f) (a.i.app f) (b.p.app f) (a.p.app f)).LiftStruct := by
  letI : HasLiftingProperty (a.i.app f) (b.p.app f) := a.hi f _ (b.hp f)
  exact (CommSq.HasLift.exists_lift (sq :=
    (CommSq.mk (b.fac_app.trans a.fac_app.symm) :
      CommSq (b.i.app f) (a.i.app f) (b.p.app f) (a.p.app f)))).some

namespace SourceConstruction.FromData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (s : Functor.EssentialIndexData.{w} D C)
  {kappa' : Cardinal.{w'}} [Fact kappa'.IsRegular]
  [OrderBot kappa'.ord.ToType] (d' : CofibrantGenerationData C kappa')
  (s' : Functor.EssentialIndexData.{w'} D C)

local instance firstIndexLocallySmall : LocallySmall.{w} s.index := locallySmall_self s.index
local instance secondIndexLocallySmall : LocallySmall.{w'} s'.index := locallySmall_self s'.index

/-- Independent coefficient families, cardinals and full index equivalences
give literally the same model record on the unchanged original carrier. -/
theorem modelCategory_eq : modelCategory d s = modelCategory d' s' := by
  apply modelCategory_eq_of_classes
  · exact (EssentialIndex.fibrations_eq s.equivalence d).trans
      (EssentialIndex.fibrations_eq s'.equivalence d').symm
  · exact (EssentialIndex.cofibrations_eq s.equivalence d).trans
      (EssentialIndex.cofibrations_eq s'.equivalence d').symm
  · exact (EssentialIndex.weakEquivalences_eq s.equivalence d).trans
      (EssentialIndex.weakEquivalences_eq s'.equivalence d').symm

/-- Actual original lifting compares the two first middle diagrams. -/
def cofibrantComparison (f : Arrow (D ⥤ C)) :
    (cofibrantFactorizationData d s).Z.obj f ⟶ (cofibrantFactorizationData d' s').Z.obj f :=
  (factorComparisonLift ((trivialFibrations C).functorCategory D)
    (cofibrantFactorizationData d s) (cofibrantFactorizationData d' s') f).l

/-- Both first-factor equations concern that same whole comparison map. -/
theorem cofibrantComparison_triangles (f : Arrow (D ⥤ C)) :
    (cofibrantFactorizationData d s).i.app f ≫ cofibrantComparison d s d' s' f =
        (cofibrantFactorizationData d' s').i.app f ∧
      cofibrantComparison d s d' s' f ≫ (cofibrantFactorizationData d' s').p.app f =
        (cofibrantFactorizationData d s).p.app f :=
  ⟨(factorComparisonLift ((trivialFibrations C).functorCategory D)
      (cofibrantFactorizationData d s) (cofibrantFactorizationData d' s') f).fac_left,
    (factorComparisonLift ((trivialFibrations C).functorCategory D)
      (cofibrantFactorizationData d s) (cofibrantFactorizationData d' s') f).fac_right⟩

/-- Actual whole-diagram lifting also compares the two second middle diagrams. -/
def fibrantComparison (f : Arrow (D ⥤ C)) :
    (fibrantFactorizationData d s).Z.obj f ⟶ (fibrantFactorizationData d' s').Z.obj f :=
  (factorComparisonLift ((fibrations C).functorCategory D)
    (fibrantFactorizationData d s) (fibrantFactorizationData d' s') f).l

/-- Both original second-factor triangles commute for the same comparison. -/
theorem fibrantComparison_triangles (f : Arrow (D ⥤ C)) :
    (fibrantFactorizationData d s).i.app f ≫ fibrantComparison d s d' s' f =
        (fibrantFactorizationData d' s').i.app f ∧
      fibrantComparison d s d' s' f ≫ (fibrantFactorizationData d' s').p.app f =
        (fibrantFactorizationData d s).p.app f :=
  ⟨(factorComparisonLift ((fibrations C).functorCategory D)
      (fibrantFactorizationData d s) (fibrantFactorizationData d' s') f).fac_left,
    (factorComparisonLift ((fibrations C).functorCategory D)
      (fibrantFactorizationData d s) (fibrantFactorizationData d' s') f).fac_right⟩

/-- Both first projections are weak; the original right triangle and
two-out-of-three therefore make the whole first comparison objectwise weak. -/
theorem cofibrantComparison_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D (cofibrantComparison d s d' s' f) := by
  let W := (weakEquivalences C).functorCategory D
  apply W.of_postcomp (cofibrantComparison d s d' s' f)
    ((cofibrantFactorizationData d' s').p.app f)
    (cofibrantFactorizationData_right_weak d' s' f)
  rw [(cofibrantComparison_triangles d s d' s' f).2]
  exact cofibrantFactorizationData_right_weak d s f

/-- Weakness of the two second inclusions and their original left triangle
give objectwise weakness of the whole second comparison. -/
theorem fibrantComparison_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D (fibrantComparison d s d' s' f) := by
  let W := (weakEquivalences C).functorCategory D
  apply W.of_precomp ((fibrantFactorizationData d s).i.app f)
    (fibrantComparison d s d' s' f) (fibrantFactorizationData_left_weak d s f)
  rw [(fibrantComparison_triangles d s d' s' f).1]
  exact fibrantFactorizationData_left_weak d' s' f

/-- The first inclusion comparison fixes the entire original source. -/
def cofibrantComparisonLeftArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((cofibrantFactorizationData d s).i.app f) ⟶
      Arrow.mk ((cofibrantFactorizationData d' s').i.app f) :=
  Arrow.homMk (𝟙 f.left) (cofibrantComparison d s d' s' f)
    (by
      change (𝟙 f.left) ≫ (cofibrantFactorizationData d' s').i.app f =
        (cofibrantFactorizationData d s).i.app f ≫ cofibrantComparison d s d' s' f
      simpa only [Category.id_comp] using (cofibrantComparison_triangles d s d' s' f).1.symm)

/-- The first projection comparison fixes the entire original target. -/
def cofibrantComparisonRightArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((cofibrantFactorizationData d s).p.app f) ⟶
      Arrow.mk ((cofibrantFactorizationData d' s').p.app f) :=
  Arrow.homMk (cofibrantComparison d s d' s' f) (𝟙 f.right)
    (by
      change cofibrantComparison d s d' s' f ≫ (cofibrantFactorizationData d' s').p.app f =
        (cofibrantFactorizationData d s).p.app f ≫ 𝟙 f.right
      exact (cofibrantComparison_triangles d s d' s' f).2.trans (Category.comp_id _).symm)

/-- The second inclusion comparison retains the same unchanged original source. -/
def fibrantComparisonLeftArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((fibrantFactorizationData d s).i.app f) ⟶
      Arrow.mk ((fibrantFactorizationData d' s').i.app f) :=
  Arrow.homMk (𝟙 f.left) (fibrantComparison d s d' s' f)
    (by
      change (𝟙 f.left) ≫ (fibrantFactorizationData d' s').i.app f =
        (fibrantFactorizationData d s).i.app f ≫ fibrantComparison d s d' s' f
      simpa only [Category.id_comp] using (fibrantComparison_triangles d s d' s' f).1.symm)

/-- The second projection comparison retains the same unchanged original target. -/
def fibrantComparisonRightArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((fibrantFactorizationData d s).p.app f) ⟶
      Arrow.mk ((fibrantFactorizationData d' s').p.app f) :=
  Arrow.homMk (fibrantComparison d s d' s' f) (𝟙 f.right)
    (by
      change fibrantComparison d s d' s' f ≫ (fibrantFactorizationData d' s').p.app f =
        (fibrantFactorizationData d s).p.app f ≫ 𝟙 f.right
      exact (fibrantComparison_triangles d s d' s' f).2.trans (Category.comp_id _).symm)

/-- The two first Arrow comparisons have the same actual middle map and
literal identity transformations at the original endpoints. -/
theorem cofibrantComparisonArrow_endpoints (f : Arrow (D ⥤ C)) :
    (cofibrantComparisonLeftArrow d s d' s' f).left = 𝟙 f.left ∧
      (cofibrantComparisonRightArrow d s d' s' f).right = 𝟙 f.right ∧
      (cofibrantComparisonLeftArrow d s d' s' f).right =
        (cofibrantComparisonRightArrow d s d' s' f).left := ⟨rfl, rfl, rfl⟩

/-- The second Arrow comparisons also retain both endpoints and the same
whole natural transformation between the actual middle diagrams. -/
theorem fibrantComparisonArrow_endpoints (f : Arrow (D ⥤ C)) :
    (fibrantComparisonLeftArrow d s d' s' f).left = 𝟙 f.left ∧
      (fibrantComparisonRightArrow d s d' s' f).right = 𝟙 f.right ∧
      (fibrantComparisonLeftArrow d s d' s' f).right =
        (fibrantComparisonRightArrow d s d' s' f).left := ⟨rfl, rfl, rfl⟩

end SourceConstruction.FromData

namespace SourceConstruction

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] [IsCombinatorialModelCategory.{w} C] [EssentiallySmall.{w} D]
  {kappa' : Cardinal.{w'}} [Fact kappa'.IsRegular] [OrderBot kappa'.ord.ToType]
  (d' : CofibrantGenerationData C kappa') (s' : Functor.EssentialIndexData.{w'} D C)

/-- The combinatorial projective construction agrees with the construction from
independently chosen coefficient generation and small-index equivalence data. -/
theorem modelCategory_eq_fromData :
    modelCategory (D := D) (C := C) = FromData.modelCategory d' s' := by
  let : Fact (cardinal C).IsRegular := cardinal_regular C
  let : OrderBot (cardinal C).ord.ToType := orderBot C
  exact FromData.modelCategory_eq (baseData C) (essentialIndex (D := D) (C := C)) d' s'

end SourceConstruction

end HomotopicalAlgebra.FunctorProjective
