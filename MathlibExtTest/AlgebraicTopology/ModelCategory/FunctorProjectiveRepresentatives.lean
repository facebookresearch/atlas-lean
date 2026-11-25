/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Representatives
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Complete original-object and same-cardinal representative-family contracts -/
set_option autoImplicit false
noncomputable section
universe w uD vD uS vS uM vM
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.FunctorProjective HomotopicalAlgebra.FunctorProjective.Representatives

namespace MathlibExtTest.FunctorProjectiveRepresentatives

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocallySmall.{w} S]
  (e : D ≌ S) (d : CofibrantGenerationData M κ) (P : MorphismProperty M)

example {x y : D} (i : x ≅ y) (z : D) : (x ⟶ z) ≃ (y ⟶ z) :=
  indexHomEquiv i z

example {x y : D} (i : x ≅ y) (z : D) (f : x ⟶ z) :
    indexHomEquiv i z f = i.inv ≫ f := rfl

example {x y : D} (i : x ≅ y) (z : D) (f : y ⟶ z) :
    (indexHomEquiv i z).symm f = i.hom ≫ f := rfl

example {x y : D} (i : x ≅ y) (A : M) (z : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor d x).obj A).obj z ≅ ((freeFunctor d y).obj A).obj z := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexComponentIso d i A z

example {x y : D} (i : x ≅ y) (A : M) (z : D) (f : x ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    indexInsertion d x A z f ≫ (indexComponentIso d i A z).hom =
      indexInsertion d y A z (i.inv ≫ f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexComponentIso_insertion d i A z f

example {x y : D} (i : x ≅ y) (A : M) (z : D) (f : y ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    indexInsertion d y A z f ≫ (indexComponentIso d i A z).inv =
      indexInsertion d x A z (i.hom ≫ f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexComponentIso_insertion_inv d i A z f

example {x y : D} (i : x ≅ y) :
    (fun (z : D) (f : x ⟶ z) => indexHomEquiv i z f) =
      fun (z : D) (f : x ⟶ z) => i.inv ≫ f :=
  indexHomEquiv_forward_function i

example {x y : D} (i : x ≅ y) :
    (fun (z : D) (f : y ⟶ z) => (indexHomEquiv i z).symm f) =
      fun (z : D) (f : y ⟶ z) => i.hom ≫ f :=
  indexHomEquiv_inverse_function i

example {x y : D} (i : x ≅ y) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (A : M) (z : D) => ((indexFreeIso d i).hom.app A).app z) =
      fun (A : M) (z : D) => (indexComponentIso d i A z).hom := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexFreeIso_hom_function d i

example {x y : D} (i : x ≅ y) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (A : M) (z : D) => ((indexFreeIso d i).inv.app A).app z) =
      fun (A : M) (z : D) => (indexComponentIso d i A z).inv := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexFreeIso_inv_function d i

example (x : D) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction d x).unit.app A = indexInsertion d x A x (𝟙 x) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexUnit_insertion d x A

example (x z : D) (X : D ⥤ M) (f : x ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    indexInsertion d x (X.obj x) z f ≫ ((freeEvaluationAdjunction d x).counit.app X).app z =
      X.map f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexCounit_insertion d x z X f

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (x : D) (A : M) => (freeEvaluationAdjunction d x).unit.app A) =
      fun (x : D) (A : M) => indexInsertion d x A x (𝟙 x) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexUnit_insertion_function d

example {x y : D} (i : x ≅ y) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction d x).unit.app A ≫ ((indexFreeIso d i).hom.app A).app x =
      indexInsertion d y A x i.inv := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexFreeIso_unit d i A

example {x y : D} (i : x ≅ y) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction d y).unit.app A ≫ ((indexFreeIso d i).inv.app A).app y =
      indexInsertion d x A y i.hom := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexFreeIso_unit_inv d i A

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (x z : D) (X : D ⥤ M) (f : x ⟶ z) =>
      indexInsertion d x (X.obj x) z f ≫ ((freeEvaluationAdjunction d x).counit.app X).app z) =
      fun (x z : D) (X : D ⥤ M) (f : x ⟶ z) => X.map f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexCounit_insertion_function d

example {x y : D} (i : x ≅ y) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (A B : M) (f : A ⟶ B) (z : D) =>
      ((freeFunctor d x).map f).app z ≫ ((indexFreeIso d i).hom.app B).app z) =
      fun (A B : M) (f : A ⟶ B) (z : D) =>
        ((indexFreeIso d i).hom.app A).app z ≫ ((freeFunctor d y).map f).app z := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexFreeIso_coefficient_function d i

example {x y : D} (i : x ≅ y) (A : M) {z z' : D} (g : z ⟶ z') :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor d x).obj A).map g ≫ (indexComponentIso d i A z').hom =
      (indexComponentIso d i A z).hom ≫ ((freeFunctor d y).obj A).map g := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact indexComponentIso_naturality d i A g

example (x : D) (f : Arrow M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    Arrow.mk ((freeFunctor d x).map f.hom) ≅
      Arrow.mk ((freeFunctor d (e.inverse.obj (e.functor.obj x))).map f.hom) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact originalFreeArrowIso e d x f

example (x : D) (f : Arrow M) (z : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (originalFreeArrowIso e d x f).hom.left.app z =
        (indexComponentIso d (e.unitIso.app x) f.left z).hom ∧
      (originalFreeArrowIso e d x f).hom.right.app z =
        (indexComponentIso d (e.unitIso.app x) f.right z).hom ∧
      (originalFreeArrowIso e d x f).inv.left.app z =
        (indexComponentIso d (e.unitIso.app x) f.left z).inv ∧
      (originalFreeArrowIso e d x f).inv.right.app z =
        (indexComponentIso d (e.unitIso.app x) f.right z).inv := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact originalFreeArrowIso_fields e d x f z

example {X Y : D ⥤ M} (f : X ⟶ Y) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    family e d P f ↔ ∃ q : S × P.toSet,
      Arrow.mk f = Arrow.mk ((freeFunctor d (e.inverse.obj q.1)).map q.2.1.hom) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_iff e d P f

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    family e d P ≤ freeGenerators d P := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_le_allOriginal e d P

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    freeGenerators d P ≤ (family e d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact allOriginal_le_family_isoClosure e d P

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).isoClosure = (freeGenerators d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_isoClosure e d P

example : (family e d P).rlp = P.rlp.functorCategory D := family_rlp e d P

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).rlp = (freeGenerators d P).rlp := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_rlp_eq_allOriginal e d P

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).rlp.llp = (freeGenerators d P).rlp.llp := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact family_left_eq_allOriginal e d P

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).strictMap (e.congrLeft (E := M)).functor ≤
      (freeGenerators (D := S) d P).isoClosure := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact mapped_family_le_small_isoClosure e d P

example :
    family e d P ≤ (normalizedTarget e d P).inverseImage (e.congrLeft (E := M)).functor :=
  family_le_normalized_inverseImage e d P

section ActualSmallRepresentatives
variable [Small.{w} S] [P.IsSmall.{w}]

example : (family e d P).IsSmall.{w} := family_isSmall e d P

example : (normalizedTarget e d P).IsSmall.{w} := normalizedTarget_isSmall e d P

example : LocallySmall.{w} (D ⥤ M) := originalFunctor_locallySmall e d

example (hP : P.IsCardinalForSmallObjectArgument κ) :
    (normalizedTarget e d P).IsCardinalForSmallObjectArgument κ :=
  normalizedTarget_eligible e d P hP

example (hP : P.IsCardinalForSmallObjectArgument κ) :
    (family e d P).IsCardinalForSmallObjectArgument κ :=
  family_eligible e d P hP

example (hP : P.IsCardinalForSmallObjectArgument κ) :
    FunctorialFactorizationData (family e d P).rlp.llp (family e d P).rlp :=
  factorizationData e d P hP

example (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    factorizationData e d P hP = SmallObject.functorialFactorizationData (family e d P) κ :=
  factorizationData_eq e d P hP

example (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationData e d P hP).Z =
      (SmallObject.functorialFactorizationData (family e d P) κ).Z :=
  factorizationData_Z e d P hP

example (hP : P.IsCardinalForSmallObjectArgument κ) (f : Arrow (D ⥤ M)) (x : D) :
    ((factorizationData e d P hP).i.app f).app x ≫
      ((factorizationData e d P hP).p.app f).app x = f.hom.app x :=
  factorizationData_fac_app e d P hP f x

example (hP : P.IsCardinalForSmallObjectArgument κ) (f : Arrow (D ⥤ M)) :
    (factorizationData e d P hP).Z.map (𝟙 f) = 𝟙 ((factorizationData e d P hP).Z.obj f) :=
  factorizationData_map_id e d P hP f

example (hP : P.IsCardinalForSmallObjectArgument κ) {f g k : Arrow (D ⥤ M)}
    (a : f ⟶ g) (b : g ⟶ k) :
    (factorizationData e d P hP).Z.map (a ≫ b) =
      (factorizationData e d P hP).Z.map a ≫ (factorizationData e d P hP).Z.map b :=
  factorizationData_map_comp e d P hP a b

example (hP : P.IsCardinalForSmallObjectArgument κ) {f g : Arrow (D ⥤ M)}
    (a : f ⟶ g) :
    a.left ≫ (factorizationData e d P hP).i.app g =
      (factorizationData e d P hP).i.app f ≫ (factorizationData e d P hP).Z.map a :=
  factorizationData_i_naturality e d P hP a

example (hP : P.IsCardinalForSmallObjectArgument κ) {f g : Arrow (D ⥤ M)}
    (a : f ⟶ g) :
    (factorizationData e d P hP).Z.map a ≫ (factorizationData e d P hP).p.app g =
      (factorizationData e d P hP).p.app f ≫ a.right :=
  factorizationData_p_naturality e d P hP a

example (hP : P.IsCardinalForSmallObjectArgument κ) {f g : Arrow (D ⥤ M)}
    (a : f ⟶ g) (x : D) :
    a.left.app x ≫ ((factorizationData e d P hP).i.app g).app x =
      ((factorizationData e d P hP).i.app f).app x ≫
        ((factorizationData e d P hP).Z.map a).app x :=
  factorizationData_i_naturality_app e d P hP a x

example (hP : P.IsCardinalForSmallObjectArgument κ) {f g : Arrow (D ⥤ M)}
    (a : f ⟶ g) (x : D) :
    ((factorizationData e d P hP).Z.map a).app x ≫
        ((factorizationData e d P hP).p.app g).app x =
      ((factorizationData e d P hP).p.app f).app x ≫ a.right.app x :=
  factorizationData_p_naturality_app e d P hP a x

example (hP : P.IsCardinalForSmallObjectArgument κ) (f : Arrow (D ⥤ M)) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => (family e d P).homFamily)
      ((factorizationData e d P hP).i.app f) :=
  factorizationCellComplex e d P hP f

example (hP : P.IsCardinalForSmallObjectArgument κ) (f : Arrow (D ⥤ M)) :
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationCellComplex e d P hP f).F =
      (SmallObject.relativeCellComplexιObj (family e d P) κ f.hom).F :=
  factorizationCellComplex_F e d P hP f

example (hP : P.IsCardinalForSmallObjectArgument κ) (f : Arrow (D ⥤ M)) :
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (factorizationCellComplex e d P hP f).incl =
      (SmallObject.relativeCellComplexιObj (family e d P) κ f.hom).incl :=
  factorizationCellComplex_incl e d P hP f

example (hP : P.IsCardinalForSmallObjectArgument κ) :
    letI : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
    (family e d P).IsSmall.{w} ∧ LocallySmall.{w} (D ⥤ M) ∧ HasPushouts (D ⥤ M) ∧
      HasCoproducts.{w} (D ⥤ M) ∧ HasIterationOfShape κ.ord.ToType (D ⥤ M) := by
  let _ : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
  exact ⟨SmallObject.isSmall (family e d P) κ, SmallObject.locallySmall (family e d P) κ,
    SmallObject.hasPushouts (family e d P) κ, SmallObject.hasCoproducts (family e d P) κ,
    SmallObject.hasIterationOfShape (family e d P) κ⟩

example (hP : P.IsCardinalForSmallObjectArgument κ) {A B X Y : D ⥤ M}
    (i : A ⟶ B) (hi : family e d P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => (family e d P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op A)) := by
  let _ : (family e d P).IsCardinalForSmallObjectArgument κ := family_eligible e d P hP
  exact SmallObject.preservesColimit (family e d P) κ i hi f c

example : (family e d d.I).IsCardinalForSmallObjectArgument κ := familyI_eligible e d
example : (family e d d.J).IsCardinalForSmallObjectArgument κ := familyJ_eligible e d

example {X Y : M} (f : X ⟶ Y) (hf : P f) (x : D) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).isoClosure ((freeFunctor d x).map f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact allOriginal_le_family_isoClosure e d P _ (freeGenerator_mem d P x f hf)

example {X Y : M} (f : X ⟶ Y) (hf : P f) (s : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    family e d P ((freeFunctor d (e.inverse.obj s)).map f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact map_mem_adjointFamilyGenerators
    (fun s : S => freeFunctor (D := D) d (e.inverse.obj s)) P s f hf

example {X Y : D ⥤ M} (f : X ⟶ Y) (hf : (family e d P).rlp f) (x : D) :
    P.rlp (f.app x) := by
  rw [family_rlp] at hf
  exact hf x

example {X Y : D ⥤ M} (f : X ⟶ Y) (hf : ∀ x : D, P.rlp (f.app x)) :
    (family e d P).rlp f := by
  rw [family_rlp]
  exact hf

example {X Y : D ⥤ M} (f : X ⟶ Y)
    (hf : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeGenerators d P).rlp.llp f) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (family e d P).rlp.llp f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [family_left_eq_allOriginal]
  exact hf

example {X Y : D ⥤ M} (f : X ⟶ Y) (hf : (family e d P).rlp.llp f) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeGenerators d P).rlp.llp f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  rw [← family_left_eq_allOriginal e d P]
  exact hf

example :
    FunctorialFactorizationData (family e d d.I).rlp.llp
      ((trivialFibrations M).functorCategory D) :=
  Representatives.cofibrantFactorizationData e d

example :
    FunctorialFactorizationData (family e d d.J).rlp.llp
      ((fibrations M).functorCategory D) :=
  Representatives.fibrantFactorizationData e d

example :
    (Representatives.cofibrantFactorizationData e d).Z =
      (factorizationData e d d.I d.I_smallObject).Z :=
  Representatives.cofibrantFactorizationData_Z e d

example :
    (Representatives.fibrantFactorizationData e d).Z =
      (factorizationData e d d.J d.J_smallObject).Z :=
  Representatives.fibrantFactorizationData_Z e d

example (f : Arrow (D ⥤ M)) (x : D) :
    ((Representatives.cofibrantFactorizationData e d).i.app f).app x ≫
      ((Representatives.cofibrantFactorizationData e d).p.app f).app x = f.hom.app x :=
  Representatives.cofibrantFactorizationData_fac_app e d f x

example (f : Arrow (D ⥤ M)) (x : D) :
    ((Representatives.fibrantFactorizationData e d).i.app f).app x ≫
      ((Representatives.fibrantFactorizationData e d).p.app f).app x = f.hom.app x :=
  Representatives.fibrantFactorizationData_fac_app e d f x

end ActualSmallRepresentatives

example :
    (family e d d.I).rlp = (trivialFibrations M).functorCategory D ∧
      (family e d d.J).rlp = (fibrations M).functorCategory D :=
  familyI_familyJ_rlp e d

section RaisedOriginalIndex

/-- The original object type is raised with the stock category. -/
local instance raisedOriginalObjectCategory : Category.{vS} (ULift.{uS + 1} S) :=
  uliftCategory S
/-- The original Hom universe is independently raised with the stock category. -/
local instance raisedOriginalHomCategory :
    Category.{max (vS + 1) vS} (ULiftHom.{vS + 1} (ULift.{uS + 1} S)) :=
  @ULiftHom.category (ULift.{uS + 1} S) (inferInstance : Category.{vS} (ULift.{uS + 1} S))

example [Small.{w} S] :
    IsCardinalForSmallObjectArgument
      (family (ULiftHomULiftCategory.equiv.{vS + 1, uS + 1} S).symm d d.I) κ :=
  familyI_eligible (ULiftHomULiftCategory.equiv S).symm d

example [Small.{w} S] :
    (family (ULiftHomULiftCategory.equiv.{vS + 1, uS + 1} S).symm d d.J).rlp =
      (fibrations M).functorCategory (ULiftHom.{vS + 1} (ULift.{uS + 1} S)) := by
  rw [family_rlp, d.J_rlp]

end RaisedOriginalIndex

example :
    IsCardinalForSmallObjectArgument
      (family (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{w + 1})) d d.I) κ :=
  familyI_eligible (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{w + 1})) d

example :
    IsCardinalForSmallObjectArgument
      (family (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) d d.I) κ :=
  familyI_eligible (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) d

example :
    IsCardinalForSmallObjectArgument
      (family (κ := κ)
        (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) d d.J) κ :=
  familyJ_eligible (κ := κ)
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) d

end MathlibExtTest.FunctorProjectiveRepresentatives
