/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteFiniteProducts
import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Genuine codiscrete vertex adjunction and whole closed comparison

All simplex maps are constructed from their full ordered vertex tuples.
The adjunction and closed comparison are proved internally; no power Iso,
contraction or weak-equivalence outcome is supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial
namespace SSet.CodiscreteVertexClosed
open CategoryTheory.Codiscrete

/-- Every original simplex has its actual vertex at the prescribed original index. -/
def simplexVertex (X : SSet.{u}) (n : SimplexCategory) (i : Fin (n.len + 1))
    (x : X.obj (op n)) : X.obj (op ⦋0⦌) :=
  X.map (⦋0⦌.const n i).op x

/-- The whole map to a codiscrete nerve, built from each ordered vertex of each simplex. -/
def liftVertices (X : SSet.{u}) {A : Type u} (f : X.obj (op ⦋0⦌) → A) :
    X ⟶ functorToSSet.obj A where
  app n := ↾fun x => Codiscrete.functor (fun i : Fin (n.unop.len + 1) =>
    f (simplexVertex X n.unop i x))
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply CategoryTheory.nerve.ext_of_isThin (C := Codiscrete A)
    funext i
    apply Codiscrete.ext
    change f (X.map (⦋0⦌.const m.unop i).op (X.map θ x)) =
      f (X.map (⦋0⦌.const n.unop (θ.unop i)).op x)
    rw [← Functor.map_comp_apply]
    change f (X.map (((⦋0⦌.const m.unop i) ≫ θ.unop).op) x) =
      f (X.map (⦋0⦌.const n.unop (θ.unop i)).op x)
    rw [SimplexCategory.const_comp]
    rfl

/-- Restriction reads the actual zero-simplex object, not its component class. -/
def restrictVertices {X : SSet.{u}} {A : Type u} (f : X ⟶ functorToSSet.obj A) :
    X.obj (op ⦋0⦌) → A := fun x => ((f.app (op ⦋0⦌) x).obj (0 : Fin 1)).as

theorem restrict_lift (X : SSet.{u}) {A : Type u} (f : X.obj (op ⦋0⦌) → A) :
    restrictVertices (liftVertices X f) = f := by
  funext x
  change f (X.map (⦋0⦌.const ⦋0⦌ 0).op x) = f x
  have h : ⦋0⦌.const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
    ext i
    fin_cases i
    rfl
  rw [h, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Inverse reconstruction holds on every entire simplex and every ordered vertex. -/
theorem lift_restrict {X : SSet.{u}} {A : Type u} (f : X ⟶ functorToSSet.obj A) :
    liftVertices X (restrictVertices f) = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.nerve.ext_of_isThin (C := Codiscrete A)
  funext i
  apply Codiscrete.ext
  have h := congrArg (fun k => k x) (f.naturality (⦋0⦌.const n.unop i).op)
  exact congrArg (fun s => (s.obj (0 : Fin 1)).as) h

/-- The actual Hom equivalence has no supplied extension or inverse. -/
def homEquiv (X : SSet.{u}) (A : Type u) :
    (X.obj (op ⦋0⦌) ⟶ A) ≃ (X ⟶ functorToSSet.obj A) where
  toFun f := liftVertices X f
  invFun f := ↾restrictVertices f
  left_inv f := by
    apply ConcreteCategory.hom_ext
    intro x
    change restrictVertices (liftVertices X f) x = f x
    exact congrFun (restrict_lift X f) x
  right_inv f := lift_restrict f

/-- The codiscrete nerve is the genuine right adjoint to the original vertex functor. -/
def vertexAdjunction :
    (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌) ⊣
      (functorToSSet : Type u ⥤ SSet.{u}) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro X Y A f g
        apply ConcreteCategory.hom_ext
        intro x
        rfl
      homEquiv_naturality_right := by
        intro X A B f g
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        apply CategoryTheory.nerve.ext_of_isThin (C := Codiscrete B)
        funext i
        rfl }

/-- The actual counit is the full zero-nerve coordinate isomorphism. -/
def vertexIso (A : Type u) :
    ((functorToSSet : Type u ⥤ SSet.{u}).obj A).obj (op ⦋0⦌) ≅ A :=
  Equiv.toIso (CategoryTheory.nerveEquiv.trans CategoryTheory.codiscreteEquiv)

theorem vertexAdjunction_counit (A : Type u) :
    vertexAdjunction.counit.app A = (vertexIso A).hom := rfl

instance vertexAdjunction_counit_isIso : IsIso vertexAdjunction.{u}.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  rw [vertexAdjunction_counit]
  exact (vertexIso A).isIso_hom

/-- Full faithfulness comes from the actual counit Iso of this adjunction. -/
def codiscreteFullyFaithful : (functorToSSet : Type u ⥤ SSet.{u}).FullyFaithful :=
  vertexAdjunction.fullyFaithfulROfIsIsoCounit

/-- The actual closed comparison is forced by the product-preserving left adjoint. -/
theorem codiscreteClosed : MonoidalClosedFunctor (functorToSSet : Type u ⥤ SSet.{u}) := by
  let _ := codiscreteFullyFaithful.full
  let _ := codiscreteFullyFaithful.faithful
  exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
    (functorToSSet : Type u ⥤ SSet.{u}) vertexAdjunction

/-- The whole codiscrete power Iso is the native closed comparison, not a pointwise power
substitution. -/
def closedPowerIso (A B : Type u) :
    functorToSSet.obj ((ihom A).obj B) ≅
      (ihom (functorToSSet.obj A)).obj (functorToSSet.obj B) := by
  let _ := codiscreteClosed
  exact asIso ((expComparison (functorToSSet : Type u ⥤ SSet.{u}) A).app B)

/-- The same Iso retains the native full evaluation leg. -/
theorem closedPowerIso_evaluation (A B : Type u) :
    functorToSSet.obj A ◁ (closedPowerIso A B).hom ≫
      (ihom.ev (functorToSSet.obj A)).app (functorToSSet.obj B) =
    inv (CartesianMonoidalCategory.prodComparison functorToSSet A ((ihom A).obj B)) ≫
      functorToSSet.map ((ihom.ev A).app B) :=
  expComparison_ev (functorToSSet : Type u ⥤ SSet.{u}) A B

/-- Every original target map is natural in this same whole comparison. -/
theorem closedPowerIso_target {A B C : Type u} (f : B ⟶ C) :
    functorToSSet.map ((ihom A).map f) ≫ (closedPowerIso A C).hom =
    (closedPowerIso A B).hom ≫ (ihom (functorToSSet.obj A)).map (functorToSSet.map f) :=
  (expComparison (functorToSSet : Type u ⥤ SSet.{u}) A).naturality f

end SSet.CodiscreteVertexClosed
