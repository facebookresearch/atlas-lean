/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Connected components and constant simplicial sets

The connected-component functor is left adjoint to the constant simplicial-set functor, with an explicit equivalence classifying whole simplicial maps into a constant target. The counit identifies the connected components of a constant simplicial set with its carrier, and its isomorphism proves that the constant functor is fully faithful.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SSet.PiZeroConstantAdjunction
variable {X : SSet.{u}}

theorem all_vertices_same_component {n : SimplexCategoryᵒᵖ} (s : X.obj n)
    (α β : ⦋0⦌ ⟶ n.unop) :
    π₀.mk (X.map α.op s) = π₀.mk (X.map β.op s) := by
  obtain ⟨⟨n⟩⟩ := n
  have hα : α = ⦋0⦌.const ⦋n⦌ (α 0) := by
    ext i
    fin_cases i
    rfl
  have hβ : β = ⦋0⦌.const ⦋n⦌ (β 0) := by
    ext i
    fin_cases i
    rfl
  rw [hα, hβ]
  rcases le_total (α 0) (β 0) with h | h
  · apply π₀.sound
    exact Edge.mk (X.map (SimplexCategory.mkOfLe (α 0) (β 0) h).op s)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)
  · symm
    apply π₀.sound
    exact Edge.mk (X.map (SimplexCategory.mkOfLe (β 0) (α 0) h).op s)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)
      (by
        dsimp [SimplicialObject.δ]
        rw [← Functor.map_comp_apply, ← op_comp]
        apply congrArg (fun q : ⦋0⦌ ⟶ ⦋n⦌ ↦ X.map q.op s)
        ext j
        fin_cases j
        rfl)


/-- The actual connected-component label is independent of the chosen vertex of each simplex. -/
def componentMap (X : SSet.{u}) : X ⟶ (SimplicialObject.const (Type u)).obj (π₀ X) where
  app n := ↾fun x => π₀.mk (X.map (⦋0⦌.const n.unop 0).op x)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    change π₀.mk (X.map (⦋0⦌.const m.unop 0).op (X.map θ x)) =
      π₀.mk (X.map (⦋0⦌.const n.unop 0).op x)
    rw [← Functor.map_comp_apply]
    change π₀.mk (X.map (((⦋0⦌.const m.unop 0) ≫ θ.unop).op) x) =
      π₀.mk (X.map (⦋0⦌.const n.unop 0).op x)
    exact all_vertices_same_component x _ _

/-- Actual maps to a discrete constant target are constant along every source edge. -/
def descend {A : Type u} (f : X ⟶ (SimplicialObject.const (Type u)).obj A) :
    π₀ X → A :=
  π₀.lift (f.app (op ⦋0⦌)) (fun a b e => by
    have ha := congrArg (fun h => h e.edge) (f.naturality (SimplexCategory.δ (1 : Fin 2)).op)
    have hb := congrArg (fun h => h e.edge) (f.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    have hs : X.map (SimplexCategory.δ (1 : Fin 2)).op e.edge = a := e.src_eq
    have ht : X.map (SimplexCategory.δ (0 : Fin 2)).op e.edge = b := e.tgt_eq
    have h : f.app (op ⦋0⦌) (X.map (SimplexCategory.δ (1 : Fin 2)).op e.edge) =
        f.app (op ⦋0⦌) (X.map (SimplexCategory.δ (0 : Fin 2)).op e.edge) := by
      exact ha.trans hb.symm
    rw [hs, ht] at h
    exact h)

/-- The reverse map is actual postcomposition of the component-label transformation. -/
def liftComponentMap (X : SSet.{u}) {A : Type u} (f : π₀ X ⟶ A) :
    X ⟶ (SimplicialObject.const (Type u)).obj A :=
  componentMap X ≫ (SimplicialObject.const (Type u)).map f

theorem descend_lift (X : SSet.{u}) {A : Type u} (f : π₀ X ⟶ A) :
    descend (liftComponentMap X f) = f := by
  funext c
  induction c using π₀.rec with
  | mk x => simp [descend, liftComponentMap, componentMap]

/-- Reconstruction is a whole simplicial map, not a pointwise-zero equivalence claim. -/
theorem lift_descend {A : Type u} (f : X ⟶ (SimplicialObject.const (Type u)).obj A) :
    liftComponentMap X (↾descend f) = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg (fun g => g x) (f.naturality (⦋0⦌.const n.unop 0).op)
  change f.app (op ⦋0⦌) (X.map (⦋0⦌.const n.unop 0).op x) = f.app n x
  exact h

/-- The actual component quotient classifies whole maps to the inner-constant target. -/
def homEquiv (X : SSet.{u}) (A : Type u) :
    (π₀ X ⟶ A) ≃ (X ⟶ (SimplicialObject.const (Type u)).obj A) where
  toFun := liftComponentMap X
  invFun f := ↾descend f
  left_inv f := by
    apply ConcreteCategory.hom_ext
    intro c
    change descend (liftComponentMap X f) c = f c
    exact congrFun (descend_lift X f) c
  right_inv := lift_descend

/-- The connected-component functor is left adjoint to the genuine inner-constant embedding. -/
def adjunction : π₀Functor.{u} ⊣ SimplicialObject.const (Type u) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro X Y A f g
        apply ConcreteCategory.hom_ext
        intro c
        induction c using π₀.rec with
        | mk x => rfl
      homEquiv_naturality_right := by
        intro X A B f g
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        rfl }

/-- The actual quotient of a discrete constant target recovers exactly that target. -/
def piZeroConstEquiv (A : Type u) :
    π₀ ((SimplicialObject.const (Type u)).obj A) ≃ A where
  toFun := π₀.lift (fun a => a) (fun _ _ e => e.src_eq.symm.trans e.tgt_eq)
  invFun a := π₀.mk a
  left_inv c := by induction c using π₀.rec with | mk a => rfl
  right_inv a := rfl

/-- The actual quotient of a discrete constant simplicial set is isomorphic to its carrier. -/
def piZeroConstIso (A : Type u) :
    π₀ ((SimplicialObject.const (Type u)).obj A) ≅ A :=
  Equiv.toIso (piZeroConstEquiv A)

theorem adjunction_counit (A : Type u) :
    adjunction.counit.app A = (piZeroConstIso A).hom := rfl

instance adjunction_counit_isIso : IsIso adjunction.{u}.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  rw [adjunction_counit]
  exact (piZeroConstIso A).isIso_hom

/-- Full faithfulness is derived from the actual quotient counit Iso. -/
def constantFullyFaithful : (SimplicialObject.const (Type u)).FullyFaithful :=
  adjunction.fullyFaithfulROfIsIsoCounit

end SSet.PiZeroConstantAdjunction
