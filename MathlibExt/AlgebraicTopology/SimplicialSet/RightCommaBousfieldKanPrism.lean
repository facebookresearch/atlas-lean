/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanHomotopy

/-!
# Degreewise prism for the right-comma Bousfield--Kan comparison

An outer chain `d₀ ⟶ ⋯ ⟶ dₙ` and an inner chain in
`CostructuredArrow F d₀` determine two `Fin (n+1)`-diagrams in `D`: the
inner chain projected through `F`, and the outer chain itself.  The comma
arrows followed by the outer composites `d₀ ⟶ dᵢ` form a natural
transformation between them.  Its nerve cylinder gives the degreewise splice
used by the future mixed diagonal prism.

This file stops at one weighted summand and its two endpoint formulas.  It
makes no global simplicial homotopy, realization, weak-equivalence,
homotopy-fiber, or Quillen-Theorem-A claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial CategoryTheory.Prod

namespace SSet

universe u v w hIndex

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

attribute [local instance] uliftCategory

/-- The canonical map from the left endpoint of a composable-arrow chain to
each of its objects. -/
def outerChainFromLeftNatTrans
    {D : Type u} [Category.{hIndex} D] {n : ℕ} (s : ComposableArrows D n) :
    (Functor.const (Fin (n + 1))).obj s.left ⟶ s where
  app i := s.map' 0 i.val
  naturality i j f := by
    have hOuter : s.map' 0 j.val = s.map' 0 i.val ≫ s.map f := by
      calc
        s.map' 0 j.val = s.map' 0 i.val ≫
            s.map' i.val j.val (leOfHom f)
              (Nat.le_of_lt_succ j.isLt) :=
          s.map'_comp 0 i.val j.val (Nat.zero_le _)
            (leOfHom f) (Nat.le_of_lt_succ j.isLt)
        _ = s.map' 0 i.val ≫ s.map f :=
          congrArg (s.map' 0 i.val ≫ ·)
            (congrArg s.map (Subsingleton.elim _ _))
    change 𝟙 s.left ≫ s.map' 0 j.val = s.map' 0 i.val ≫ s.map f
    rw [Category.id_comp]
    exact hOuter

@[simp]
theorem outerChainFromLeftNatTrans_app
    {D : Type u} [Category.{hIndex} D] {n : ℕ}
    (s : ComposableArrows D n) (i : Fin (n + 1)) :
    (outerChainFromLeftNatTrans s).app i = s.map' 0 i.val :=
  rfl

/-- The comma/outer-chain bridge from the projected inner chain to the outer
chain.  Its component is `F(cᵢ) ⟶ d₀ ⟶ dᵢ`. -/
def rightCommaChainBridge (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n) :
    X ⋙ (rightCommaProjectionFunctor F s.left ⋙ F) ⟶ s := by
  change Fin (n + 1) ⥤ CostructuredArrow F s.left at X
  refine
    { app := fun i => (X.obj i).hom ≫ s.map' 0 i.val
      naturality := ?_ }
  intro i j f
  have hComma : F.map (X.map f).left ≫ (X.obj j).hom = (X.obj i).hom :=
    CostructuredArrow.w (X.map f)
  have hOuter : s.map' 0 j.val = s.map' 0 i.val ≫ s.map f := by
    calc
      s.map' 0 j.val = s.map' 0 i.val ≫
          s.map' i.val j.val (leOfHom f)
            (Nat.le_of_lt_succ j.isLt) :=
        s.map'_comp 0 i.val j.val (Nat.zero_le _)
          (leOfHom f) (Nat.le_of_lt_succ j.isLt)
      _ = s.map' 0 i.val ≫ s.map f :=
        congrArg (s.map' 0 i.val ≫ ·)
          (congrArg s.map (Subsingleton.elim _ _))
  calc
    F.map (X.map f).left ≫ ((X.obj j).hom ≫ s.map' 0 j.val) =
        (F.map (X.map f).left ≫ (X.obj j).hom) ≫
          s.map' 0 j.val := (Category.assoc _ _ _).symm
    _ = (X.obj i).hom ≫ s.map' 0 j.val :=
      congrArg (· ≫ s.map' 0 j.val) hComma
    _ = (X.obj i).hom ≫ (s.map' 0 i.val ≫ s.map f) :=
      congrArg ((X.obj i).hom ≫ ·) hOuter
    _ = ((X.obj i).hom ≫ s.map' 0 i.val) ≫ s.map f :=
      (Category.assoc _ _ _).symm

@[simp]
theorem rightCommaChainBridge_app (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (i : Fin (n + 1)) :
    (rightCommaChainBridge F s X).app i =
      (X.obj i).hom ≫ s.map' 0 i.val :=
  rfl

/-- The finite chain index, viewed in the ambient object universe. -/
abbrev rightCommaPrismIndex (n : ℕ) : Type u :=
  ULift.{u} (Fin (n + 1))

/-- The identity chain on the finite prism index, with its codomain lifted to
the ambient object universe. -/
def rightCommaPrismIndexSimplex (n : ℕ) :
    ComposableArrows (rightCommaPrismIndex.{u} n) n where
  obj i := ULift.up i
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Reinterpret a composable chain as a functor whose source type lies in the
ambient object universe. -/
def rightCommaPrismLiftChain {E : Type u} [Category.{v} E] {n : ℕ}
    (s : ComposableArrows E n) : rightCommaPrismIndex.{max u v} n ⥤ E where
  obj i := s.obj i.down
  map f := s.map f
  map_id i := s.map_id i.down
  map_comp f g := s.map_comp f g

/-- Mapping the original finite index chain recovers every original composable arrow. -/
@[simp]
theorem nerveMap_rightCommaPrismLiftChain_indexSimplex
    {E : Type u} [Category.{v} E] {n : ℕ}
    (s : ComposableArrows E n) :
    ((rightCommaPrismLiftChain s).mapComposableArrows n).obj
        (rightCommaPrismIndexSimplex.{max u v} n) = s := by
  rfl

/-- The comma-chain bridge with both category object types in the ambient
universe, as required by the nerve-homotopy constructor. -/
def rightCommaChainBridgeLift (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n) :
    rightCommaPrismLiftChain
        (X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F)) ⟶
      rightCommaPrismLiftChain s where
  app i := (rightCommaChainBridge F s X).app i.down
  naturality _ _ f := (rightCommaChainBridge F s X).naturality f

@[simp]
theorem rightCommaChainBridgeLift_app (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (i : rightCommaPrismIndex.{max u v w} n) :
    (rightCommaChainBridgeLift F s X).app i =
      (X.obj i.down).hom ≫ s.map' 0 i.down.val :=
  rfl

/-- The all-zero interval simplex used by the degreewise prism. -/
def rightCommaPrismZero (n : ℕ) :
    (Δ[1] : SSet.{u}).obj (op ⦋n⦌) :=
  let I : (nerve (rightCommaPrismIndex.{u} n)).obj (op ⦋n⦌) :=
    rightCommaPrismIndexSimplex n
  (SSet.ι₀.app (op ⦋n⦌) I).2

/-- The all-one interval simplex used by the degreewise prism. -/
def rightCommaPrismOne (n : ℕ) :
    (Δ[1] : SSet.{u}).obj (op ⦋n⦌) :=
  let I : (nerve (rightCommaPrismIndex.{u} n)).obj (op ⦋n⦌) :=
    rightCommaPrismIndexSimplex n
  (SSet.ι₁.app (op ⦋n⦌) I).2

/-- Degreewise comma/outer-chain splice at an arbitrary interval simplex. -/
def rightCommaPrismSimplex (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    (nerve D).obj (op ⦋n⦌) :=
  ((CategoryTheory.NatTrans.nerveCylinderFunctor
      (rightCommaChainBridgeLift F s X)).mapComposableArrows n).obj
    ((rightCommaPrismIndexSimplex.{max u v w} n).prod'
      (SSet.stdSimplex.asOrderHom t).toFunctor)

/-- At the all-zero interval simplex, the prism is the nerve of the projected
inner chain. -/
theorem rightCommaPrismSimplex_zero (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n) :
    rightCommaPrismSimplex F s X (rightCommaPrismZero.{max u v w} n) =
      X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F) := by
  let α := rightCommaChainBridgeLift F s X
  let I := rightCommaPrismIndexSimplex.{max u v w} n
  have hTime : (SSet.stdSimplex.asOrderHom
      (rightCommaPrismZero.{max u v w} n)).toFunctor =
      (Functor.const (Fin (n + 1))).obj (0 : Fin 2) := rfl
  have hEnd :
      ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj
        (I.prod' ((Functor.const (Fin (n + 1))).obj (0 : Fin 2))) =
      ((rightCommaPrismLiftChain
        (X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F))).mapComposableArrows n).obj
          I := by
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      change HEq
        ((CategoryTheory.NatTrans.nerveCylinderFunctor α).map (I.map f ×ₘ 𝟙 (0 : Fin 2)))
        ((rightCommaPrismLiftChain
          (X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F))).map (I.map f))
      exact heq_of_eq (CategoryTheory.NatTrans.nerveCylinderFunctor_map_zero α (I.map f))
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj
      (I.prod' (SSet.stdSimplex.asOrderHom (rightCommaPrismZero.{max u v w} n)).toFunctor) = _
  rw [hTime]
  exact hEnd.trans (nerveMap_rightCommaPrismLiftChain_indexSimplex
    (X ⋙ (rightCommaProjectionFunctor.{u, v, w} F s.left ⋙ F)))

/-- At the all-one interval simplex, the prism is the outer indexing chain. -/
theorem rightCommaPrismSimplex_one (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n) :
    rightCommaPrismSimplex F s X (rightCommaPrismOne.{max u v w} n) = s := by
  let α := rightCommaChainBridgeLift F s X
  let I := rightCommaPrismIndexSimplex.{max u v w} n
  have hTime : (SSet.stdSimplex.asOrderHom
      (rightCommaPrismOne.{max u v w} n)).toFunctor =
      (Functor.const (Fin (n + 1))).obj (1 : Fin 2) := rfl
  have hEnd :
      ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj
        (I.prod' ((Functor.const (Fin (n + 1))).obj (1 : Fin 2))) =
      ((rightCommaPrismLiftChain s).mapComposableArrows n).obj I := by
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      change HEq
        ((CategoryTheory.NatTrans.nerveCylinderFunctor α).map (I.map f ×ₘ 𝟙 (1 : Fin 2)))
        ((rightCommaPrismLiftChain s).map (I.map f))
      exact heq_of_eq (CategoryTheory.NatTrans.nerveCylinderFunctor_map_one α (I.map f))
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj
      (I.prod' (SSet.stdSimplex.asOrderHom (rightCommaPrismOne.{max u v w} n)).toFunctor) = _
  rw [hTime]
  exact hEnd.trans (nerveMap_rightCommaPrismLiftChain_indexSimplex s)

end SSet

end
