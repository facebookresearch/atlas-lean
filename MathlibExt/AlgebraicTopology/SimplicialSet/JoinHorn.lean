/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Join
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftIso

/-!
# Boundary--positive-horn pushout joins

For p,q ≥ 0, the two standard pushout joins are the shifted horns
\[
  (∂Δ^p ⋆ Δ^{q+1}) ∪ (Δ^p ⋆ Λ^{q+1}_j)
    ≅ Λ^{p+q+2}_{p+1+j}
\]
and
\[
  (Δ^{p+1} ⋆ ∂Δ^q) ∪ (Λ^{p+1}_i ⋆ Δ^q)
    ≅ Λ^{p+q+2}_i.
\]
The horn dimension is positive in both formulas. No zero-dimensional horn
case is asserted; the degenerate cases handled here are the zero-dimensional
boundary factors `∂Δ[0]`.
This is Joyal's Lemma 3.11(ii--iii), equivalently Kerodon Lemma 4.3.6.16
(Tag 018N).

The public API consists of the shifted indices, chosen pushout corners, the
four maps from their pieces to the shifted horns, point and Arrow
isomorphisms, strict coprojection equations, final-inclusion equations, and
monomorphism instances for the chosen corner maps. Face arithmetic and the
zero/successor constructions live under SSet.JoinHorn.Internal.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-!
## Canonical indices and corners
-/

/-- The right horn index shifted past the p+1 vertices of the left simplex. -/
def rightJoinHornIndex (p q : ℕ) (j : Fin (q + 2)) :
    Fin ((p + (q + 1) + 1) + 1) :=
  JoinHorn.Internal.rightJoinHornIndex p q j

/-- The left horn index viewed in the joined simplex. -/
def leftJoinHornIndex (p q : ℕ) (i : Fin (p + 2)) :
    Fin (((p + 1) + q + 1) + 1) :=
  JoinHorn.Internal.leftJoinHornIndex p q i

@[simp]
theorem rightJoinHornIndex_val (p q : ℕ) (j : Fin (q + 2)) :
    (rightJoinHornIndex p q j).val = p + 1 + j.val :=
  rfl

@[simp]
theorem leftJoinHornIndex_val (p q : ℕ) (i : Fin (p + 2)) :
    (leftJoinHornIndex p q i).val = i.val :=
  rfl

/-- The chosen pushout corner for the right-oriented decomposition. -/
noncomputable def joinBoundaryHornRightPushoutObjObj (p q : ℕ)
    (j : Fin (q + 2)) :
    join.{u}.PushoutObjObj (boundary.{u} p).ι (horn.{u} (q + 1) j).ι :=
  JoinHorn.Internal.joinBoundaryHornRightPushoutObjObj p q j

/-- The chosen pushout corner for the left-oriented decomposition. -/
noncomputable def joinHornBoundaryLeftPushoutObjObj (p q : ℕ)
    (i : Fin (p + 2)) :
    join.{u}.PushoutObjObj (horn.{u} (p + 1) i).ι (boundary.{u} q).ι :=
  JoinHorn.Internal.joinHornBoundaryLeftPushoutObjObj p q i

namespace JoinHorn.Internal

/-- Opaque assembly of the right-oriented public data from the internal proof. -/
structure RightPublicData (p q : ℕ) (j : Fin (q + 2)) where
  /-- The map from the horn piece. -/
  factorMap :
    (Δ[p] : SSet.{u}) ⋆ (horn (q + 1) j : SSet.{u}) ⟶
      (horn (p + (q + 1) + 1) (SSet.rightJoinHornIndex p q j) : SSet.{u})
  /-- The map from the boundary piece. -/
  boundaryFactorMap :
    (boundary p : SSet.{u}) ⋆ (Δ[q + 1] : SSet.{u}) ⟶
      (horn (p + (q + 1) + 1) (SSet.rightJoinHornIndex p q j) : SSet.{u})
  /-- The induced isomorphism on the pushout point. -/
  pointIso :
    (SSet.joinBoundaryHornRightPushoutObjObj.{u} p q j).pt ≅
      (horn (p + (q + 1) + 1) (SSet.rightJoinHornIndex p q j) : SSet.{u})
  factorMap_ι : factorMap ≫
      (horn (p + (q + 1) + 1) (SSet.rightJoinHornIndex p q j)).ι =
    (join.obj (Δ[p] : SSet.{u})).map (horn (q + 1) j).ι ≫
      (joinStdSimplexIso p (q + 1)).hom
  boundaryFactorMap_ι : boundaryFactorMap ≫
      (horn (p + (q + 1) + 1) (SSet.rightJoinHornIndex p q j)).ι =
    (join.map (boundary p).ι).app (Δ[q + 1] : SSet.{u}) ≫
      (joinStdSimplexIso p (q + 1)).hom
  pointIso_hom_inl :
    (SSet.joinBoundaryHornRightPushoutObjObj.{u} p q j).inl ≫ pointIso.hom =
      factorMap
  pointIso_hom_inr :
    (SSet.joinBoundaryHornRightPushoutObjObj.{u} p q j).inr ≫ pointIso.hom =
      boundaryFactorMap
  pointIso_hom_ι : pointIso.hom ≫
      (horn (p + (q + 1) + 1) (SSet.rightJoinHornIndex p q j)).ι =
    (SSet.joinBoundaryHornRightPushoutObjObj p q j).ι ≫
      (joinStdSimplexIso p (q + 1)).hom

/-- Opaque assembly of the left-oriented public data from the internal proof. -/
structure LeftPublicData (p q : ℕ) (i : Fin (p + 2)) where
  /-- The map from the horn piece. -/
  hornFactorMap :
    (horn (p + 1) i : SSet.{u}) ⋆ (Δ[q] : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (SSet.leftJoinHornIndex p q i) : SSet.{u})
  /-- The map from the boundary piece. -/
  boundaryFactorMap :
    (Δ[p + 1] : SSet.{u}) ⋆ (boundary q : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (SSet.leftJoinHornIndex p q i) : SSet.{u})
  /-- The induced isomorphism on the pushout point. -/
  pointIso :
    (SSet.joinHornBoundaryLeftPushoutObjObj.{u} p q i).pt ≅
      (horn ((p + 1) + q + 1) (SSet.leftJoinHornIndex p q i) : SSet.{u})
  hornFactorMap_ι : hornFactorMap ≫
      (horn ((p + 1) + q + 1) (SSet.leftJoinHornIndex p q i)).ι =
    (join.map (horn (p + 1) i).ι).app (Δ[q] : SSet.{u}) ≫
      (joinStdSimplexIso (p + 1) q).hom
  boundaryFactorMap_ι : boundaryFactorMap ≫
      (horn ((p + 1) + q + 1) (SSet.leftJoinHornIndex p q i)).ι =
    (join.obj (Δ[p + 1] : SSet.{u})).map (boundary q).ι ≫
      (joinStdSimplexIso (p + 1) q).hom
  pointIso_hom_inl :
    (SSet.joinHornBoundaryLeftPushoutObjObj.{u} p q i).inl ≫ pointIso.hom =
      boundaryFactorMap
  pointIso_hom_inr :
    (SSet.joinHornBoundaryLeftPushoutObjObj.{u} p q i).inr ≫ pointIso.hom =
      hornFactorMap
  pointIso_hom_ι : pointIso.hom ≫
      (horn ((p + 1) + q + 1) (SSet.leftJoinHornIndex p q i)).ι =
    (SSet.joinHornBoundaryLeftPushoutObjObj p q i).ι ≫
      (joinStdSimplexIso (p + 1) q).hom

/-- The internally constructed right-oriented data, sealed behind the public API. -/
noncomputable opaque rightPublicData (p q : ℕ) (j : Fin (q + 2)) :
    RightPublicData.{u} p q j := by
  refine
    { factorMap := joinBoundaryHornRightFactorMap p q j
      boundaryFactorMap := joinBoundaryHornRightBoundaryFactorMap p q j
      pointIso := joinBoundaryHornRightPointIso p q j
      factorMap_ι := ?_
      boundaryFactorMap_ι := ?_
      pointIso_hom_inl := ?_
      pointIso_hom_inr := ?_
      pointIso_hom_ι := ?_ }
  · exact joinBoundaryHornRightFactorMap_ι p q j
  · exact joinBoundaryHornRightBoundaryFactorMap_ι p q j
  · exact joinBoundaryHornRightPointIso_hom_inl p q j
  · exact joinBoundaryHornRightPointIso_hom_inr p q j
  · exact joinBoundaryHornRightPointIso_hom_ι p q j

/-- The internally constructed left-oriented data, sealed behind the public API. -/
noncomputable opaque leftPublicData (p q : ℕ) (i : Fin (p + 2)) :
    LeftPublicData.{u} p q i := by
  refine
    { hornFactorMap := joinHornBoundaryLeftHornFactorMap p q i
      boundaryFactorMap := joinHornBoundaryLeftBoundaryFactorMap p q i
      pointIso := joinHornBoundaryLeftPointIso p q i
      hornFactorMap_ι := ?_
      boundaryFactorMap_ι := ?_
      pointIso_hom_inl := ?_
      pointIso_hom_inr := ?_
      pointIso_hom_ι := ?_ }
  · exact joinHornBoundaryLeftHornFactorMap_ι p q i
  · exact joinHornBoundaryLeftBoundaryFactorMap_ι p q i
  · exact joinHornBoundaryLeftPointIso_hom_inl p q i
  · exact joinHornBoundaryLeftPointIso_hom_inr p q i
  · exact joinHornBoundaryLeftPointIso_hom_ι p q i

end JoinHorn.Internal

/-!
## Canonical maps from the four pieces
-/

/-- The map from the right horn piece to the shifted horn. -/
noncomputable def joinBoundaryHornRightFactorMap (p q : ℕ)
    (j : Fin (q + 2)) :
    (Δ[p] : SSet.{u}) ⋆ (horn (q + 1) j : SSet.{u}) ⟶
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  (JoinHorn.Internal.rightPublicData p q j).factorMap

/-- The map from the right boundary piece to the shifted horn. -/
noncomputable def joinBoundaryHornRightBoundaryFactorMap (p q : ℕ)
    (j : Fin (q + 2)) :
    (boundary p : SSet.{u}) ⋆ (Δ[q + 1] : SSet.{u}) ⟶
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  (JoinHorn.Internal.rightPublicData p q j).boundaryFactorMap

/-- The map from the left horn piece to the shifted horn. -/
noncomputable def joinHornBoundaryLeftHornFactorMap (p q : ℕ)
    (i : Fin (p + 2)) :
    (horn (p + 1) i : SSet.{u}) ⋆ (Δ[q] : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  (JoinHorn.Internal.leftPublicData p q i).hornFactorMap

/-- The map from the left boundary piece to the shifted horn. -/
noncomputable def joinHornBoundaryLeftBoundaryFactorMap (p q : ℕ)
    (i : Fin (p + 2)) :
    (Δ[p + 1] : SSet.{u}) ⋆ (boundary q : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  (JoinHorn.Internal.leftPublicData p q i).boundaryFactorMap

@[reassoc]
theorem joinBoundaryHornRightFactorMap_ι (p q : ℕ)
    (j : Fin (q + 2)) :
    joinBoundaryHornRightFactorMap.{u} p q j ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (join.obj (Δ[p] : SSet.{u})).map (horn (q + 1) j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  exact (JoinHorn.Internal.rightPublicData p q j).factorMap_ι

@[reassoc]
theorem joinBoundaryHornRightBoundaryFactorMap_ι (p q : ℕ)
    (j : Fin (q + 2)) :
    joinBoundaryHornRightBoundaryFactorMap.{u} p q j ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (join.map (boundary p).ι).app (Δ[q + 1] : SSet.{u}) ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  exact (JoinHorn.Internal.rightPublicData p q j).boundaryFactorMap_ι

@[reassoc]
theorem joinHornBoundaryLeftHornFactorMap_ι (p q : ℕ)
    (i : Fin (p + 2)) :
    joinHornBoundaryLeftHornFactorMap.{u} p q i ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (join.map (horn (p + 1) i).ι).app (Δ[q] : SSet.{u}) ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  exact (JoinHorn.Internal.leftPublicData p q i).hornFactorMap_ι

@[reassoc]
theorem joinHornBoundaryLeftBoundaryFactorMap_ι (p q : ℕ)
    (i : Fin (p + 2)) :
    joinHornBoundaryLeftBoundaryFactorMap.{u} p q i ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (join.obj (Δ[p + 1] : SSet.{u})).map (boundary q).ι ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  exact (JoinHorn.Internal.leftPublicData p q i).boundaryFactorMap_ι

/-!
## Point and Arrow identifications
-/

/-- The right-oriented boundary--horn corner is the shifted horn. -/
noncomputable def joinBoundaryHornRightPointIso (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).pt ≅
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  (JoinHorn.Internal.rightPublicData p q j).pointIso

/-- The left-oriented horn--boundary corner is the shifted horn. -/
noncomputable def joinHornBoundaryLeftPointIso (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).pt ≅
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  (JoinHorn.Internal.leftPublicData p q i).pointIso

/-- The right point isomorphism restricts to the horn piece strictly. -/
@[reassoc]
theorem joinBoundaryHornRightPointIso_hom_inl (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inl ≫
        (joinBoundaryHornRightPointIso p q j).hom =
      joinBoundaryHornRightFactorMap p q j := by
  exact (JoinHorn.Internal.rightPublicData p q j).pointIso_hom_inl

/-- The right point isomorphism restricts to the boundary piece strictly. -/
@[reassoc]
theorem joinBoundaryHornRightPointIso_hom_inr (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inr ≫
        (joinBoundaryHornRightPointIso p q j).hom =
      joinBoundaryHornRightBoundaryFactorMap p q j := by
  exact (JoinHorn.Internal.rightPublicData p q j).pointIso_hom_inr

/-- The left point isomorphism restricts to the boundary piece strictly. -/
@[reassoc]
theorem joinHornBoundaryLeftPointIso_hom_inl (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inl ≫
        (joinHornBoundaryLeftPointIso p q i).hom =
      joinHornBoundaryLeftBoundaryFactorMap p q i := by
  exact (JoinHorn.Internal.leftPublicData p q i).pointIso_hom_inl

/-- The left point isomorphism restricts to the horn piece strictly. -/
@[reassoc]
theorem joinHornBoundaryLeftPointIso_hom_inr (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inr ≫
        (joinHornBoundaryLeftPointIso p q i).hom =
      joinHornBoundaryLeftHornFactorMap p q i := by
  exact (JoinHorn.Internal.leftPublicData p q i).pointIso_hom_inr

@[reassoc]
theorem joinBoundaryHornRightPointIso_hom_ι (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPointIso.{u} p q j).hom ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (joinBoundaryHornRightPushoutObjObj p q j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  exact (JoinHorn.Internal.rightPublicData p q j).pointIso_hom_ι

@[reassoc]
theorem joinHornBoundaryLeftPointIso_hom_ι (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPointIso.{u} p q i).hom ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p q i).ι ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  exact (JoinHorn.Internal.leftPublicData p q i).pointIso_hom_ι

/-- Joining a boundary on the left with a positive-dimensional horn on the
right gives the shifted horn. -/
noncomputable def joinBoundaryHornRightArrowIso (p q : ℕ) (j : Fin (q + 2)) :
    Arrow.mk (joinBoundaryHornRightPushoutObjObj.{u} p q j).ι ≅
      Arrow.mk (horn (p + (q + 1) + 1)
        (rightJoinHornIndex p q j)).ι :=
  Arrow.isoMk (joinBoundaryHornRightPointIso p q j)
    (joinStdSimplexIso p (q + 1))
    (joinBoundaryHornRightPointIso_hom_ι p q j)

/-- Joining a positive-dimensional horn on the left with a boundary on the
right gives the shifted horn. -/
noncomputable def joinHornBoundaryLeftArrowIso (p q : ℕ) (i : Fin (p + 2)) :
    Arrow.mk (joinHornBoundaryLeftPushoutObjObj.{u} p q i).ι ≅
      Arrow.mk (horn ((p + 1) + q + 1)
        (leftJoinHornIndex p q i)).ι :=
  Arrow.isoMk (joinHornBoundaryLeftPointIso p q i)
    (joinStdSimplexIso (p + 1) q)
    (joinHornBoundaryLeftPointIso_hom_ι p q i)

@[simp]
theorem joinBoundaryHornRightArrowIso_hom_right (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightArrowIso.{u} p q j).hom.right =
      (joinStdSimplexIso p (q + 1)).hom :=
  rfl

@[simp]
theorem joinHornBoundaryLeftArrowIso_hom_right (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftArrowIso.{u} p q i).hom.right =
      (joinStdSimplexIso (p + 1) q).hom :=
  rfl

/-- The right Arrow isomorphism retains its horn coprojection strictly. -/
@[reassoc]
theorem joinBoundaryHornRightArrowIso_hom_inl (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inl ≫
        (joinBoundaryHornRightArrowIso p q j).hom.left =
      joinBoundaryHornRightFactorMap p q j :=
  joinBoundaryHornRightPointIso_hom_inl p q j

/-- The right Arrow isomorphism retains its boundary coprojection strictly. -/
@[reassoc]
theorem joinBoundaryHornRightArrowIso_hom_inr (p q : ℕ)
    (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).inr ≫
        (joinBoundaryHornRightArrowIso p q j).hom.left =
      joinBoundaryHornRightBoundaryFactorMap p q j :=
  joinBoundaryHornRightPointIso_hom_inr p q j

/-- The left Arrow isomorphism retains its boundary coprojection strictly. -/
@[reassoc]
theorem joinHornBoundaryLeftArrowIso_hom_inl (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inl ≫
        (joinHornBoundaryLeftArrowIso p q i).hom.left =
      joinHornBoundaryLeftBoundaryFactorMap p q i :=
  joinHornBoundaryLeftPointIso_hom_inl p q i

/-- The left Arrow isomorphism retains its horn coprojection strictly. -/
@[reassoc]
theorem joinHornBoundaryLeftArrowIso_hom_inr (p q : ℕ)
    (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).inr ≫
        (joinHornBoundaryLeftArrowIso p q i).hom.left =
      joinHornBoundaryLeftHornFactorMap p q i :=
  joinHornBoundaryLeftPointIso_hom_inr p q i

/-- The right Arrow isomorphism retains the full final inclusion. -/
@[reassoc]
theorem joinBoundaryHornRightArrowIso_hom_w (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightArrowIso.{u} p q j).hom.left ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (joinBoundaryHornRightPushoutObjObj p q j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom :=
  joinBoundaryHornRightPointIso_hom_ι p q j

/-- The left Arrow isomorphism retains the full final inclusion. -/
@[reassoc]
theorem joinHornBoundaryLeftArrowIso_hom_w (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftArrowIso.{u} p q i).hom.left ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p q i).ι ≫
        (joinStdSimplexIso (p + 1) q).hom :=
  joinHornBoundaryLeftPointIso_hom_ι p q i

/-- The chosen right boundary--horn corner map is a monomorphism. -/
instance joinBoundaryHornRightPushoutObjObj_ι_mono (p q : ℕ)
    (j : Fin (q + 2)) :
    Mono (joinBoundaryHornRightPushoutObjObj.{u} p q j).ι := by
  let _ : Mono ((joinBoundaryHornRightPushoutObjObj.{u} p q j).ι ≫
      (joinStdSimplexIso p (q + 1)).hom) := by
    rw [← joinBoundaryHornRightPointIso_hom_ι]
    infer_instance
  exact mono_of_mono_fac (rfl :
    (joinBoundaryHornRightPushoutObjObj.{u} p q j).ι ≫
      (joinStdSimplexIso p (q + 1)).hom = _)

/-- The chosen left horn--boundary corner map is a monomorphism. -/
instance joinHornBoundaryLeftPushoutObjObj_ι_mono (p q : ℕ)
    (i : Fin (p + 2)) :
    Mono (joinHornBoundaryLeftPushoutObjObj.{u} p q i).ι := by
  let _ : Mono ((joinHornBoundaryLeftPushoutObjObj.{u} p q i).ι ≫
      (joinStdSimplexIso (p + 1) q).hom) := by
    rw [← joinHornBoundaryLeftPointIso_hom_ι]
    infer_instance
  exact mono_of_mono_fac (rfl :
    (joinHornBoundaryLeftPushoutObjObj.{u} p q i).ι ≫
      (joinStdSimplexIso (p + 1) q).hom = _)

end SSet
