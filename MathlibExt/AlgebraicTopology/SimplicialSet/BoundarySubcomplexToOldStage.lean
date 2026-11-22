/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ProperFaceCellGeometry
import MathlibExt.AlgebraicTopology.SimplicialSet.EmptyFaceTensorPullback

/-!
# Boundary subcomplex maps into diagonal skeleta

Every subcomplex of the degree n + 1 simplex boundary determines a coefficient-tensored map into the nth diagonal skeleton, naturally in the diagram and compatibly with subcomplex inclusions. The preceding stage invariant gives a weak comparison for the empty subcomplex; sharp rows and weak relative comparisons for all simplex operators extend this conclusion to every proper face.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkBoundaryOldStage
open SharpComparisonDraft RezkSkeletalCell RezkProperFaceCell

/-- A literal boundary subcomplex of the original row cell enters the
preceding skeleton through the actual native attachment domain. -/
def toOldStage (X : SimplicialObject SSet.{u}) (n : ℕ)
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (hA : A ≤ boundary (n + 1)) :
    X.obj (op ⦋n + 1⦌) ⊗ A ⟶ diagonalFiltration X n :=
  (X.obj (op ⦋n + 1⦌) ◁ Subcomplex.homOfLE hA) ≫
    Subcomplex.unionProd.ι₁ (outerLatching X (n + 1)) (boundary (n + 1)) ≫
      diagonalAttachmentTopMap X n

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem toOldStage_ι (X : SimplicialObject SSet.{u}) (n : ℕ)
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (hA : A ≤ boundary (n + 1)) :
    toOldStage X n A hA ≫ (diagonalFiltration X n).ι =
      (X.obj (op ⦋n + 1⦌) ◁ A.ι) ≫ diagonalCellMap X (n + 1) := by
  dsimp only [toOldStage]
  rw [Category.assoc, Category.assoc, diagonalAttachmentTopMap_ι]
  dsimp only [diagonalAttachmentDomain]
  rw [Subcomplex.unionProd.ι₁_ι_assoc, ← Category.assoc, ← whiskerLeft_comp,
    Subcomplex.homOfLE_ι]

/-- Naturality over the ORIGINAL previous finite stage. -/
@[reassoc]
theorem toOldStage_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ)
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (hA : A ≤ boundary (n + 1)) :
    toOldStage X n A hA ≫ diagonalFiltrationNatMap eta n =
      (eta.app (op ⦋n + 1⦌) ▷ (A : SSet.{u})) ≫ toOldStage Y n A hA := by
  apply (cancel_mono (diagonalFiltration Y n).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι, toOldStage_ι_assoc, toOldStage_ι]
  calc
    (X.obj (op ⦋n + 1⦌) ◁ A.ι) ≫ (diagonalCellMap X (n + 1) ≫ simplicialDiagonalFunctor.map eta) =
        (X.obj (op ⦋n + 1⦌) ◁ A.ι) ≫
          ((eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1]) ≫ diagonalCellMap Y (n + 1)) := by
      rw [← diagonalCellMap_naturality, tensorHom_id]
    _ = (eta.app (op ⦋n + 1⦌) ▷ (A : SSet.{u})) ≫
        ((Y.obj (op ⦋n + 1⦌) ◁ A.ι) ≫ diagonalCellMap Y (n + 1)) := by
      rw [← Category.assoc, whisker_exchange, Category.assoc]

/-- All actual incidence maps commute with their old-stage maps. -/
@[reassoc]
theorem inclusion_toOldStage (X : SimplicialObject SSet.{u}) (n : ℕ)
    {A B : (Δ[n + 1] : SSet.{u}).Subcomplex} (hA : A ≤ boundary (n + 1))
    (hB : B ≤ boundary (n + 1)) (h : A ≤ B) :
    (X.obj (op ⦋n + 1⦌) ◁ Subcomplex.homOfLE h) ≫ toOldStage X n B hB =
      toOldStage X n A hA := by
  apply (cancel_mono (diagonalFiltration X n).ι).mp
  rw [Category.assoc, toOldStage_ι, toOldStage_ι, ← Category.assoc,
    ← whiskerLeft_comp, Subcomplex.homOfLE_ι]

/-- The actual proper-face restriction equals its original ordinal-cell
construction, so the proved operator HC applies to this SAME arrow. -/
theorem toOldStage_face_eq (X : SimplicialObject SSet.{u}) (n : ℕ)
    (S : Finset (Fin (n + 2))) (proper : S ⊂ Finset.univ) (hne : S.Nonempty) :
    toOldStage X n (stdSimplex.face S) (properFace_le_boundary S proper) =
      properFaceToOldStage X n S proper hne := by
  apply (cancel_mono (diagonalFiltration X n).ι).mp
  rw [toOldStage_ι, properFaceToOldStage_ι]

/-- Empty faces remain in the proof: their actual square is a strict
pullback because of its empty second coordinate. -/
theorem empty_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ)
    (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (toOldStage X n ⊥ bot_le)
          (eta.app (op ⦋n + 1⦌) ▷ (⊥ : (Δ[n + 1] : SSet.{u}).Subcomplex))
        (toOldStage_naturality eta n ⊥ bot_le) ≫
        comparison (diagonalFiltrationNatMap eta n) (toOldStage Y n ⊥ bot_le)) := by
  exact RezkEmptyFace.emptyTensor_hc (toOldStage X n ⊥ bot_le)
    (eta.app (op ⦋n + 1⦌) ▷ (⊥ : (Δ[n + 1] : SSet.{u}).Subcomplex))
    (diagonalFiltrationNatMap eta n) (toOldStage Y n ⊥ bot_le) previous.1

/-- EVERY proper face is HC to the old skeleton. Nonempty faces use the
actual ALL-operator cell law; empty faces use the strict initial square. -/
theorem face_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (S : Finset (Fin (n + 2))) (proper : S ⊂ Finset.univ)
    (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (toOldStage X n (stdSimplex.face S) (properFace_le_boundary S proper))
        (eta.app (op ⦋n + 1⦌) ▷ (stdSimplex.face S : SSet.{u}))
        (toOldStage_naturality eta n (stdSimplex.face S) (properFace_le_boundary S proper)) ≫
        comparison (diagonalFiltrationNatMap eta n)
          (toOldStage Y n (stdSimplex.face S) (properFace_le_boundary S proper))) := by
  classical
  by_cases hne : S.Nonempty
  · let oldSquare : CommSq
        (toOldStage X n (stdSimplex.face S) (properFace_le_boundary S proper))
        (eta.app (op ⦋n + 1⦌) ▷ (stdSimplex.face S : SSet.{u}))
        (diagonalFiltrationNatMap eta n)
        (toOldStage Y n (stdSimplex.face S) (properFace_le_boundary S proper)) :=
      CommSq.mk (toOldStage_naturality eta n _ _)
    let faceSquare : CommSq (properFaceToOldStage X n S proper hne)
        (eta.app (op ⦋n + 1⦌) ▷ (stdSimplex.face S : SSet.{u}))
        (diagonalFiltrationNatMap eta n) (properFaceToOldStage Y n S proper hne) :=
      CommSq.mk (properFaceToOldStage_naturality eta n S proper hne)
    exact (RezkCompatiblePushout.hc_weakSquare_iff oldSquare faceSquare
      (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id, Category.id_comp] using
        toOldStage_face_eq X n S proper hne)
      (by simp) (by simp)
      (by simpa only [Category.comp_id, Category.id_comp] using
        toOldStage_face_eq Y n S proper hne)
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr
        (properFaceToOldStage_hc eta hrows hoperators n S proper hne previous)
  · have empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    have aux (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (hA : A ≤ boundary (n + 1))
        (hbot : A = ⊥) :
        WeakEquivalence
          (pullback.lift (toOldStage X n A hA) (eta.app (op ⦋n + 1⦌) ▷ (A : SSet.{u}))
            (toOldStage_naturality eta n A hA) ≫
            comparison (diagonalFiltrationNatMap eta n) (toOldStage Y n A hA)) := by
      subst A
      exact empty_hc eta n previous
    exact aux _ _ (stdSimplex.face_empty (n + 1))

end SSet.RezkBoundaryOldStage
