/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalCellOperatorGeometry
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteFaceIncidenceGeometry
import Lean.Elab.Tactic.Omega

/-!
# Proper simplex faces in the preceding diagonal skeleton

Each nonempty simplex face is isomorphic to the standard simplex of dimension its vertex count minus one. Proper faces in degree n + 1 give natural coefficient-tensored maps into the nth diagonal skeleton, with their prescribed inclusion equations. Sharp row maps, weak relative comparisons for every simplex operator, and the nth stage invariant make the resulting comparison maps weak equivalences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkProperFaceCell
open SharpComparisonDraft RezkCompatiblePushout RezkSkeletalCell

/-- A nonempty actual vertex face is represented by its original ordered
vertex set, with both native representability Iso legs. -/
def faceIso {N : ℕ} (S : Finset (Fin (N + 1))) (hne : S.Nonempty) :
    Δ[S.card - 1] ≅ (stdSimplex.face S : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy S (S.card - 1)
      (S.orderIsoOfFin (Nat.sub_add_cancel (Finset.card_pos.mpr hne)).symm))

/-- The original ordinal inclusion, without chosen image or coherence input. -/
def faceOrdinal {N : ℕ} (S : Finset (Fin (N + 1))) (hne : S.Nonempty) :
    ⦋S.card - 1⦌ ⟶ ⦋N⦌ :=
  SimplexCategory.Hom.mk
    (S.orderEmbOfFin (Nat.sub_add_cancel (Finset.card_pos.mpr hne)).symm).toOrderHom

@[reassoc]
theorem faceIso_hom_ι {N : ℕ} (S : Finset (Fin (N + 1))) (hne : S.Nonempty) :
    (faceIso S hne).hom ≫ (stdSimplex.face S).ι = SSet.stdSimplex.map (faceOrdinal S hne) := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- Every proper face is in the actual boundary, including empty faces. -/
theorem properFace_le_boundary {N : ℕ} (S : Finset (Fin (N + 1)))
    (proper : S ⊂ Finset.univ) : stdSimplex.face.{u} S ≤ boundary N := by
  classical
  have missing : ∃ i, i ∉ S := by
    by_contra no_missing
    have all : ∀ i, i ∈ S := by simpa only [not_exists, not_not] using no_missing
    have eq : S = Finset.univ := by ext i; simp [all i]
    exact proper.ne eq
  obtain ⟨i, hi⟩ := missing
  have subset : S ≤ ({i}ᶜ : Finset (Fin (N + 1))) := by
    intro v hv
    have ne : v ≠ i := by intro eq; subst v; exact hi hv
    simpa using ne
  have face_le : stdSimplex.face.{u} S ≤ stdSimplex.face {i}ᶜ := by
    intro a x hx
    exact hx.trans subset
  exact face_le.trans (face_singleton_compl_le_boundary i)

/-- The original proper face dimension is an old skeleton degree. -/
theorem properFace_degree_le (n : ℕ) (S : Finset (Fin (n + 2)))
    (proper : S ⊂ Finset.univ) : S.card - 1 ≤ n := by
  have lt := Finset.card_lt_card proper
  simp only [Finset.card_univ, Fintype.card_fin] at lt
  omega

/-- This face cell enters the old skeleton by its actual ordinal operator,
then the original old kth cell. No attachment or HC outcome is supplied. -/
def properFaceToOldStage (X : SimplicialObject SSet.{u}) (n : ℕ)
    (S : Finset (Fin (n + 2))) (proper : S ⊂ Finset.univ) (hne : S.Nonempty) :
    X.obj (op ⦋n + 1⦌) ⊗ (stdSimplex.face S : SSet.{u}) ⟶ diagonalFiltration X n :=
  (X.obj (op ⦋n + 1⦌) ◁ (faceIso S hne).inv) ≫
    (X.map (faceOrdinal S hne).op ▷ Δ[S.card - 1]) ≫
      cellToStage X (S.card - 1) n (properFace_degree_le n S proper)

/-- The projection into the full diagonal is the ORIGINAL coefficient face
cell, retaining its actual face inclusion and every inner simplex operator. -/
@[reassoc]
theorem properFaceToOldStage_ι (X : SimplicialObject SSet.{u}) (n : ℕ)
    (S : Finset (Fin (n + 2))) (proper : S ⊂ Finset.univ) (hne : S.Nonempty) :
    properFaceToOldStage X n S proper hne ≫ (diagonalFiltration X n).ι =
      (X.obj (op ⦋n + 1⦌) ◁ (stdSimplex.face S).ι) ≫ diagonalCellMap X (n + 1) := by
  have inverse : (faceIso.{u} S hne).inv ≫ SSet.stdSimplex.map (faceOrdinal S hne) =
      (stdSimplex.face S).ι := by
    rw [← faceIso_hom_ι, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  dsimp only [properFaceToOldStage]
  rw [Category.assoc, Category.assoc, cellToStage_ι]
  rw [diagonalCellMap_operator]
  simp only [← Category.assoc, ← whiskerLeft_comp]
  rw [inverse]

/-- Naturality is over the actual old finite-stage map. -/
@[reassoc]
theorem properFaceToOldStage_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (S : Finset (Fin (n + 2))) (proper : S ⊂ Finset.univ) (hne : S.Nonempty) :
    properFaceToOldStage X n S proper hne ≫ diagonalFiltrationNatMap eta n =
      (eta.app (op ⦋n + 1⦌) ▷ (stdSimplex.face S : SSet.{u})) ≫
        properFaceToOldStage Y n S proper hne := by
  apply (cancel_mono (diagonalFiltration Y n).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι, properFaceToOldStage_ι_assoc,
    properFaceToOldStage_ι]
  rw [← diagonalCellMap_naturality]
  simp only [tensorHom_id]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ diagonalCellMap Y (n + 1))
      (whisker_exchange (eta.app (op ⦋n + 1⦌)) (stdSimplex.face S).ι)

/-- A nonempty face's incoming HC is DERIVED from the previous all-cell
invariant and the original ALL operator comparisons, via both face Iso legs. -/
theorem properFaceToOldStage_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (S : Finset (Fin (n + 2))) (proper : S ⊂ Finset.univ) (hne : S.Nonempty)
    (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (properFaceToOldStage X n S proper hne)
        (eta.app (op ⦋n + 1⦌) ▷ (stdSimplex.face S : SSet.{u}))
        (properFaceToOldStage_naturality eta n S proper hne) ≫
        comparison (diagonalFiltrationNatMap eta n) (properFaceToOldStage Y n S proper hne)) := by
  let theta := faceOrdinal S hne
  let k := S.card - 1
  have hk : k ≤ n := properFace_degree_le n S proper
  have operatorHC := operator_cell_incoming_from_actual_stage_invariant
    eta hrows hoperators theta hk previous
  let faceSquare : CommSq (properFaceToOldStage X n S proper hne)
      (eta.app (op ⦋n + 1⦌) ▷ (stdSimplex.face S : SSet.{u}))
      (diagonalFiltrationNatMap eta n) (properFaceToOldStage Y n S proper hne) :=
    CommSq.mk (properFaceToOldStage_naturality eta n S proper hne)
  let fx := (X.map theta.op ▷ Δ[k]) ≫ cellToStage X k n hk
  let fy := (Y.map theta.op ▷ Δ[k]) ≫ cellToStage Y k n hk
  let operatorSquare : CommSq fx (eta.app (op ⦋n + 1⦌) ▷ Δ[k])
      (diagonalFiltrationNatMap eta n) fy := CommSq.mk (by
    dsimp only [fx, fy]
    rw [Category.assoc, cellToStage_naturality]
    simp only [← Category.assoc, ← comp_whiskerRight]
    rw [eta.naturality theta.op])
  exact (hc_weakSquare_iff faceSquare operatorSquare
    (X.obj (op ⦋n + 1⦌) ◁ (faceIso S hne).inv) (𝟙 _)
    (Y.obj (op ⦋n + 1⦌) ◁ (faceIso S hne).inv) (𝟙 _)
    (by simp [fx, properFaceToOldStage, theta, k])
    (whisker_exchange (eta.app (op ⦋n + 1⦌)) (faceIso S hne).inv)
    (by simp) (by simp [fy, properFaceToOldStage, theta, k])
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr operatorHC

end SSet.RezkProperFaceCell
