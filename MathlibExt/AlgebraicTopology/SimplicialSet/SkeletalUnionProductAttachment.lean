/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FullLatchingFromFiniteStages
import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalProductBoundarySquare
import MathlibExt.AlgebraicTopology.SimplicialSet.UnionIncomingHC
import MathlibExt.AlgebraicTopology.SimplicialSet.IncomingHCPasting

/-!
# Pushout presentations of diagonal skeletal attachment domains

The boundary and latching pieces of a diagonal skeletal attachment form a natural union-product pushout presentation. The induced chosen-pushout map is isomorphic, as a complete arrow, to the attachment-domain map, with all four comparison legs recorded. Sharp row maps and weak relative comparisons for every simplex operator imply that this attachment-domain map is sharp.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalAttachment
open SharpComparisonDraft RezkCompatiblePushout RezkSkeletalProduct

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The boundary piece uses the actual row map and original boundary inclusion. -/
@[reassoc]
theorem boundary_piece_naturality {X Y : SimplicialObject SSet.{u}}
    (eta : X ⟶ Y) (n : ℕ) :
    Subcomplex.unionProd.ι₁ (outerLatching X (n + 1)) (boundary (n + 1)) ≫
        diagonalAttachmentDomainMap eta n =
      (eta.app (op ⦋n + 1⦌) ▷ (boundary (n + 1) : SSet.{u})) ≫
        Subcomplex.unionProd.ι₁ (outerLatching Y (n + 1)) (boundary (n + 1)) := by
  apply (cancel_mono (diagonalAttachmentDomain Y n).ι).mp
  rw [Category.assoc, diagonalAttachmentDomainMap_ι]
  dsimp only [diagonalAttachmentDomain]
  rw [Subcomplex.unionProd.ι₁_ι_assoc, Category.assoc, Subcomplex.unionProd.ι₁_ι]
  simpa only [tensorHom_id] using
    whisker_exchange (eta.app (op ⦋n + 1⦌)) (boundary (n + 1)).ι

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The latching piece keeps the original latching inclusion and full simplex. -/
@[reassoc]
theorem latching_piece_naturality {X Y : SimplicialObject SSet.{u}}
    (eta : X ⟶ Y) (n : ℕ) :
    Subcomplex.unionProd.ι₂ (outerLatching X (n + 1)) (boundary (n + 1)) ≫
        diagonalAttachmentDomainMap eta n =
      (outerLatchingMap eta (n + 1) ▷ Δ[n + 1]) ≫
        Subcomplex.unionProd.ι₂ (outerLatching Y (n + 1)) (boundary (n + 1)) := by
  apply (cancel_mono (diagonalAttachmentDomain Y n).ι).mp
  rw [Category.assoc, diagonalAttachmentDomainMap_ι]
  dsimp only [diagonalAttachmentDomain]
  rw [Subcomplex.unionProd.ι₂_ι_assoc, Category.assoc, Subcomplex.unionProd.ι₂_ι]
  simp only [tensorHom_id, ← comp_whiskerRight, outerLatchingMap_ι]

/-- The literal chosen pushout map of the two union-product spans. -/
def chosenMap {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :=
  pushout.map
    ((outerLatching X (n + 1)).ι ▷ (boundary (n + 1) : SSet.{u}))
    ((outerLatching X (n + 1) : SSet.{u}) ◁ (boundary (n + 1)).ι)
    ((outerLatching Y (n + 1)).ι ▷ (boundary (n + 1) : SSet.{u}))
    ((outerLatching Y (n + 1) : SSet.{u}) ◁ (boundary (n + 1)).ι)
    (eta.app (op ⦋n + 1⦌) ▷ (boundary (n + 1) : SSet.{u}))
    (outerLatchingMap eta (n + 1) ▷ Δ[n + 1])
    (outerLatchingMap eta (n + 1) ▷ (boundary (n + 1) : SSet.{u}))
    (by simp only [← comp_whiskerRight, outerLatchingMap_ι])
    (by exact whisker_exchange (outerLatchingMap eta (n + 1)) (boundary (n + 1)).ι)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Both native chosen-pushout Isos identify the map with the actual
diagonalAttachmentDomainMap. This is not an isomorphic replacement goal. -/
def attachmentArrowIso {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    Arrow.mk (chosenMap eta n) ≅ Arrow.mk (diagonalAttachmentDomainMap eta n) := by
  let sx := Subcomplex.unionProd.isPushout (outerLatching X (n + 1)) (boundary (n + 1))
  let sy := Subcomplex.unionProd.isPushout (outerLatching Y (n + 1)) (boundary (n + 1))
  refine Arrow.isoMk sx.isoPushout.symm sy.isoPushout.symm ?_
  change sx.isoPushout.inv ≫ diagonalAttachmentDomainMap eta n =
    chosenMap eta n ≫ sy.isoPushout.inv
  apply pushout.hom_ext
  · simp only [← Category.assoc, sx.inl_isoPushout_inv]
    rw [boundary_piece_naturality]
    simp [chosenMap, Category.assoc]
  · simp only [← Category.assoc, sx.inr_isoPushout_inv]
    rw [latching_piece_naturality]
    simp [chosenMap, Category.assoc]

/-- All four Arrow legs are the actual native chosen-pushout Iso legs. -/
theorem attachmentArrowIso_fourLegs {X Y : SimplicialObject SSet.{u}}
    (eta : X ⟶ Y) (n : ℕ) :
    (attachmentArrowIso eta n).hom.left =
        (Subcomplex.unionProd.isPushout (outerLatching X (n + 1))
            (boundary (n + 1))).isoPushout.inv ∧
      (attachmentArrowIso eta n).hom.right =
        (Subcomplex.unionProd.isPushout (outerLatching Y (n + 1))
            (boundary (n + 1))).isoPushout.inv ∧
      (attachmentArrowIso eta n).inv.left =
        (Subcomplex.unionProd.isPushout (outerLatching X (n + 1))
            (boundary (n + 1))).isoPushout.hom ∧
      (attachmentArrowIso eta n).inv.right =
        (Subcomplex.unionProd.isPushout (outerLatching Y (n + 1))
            (boundary (n + 1))).isoPushout.hom := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The actual union-product attachment domain is Sharp, derived from the
original rows and ALL operator comparisons. Neither its Sharp assertion nor
a latching-stage Sharp assertion is supplied as an input. -/
theorem attachment_domain_sharp_from_original_all_operators
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n)))
    (hoperators : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) (n : ℕ) :
    Sharp (diagonalAttachmentDomainMap eta n) := by
  have latching := RezkFullLatching.sharp_and_incoming_from_original_all_operators
    eta hrows hoperators n
  let sq : CommSq (outerLatching X (n + 1)).ι (outerLatchingMap eta (n + 1))
      (eta.app (op ⦋n + 1⦌)) (outerLatching Y (n + 1)).ι :=
    CommSq.mk (outerLatchingMap_ι eta (n + 1)).symm
  have leftHC := finite_tensor_hc sq (hrows ⦋n + 1⦌) latching.2
    (K := (boundary (n + 1) : SSet.{u}))
  have rightHC := tensor_boundary_hc (outerLatchingMap eta (n + 1))
    (boundary (n + 1)).ι latching.1
  let _ : Mono ((outerLatching X (n + 1) : SSet.{u}) ◁ (boundary (n + 1)).ι) := by
    change Mono ((tensorLeft (outerLatching X (n + 1) : SSet.{u})).map (boundary (n + 1)).ι)
    infer_instance
  let _ : Mono ((outerLatching Y (n + 1) : SSet.{u}) ◁ (boundary (n + 1)).ι) := by
    change Mono ((tensorLeft (outerLatching Y (n + 1) : SSet.{u})).map (boundary (n + 1)).ι)
    infer_instance
  have result := sharp_compatible_pushout
    ((outerLatching X (n + 1)).ι ▷ (boundary (n + 1) : SSet.{u}))
    ((outerLatching X (n + 1) : SSet.{u}) ◁ (boundary (n + 1)).ι)
    ((outerLatching Y (n + 1)).ι ▷ (boundary (n + 1) : SSet.{u}))
    ((outerLatching Y (n + 1) : SSet.{u}) ◁ (boundary (n + 1)).ι)
    (outerLatchingMap eta (n + 1) ▷ (boundary (n + 1) : SSet.{u}))
    (eta.app (op ⦋n + 1⦌) ▷ (boundary (n + 1) : SSet.{u}))
    (outerLatchingMap eta (n + 1) ▷ Δ[n + 1])
    (by simp only [← comp_whiskerRight, outerLatchingMap_ι])
    (by exact whisker_exchange (outerLatchingMap eta (n + 1)) (boundary (n + 1)).ι)
    (tensor_map_sharp _ _ latching.1) (tensor_map_sharp _ _ (hrows ⦋n + 1⦌))
    (tensor_map_sharp _ _ latching.1) leftHC rightHC
  exact (SharpCoproductClosure.sharp_arrowIso_iff (attachmentArrowIso eta n)).mp result.1

end SSet.RezkSkeletalAttachment
