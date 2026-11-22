/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalAttachmentTopIncomingHC
import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalUnionProductIncomingHC

/-!
# Sharpness and incoming squares at a skeletal successor

For a bisimplicial map with sharp rows and weak operator-relative comparisons, a preceding skeletal cell invariant yields a sharp successor-stage map and homotopy cartesian incoming squares for the old stage and the new cell. An arrow isomorphism identifies the chosen attachment pushout map with the actual successor map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalSuccessor
open SharpComparisonDraft RezkCompatiblePushout RezkSkeletalProduct RezkSkeletalCell
    RezkSkeletalAttachment

/-- The literal chosen successor pushout map for the original skeleton. -/
def chosenMap {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :=
  pushout.map (diagonalAttachmentTopMap X n) (diagonalAttachmentDomain X n).ι
    (diagonalAttachmentTopMap Y n) (diagonalAttachmentDomain Y n).ι
    (diagonalFiltrationNatMap eta n) (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1])
    (diagonalAttachmentDomainMap eta n)
    (diagonalAttachmentTopMap_naturality eta n).symm (diagonalAttachmentDomainMap_ι eta n).symm

/-- All original maps are retained by the actual chosen pushout Isos. -/
def successorArrowIso {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    Arrow.mk (chosenMap eta n) ≅ Arrow.mk (diagonalFiltrationNatMap eta (n + 1)) := by
  let sx := diagonalFiltrationSucc_isPushout X n
  let sy := diagonalFiltrationSucc_isPushout Y n
  refine Arrow.isoMk sx.isoPushout.symm sy.isoPushout.symm ?_
  change sx.isoPushout.inv ≫ diagonalFiltrationNatMap eta (n + 1) =
    chosenMap eta n ≫ sy.isoPushout.inv
  apply pushout.hom_ext
  · simp only [← Category.assoc, sx.inl_isoPushout_inv]
    rw [← diagonalFiltrationMap_naturality eta (Nat.le_succ n)]
    simp [chosenMap, Category.assoc]
  · simp only [← Category.assoc, sx.inr_isoPushout_inv]
    rw [← diagonalCellToFiltrationSucc_naturality eta n]
    simp [chosenMap, Category.assoc]

/-- The four legs are the actual native successor-pushout forward/inverse maps. -/
theorem successorArrowIso_fourLegs {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    (successorArrowIso eta n).hom.left = (diagonalFiltrationSucc_isPushout X n).isoPushout.inv ∧
      (successorArrowIso eta n).hom.right = (diagonalFiltrationSucc_isPushout Y n).isoPushout.inv ∧
      (successorArrowIso eta n).inv.left = (diagonalFiltrationSucc_isPushout X n).isoPushout.hom ∧
      (successorArrowIso eta n).inv.right =
          (diagonalFiltrationSucc_isPushout Y n).isoPushout.hom := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The actual successor skeleton is Sharp, and both old skeleton and new
cell enter it by HC squares. The two attachment HC inputs are DERIVED from
finite face and latching incidence, not supplied by a caller. -/
theorem successor_sharp_and_both_incoming
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) :
    Sharp (diagonalFiltrationNatMap eta (n + 1)) ∧
      WeakEquivalence
        (pullback.lift (diagonalFiltrationMap X (Nat.le_succ n)) (diagonalFiltrationNatMap eta n)
          (diagonalFiltrationMap_naturality eta (Nat.le_succ n)).symm ≫
          comparison (diagonalFiltrationNatMap eta (n + 1))
              (diagonalFiltrationMap Y (Nat.le_succ n))) ∧
      WeakEquivalence
        (pullback.lift (diagonalCellToFiltrationSucc X n) (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1])
          (diagonalCellToFiltrationSucc_naturality eta n).symm ≫
          comparison (diagonalFiltrationNatMap eta (n + 1))
              (diagonalCellToFiltrationSucc Y n)) := by
  have topHC := attachment_top_hc_from_actual_prior_invariant eta hrows hoperators n previous
  have cellHC := attachment_domain_incoming_from_original_all_operators eta hrows hoperators n
  have domainSharp := attachment_domain_sharp_from_original_all_operators eta hrows hoperators n
  have result := sharp_compatible_pushout
    (diagonalAttachmentTopMap X n) (diagonalAttachmentDomain X n).ι
    (diagonalAttachmentTopMap Y n) (diagonalAttachmentDomain Y n).ι
    (diagonalAttachmentDomainMap eta n) (diagonalFiltrationNatMap eta n)
    (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1])
    (diagonalAttachmentTopMap_naturality eta n).symm (diagonalAttachmentDomainMap_ι eta n).symm
    domainSharp previous.1 (tensor_map_sharp _ _ (hrows ⦋n + 1⦌)) topHC cellHC
  let E := successorArrowIso eta n
  have nextSharp : Sharp (diagonalFiltrationNatMap eta (n + 1)) :=
    (SharpCoproductClosure.sharp_arrowIso_iff E).mp result.1
  let sx := diagonalFiltrationSucc_isPushout X n
  let sy := diagonalFiltrationSucc_isPushout Y n
  have transport : chosenMap eta n ≫ sy.isoPushout.inv =
      sx.isoPushout.inv ≫ diagonalFiltrationNatMap eta (n + 1) := by
    simpa only [E, Arrow.mk_hom, (successorArrowIso_fourLegs eta n).1,
      (successorArrowIso_fourLegs eta n).2.1] using E.hom.w.symm
  let oldLeft : CommSq (pushout.inl (diagonalAttachmentTopMap X n) (diagonalAttachmentDomain X n).ι)
      (diagonalFiltrationNatMap eta n) (chosenMap eta n)
      (pushout.inl (diagonalAttachmentTopMap Y n) (diagonalAttachmentDomain Y n).ι) :=
    CommSq.mk (by simp [chosenMap])
  let newLeft : CommSq (diagonalFiltrationMap X (Nat.le_succ n)) (diagonalFiltrationNatMap eta n)
      (diagonalFiltrationNatMap eta (n + 1)) (diagonalFiltrationMap Y (Nat.le_succ n)) :=
    CommSq.mk (diagonalFiltrationMap_naturality eta (Nat.le_succ n)).symm
  have oldHC := (hc_weakSquare_iff oldLeft newLeft (𝟙 _) sx.isoPushout.inv (𝟙 _) sy.isoPushout.inv
    (by simp) (by simp)
    transport (by simp)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mp result.2.1
  let oldCell : CommSq (pushout.inr (diagonalAttachmentTopMap X n) (diagonalAttachmentDomain X n).ι)
      (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1]) (chosenMap eta n)
      (pushout.inr (diagonalAttachmentTopMap Y n) (diagonalAttachmentDomain Y n).ι) :=
    CommSq.mk (by simp [chosenMap])
  let newCell : CommSq (diagonalCellToFiltrationSucc X n) (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1])
      (diagonalFiltrationNatMap eta (n + 1)) (diagonalCellToFiltrationSucc Y n) :=
    CommSq.mk (diagonalCellToFiltrationSucc_naturality eta n).symm
  have newHC := (hc_weakSquare_iff oldCell newCell (𝟙 _) sx.isoPushout.inv (𝟙 _) sy.isoPushout.inv
    (by simp) (by simp)
    transport (by simp)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mp result.2.2.1
  exact ⟨nextSharp, oldHC, newHC⟩

end SSet.RezkSkeletalSuccessor
