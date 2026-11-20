/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Walls.bri2reconcile
import Code.Walls.briraysintree
import Code.Walls.bof2leafcount

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls





theorem bra_G_le_lattice (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) :
    bri2_G ω L ≤ hypercubicLattice 2 :=
  bri2_le_lattice ω L








theorem bra_ray_crux_transfers (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ)
    (T : SimpleGraph (Site 2)) [LocallyFinite T] (hT : T ≤ bri2_G ω L)
    {w x : Site 2} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x) (hw : w ∈ box 2 R)
    (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧
      (∃ k, r k ∈ vertexBoundary 2 R) :=
  bri_branchRay_reaches_boundary T (le_trans hT (bri2_le_lattice ω L)) hR hwx hw hinf









theorem bra_hub_cut_of_centreSep (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) {j k₁ k₂ k₃ : Site 2}
    (h₁₂ : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable
              (bgf2_centre L k₁) (bgf2_centre L k₂))
    (h₁₃ : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable
              (bgf2_centre L k₁) (bgf2_centre L k₃))
    (h₂₃ : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable
              (bgf2_centre L k₂) (bgf2_centre L k₃)) :
    ¬ (bkg_deleteVertex (bri2_G ω L) j).Reachable k₁ k₂ ∧
    ¬ (bkg_deleteVertex (bri2_G ω L) j).Reachable k₁ k₃ ∧
    ¬ (bkg_deleteVertex (bri2_G ω L) j).Reachable k₂ k₃ :=
  ⟨bri2_sep_sound h₁₂, bri2_sep_sound h₁₃, bri2_sep_sound h₂₃⟩















theorem bra_count (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ)
    (S : Finset (Site 2))
    {T : SimpleGraph {v // v ∈ S}} [DecidableRel T.Adj]
    (hTH : T ≤ bfct_restrict (bri2_G ω L) S) (hT : T.IsTree)
    {ι : Type*} [Fintype ι] (f : ι → {v // v ∈ S}) (hf : Function.Injective f)
    (hcut : ∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S},
        a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex (bri2_G ω L) (f i : Site 2)).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧
        ¬ (bkg_deleteVertex (bri2_G ω L) (f i : Site 2)).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧
        ¬ (bkg_deleteVertex (bri2_G ω L) (f i : Site 2)).Reachable (a₂ : Site 2) (a₃ : Site 2))
    (B : Finset {v // v ∈ S}) (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
    Fintype.card ι ≤ B.card := by
  classical
  exact bfct_count (bri2_G ω L) S hTH hT f hf hcut B hleaf













theorem bra_armImage_centre_iff_hubBox {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen ω L 0) (a : Site 2) :
    bgf2_q ω L a = 0 ↔ a ∈ bc61_boxAround 2 L 0 :=
  bgf2_q_eq_zero_iff_mem h0







theorem bra_strictLoss_witness {L : ℕ} (hL : 1 ≤ L) :
    ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0) :=
  bgf2_onlyBox0_not_merged hL






theorem bra_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bri_datum_implies_count ω L R h









































theorem bra_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bri2_G ω L ≤ hypercubicLattice 2) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (T : SimpleGraph (Site 2)) [LocallyFinite T],
      T ≤ bri2_G ω L → ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R →
      (ray34_AvoidCluster T {x} w).Infinite →
      ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
        (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧
        (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    
    (∀ L : ℕ, 1 ≤ L → ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L; exact bra_G_le_lattice ω L
  · intro ω L T _ hT w x R hR hwx hw hinf
    exact bra_ray_crux_transfers ω L T hT hR hwx hw hinf
  · intro L hL; exact bra_strictLoss_witness hL
  · intro ω L R h; exact bra_datum_implies_count ω L R h

end StatMech.Walls
