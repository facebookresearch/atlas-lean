/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Walls.bdcdetcount
import Code.Walls.bararmray

open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls






def bri2_G (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : SimpleGraph (Site 2) :=
  SimpleGraph.comap (bgf2_centre L) (bgf2_Gf ω L)

@[simp] theorem bri2_G_adj (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j k : Site 2) :
    (bri2_G ω L).Adj j k ↔ (bgf2_Gf ω L).Adj (bgf2_centre L j) (bgf2_centre L k) :=
  Iff.rfl




theorem bri2_q_centre_imp {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {a j : Site 2}
    (h : bgf2_q ω L a = bgf2_centre L j) : bgn_idx L a = j := by
  unfold bgf2_q at h
  by_cases hP : bgf2_IndexAllOpen ω L (bgn_idx L a)
  · rw [if_pos hP] at h; exact bgf2_centre_inj h
  · rw [if_neg hP] at h; rw [h, bgf2_idx_centre]


theorem bri2_q_centre (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) :
    bgf2_q ω L (bgf2_centre L j) = bgf2_centre L j := by
  unfold bgf2_q
  by_cases hP : bgf2_IndexAllOpen ω L (bgn_idx L (bgf2_centre L j))
  · rw [if_pos hP, bgf2_idx_centre]
  · rw [if_neg hP]




theorem bri2_le_bgn_Gn (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) :
    bri2_G ω L ≤ bgn_Gn ω L := by
  intro j k hjk
  rw [bri2_G_adj, bgf2_Gf_adj] at hjk
  obtain ⟨hne, a, b, ha, hb, hab⟩ := hjk
  refine ⟨?_, a, b, bri2_q_centre_imp ha, bri2_q_centre_imp hb, hab⟩
  intro hjk; exact hne (by rw [hjk])





theorem bri2_le_lattice (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) :
    bri2_G ω L ≤ hypercubicLattice 2 :=
  le_trans (bri2_le_bgn_Gn ω L) (bsg_Gn_le_lattice ω L)









def bri2_hom (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : bri2_G ω L →g bgf2_Gf ω L where
  toFun := bgf2_centre L
  map_rel' := fun {a b} h => h




theorem bri2_faithful_sound {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j k : Site 2}
    (h : (bri2_G ω L).Reachable j k) :
    Connected 2 ω (bgf2_centre L j) (bgf2_centre L k) := by
  have hGf : (bgf2_Gf ω L).Reachable (bgf2_centre L j) (bgf2_centre L k) := h.map (bri2_hom ω L)
  have hf := bgf2_faithful ω L (bgf2_centre L j) (bgf2_centre L k)
  rw [bri2_q_centre, bri2_q_centre] at hf
  exact hf.mp hGf









def bri2_delHom (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j₀ : Site 2) :
    bkg_deleteVertex (bri2_G ω L) j₀ →g bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j₀) where
  toFun := bgf2_centre L
  map_rel' := by
    rintro p q ⟨hadj, hp, hq⟩
    exact ⟨hadj, fun h => hp (bgf2_centre_inj h), fun h => hq (bgf2_centre_inj h)⟩




theorem bri2_sep_sound {ω : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j₀ j k : Site 2}
    (h : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j₀)).Reachable
          (bgf2_centre L j) (bgf2_centre L k)) :
    ¬ (bkg_deleteVertex (bri2_G ω L) j₀).Reachable j k := by
  intro hr
  exact h (hr.map (bri2_delHom ω L j₀))

end StatMech.Walls
