/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.PrivateArmProve
import Code.Percolation.BKForestLib
import Code.Percolation.ForestSelectorProve
import Code.Percolation.SpanningTreeArmClose
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.ForestAcyclicityClose
import Code.Percolation.ForestPathStructure

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












theorem frc_connected_of_sameArm (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d}
    (hxu : Connected d ω x u) (hneu : x ≠ u)
    (hxv : Connected d ω x v) (hnev : x ≠ v)
    (hsame : fsp_sameArm ω x u v) :
    Connected d (removeSite x ω) u v := by
  
  
  have hwu : Connected d (removeSite x ω) (fsp_armWitness ω x u) u :=
    fsp_armWitness_inArm ω hxu hneu
  have hwv : Connected d (removeSite x ω) (fsp_armWitness ω x v) v :=
    fsp_armWitness_inArm ω hxv hnev
  exact hwu.symm.trans (hsame.trans hwv)















theorem frc_claw_centralArm_connects_downstream (ω : ConfigSpace (Sym2 (Site d)))
    {x₀ : Site d} {y : Fin 3 → Site d} {lx : Site d → Fin 3} {bx0 : Site d}
    (hx0_bx0_conn : Connected d ω x₀ bx0) (hx0_bx0_ne : x₀ ≠ bx0)
    (hx0_ycx_conn : Connected d ω x₀ (y (lx bx0))) (hx0_ycx_ne : x₀ ≠ y (lx bx0))
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hydown : ∀ i, lx (y i) = i) :
    Connected d (removeSite x₀ ω) bx0 (y (lx bx0)) := by
  
  have hcoll : lx bx0 = lx (y (lx bx0)) := (hydown (lx bx0)).symm
  
  have hsame : fsp_sameArm ω x₀ bx0 (y (lx bx0)) :=
    (hlxf bx0 (y (lx bx0)) hx0_bx0_conn hx0_bx0_ne hx0_ycx_conn hx0_ycx_ne).mp hcoll
  exact frc_connected_of_sameArm ω hx0_bx0_conn hx0_bx0_ne hx0_ycx_conn hx0_ycx_ne hsame


















theorem frc_not_twoSidedPrivateFar_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) : ¬ fps_TwoSidedPrivateFar ω n := by
  classical
  obtain ⟨x₀, y, lx, ly, ⟨hx0box, htri0⟩, hydata, hyinj, hlxf, hlyf, hydown, hGstar⟩ := hclaw
  rintro ⟨b, hbdata, hpair⟩
  set T := tfc_trifFinset ω n with hT
  
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i =>
    tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  
  obtain ⟨_, hbx0conn, hbx0inf⟩ := hbdata x₀ hx0box htri0
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω hbx0inf
  have hne_x0_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  
  set cx : Fin 3 := lx (b x₀) with hcx
  
  
  have hyc_box : y cx ∈ box d n := (hydata cx).1
  have hyc_tri : IsTrifurcation d ω (y cx) := (hydata cx).2.1
  have hx0_yc_ne : x₀ ≠ y cx := (hydata cx).2.2.1
  have hx0_yc_conn : Connected d ω x₀ (y cx) := (hydata cx).2.2.2
  
  have hx0_yc_neq : x₀ ≠ y cx := hx0_yc_ne
  
  have hconn_central : Connected d (removeSite x₀ ω) (b x₀) (y cx) :=
    frc_claw_centralArm_connects_downstream ω hbx0conn hne_x0_bx0
      (by simpa [hcx] using hx0_yc_conn) (by simpa [hcx] using hx0_yc_ne) hlxf hydown
  
  have hsamecluster : Connected d ω x₀ (y cx) := hx0_yc_conn
  obtain ⟨hprivx, _hprivy, _hfar⟩ :=
    hpair x₀ hx0box htri0 (y cx) hyc_box hyc_tri hx0_yc_neq hsamecluster
  
  exact hprivx hconn_central










theorem frc_claw_excludes_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : stac_ClawConfig ω n) (hres : fps_TwoSidedPrivateFar ω n) : False :=
  frc_not_twoSidedPrivateFar_of_claw ω n hclaw hres











theorem frc_uniform_twoSidedPrivateFar_false
    (hex : ∃ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n ∧ stac_ClawConfig ω n) :
    ¬ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fps_TwoSidedPrivateFar ω n) := by
  obtain ⟨ω, n, hn, hclaw⟩ := hex
  intro huniform
  exact frc_not_twoSidedPrivateFar_of_claw ω n hclaw (huniform ω n hn)

end Percolation

end StatMech
