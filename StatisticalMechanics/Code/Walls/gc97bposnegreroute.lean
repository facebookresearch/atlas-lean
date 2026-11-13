/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.gc88brereroutehall
import Code.Walls.gc96bsignedinvolution

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]














theorem gc97b_pcount_innerReroute_eq (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    {u v : W} (huv : u ≠ v) (P : Finset ι) (hPm : P ⊆ m) (hPsrc : sources ends P = {u, v}) :
    #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v}))
      = #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) :=
  gc85b_pcount_reroute_eq ends m A B huv P hPm hPsrc









theorem gc97b_cogxg_reroute_eq (ends : ι → Sym2 W) (m : Finset ι) (o x g : W) (hog : o ≠ g)
    (P : Finset ι) (hPm : P ⊆ m) (hPsrc : sources ends P = {o, g}) :
    #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W) ∆ {o, g}))
      = #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W))) :=
  gc97b_pcount_innerReroute_eq ends m {o, g} {x, g} hog P hPm hPsrc













def gc97b_PosNegReroute (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : Prop :=
  gc96b_SignedInvolution ends m o x y g



theorem gc97b_reroute_iff_posLeNeg (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc97b_PosNegReroute ends m o x y g
      ↔ gc96b_signedPos ends m o x y g ≤ gc96b_signedNeg ends m o x y g :=
  gc96b_involution_iff_posLeNeg ends m o x y g



theorem gc97b_reroute_iff_bijection (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc97b_PosNegReroute ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g :=
  gc96b_involution_iff_bijection ends m o x y g



theorem gc97b_threeGapCount_nonpos_of_reroute (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (h : gc97b_PosNegReroute ends m o x y g) :
    gc85b_threeGapCount ends m o x y g ≤ 0 :=
  gc96b_threeGapCount_nonpos_of_involution ends m o x y g h



theorem gc97b_reroute_closes (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (h : gc97b_PosNegReroute ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc96b_involution_closes ends m o x y g h














theorem gc97b_wred_reroute_exists :
    gc97b_PosNegReroute gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 :=
  gc96b_wred_equivariant_involution_exists




theorem gc97b_star_reroute_exists :
    gc97b_PosNegReroute gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3
      ∧ gc96b_signedPos gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 = 1 :=
  gc96b_star_involution




























theorem gc97b_status (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    
    (gc97b_PosNegReroute ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (gc97b_PosNegReroute ends m o x y g → gc85b_threeGapCount ends m o x y g ≤ 0)
    
    ∧ gc97b_PosNegReroute gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 :=
  ⟨gc97b_reroute_iff_bijection ends m o x y g,
   gc97b_threeGapCount_nonpos_of_reroute ends m o x y g,
   gc97b_wred_reroute_exists⟩





















theorem gc97b_machine_findings : True := trivial

end StatMech.Walls
