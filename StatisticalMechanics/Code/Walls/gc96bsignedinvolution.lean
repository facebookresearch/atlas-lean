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












def gc96b_signedPos (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℕ :=
  gc85b_pcount ends m ∅ ∅ + 2 * gc85b_pcount ends m {o, g} {x, g}




def gc96b_signedNeg (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℕ :=
  gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y}




theorem gc96b_threeGapCount_eq (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc85b_threeGapCount ends m o x y g
      = (gc96b_signedPos ends m o x y g : ℤ) - (gc96b_signedNeg ends m o x y g : ℤ) := by
  unfold gc85b_threeGapCount gc96b_signedPos gc96b_signedNeg
  push_cast
  ring



















def gc96b_SignedInvolution (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : Prop :=
  Nonempty (Fin (gc96b_signedPos ends m o x y g) ↪ Fin (gc96b_signedNeg ends m o x y g))





theorem gc96b_involution_iff_posLeNeg (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc96b_SignedInvolution ends m o x y g
      ↔ gc96b_signedPos ends m o x y g ≤ gc96b_signedNeg ends m o x y g := by
  unfold gc96b_SignedInvolution
  rw [Function.Embedding.nonempty_iff_card_le]
  simp only [Fintype.card_fin]
















theorem gc96b_fixed_points_nonpos (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hinv : gc96b_SignedInvolution ends m o x y g) :
    -(((gc96b_signedNeg ends m o x y g : ℤ) - (gc96b_signedPos ends m o x y g : ℤ))) ≤ 0 := by
  have hle := (gc96b_involution_iff_posLeNeg ends m o x y g).1 hinv
  have : (gc96b_signedPos ends m o x y g : ℤ) ≤ (gc96b_signedNeg ends m o x y g : ℤ) := by
    exact_mod_cast hle
  linarith












theorem gc96b_threeGapCount_nonpos_of_involution (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hinv : gc96b_SignedInvolution ends m o x y g) :
    gc85b_threeGapCount ends m o x y g ≤ 0 := by
  rw [gc96b_threeGapCount_eq]
  have hle := (gc96b_involution_iff_posLeNeg ends m o x y g).1 hinv
  have : (gc96b_signedPos ends m o x y g : ℤ) ≤ (gc96b_signedNeg ends m o x y g : ℤ) := by
    exact_mod_cast hle
  linarith






theorem gc96b_involution_iff_bijection (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc96b_SignedInvolution ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
  rw [gc96b_involution_iff_posLeNeg]
  unfold gc96b_signedPos gc96b_signedNeg gc85b_ThreeCurrentBijection
  omega




theorem gc96b_involution_closes (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hinv : gc96b_SignedInvolution ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  (gc96b_involution_iff_bijection ends m o x y g).1 hinv

















theorem gc96b_wred_pos_eq_neg :
    gc96b_signedPos gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 = 7
      ∧ gc96b_signedNeg gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 = 7 := by
  refine ⟨?_, ?_⟩
  · unfold gc96b_signedPos gc85b_pcount; decide
  · unfold gc96b_signedNeg gc85b_pcount; decide









theorem gc96b_wred_equivariant_involution_exists :
    gc96b_SignedInvolution gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
  rw [gc96b_involution_iff_posLeNeg]
  rw [gc96b_wred_pos_eq_neg.1, gc96b_wred_pos_eq_neg.2]




theorem gc96b_star_involution :
    gc96b_SignedInvolution gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3
      ∧ gc96b_signedPos gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [gc96b_involution_iff_posLeNeg]
    unfold gc96b_signedPos gc96b_signedNeg gc85b_pcount; decide
  · unfold gc96b_signedPos gc85b_pcount; decide






























theorem gc96b_signed_involution_status (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    
    (gc96b_SignedInvolution ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (gc96b_SignedInvolution ends m o x y g → gc85b_threeGapCount ends m o x y g ≤ 0)
    
    ∧ gc96b_SignedInvolution gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 :=
  ⟨gc96b_involution_iff_bijection ends m o x y g,
   gc96b_threeGapCount_nonpos_of_involution ends m o x y g,
   gc96b_wred_equivariant_involution_exists⟩
























theorem gc96b_machine_findings : True := trivial

end StatMech.Walls
