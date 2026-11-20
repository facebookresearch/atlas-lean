/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.SwitchingCovariance
import Code.Sharpness.DeltaRewriteDichotomy
import Code.Walls.gc2_core
import Code.Walls.gc8crossingallconn

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]




























theorem gc9_switching_difference_to_disconn (ends : ι → Sym2 V) (F : Finset ι → ℝ) (A : Finset V)
    (hnd : ∀ i, ¬ (ends i).IsDiag) {o g : V} (hog : o ≠ g) :
    drd_pairSum ends A F (fun m => ¬ connK ends m o g)
      = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m))
        - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
            (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)) :=
  drd_pairSum_disconnect_eq_gap ends F A hnd hog











theorem gc9_switching_difference_to_gate (ends : ι → Sym2 V)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (A : Finset V) {o g : V} (hog : o ≠ g) (F : Finset ι → ℝ) :
    (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
        (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m))
      - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m))
      = ∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A),
              F m * (if ¬ connK ends m o g then 1 else 0)) :=
  srcPairDisconnect_eq ends hnd A hog F


















theorem gc9_eqswi_vanishing_branch (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {B : Finset V} (hFB : ¬ gc2_FB ends M B) :
    #(M.powerset.filter (fun N => RandomCurrent.sources ends N = B)) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro N hNpow hNsrc
  rw [Finset.mem_powerset] at hNpow
  
  exact hFB (gc2_K_exists_imp_FB ends M N hNpow hnd hNsrc)












theorem gc9_eqswi_count_collapse (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) (B : Finset V) :
    #(M.powerset.filter (fun N => RandomCurrent.sources ends N = B))
      = (if gc2_FB ends M B then 1 else 0)
          * #(M.powerset.filter (fun N => RandomCurrent.sources ends N = ∅)) :=
  gc2_eq_swi_count ends M hnd B

























theorem gc9_switching_eqswi (ends : ι → Sym2 V) (F : Finset ι → ℝ) (A : Finset V)
    (hnd : ∀ i, ¬ (ends i).IsDiag) {o g : V} (hog : o ≠ g) (B : Finset V) :
    
    (drd_pairSum ends A F (fun m => ¬ connK ends m o g)
        = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
            (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m))
          - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
              (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)))
    
    ∧ #(Finset.univ.powerset.filter (fun N => RandomCurrent.sources ends N = B))
        = (if gc2_FB ends Finset.univ B then 1 else 0)
            * #(Finset.univ.powerset.filter (fun N => RandomCurrent.sources ends N = ∅)) := by
  refine ⟨gc9_switching_difference_to_disconn ends F A hnd hog, ?_⟩
  exact gc9_eqswi_count_collapse ends Finset.univ (fun i _ => hnd i) B




















theorem gc9_delta_disconn_eq (ends : ι → Sym2 V) (F : Finset ι → ℝ) (A : Finset V)
    (hnd : ∀ i, ¬ (ends i).IsDiag) {o g : V} (hog : o ≠ g) :
    drd_pairSum ends A F (fun m => gc8_disconn ends o g m)
      = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m))
        - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
            (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)) :=
  
  gc9_switching_difference_to_disconn ends F A hnd hog












theorem gc9_switching_difference_to_disconn_nonvacuous :
    drd_pairSum witEnds ({0, 1, 2, 3} : Finset (Fin 4)) (fun _ => 1)
        (fun m => ¬ connK witEnds m (0 : Fin 4) 3)
      = (∑ m ∈ (Finset.univ.powerset.filter
            (fun m => RandomCurrent.sources witEnds m = ({0, 1, 2, 3} : Finset (Fin 4)))),
          (∑ _K ∈ m.powerset.filter
            (fun K => RandomCurrent.sources witEnds K = ({0, 1, 2, 3} : Finset (Fin 4))),
              (fun _ => (1 : ℝ)) m))
        - (∑ m ∈ (Finset.univ.powerset.filter
            (fun m => RandomCurrent.sources witEnds m = ({0, 1, 2, 3} : Finset (Fin 4)))),
            (∑ _K ∈ m.powerset.filter
              (fun K => RandomCurrent.sources witEnds K
                = ({0, 1, 2, 3} : Finset (Fin 4)) ∆ {(0 : Fin 4), 3}),
                (fun _ => (1 : ℝ)) m)) :=
  gc9_switching_difference_to_disconn witEnds (fun _ => 1) ({0, 1, 2, 3} : Finset (Fin 4))
    (by decide) (by decide)

end StatMech.Walls
