/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc27polyineq
import Code.Walls.gc83crosspairing
import Code.Walls.gc84b_grahamsospositiv
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.gc96bsignedinvolution
import Code.Walls.gc97bposnegreroute
import Code.Walls.gc98bchainaccounting

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
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]
















theorem gc99_complete_chain (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (gc87b_CogxgLeT3 ends m o x y g → gc86b_CogxgResidual ends m o x y g)
    
    ∧ (gc86b_CogxgResidual ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc85b_threeGapCount ends m o x y g ≤ 0)
    
    ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨fun hle => gc87b_residual_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle,
   (gc86b_bijection_iff_residual ends m o x y g).symm,
   (gc85b_threeGapCount_nonpos_iff_bijection ends m o x y g).symm,
   fun hle => gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle⟩




















theorem gc99_equivalent_residue_forms (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    
    (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc85b_threeGapCount ends m o x y g ≤ 0)
    
    ∧ (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc96b_SignedInvolution ends m o x y g)
    
    ∧ (gc85b_ThreeCurrentBijection ends m o x y g ↔ gc97b_PosNegReroute ends m o x y g)
    
    ∧ (gc96b_SignedInvolution ends m o x y g
        ↔ gc96b_signedPos ends m o x y g ≤ gc96b_signedNeg ends m o x y g) :=
  ⟨(gc85b_threeGapCount_nonpos_iff_bijection ends m o x y g).symm,
   (gc96b_involution_iff_bijection ends m o x y g).symm,
   (gc97b_reroute_iff_bijection ends m o x y g).symm,
   gc96b_involution_iff_posLeNeg ends m o x y g⟩


















theorem gc99_proved_fragments (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (connK ends R o x ∨ connK ends R o y ∨ connK ends R o g)
    
    ∧ (∀ u v : W, u ≠ v → connK ends R u v → gc86b_ncount ends R {u, v} = gc86b_ncount ends R ∅)
    
    ∧ (gc85b_pcount ends R ∅ ∅
        ≤ gc85b_pcount ends R ∅ {o, g} + gc85b_pcount ends R ∅ {o, x} + gc85b_pcount ends R ∅ {o, y})
    
    ∧ (2 * (gc87b_T3 ends R o x y g : ℤ) ≤ gc87b_slack ends R o x y g)
    
    ∧ (∀ A B : Finset W, gc85b_pcount ends R A B
        = ∑ K₁ ∈ R.powerset.filter (fun K => sources ends K = A), gc86b_ncount ends (R \ K₁) B)
    
    ∧ gc96b_SignedInvolution gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 :=
  ⟨gc86b_o_connects_mark ends R hnd hsrc hox hoy hog,
   fun u v huv hconn => gc86b_ncount_conn_eq ends R huv hconn,
   gc86b_strong_global ends R hnd hsrc hox hoy hog,
   gc87b_two_T3_le_slack ends R hnd hsrc hox hoy hog,
   fun A B => gc85b_pcount_fiber ends R A B,
   gc96b_wred_equivariant_involution_exists⟩





theorem gc99_reroute_count_equality (ends : ι → Sym2 W) (m : Finset ι) (o x g : W) (hog : o ≠ g)
    (P : Finset ι) (hPm : P ⊆ m) (hPsrc : sources ends P = {o, g}) :
    #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W) ∆ {o, g}))
      = #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W))) :=
  gc97b_cogxg_reroute_eq ends m o x g hog P hPm hPsrc























theorem gc99_refuted_routes :
    
    (¬ gc84b_GriffithsConsequence gc84b_ghsResidual)
    
    ∧ (∃ a b c r q p t : ℝ, gc27_TwoSourceGapFamily a b c r q p t
        ∧ ¬ (t + 2 * (a * b * c) ≤ a * p + b * q + c * r))
    
    ∧ (∃ c00 c0og c0ox c0oy cogxg : ℤ,
        0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg
        ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00
        ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy))
    
    ∧ (#(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3)
        < 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3})
    
    ∧ (∃ (nS nT : ℕ) (adj : Fin nS → Fin nT → Prop), nS ≤ nT
        ∧ ∃ (fixedChoice : Fin nS → Fin nT), ¬ Function.Injective fixedChoice) :=
  ⟨gc84b_no_positivstellensatz,
   gc27_twoSourceGaps_insufficient,
   gc85b_pairwise_insufficient,
   gc98b_tri_image_too_small.2.2,
   gc87b_local_template_insufficient⟩





theorem gc99_arithmetic_room_circular (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc98b_DisjointAccounting ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g :=
  gc98b_accounting_iff_target ends m o x y g















theorem gc99_minimal_residue (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hle : gc87b_CogxgLeT3 ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle













theorem gc99_residue_closes_ghs {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
        sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
        gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  
  have hOX : (some o : Option V) ≠ some x := by simp [hox]
  have hOY : (some o : Option V) ≠ some y := by simp [hoy]
  have hOg : (some o : Option V) ≠ none := by simp
  refine gc85b_ursell_nonpos_of_bijection G β h hβ hh o x y hox hoy hxy ?_ hsupp
  intro m hm
  
  have hsrcU : sources (endsM (withGhost G) m) (univ : Finset (Copy (withGhost G) m))
      = ({some o, some x, some y, none} : Finset (Option V)) := by
    rw [sources_eq, profileFlux_univ]; exact hm
  
  have hnd : ∀ i ∈ (univ : Finset (Copy (withGhost G) m)), ¬ (endsM (withGhost G) m i).IsDiag :=
    fun i _ => endsM_not_isDiag (withGhost G) m i
  
  exact gc99_minimal_residue (endsM (withGhost G) m) univ hnd hsrcU hOX hOY hOg (hres m hm)






theorem gc99_residue_nonvacuous :
    gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1
      ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 :=
  gc87b_tri_residue_nonvacuous




















theorem gc99_status {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    
    (∀ {ι' : Type} [DecidableEq ι'] [Fintype ι'] (ends : ι' → Sym2 (Option V)) (m : Finset ι'),
        (∀ i ∈ m, ¬ (ends i).IsDiag) →
        sources ends m = ({some o, some x, some y, none} : Finset (Option V)) →
        gc87b_CogxgLeT3 ends m (some o) (some x) (some y) none →
        gc85b_ThreeCurrentBijection ends m (some o) (some x) (some y) none)
    
    ∧ (2 * (gc87b_T3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 : ℤ)
        ≤ gc87b_slack gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3)
    
    ∧ (¬ gc84b_GriffithsConsequence gc84b_ghsResidual)
    
    ∧ ((∀ m : ↥(withGhost G).edgeFinset → ℕ,
          sources (withGhost G) (ofEdgeFun (withGhost G) m)
            = ({some o, some x, some y, none} : Finset (Option V)) →
          gc87b_CogxgLeT3 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
        → gc82_ThreeGapAllConnSupported G β h o x y
        → eg_ursell3 G β h o x y ≤ 0) := by
  have hOX : (some o : Option V) ≠ some x := by simp [hox]
  have hOY : (some o : Option V) ≠ some y := by simp [hoy]
  have hOg : (some o : Option V) ≠ none := by simp
  refine ⟨?_, ?_, gc84b_no_positivstellensatz, ?_⟩
  · intro ι' _ _ ends m hnd hsrc hle
    exact gc99_minimal_residue ends m hnd hsrc hOX hOY hOg hle
  · exact gc87b_two_T3_le_slack gc87b_triEnds (univ : Finset (Fin 3))
      (fun i _ => by fin_cases i <;> decide) gc87b_tri_sources (by decide) (by decide) (by decide)
  · intro hres hsupp
    exact gc99_residue_closes_ghs G β h hβ hh o x y hox hoy hxy hres hsupp





























theorem gc99_consolidation_notes : True := trivial

end StatMech.Walls
