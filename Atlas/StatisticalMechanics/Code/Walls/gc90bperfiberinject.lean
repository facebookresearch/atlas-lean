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
import Code.Walls.gc89bmetricinjection

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











theorem gc90b_ncount_mono (ends : ι → Sym2 W) {R R' : Finset ι} (hRR : R ⊆ R') :
    gc86b_ncount ends R ∅ ≤ gc86b_ncount ends R' ∅ := by
  unfold gc86b_ncount
  apply Finset.card_le_card
  intro K hK
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK ⊢
  exact ⟨hK.1.trans hRR, hK.2⟩












theorem gc90b_perK1_le (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hP : P ⊆ K₁) :
    gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ (K₁ \ P)) ∅ := by
  apply gc90b_ncount_mono
  apply Finset.sdiff_subset_sdiff (Finset.Subset.refl m)
  exact Finset.sdiff_subset











noncomputable def gc90b_cogxgFibers (ends : ι → Sym2 W) (m : Finset ι) (o x g : W) :
    Finset (Finset ι) :=
  (m.powerset.filter (fun K => sources ends K = ({o, g} : Finset W))).filter
    (fun K₁ => connK ends (m \ K₁) x g)


noncomputable def gc90b_T3Fibers (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    Finset (Finset ι) :=
  (m.powerset.filter (fun K => sources ends K = (∅ : Finset W))).filter
    (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g)


theorem gc90b_cogxg_eq_sum (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    gc85b_pcount ends m {o, g} {x, g}
      = ∑ K₁ ∈ gc90b_cogxgFibers ends m o x g, gc86b_ncount ends (m \ K₁) ∅ :=
  gc87b_cogxg_fiber_conn (o := o) (x := x) (y := y) (g := g) ends m hnd hxg


theorem gc90b_T3_eq_sum (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc87b_T3 ends m o x y g
      = ∑ J₁ ∈ gc90b_T3Fibers ends m o x y g, gc86b_ncount ends (m \ J₁) ∅ := rfl














theorem gc90b_cogxg_le_of_assignment (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g)
    (φ : Finset ι → Finset ι)
    (hφmem : ∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g)
    (hcap : ∀ J₁ ∈ gc90b_T3Fibers ends m o x y g,
      ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
        gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) :
    gc85b_pcount ends m {o, g} {x, g} ≤ gc87b_T3 ends m o x y g := by
  rw [gc90b_cogxg_eq_sum ends m hnd hxg (o := o) (y := y), gc90b_T3_eq_sum ends m o x y g]
  
  have hfib :
      ∑ K₁ ∈ gc90b_cogxgFibers ends m o x g, gc86b_ncount ends (m \ K₁) ∅
        = ∑ J₁ ∈ gc90b_T3Fibers ends m o x y g,
            ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
              gc86b_ncount ends (m \ K₁) ∅ := by
    rw [Finset.sum_fiberwise_of_maps_to (g := φ)
          (fun K₁ hK₁ => hφmem K₁ hK₁)]
  rw [hfib]
  exact Finset.sum_le_sum hcap







theorem gc90b_close_of_assignment (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g)
    (φ : Finset ι → Finset ι)
    (hφmem : ∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g)
    (hcap : ∀ J₁ ∈ gc90b_T3Fibers ends m o x y g,
      ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
        gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog
    (gc90b_cogxg_le_of_assignment ends m hnd hxg φ hφmem hcap)














def gc90b_starEnds : Fin 5 → Sym2 (Fin 4) :=
  fun i => if i = 0 then s(0, 1) else if i = 1 then s(0, 2) else s(0, 3)



theorem gc90b_star_sources :
    sources gc90b_starEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide





theorem gc90b_star_cogxgFibers :
    sources gc90b_starEnds ({2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
    ∧ sources gc90b_starEnds ({3} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
    ∧ sources gc90b_starEnds ({4} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide




theorem gc90b_star_canonical_merge :
    (({2} : Finset (Fin 5)) \ ({2} : Finset (Fin 5)) = (∅ : Finset (Fin 5)))
      ∧ (({3} : Finset (Fin 5)) \ ({3} : Finset (Fin 5)) = (∅ : Finset (Fin 5)))
      ∧ (({4} : Finset (Fin 5)) \ ({4} : Finset (Fin 5)) = (∅ : Finset (Fin 5))) := by
  refine ⟨by decide, by decide, by decide⟩








theorem gc90b_star_perJ1_fails :
    
    gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({2} : Finset (Fin 5))) ∅ = 2
      ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({3} : Finset (Fin 5))) ∅ = 2
      ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ ({4} : Finset (Fin 5))) ∅ = 2
    
      ∧ gc86b_ncount gc90b_starEnds ((univ : Finset (Fin 5)) \ (∅ : Finset (Fin 5))) ∅ = 4
    
      ∧ (2 + 2 + 2 : ℕ) > gc86b_ncount gc90b_starEnds
          ((univ : Finset (Fin 5)) \ (∅ : Finset (Fin 5))) ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide



















theorem gc90b_perfiber_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g) :
    
    (∀ (K₁ P : Finset ι), P ⊆ K₁ →
        gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ (K₁ \ P)) ∅)
    
    ∧ (∀ (φ : Finset ι → Finset ι),
        (∀ K₁ ∈ gc90b_cogxgFibers ends m o x g, φ K₁ ∈ gc90b_T3Fibers ends m o x y g) →
        (∀ J₁ ∈ gc90b_T3Fibers ends m o x y g,
          ∑ K₁ ∈ (gc90b_cogxgFibers ends m o x g).filter (fun K => φ K = J₁),
            gc86b_ncount ends (m \ K₁) ∅ ≤ gc86b_ncount ends (m \ J₁) ∅) →
        gc85b_ThreeCurrentBijection ends m o x y g) := by
  refine ⟨fun K₁ P hP => gc90b_perK1_le ends hP, ?_⟩
  intro φ hφmem hcap
  exact gc90b_close_of_assignment ends m hnd hsrc hox hoy hog hxg φ hφmem hcap
















theorem gc90b_machine_findings : True := trivial

end StatMech.Walls
