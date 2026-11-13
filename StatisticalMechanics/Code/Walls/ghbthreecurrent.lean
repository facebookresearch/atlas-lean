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
import Code.Walls.gc89bmetricinjection
import Code.Walls.ghggrahamclose

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

























theorem ghb_count_reduction (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hle : gc87b_CogxgLeT3 ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle








theorem ghb_two_T3_le_slack (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g :=
  gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog
























def ghb_gks_drop_count_shadow (ends : ι → Sym2 W) (m : Finset ι) : Prop :=
  gc85b_SwitchDominance ends m










theorem ghb_gks_drop_is_pairwise_at_count :
    ∃ c00 c0og c0ox c0oy cogxg : ℤ,
      0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg
      ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00
      ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy) :=
  gc85b_pairwise_insufficient








theorem ghb_count_shadow_insufficient :
    ¬ (∀ c00 c0og c0ox c0oy cogxg : ℤ,
        0 ≤ c00 → 0 ≤ c0og → 0 ≤ c0ox → 0 ≤ c0oy → 0 ≤ cogxg →
        cogxg ≤ c0og → cogxg ≤ c0ox → cogxg ≤ c0oy → cogxg ≤ c00 →
        c00 + 2 * cogxg ≤ c0og + c0ox + c0oy) := by
  intro hall
  obtain ⟨c00, c0og, c0ox, c0oy, cogxg, h0, h1, h2, h3, h4, h5, h6, h7, h8, hviol⟩ :=
    gc85b_pairwise_insufficient
  exact hviol (hall c00 c0og c0ox c0oy cogxg h0 h1 h2 h3 h4 h5 h6 h7 h8)















theorem ghb_three_current_holds_star :
    gc85b_ThreeCurrentBijection gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 :=
  gc86b_star_bijection.1





theorem ghb_three_current_holds_triangle :
    gc85b_ThreeCurrentBijection gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
  refine ghb_count_reduction gc87b_triEnds (univ : Finset (Fin 3)) ?_ gc87b_tri_sources
    (by decide) (by decide) (by decide) gc87b_tri_residue_nonvacuous.2
  
  intro i _
  fin_cases i <;> decide
























theorem ghb_canonical_reroute_lands (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m)
    (hP : P ⊆ K₁) (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (hK₁ : sources ends K₁ = ({o, g} : Finset W)) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hxg : connK ends (m \ K₁) x g) :
    (K₁ \ P) ⊆ m ∧ sources ends (K₁ \ P) = (∅ : Finset W)
      ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y
      ∧ connK ends (m \ (K₁ \ P)) o g :=
  gc89b_canonical_map_lands ends hK₁m hP hnd hsrc hox hoy hog hxy hxg' hyg hK₁ hPsrc hxg




































theorem ghb_three_current_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (∃ c00 c0og c0ox c0oy cogxg : ℤ,
        0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg
        ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00
        ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy))
    
    ∧ (2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g) :=
  ⟨fun hle => ghb_count_reduction ends m hnd hsrc hox hoy hog hle,
   gc85b_pairwise_insufficient,
   gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog⟩



































theorem ghb_status : True := trivial

end StatMech.Walls
