/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc7componenteven
import Code.Walls.gc7connequiv
import Code.Walls.gc6_pairingpath
import Code.Walls.gc7ghosteven

open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]
















theorem gc7_core_marks_in_cluster_even (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y g u : V)
    (hbdry : sources ends K = ({o, x, y, g} : Finset V)) :
    Even (#(({o, x, y, g} : Finset V) ∩ (compOf ends K u))) := by
  have heven := gc7_componentEven_sources ends K hnd u
  rwa [hbdry] at heven














theorem gc7_core_ox_xor_oy (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources ends K = ({o, x, y, g} : Finset V))
    (hog_disc : ¬ connK ends K o g) :
    (connK ends K o x) ≠ (connK ends K o y) := by
  have heven := gc7_core_marks_in_cluster_even ends K hnd o x y g o hbdry
  have hmemo : connK ends K o o := Relation.ReflTransGen.refl
  by_cases hx : connK ends K o x <;> by_cases hy : connK ends K o y
  · 
    exfalso
    have hset : ({o, x, y, g} : Finset V) ∩ (compOf ends K o) = {o, x, y} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_compOf]
      constructor
      · rintro ⟨hv, hvc⟩
        rcases hv with rfl | rfl | rfl | rfl
        · tauto
        · tauto
        · tauto
        · exact absurd hvc hog_disc
      · rintro (rfl | rfl | rfl)
        · exact ⟨by tauto, hmemo⟩
        · exact ⟨by tauto, hx⟩
        · exact ⟨by tauto, hy⟩
    rw [hset] at heven
    have hcard3 : (({o, x, y} : Finset V).card) = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
          Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    rw [hcard3] at heven
    exact (Nat.not_even_iff_odd.2 ⟨1, rfl⟩) heven
  · simp [hx, hy]
  · simp [hx, hy]
  · 
    exfalso
    have hset : ({o, x, y, g} : Finset V) ∩ (compOf ends K o) = {o} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_compOf]
      constructor
      · rintro ⟨hv, hvc⟩
        rcases hv with rfl | rfl | rfl | rfl
        · rfl
        · exact absurd hvc hx
        · exact absurd hvc hy
        · exact absurd hvc hog_disc
      · rintro rfl; exact ⟨by tauto, hmemo⟩
    rw [hset, Finset.card_singleton] at heven
    exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) heven













theorem gc7_core_complementary_yg (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources ends K = ({o, x, y, g} : Finset V))
    (hoy_disc : ¬ connK ends K o y)
    (hox_conn : connK ends K o x) :
    connK ends K y g := by
  have heven := gc7_core_marks_in_cluster_even ends K hnd o x y g y hbdry
  have hmemy : connK ends K y y := Relation.ReflTransGen.refl
  have hyo : ¬ connK ends K y o := fun h => hoy_disc (connK_symm ends K h)
  have hyx : ¬ connK ends K y x := fun h => hoy_disc (hox_conn.trans (connK_symm ends K h))
  by_cases hyg_conn : connK ends K y g
  · exact hyg_conn
  · exfalso
    have hset : ({o, x, y, g} : Finset V) ∩ (compOf ends K y) = {y} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_compOf]
      constructor
      · rintro ⟨hv, hvc⟩
        rcases hv with rfl | rfl | rfl | rfl
        · exact absurd hvc hyo
        · exact absurd hvc hyx
        · rfl
        · exact absurd hvc hyg_conn
      · rintro rfl; exact ⟨by tauto, hmemy⟩
    rw [hset, Finset.card_singleton] at heven
    exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) heven





theorem gc7_core_complementary_xg (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources ends K = ({o, x, y, g} : Finset V))
    (hox_disc : ¬ connK ends K o x)
    (hoy_conn : connK ends K o y) :
    connK ends K x g := by
  
  have hbdry' : sources ends K = ({o, y, x, g} : Finset V) := by
    rw [hbdry]; ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  exact gc7_core_complementary_yg ends K hnd o y x g hoy hox hog hxy.symm hyg hxg
    hbdry' hox_disc hoy_conn



















theorem gc7_core_pathCrossing_dichotomy (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources ends K = ({o, x, y, g} : Finset V))
    (hog_disc : ¬ connK ends K o g) :
    ((connK ends K o x ∧ connK ends K y g) ∨ (connK ends K o y ∧ connK ends K x g))
      ∧ ¬ ((connK ends K o x ∧ connK ends K y g) ∧ (connK ends K o y ∧ connK ends K x g)) := by
  have hxor := gc7_core_ox_xor_oy ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hog_disc
  refine ⟨?_, ?_⟩
  · 
    by_cases hx : connK ends K o x
    · left
      refine ⟨hx, ?_⟩
      have hoy_disc : ¬ connK ends K o y := by
        intro hy; exact hxor (by simp [hx, hy])
      exact gc7_core_complementary_yg ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hoy_disc hx
    · right
      have hy : connK ends K o y := by
        by_contra hy; exact hxor (by simp [hx, hy])
      exact ⟨hy, gc7_core_complementary_xg ends K hnd o x y g hox hoy hog hxy hxg hyg hbdry hx hy⟩
  · 
    rintro ⟨⟨hox_c, _⟩, ⟨hoy_c, _⟩⟩
    exact hxor (by simp [hox_c, hoy_c])













theorem gc7_core_allConnected_of_arcs (ends : ι → Sym2 V) (K : Finset ι) {o x y g : V}
    (hox : connK ends K o x) (hoy : connK ends K o y) (hog : connK ends K o g) :
    connK ends K o o ∧ connK ends K o x ∧ connK ends K o y ∧ connK ends K o g :=
  ⟨Relation.ReflTransGen.refl, hox, hoy, hog⟩













theorem gc7_core_pathCrossing_trichotomy (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources ends K = ({o, x, y, g} : Finset V)) :
    (connK ends K o g)
      ∨ (connK ends K o x ∧ connK ends K y g)
      ∨ (connK ends K o y ∧ connK ends K x g) := by
  by_cases hog_disc : connK ends K o g
  · exact Or.inl hog_disc
  · exact Or.inr ((gc7_core_pathCrossing_dichotomy ends K hnd o x y g
      hox hoy hog hxy hxg hyg hbdry hog_disc).1)















theorem gc7_core_crossing_forces_oneCluster (ends : ι → Sym2 V) (K : Finset ι) {o x y g w : V}
    (hox : connK ends K o x) (hyg : connK ends K y g)
    (hwo : connK ends K w o) (hwy : connK ends K w y) :
    connK ends K o x ∧ connK ends K o y ∧ connK ends K o g := by
  
  have hoy : connK ends K o y := (connK_symm ends K hwo).trans hwy
  exact ⟨hox, hoy, hoy.trans hyg⟩







variable {W : Type*} [Fintype W] [DecidableEq W]










theorem gc7_core_pathCrossing_dichotomy_edgeCopy (G : SimpleGraph W) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources (endsM G m) K = ({o, x, y, g} : Finset W))
    (hog_disc : ¬ connK (endsM G m) K o g) :
    ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g)
        ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g))
      ∧ ¬ ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g)
        ∧ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g)) :=
  gc7_core_pathCrossing_dichotomy (endsM G m) K (fun i _ => endsM_not_isDiag G m i)
    o x y g hox hoy hog hxy hxg hyg hbdry hog_disc




theorem gc7_core_pathCrossing_trichotomy_edgeCopy (G : SimpleGraph W) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources (endsM G m) K = ({o, x, y, g} : Finset W)) :
    (connK (endsM G m) K o g)
      ∨ (connK (endsM G m) K o x ∧ connK (endsM G m) K y g)
      ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g) :=
  gc7_core_pathCrossing_trichotomy (endsM G m) K (fun i _ => endsM_not_isDiag G m i)
    o x y g hox hoy hog hxy hxg hyg hbdry

















theorem gc7_core_pairing1_arcs_realised (G : SimpleGraph W) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) (N₁ N₂ : Finset (Copy G m)) (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hN₁ : N₁ ⊆ K) (hN₂ : N₂ ⊆ K)
    (hb1 : sources (endsM G m) N₁ = ({o, x} : Finset W))
    (hb2 : sources (endsM G m) N₂ = ({y, g} : Finset W)) :
    connK (endsM G m) K o x ∧ connK (endsM G m) K y g := by
  
  refine ⟨?_, ?_⟩
  · exact gc6_pairingPath_abstract (endsM G m) N₁ K
      (fun i _ => endsM_not_isDiag G m i) hN₁ hb1 hox
  · exact gc6_pairingPath_abstract (endsM G m) N₂ K
      (fun i _ => endsM_not_isDiag G m i) hN₂ hb2 hyg












theorem gc7_core_dichotomy_nonvacuous :
    let ends : Fin 2 → Sym2 (Fin 4) := fun i => if i = 0 then s(0, 1) else s(2, 3)
    sources ends (univ : Finset (Fin 2)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ connK ends (univ : Finset (Fin 2)) 0 1
      ∧ connK ends (univ : Finset (Fin 2)) 2 3 := by
  intro ends
  refine ⟨?_, ?_, ?_⟩
  · 
    decide
  · 
    exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  · 
    exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩

end StatMech.Walls
