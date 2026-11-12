/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc2_componenthandshake

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]





















theorem gc7_componentEven_abstract {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) (u : V) :
    Even (#((compOf ends M u).filter (fun x => Odd (degK ends M x)))) :=
  (even_sum_iff_even_count _ _).1 (sum_deg_comp_even ends M hnd u)










theorem gc7_oddComp_eq_sources_inter {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset ι) (u : V) :
    (compOf ends M u).filter (fun x => Odd (degK ends M x))
      = (sources ends M) ∩ (compOf ends M u) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, RandomCurrent.mem_sources]
  tauto









theorem gc7_componentEven_sources {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) (u : V) :
    Even (#((sources ends M) ∩ (compOf ends M u))) := by
  rw [← gc7_oddComp_eq_sources_inter]
  exact gc7_componentEven_abstract ends M hnd u


















theorem gc7_componentEven (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) (u : V) :
    Even (#((compOf (endsM G m) M u).filter (fun x => Odd (degK (endsM G m) M x)))) :=
  gc7_componentEven_abstract (endsM G m) M (fun i _ => endsM_not_isDiag G m i) u







theorem gc7_componentEven_sources_edgeCopy (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) (u : V) :
    Even (#((sources (endsM G m) M) ∩ (compOf (endsM G m) M u))) :=
  gc7_componentEven_sources (endsM G m) M (fun i _ => endsM_not_isDiag G m i) u


















theorem gc7_total_handshake {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) :
    Even (#(sources ends M)) := by
  
  
  have hsum : Even (∑ x : V, degK ends M x) := by
    
    have hrw : ∑ x : V, degK ends M x
        = ∑ i ∈ M, #((Finset.univ : Finset V).filter (fun x => x ∈ ends i)) := by
      unfold degK
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hrw]
    refine Finset.even_sum _ (fun i hi => ?_)
    
    obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
    have hne : a ≠ b := by
      intro h; subst h; exact hnd i hi (hab ▸ Sym2.mk_isDiag_iff.2 rfl)
    have hset : (Finset.univ : Finset V).filter (fun x => x ∈ ends i) = {a, b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hab, Sym2.mem_iff,
        Finset.mem_insert, Finset.mem_singleton]
    rw [hset, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    exact ⟨1, rfl⟩
  
  have hcount := (even_sum_iff_even_count (Finset.univ : Finset V) (degK ends M)).1 hsum
  have heq : (Finset.univ : Finset V).filter (fun x => Odd (degK ends M x)) = sources ends M := by
    ext x; simp [RandomCurrent.mem_sources]
  rwa [heq] at hcount



theorem gc7_total_handshake_edgeCopy (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) :
    Even (#(sources (endsM G m) M)) :=
  gc7_total_handshake (endsM G m) M (fun i _ => endsM_not_isDiag G m i)


















theorem gc7_componentEven_pair {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {u v : V}
    (hu_odd : Odd (degK ends M u))
    (hbdry : ∀ x, Odd (degK ends M x) → x = u ∨ x = v)
    (huv : u ≠ v) :
    v ∈ compOf ends M u := by
  have heven := gc7_componentEven_abstract ends M hnd u
  have hu_in : u ∈ compOf ends M u := by rw [mem_compOf]; exact Relation.ReflTransGen.refl
  by_contra hcon
  
  have hoddC : (compOf ends M u).filter (fun x => Odd (degK ends M x)) = {u} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxC, hxodd⟩
      rcases hbdry x hxodd with h | h
      · exact h
      · subst h; exact absurd hxC hcon
    · rintro rfl; exact ⟨hu_in, hu_odd⟩
  rw [hoddC, Finset.card_singleton] at heven
  exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) heven

end StatMech.Walls
