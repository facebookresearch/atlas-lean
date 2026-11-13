/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.ClaimIsing
import Code.Sharpness.TwoReplica
import Code.Sharpness.Switching
import Code.Sharpness.MultiReplica

open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]






noncomputable def notConnCompK (ends : ι → Sym2 V) (m : Finset ι) (o : V) : Finset V :=
  (Finset.univ : Finset V).filter (fun w => ¬ connK ends m o w)

theorem mem_notConnCompK {ends : ι → Sym2 V} {m : Finset ι} {o w : V} :
    w ∈ notConnCompK ends m o ↔ ¬ connK ends m o w := by
  simp [notConnCompK]




def edgeInsideK (ends : ι → Sym2 V) (S : Finset V) (i : ι) : Prop := ∀ w ∈ ends i, w ∈ S




def NoCrossingK (ends : ι → Sym2 V) (m : Finset ι) (S : Finset V) : Prop :=
  ∀ i ∈ m, edgeInsideK ends S i ∨ edgeInsideK ends Sᶜ i








theorem noCrossingK_of_event (ends : ι → Sym2 V) (m : Finset ι) (S : Finset V) (o : V)
    (_ho : o ∉ S) (hev : notConnCompK ends m o = S) : NoCrossingK ends m S := by
  intro i hi
  obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · left; intro w hw; rw [← hab, Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
  · 
    exfalso
    by_cases hab' : a = b
    · subst hab'; exact hb ha
    · have hadj : adjStep ends m a b :=
        ⟨i, hi, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hab'⟩
      have hbo : connK ends m o b := by
        by_contra hc; exact hb (hev ▸ (mem_notConnCompK).mpr hc)
      have hao : connK ends m o a :=
        Relation.ReflTransGen.tail hbo (adjStep_symm ends m hadj)
      exact ((mem_notConnCompK (o := o) (w := a)).not.mpr (not_not.mpr hao)) (hev ▸ ha)
  · 
    exfalso
    by_cases hab' : a = b
    · subst hab'; exact ha hb
    · have hadj : adjStep ends m a b :=
        ⟨i, hi, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hab'⟩
      have hao : connK ends m o a := by
        by_contra hc; exact ha (hev ▸ (mem_notConnCompK).mpr hc)
      have hbo : connK ends m o b := Relation.ReflTransGen.tail hao hadj
      exact ((mem_notConnCompK (o := o) (w := b)).not.mpr (not_not.mpr hbo)) (hev ▸ hb)
  · right; intro w hw; rw [Finset.mem_compl]; rw [← hab, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption











noncomputable def srcPairFamily (ends : ι → Sym2 V) (A B : Finset V) (F : Finset ι → ℝ) : ℝ :=
  ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A ∆ B)),
    (∑ _K ∈ m.powerset.filter
        (fun K => sources ends K = A ∧ sources ends (m \ K) = B), F m)

















theorem sc1_pair_switching (ends : ι → Sym2 V)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (A : Finset V) {u v : V} (huv : u ≠ v) (F : Finset ι → ℝ) :
    srcPairFamily ends (A ∆ {u, v}) {u, v} F
      = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A),
              F m * (if connK ends m u v then 1 else 0)) := by
  unfold srcPairFamily
  
  rw [symmDiff_symmDiff_cancel_right]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_filter, Finset.mem_powerset] at hm
  have hmA : sources ends m = A := hm.2
  
  have hfilter : (m.powerset.filter
      (fun K => sources ends K = (A ∆ {u, v}) ∧ sources ends (m \ K) = {u, v}))
      = m.powerset.filter (fun K => sources ends K = A ∆ {u, v}) := by
    apply Finset.filter_congr
    intro K hKp
    rw [Finset.mem_powerset] at hKp
    refine ⟨fun h => h.1, fun h1 => ⟨h1, ?_⟩⟩
    
    have hsd : m \ K = m ∆ K := by
      ext z; simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
      refine ⟨fun ⟨hmx, hkx⟩ => Or.inl ⟨hmx, hkx⟩, ?_⟩
      rintro (⟨hmx, hkx⟩ | ⟨hkx, hmx⟩)
      · exact ⟨hmx, hkx⟩
      · exact absurd (hKp hkx) hmx
    rw [hsd, sources_symmDiff, hmA, h1, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
  rw [hfilter]
  exact switching_lemma ends m (fun i _ => hnd i) A hmA huv F





theorem sc1_source_set_eq {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x} : Finset V) ∆ {y, g} = {o, g} ∆ {x, y} := by
  ext z
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hzo : z = o <;> by_cases hzx : z = x <;> by_cases hzy : z = y <;>
    by_cases hzg : z = g <;> subst_vars <;> simp_all























theorem sc1_claim1_switching (ends : ι → Sym2 V)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (o x y g : V) (S : Finset V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    srcPairFamily ends ({o, g} ∆ {x, y}) {y, g}
        (fun m => if notConnCompK ends m o = S then 1 else 0)
      = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = {o, x})),
          (∑ _K ∈ m.powerset.filter (fun K => sources ends K = {o, x}),
              (if notConnCompK ends m o = S then 1 else 0)
                * (if connK ends m y g then 1 else 0)) := by
  rw [← sc1_source_set_eq hox hoy hog hxy hxg hyg]
  exact sc1_pair_switching ends hnd {o, x} hyg
    (fun m => if notConnCompK ends m o = S then 1 else 0)

end RandomCurrent

end Sharpness

end StatMech
