/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Minimum Golay weight determines the code supported on an octad and two extra points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Each coordinate occurs twice among the three nonzero words of a binary plane. -/
theorem binary_three_weight_bound : ∀ a b : ZMod 2,
    a.val + b.val + (a+b).val ≤ 2 := by
  decide +kernel

/-- A Golay code supported on fewer than twelve points has dimension at most one. -/
theorem golayCode_supported_eleven_span
    (S : Finset (Fin 24)) (hS : S.card ≤ 11)
    (a c : Fin 24 → ZMod 2) (ha : a ∈ golayCode) (hc : c ∈ golayCode)
    (ha0 : a ≠ 0)
    (has : ∀ i, i ∉ S → a i = 0) (hcs : ∀ i, i ∉ S → c i = 0) :
    c = 0 ∨ c = a := by
  by_contra h
  simp only [not_or] at h
  have hac0 : a+c ≠ 0 := by
    intro hz
    have he := congrArg (fun z : Fin 24 → ZMod 2 => z+c) hz
    have he' : a = c := by
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using he
    exact h.2 he'.symm
  have h1 := golayCode_weight_ge_eight a ha ha0
  have h2 := golayCode_weight_ge_eight c hc h.1
  have h3 := golayCode_weight_ge_eight (a+c) (golayCode.add_mem ha hc) hac0
  have hpoint (i : Fin 24) :
      (a i).val + (c i).val + ((a+c) i).val ≤ if i ∈ S then 2 else 0 := by
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, Pi.add_apply]
      exact binary_three_weight_bound _ _
    · simp [has i hi, hcs i hi, hi]
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hr : (∑ i : Fin 24, if i ∈ S then (2 : ℕ) else 0) = 2*S.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp [Nat.mul_comm]
  rw [hr] at htotal
  simp only [Finset.sum_add_distrib] at htotal
  omega

/-- The only codewords supported on an octad and at most two additional points
are zero and that octad's actual codeword. -/
theorem golayCode_supported_octad_extra
    (o : Fin 759) (E : Finset (Fin 24)) (hE : E.card ≤ 2)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hcs : ∀ i, i ∉ golayOctadSupport o ∪ E → c i = 0) :
    c = 0 ∨ c = golayOctadWord o := by
  have hS : (golayOctadSupport o ∪ E).card ≤ 11 := by
    have hu := Finset.card_union_le (golayOctadSupport o) E
    rw [golayOctadSupport_card] at hu
    omega
  have hn : golayOctadWord o ≠ 0 := by
    intro hz
    have hw := golayOctadWord_weight o
    rw [hz] at hw
    norm_num at hw
  have has : ∀ i, i ∉ golayOctadSupport o ∪ E → golayOctadWord o i = 0 := by
    intro i hi
    by_contra hn
    exact hi (Finset.mem_union_left E ((golayOctadWord_ne_zero_iff o i).mp hn))
  exact golayCode_supported_eleven_span (golayOctadSupport o ∪ E) hS
    (golayOctadWord o) c (golayOctadWord_mem_code o) hc hn has hcs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
