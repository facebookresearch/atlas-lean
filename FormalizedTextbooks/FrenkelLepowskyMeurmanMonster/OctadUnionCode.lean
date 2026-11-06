/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The minimum Golay weight bounds the code supported on a twelve-point union. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairQProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- In a binary three-dimensional span, each coordinate occurs at most four times. -/
theorem binary_seven_weight_bound : ∀ a b c : ZMod 2,
    a.val + b.val + (a+b).val + c.val + (a+c).val + (b+c).val + (a+b+c).val ≤ 4 := by
  decide +kernel

/-- A Golay code supported on at most twelve coordinates has dimension at most two:
any third word belongs to the span of two distinct nonzero words. -/
theorem golayCode_supported_twelve_span
    (S : Finset (Fin 24)) (hS : S.card ≤ 12)
    (a b c : Fin 24 → ZMod 2)
    (ha : a ∈ golayCode) (hb : b ∈ golayCode) (hc : c ∈ golayCode)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (has : ∀ i, i ∉ S → a i = 0)
    (hbs : ∀ i, i ∉ S → b i = 0)
    (hcs : ∀ i, i ∉ S → c i = 0) :
    c = 0 ∨ c = a ∨ c = b ∨ c = a+b := by
  by_contra h
  simp only [not_or] at h
  have hsum0 (x y : Fin 24 → ZMod 2) : x+y = 0 ↔ x=y := by
    constructor
    · intro hxy
      have hz := congrArg (fun z => z+y) hxy
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hz
    · rintro rfl
      exact ZModModule.add_self x
  have hab0 : a+b ≠ 0 := (hsum0 a b).not.mpr hab
  have hac0 : a+c ≠ 0 := by
    exact (hsum0 a c).not.mpr (Ne.symm h.2.1)
  have hbc0 : b+c ≠ 0 := by
    exact (hsum0 b c).not.mpr (Ne.symm h.2.2.1)
  have habc0 : a+b+c ≠ 0 := by
    exact (hsum0 (a+b) c).not.mpr (Ne.symm h.2.2.2)
  have h1 := golayCode_weight_ge_eight a ha ha0
  have h2 := golayCode_weight_ge_eight b hb hb0
  have h3 := golayCode_weight_ge_eight (a+b) (golayCode.add_mem ha hb) hab0
  have h4 := golayCode_weight_ge_eight c hc h.1
  have h5 := golayCode_weight_ge_eight (a+c) (golayCode.add_mem ha hc) hac0
  have h6 := golayCode_weight_ge_eight (b+c) (golayCode.add_mem hb hc) hbc0
  have h7 := golayCode_weight_ge_eight (a+b+c)
    (golayCode.add_mem (golayCode.add_mem ha hb) hc) habc0
  have hpoint (i : Fin 24) :
      (a i).val + (b i).val + ((a+b) i).val + (c i).val +
        ((a+c) i).val + ((b+c) i).val + ((a+b+c) i).val ≤
          if i ∈ S then 4 else 0 := by
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, Pi.add_apply]
      exact binary_seven_weight_bound _ _ _
    · simp [has i hi, hbs i hi, hcs i hi, hi]
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hr : (∑ i : Fin 24, if i ∈ S then (4 : ℕ) else 0) = 4*S.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp [Nat.mul_comm]
  rw [hr] at htotal
  simp only [Finset.sum_add_distrib] at htotal
  omega

/-- Zero syndrome is exactly membership in the actual Golay code. -/
theorem golaySyndrome_zero_iff_code (c : Fin 24 → ZMod 2) :
    golaySyndrome c = 0 ↔ c ∈ golayCode := by
  constructor
  · intro hz
    have hd := golayCodeCocode_decomposition c
    rw [hz, map_zero, sub_zero, add_zero] at hd
    exact hd.symm ▸ ⟨_, rfl⟩
  · rintro ⟨a, rfl⟩
    exact golaySyndrome_encoder a

/-- On a twelve-coordinate support, equal syndrome means that two binary
patterns differ by one of the four words in the two-octad span. -/
theorem golaySyndrome_supported_twelve_affine
    (S : Finset (Fin 24)) (hS : S.card ≤ 12)
    (a b c t : Fin 24 → ZMod 2)
    (ha : a ∈ golayCode) (hb : b ∈ golayCode)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (has : ∀ i, i ∉ S → a i = 0)
    (hbs : ∀ i, i ∉ S → b i = 0)
    (hcs : ∀ i, i ∉ S → c i = 0)
    (hts : ∀ i, i ∉ S → t i = 0) :
    golaySyndrome c = golaySyndrome t ↔
      c+t = 0 ∨ c+t = a ∨ c+t = b ∨ c+t = a+b := by
  have hzero : golaySyndrome c = golaySyndrome t ↔ golaySyndrome (c+t) = 0 := by
    rw [map_add]
    constructor
    · intro h
      rw [h, ZModModule.add_self]
    · intro h
      have hz := congrArg (fun z => z+golaySyndrome t) h
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hz
  rw [hzero, golaySyndrome_zero_iff_code]
  constructor
  · intro hc
    apply golayCode_supported_twelve_span S hS a b (c+t) ha hb hc ha0 hb0 hab has hbs
    intro i hi
    simp [hcs i hi, hts i hi]
  · intro h
    rcases h with h | h | h | h <;> rw [h]
    · exact golayCode.zero_mem
    · exact ha
    · exact hb
    · exact golayCode.add_mem ha hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
