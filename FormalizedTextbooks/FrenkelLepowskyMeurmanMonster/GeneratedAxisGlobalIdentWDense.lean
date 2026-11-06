/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctadFastDense
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWCore

/-! # Factory: a low-memory self octad sum for dense targets (gident2)

The collapsed octad self sum `selfOctZ V` (the sum of the squares of the octad coordinates of
`V`) is the middle field of two big-number products: the octad terms packed at their field
indices `64 o + e` and at the reversed indices `65535 - (64 o + e)` (`selfOctM`, with gtenth's
`OctadDense.octMidDot`).  This replaces the per-term field reads of `selfOctP`, whose kernel
memory grows with the number of octad terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-- The octad terms of a representation at reversed field indices. -/
def octRevFlat (V : IdentVec) : List (ℕ × ℤ) := (octLFlat V).map (fun p => (65535 - p.1, p.2))

/-- The applicability check of the multiplicative self octad sum at field width `w`. -/
def selfOctMOk (w : ℕ) (V : IdentVec) : Bool :=
  (octLFlat V).all (fun p => decide (p.1 < 2 ^ 16)) &&
    decide (2 * (2 * 65536 * ((absSum (octLFlat V) + 1) * (absSum (octLFlat V) + 1))) < 2 ^ w)

/-- The multiplicative self octad sum (falls back to the collapsed sum). -/
def selfOctM (w : ℕ) (V : IdentVec) : ℤ :=
  if selfOctMOk w V then
    OctadDense.octMidDot w (packH w 10 16 (octLFlat V)) (packH w 10 16 (octRevFlat V))
  else selfOctZ V

/-- A weighted sum of index sums over a range containing all indices. -/
theorem sum_mul_idxSum (f : ℕ → ℤ) (N : ℕ) : ∀ l : List (ℕ × ℤ), (∀ p ∈ l, p.1 < N) →
    ∑ i ∈ Finset.range N, f i * idxSum l i = (l.map (fun p => p.2 * f p.1)).sum
  | [], _ => by simp [idxSum]
  | p :: l, h => by
    have ih := sum_mul_idxSum f N l (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    have hs : ∀ i, idxSum (p :: l) i = (if p.1 = i then p.2 else 0) + idxSum l i := by
      intro i
      simp [idxSum]
    simp only [hs, mul_add, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [Finset.sum_eq_single p.1]
    · rw [ite_eq_left rfl]
      ring
    · intro i _ hne
      rw [ite_eq_right (Ne.symm hne), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hp) hnot

/-- Index sums at reversed indices. -/
theorem idxSum_rev (l : List (ℕ × ℤ)) (h : ∀ p ∈ l, p.1 < 65536) (i : ℕ) (hi : i < 65536) :
    idxSum (l.map (fun p => (65535 - p.1, p.2))) (65535 - i) = idxSum l i := by
  unfold idxSum
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have := h p hp
  simp only [Function.comp_apply]
  congr 1
  apply propext
  omega

/-- The multiplicative self octad sum is the collapsed octad self sum. -/
theorem selfOctM_eq (w : ℕ) (V : IdentVec) : selfOctM w V = selfOctZ V := by
  unfold selfOctM
  split_ifs with h
  · simp only [selfOctMOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    set S := absSum (octLFlat V) with hSdef
    have hS : S < 2 ^ w := by
      have : S < (S + 1) * (S + 1) := by nlinarith
      omega
    have hrev : ∀ p ∈ octRevFlat V, p.1 < 2 ^ 16 := by
      intro p hp
      unfold octRevFlat at hp
      rw [List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      simp only
      norm_num
      omega
    have hSr : absSum (octRevFlat V) = S := by
      unfold octRevFlat absSum
      rw [List.map_map]
      rfl
    obtain ⟨a1, a2⟩ := packH_spec w 10 16 (octLFlat V) h1 hS
    obtain ⟨b1, b2⟩ := packH_spec w 10 16 (octRevFlat V) hrev (by rw [hSr]; exact hS)
    rw [hSr] at b1
    have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    rw [e16] at a1 b1 a2 b2 h1
    rw [OctadDense.octMidDot_eq a1 b1 (by nlinarith)]
    have hterm : ∀ i ∈ Finset.range 65536,
        sval w (packH w 10 16 (octLFlat V)) i * sval w (packH w 10 16 (octRevFlat V)) (65535 - i) =
          idxSum (octLFlat V) i * idxSum (octLFlat V) i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [a2 i hi', b2 (65535 - i) (by omega)]
      unfold octRevFlat
      rw [idxSum_rev _ h1 i hi']
    rw [Finset.sum_congr rfl hterm, sum_mul_idxSum _ 65536 _ h1]
    rfl
  · rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
