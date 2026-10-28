/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWCore
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # The odd self part of a dense target with distinct labels (r8f)

The factory's odd self part `selfOddP W` reads a packed table of `2^16` fields once per odd term;
for dense targets (more than 20000 odd terms) the kernel keeps every shifted copy of the table and
exceeds the memory budget.  When the odd labels of `W` are pairwise distinct (as for every
transported list of the factory), the collapsed odd self sum is the sum of the squares of the odd
values (`selfOddZ_of_distinct`).  Distinctness is checked by one pass over the labels that sets
and tests one bit per label in a growing bitmap (`labDistinct`, `labDistinct_spec`).  The odd part
`oddWZ` of the pairing against a listed target is additive over groups of target terms
(`oddWZ_ofList`, `oddSumF_append`), so that it can be evaluated group by group. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Bitmap check: the labels of a term list are pairwise distinct and avoid the bits of `bm`. -/
def labDistinct : List (ℕ × ℤ) → ℕ → Bool
  | [], _ => true
  | q :: qs, bm => !bm.testBit q.1 && labDistinct qs (bm ||| 1 <<< q.1)

/-- A successful bitmap check gives pairwise distinct labels. -/
theorem labDistinct_spec : ∀ (L : List (ℕ × ℤ)) (bm : ℕ), labDistinct L bm = true →
    (∀ q ∈ L, bm.testBit q.1 = false) ∧ (L.map Prod.fst).Nodup
  | [], _, _ => ⟨by simp, List.nodup_nil⟩
  | q :: qs, bm, h => by
    simp only [labDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := labDistinct_spec qs _ h2
    have hq : ∀ r ∈ qs, bm.testBit r.1 = false ∧ r.1 ≠ q.1 := by
      intro r hr
      have := ih1 r hr
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
      refine ⟨this.1, fun he => ?_⟩
      have h2 := this.2
      rw [he, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at h2
      exact Bool.noConfusion h2
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h1
      · exact (hq r hr).1
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih2⟩
      obtain ⟨r, hr, hrq⟩ := List.mem_map.mp hm
      exact (hq r hr).2 hrq

/-- The index sum of an absent label vanishes. -/
theorem idxSum_of_not_mem (L : List (ℕ × ℤ)) (i : ℕ) (h : i ∉ L.map Prod.fst) :
    idxSum L i = 0 := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    simp only [idxSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih h.2]
    simp [Ne.symm h.1]

/-- With pairwise distinct labels the index sum of a term is its value. -/
theorem idxSum_of_nodup (L : List (ℕ × ℤ)) (h : (L.map Prod.fst).Nodup) (q : ℕ × ℤ)
    (hq : q ∈ L) : idxSum L q.1 = q.2 := by
  induction L with
  | nil => simp at hq
  | cons p L ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hq with rfl | hq'
    · have h0 := idxSum_of_not_mem L q.1 h.1
      simp only [idxSum, List.map_cons, List.sum_cons] at h0 ⊢
      rw [h0]
      simp
    · have hne : p.1 ≠ q.1 := fun he => h.1 (he ▸ List.mem_map_of_mem hq')
      have := ih h.2 hq'
      simp only [idxSum, List.map_cons, List.sum_cons] at this ⊢
      rw [this]
      simp [hne]

/-- The sum of the squares of the values of a term list. -/
def sqSumZ (L : List (ℕ × ℤ)) : ℤ := (L.map (fun q => q.2 * q.2)).sum

/-- The collapsed odd self sum is the sum of squares when the odd labels are distinct. -/
theorem selfOddZ_of_distinct (V : IdentVec) (h : labDistinct V.sh.odd 0 = true) :
    selfOddZ V = sqSumZ V.sh.odd := by
  have hn := (labDistinct_spec _ _ h).2
  unfold selfOddZ sqSumZ
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [idxSum_of_nodup _ hn q hq]

/-! ## The odd part of the pairing in groups of target terms -/

/-- The odd part of the pairing over the odd terms of a term list. -/
def oddSumF (w : ℕ) (fwd : Bool) (X : List SVec) (T : List (ℕ × ℤ)) : ℤ :=
  ((T.filter (fun p => decide (49128 ≤ p.1))).map (fun q => q.2 * oddWTerm w fwd X q.1)).sum

/-- The odd part of the pairing is additive over concatenation. -/
theorem oddSumF_append (w : ℕ) (fwd : Bool) (X : List SVec) (A B : List (ℕ × ℤ)) :
    oddSumF w fwd X (A ++ B) = oddSumF w fwd X A + oddSumF w fwd X B := by
  unfold oddSumF
  rw [List.filter_append, List.map_append, List.sum_append]

/-- The odd part of the pairing against a target with a listed short block. -/
theorem oddWZ_ofList (w : ℕ) (fwd : Bool) (X : List SVec) (M : MatRep) (T : List (ℕ × ℤ))
    (d : ℚ) (t : GeneratedAxisGlobalRationalTensor) :
    oddWZ w fwd X ⟨M, ShortData.ofList T, d, t⟩ = oddSumF w fwd X T := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
