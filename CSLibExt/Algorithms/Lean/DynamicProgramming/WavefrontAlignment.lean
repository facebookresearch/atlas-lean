/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# The wavefront alignment algorithm for linear gap penalties

Global alignment in minimization form: a column of two equal letters costs `0`, a column of two
different letters costs `x = P.mismatch ≥ 1`, and every gap column costs `g = P.gap ≥ 1`. The
wavefront algorithm computes, for each score `s` and each diagonal `k = h - v` (`v` letters of
`xs` and `h` letters of `ys` consumed), a furthest-reaching offset `W(s, k)`:
`W(s, k) = slide (min (max (W(s - x, k) + 1) (W(s - g, k - 1) + 1) (W(s - g, k + 1)))
(maxOffset k))`, where `slide` follows matching letters along the diagonal, and it stops at the
first score whose wavefront reaches the end cell. A tabulated implementation therefore touches
only scores up to the optimal cost `D` and diagonals within `D / g` of the main diagonal, which
gives Ukkonen's `O(D · n)` bound for unit costs (`x = g = 1`; Myers 1986 for the
insertion/deletion-only variant); that running-time bound is not proved here. Marco-Sola et
al. (2021) introduced the gap-affine version of this recurrence (WFA); this module covers the
linear-gap case, where a gap column always costs `g`.

## Main results

* `Wavefront.wavefront_sound`: every wavefront offset is a valid cell reached by an alignment
  of the corresponding prefixes with cost at most `s`.
* `Wavefront.wavefront_complete`: every alignment of a pair of prefixes is dominated, on its
  diagonal, by the wavefront of its exact cost.
* `Wavefront.exists_wavefront_end_iff`: the end cell is reached by a score `s' ≤ s` iff some
  alignment costs at most `s`.
* `Wavefront.exists_wavefront_end_iff_nwScore`: hence the first score at which the wavefront
  reaches the end cell is the optimal Needleman–Wunsch cost
  `-nwScore P.score (-P.gap) xs ys`.

## Design notes

Offsets proposed by an operation are clamped to the largest valid offset of their diagonal
before sliding. Soundness of the clamp uses the monotonicity of the optimal prefix cost along a
diagonal, which holds for linear gap costs (removing the last letter of both prefixes never
increases the cost); for affine gaps it can fail, which is why the gap-affine WFA, whose
wavefronts carry the gap state, is not covered here. `wavefrontAux` is a fuel recursion
(`wavefront` supplies fuel `s + 1`) evaluated without memoization: the module proves the
recurrence's output, not the `O(D · n)` running time of a tabulated implementation.

## References

* E. Ukkonen, *Algorithms for approximate string matching*, Information and Control 64 (1985),
  100–118.
* E. W. Myers, *An O(ND) difference algorithm and its variations*, Algorithmica 1 (1986),
  251–266.
* S. Marco-Sola, J. C. Moure, M. Moreto and A. Espinosa, *Fast gap-affine pairwise alignment
  using the wavefront algorithm*, Bioinformatics 37 (2021), 456–463.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- Linear gap penalties: match `0`, mismatch `mismatch ≥ 1`, each gap column `gap ≥ 1`. -/
structure LinearPenalties where
  /-- Cost of a column pairing two different letters. -/
  mismatch : ℕ
  /-- Cost of a gap column. -/
  gap : ℕ
  /-- Mismatches cost at least one. -/
  mismatch_pos : 0 < mismatch
  /-- Gap columns cost at least one. -/
  gap_pos : 0 < gap

namespace LinearPenalties

variable (P : LinearPenalties) [DecidableEq α]

/-- The cost of one alignment column. -/
def columnCost : Option α × Option α → ℕ
  | (some a, some b) => if a = b then 0 else P.mismatch
  | (some _, none) => P.gap
  | (none, some _) => P.gap
  | (none, none) => 0

/-- The cost of an alignment: the sum of its column costs. -/
def cost (A : Alignment α) : ℕ := (A.map P.columnCost).sum

end LinearPenalties

namespace Wavefront

variable [DecidableEq α]

/-- The largest valid offset on diagonal `k`: `h ≤ |ys|` and `v = h - k ≤ |xs|`. -/
def maxOffset (xs ys : List α) (k : ℤ) : ℤ := min (ys.length : ℤ) (xs.length + k)

/-- Follow matching letters along diagonal `k` from offset `h`, with fuel. -/
def extend (xs ys : List α) (k : ℤ) : ℕ → ℤ → ℤ
  | 0, h => h
  | fuel + 1, h =>
      if h < maxOffset xs ys k ∧ xs[(h - k).toNat]? = ys[h.toNat]? then
        extend xs ys k fuel (h + 1)
      else h

/-- The match extension ("slide") along diagonal `k` from offset `h`. -/
def slide (xs ys : List α) (k h : ℤ) : ℤ := extend xs ys k (ys.length + 1) h

/-- The wavefront recurrence with fuel (fuel `s + 1` suffices; see `wavefront`).
`none` stands for an unreachable diagonal. Offsets proposed by an operation are clamped to the
largest valid offset of the target diagonal before sliding. -/
def wavefrontAux (P : LinearPenalties) (xs ys : List α) : ℕ → ℕ → ℤ → Option ℤ
  | 0, _, _ => none
  | fuel + 1, s, k =>
      if s = 0 then (if k = 0 then some (slide xs ys 0 0) else none)
      else if k < -(xs.length : ℤ) ∨ (ys.length : ℤ) < k then none
      else
        let fromMismatch : Option ℤ :=
          if P.mismatch ≤ s then (wavefrontAux P xs ys fuel (s - P.mismatch) k).map (· + 1)
          else none
        let fromInsertion : Option ℤ :=
          if P.gap ≤ s then (wavefrontAux P xs ys fuel (s - P.gap) (k - 1)).map (· + 1)
          else none
        let fromDeletion : Option ℤ :=
          if P.gap ≤ s then wavefrontAux P xs ys fuel (s - P.gap) (k + 1) else none
        (max fromMismatch (max fromInsertion fromDeletion)).map
          (fun h => slide xs ys k (min h (maxOffset xs ys k)))

/-- The furthest-reaching offset of score `s` on diagonal `k = h - v`. -/
def wavefront (P : LinearPenalties) (xs ys : List α) (s : ℕ) (k : ℤ) : Option ℤ :=
  wavefrontAux P xs ys (s + 1) s k

private theorem aux_fuel (P : LinearPenalties) (xs ys : List α) (s f₁ f₂ : ℕ)
    (hf₁ : s + 1 ≤ f₁) (hf₂ : s + 1 ≤ f₂) (k : ℤ) :
    wavefrontAux P xs ys f₁ s k = wavefrontAux P xs ys f₂ s k := by
  induction s using Nat.strong_induction_on generalizing f₁ f₂ k with
  | h s ih =>
    obtain ⟨f₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f₁ ≠ 0)
    obtain ⟨f₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f₂ ≠ 0)
    by_cases hs : s = 0
    · simp [wavefrontAux, hs]
    by_cases hk : k < -(xs.length : ℤ) ∨ (ys.length : ℤ) < k
    · simp [wavefrontAux, hs, hk]
    have hm : P.mismatch ≤ s →
        wavefrontAux P xs ys f₁ (s - P.mismatch) k =
          wavefrontAux P xs ys f₂ (s - P.mismatch) k := by
      intro hp
      have := P.mismatch_pos
      exact ih _ (by omega) _ _ (by omega) (by omega) _
    have hg (j : ℤ) : P.gap ≤ s →
        wavefrontAux P xs ys f₁ (s - P.gap) j =
          wavefrontAux P xs ys f₂ (s - P.gap) j := by
      intro hp
      have := P.gap_pos
      exact ih _ (by omega) _ _ (by omega) (by omega) _
    simp only [wavefrontAux, ite_eq_right hs, ite_eq_right hk]
    by_cases hx : P.mismatch ≤ s <;> by_cases hg' : P.gap ≤ s <;>
      simp [hx, hg', hm, hg]

private theorem aux_eq (P : LinearPenalties) (xs ys : List α) (s f : ℕ)
    (hf : s + 1 ≤ f) (k : ℤ) :
    wavefrontAux P xs ys f s k = wavefront P xs ys s k :=
  aux_fuel P xs ys s f (s + 1) hf le_rfl k

private theorem recurrence (P : LinearPenalties) (xs ys : List α) (s : ℕ) (k : ℤ) :
    wavefront P xs ys s k =
      if s = 0 then (if k = 0 then some (slide xs ys 0 0) else none)
      else if k < -(xs.length : ℤ) ∨ (ys.length : ℤ) < k then none
      else
        (max (if P.mismatch ≤ s then (wavefront P xs ys (s - P.mismatch) k).map
            (· + 1) else none)
          (max (if P.gap ≤ s then (wavefront P xs ys (s - P.gap) (k - 1)).map
              (· + 1) else none)
            (if P.gap ≤ s then wavefront P xs ys (s - P.gap) (k + 1) else none))).map
          (fun h => slide xs ys k (min h (maxOffset xs ys k))) := by
  rw [wavefront, wavefrontAux]
  by_cases hs : s = 0
  · simp [hs]
  by_cases hk : k < -(xs.length : ℤ) ∨ (ys.length : ℤ) < k
  · simp [hs, hk]
  have hm : P.mismatch ≤ s →
      wavefrontAux P xs ys s (s - P.mismatch) k =
        wavefront P xs ys (s - P.mismatch) k := by
    intro hp
    exact aux_eq P xs ys _ _ (by have := P.mismatch_pos; omega) _
  have hg (j : ℤ) : P.gap ≤ s →
      wavefrontAux P xs ys s (s - P.gap) j =
        wavefront P xs ys (s - P.gap) j := by
    intro hp
    exact aux_eq P xs ys _ _ (by have := P.gap_pos; omega) _
  simp only [ite_eq_right hs, ite_eq_right hk]
  by_cases hx : P.mismatch ≤ s <;> by_cases hg' : P.gap ≤ s <;>
    simp [hx, hg', hm, hg]

private theorem extend_bounds (xs ys : List α) (k h : ℤ) (f : ℕ)
    (hu : h ≤ maxOffset xs ys k) :
    h ≤ extend xs ys k f h ∧ extend xs ys k f h ≤ maxOffset xs ys k := by
  induction f generalizing h with
  | zero => simp [extend, hu]
  | succ f ih =>
    rw [extend]
    split_ifs with he
    · obtain ⟨hl, hu'⟩ := ih (h + 1) (by omega)
      exact ⟨by omega, hu'⟩
    · exact ⟨le_rfl, hu⟩

private theorem extend_closed (xs ys : List α) (k h : ℤ) (f : ℕ)
    (hu : h ≤ maxOffset xs ys k) (hf : maxOffset xs ys k - h < (f : ℤ)) :
    ¬(extend xs ys k f h < maxOffset xs ys k ∧
      xs[(extend xs ys k f h - k).toNat]? = ys[(extend xs ys k f h).toNat]?) := by
  induction f generalizing h with
  | zero => omega
  | succ f ih =>
    rw [extend]
    split_ifs with he
    · exact ih (h + 1) (by omega) (by omega)
    · exact he

private theorem slide_bounds (xs ys : List α) (k h : ℤ)
    (hu : h ≤ maxOffset xs ys k) :
    h ≤ slide xs ys k h ∧ slide xs ys k h ≤ maxOffset xs ys k :=
  extend_bounds xs ys k h _ hu

private theorem slide_closed (xs ys : List α) (k h : ℤ)
    (hl : 0 ≤ h) (hu : h ≤ maxOffset xs ys k) :
    ¬(slide xs ys k h < maxOffset xs ys k ∧
      xs[(slide xs ys k h - k).toNat]? = ys[(slide xs ys k h).toNat]?) := by
  apply extend_closed xs ys k h _ hu
  have hm : maxOffset xs ys k ≤ (ys.length : ℤ) := min_le_left _ _
  omega

omit [DecidableEq α] in
private theorem align_append (A B : Alignment α) (xs ys xs' ys' : List α)
    (ha : IsAlignment A xs ys) (hb : IsAlignment B xs' ys') :
    IsAlignment (A ++ B) (xs ++ xs') (ys ++ ys') := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ha.1 c hc
    · exact hb.1 c hc
  · simp [List.filterMap_append, ha.2.1, hb.2.1]
  · simp [List.filterMap_append, ha.2.2, hb.2.2]

omit [DecidableEq α] in
private theorem align_reverse (A : Alignment α) (xs ys : List α)
    (ha : IsAlignment A xs ys) : IsAlignment A.reverse xs.reverse ys.reverse := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    exact ha.1 c (List.mem_reverse.mp hc)
  · simp [List.filterMap_reverse, ha.2.1]
  · simp [List.filterMap_reverse, ha.2.2]

private theorem cost_reverse (P : LinearPenalties) (A : Alignment α) :
    P.cost A.reverse = P.cost A := by
  simp [LinearPenalties.cost, List.map_reverse, List.sum_reverse]

omit [DecidableEq α] in
private theorem align_swap (A : Alignment α) (xs ys : List α)
    (ha : IsAlignment A xs ys) : IsAlignment (A.map Prod.swap) ys xs := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    intro he
    apply ha.1 d hd
    exact Prod.swap_injective (by simpa using he)
  · simpa [List.filterMap_map, Function.comp_def] using ha.2.2
  · simpa [List.filterMap_map, Function.comp_def] using ha.2.1

private theorem cost_swap (P : LinearPenalties) (A : Alignment α) :
    P.cost (A.map Prod.swap) = P.cost A := by
  have hc (c : Option α × Option α) : P.columnCost c.swap = P.columnCost c := by
    rcases c with ⟨a, b⟩
    cases a <;> cases b <;> simp [LinearPenalties.columnCost, eq_comm]
  simp [LinearPenalties.cost, List.map_map, Function.comp_def, hc]

private theorem remove_left (P : LinearPenalties) (A : Alignment α)
    (a : α) (xs ys : List α) (ha : IsAlignment A (a :: xs) ys) :
    ∃ B, IsAlignment B xs ys ∧ P.cost B ≤ P.cost A + P.gap := by
  induction A generalizing a xs ys with
  | nil => simp [IsAlignment] at ha
  | cons c A ih =>
    rcases c with ⟨l, r⟩
    have ht : ∀ c ∈ A, c ≠ (none, none) := fun c hc => ha.1 c (by simp [hc])
    cases l with
    | none =>
      cases r with
      | none => exact False.elim (ha.1 _ (by simp) rfl)
      | some b =>
        have hx : A.filterMap Prod.fst = a :: xs := by simpa using ha.2.1
        have hy : b :: A.filterMap Prod.snd = ys := by simpa using ha.2.2
        obtain ⟨B, hb, hc⟩ := ih a xs (A.filterMap Prod.snd) ⟨ht, hx, rfl⟩
        refine ⟨(none, some b) :: B, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro d hd; simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · simp
            · exact hb.1 d hd
          · simpa using hb.2.1
          · simpa [hb.2.2] using hy
        · simp only [LinearPenalties.cost, List.map_cons, List.sum_cons,
            LinearPenalties.columnCost] at *
          omega
    | some b =>
      have hx : b = a ∧ A.filterMap Prod.fst = xs := by simpa using ha.2.1
      cases r with
      | none =>
        refine ⟨A, ⟨ht, hx.2, ?_⟩, ?_⟩
        · simpa using ha.2.2
        · simp [LinearPenalties.cost, LinearPenalties.columnCost]; omega
      | some d =>
        have hy : d :: A.filterMap Prod.snd = ys := by simpa using ha.2.2
        refine ⟨(none, some d) :: A, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro c hc; simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · simp
          · exact ht c hc
        · simpa using hx.2
        · simpa using hy
        · simp [LinearPenalties.cost, LinearPenalties.columnCost]; omega

private theorem remove_last_left (P : LinearPenalties) (A : Alignment α)
    (a : α) (xs ys : List α) (ha : IsAlignment A (xs ++ [a]) ys) :
    ∃ B, IsAlignment B xs ys ∧ P.cost B ≤ P.cost A + P.gap := by
  have hr := align_reverse A _ _ ha
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hr
  obtain ⟨B, hb, hc⟩ := remove_left P A.reverse a xs.reverse ys.reverse hr
  refine ⟨B.reverse, ?_, ?_⟩
  · simpa using align_reverse B _ _ hb
  · simpa only [cost_reverse] using hc

private theorem remove_last_right (P : LinearPenalties) (A : Alignment α)
    (a : α) (xs ys : List α) (ha : IsAlignment A xs (ys ++ [a])) :
    ∃ B, IsAlignment B xs ys ∧ P.cost B ≤ P.cost A + P.gap := by
  obtain ⟨B, hb, hc⟩ := remove_last_left P (A.map Prod.swap) a ys xs
    (align_swap A _ _ ha)
  refine ⟨B.map Prod.swap, align_swap B _ _ hb, ?_⟩
  simpa only [cost_swap] using hc

private theorem append_pair (P : LinearPenalties) (xs ys : List α) (k h : ℤ)
    (hl : max 0 k ≤ h) (hu : h < maxOffset xs ys k) (A : Alignment α)
    (ha : IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat)) :
    ∃ B, IsAlignment B (xs.take (h + 1 - k).toNat) (ys.take (h + 1).toNat) ∧
      P.cost B = P.cost A +
        P.columnCost (xs[(h - k).toNat]?, ys[h.toNat]?) := by
  have h0 : 0 ≤ h := le_trans (le_max_left _ _) hl
  have hk : k ≤ h := le_trans (le_max_right _ _) hl
  have hm := (lt_min_iff.mp hu)
  have hv : (h - k).toNat < xs.length := by omega
  have hh : h.toNat < ys.length := by omega
  have hvs : (h + 1 - k).toNat = (h - k).toNat + 1 := by omega
  have hhs : (h + 1).toNat = h.toNat + 1 := by omega
  let c : Option α × Option α := (some xs[(h - k).toNat], some ys[h.toNat])
  refine ⟨A ++ [c], ?_, ?_⟩
  · rw [hvs, hhs, List.take_succ_eq_append_getElem hv,
      List.take_succ_eq_append_getElem hh]
    apply align_append A [c] _ _ _ _ ha
    simp [IsAlignment, c]
  · simp [LinearPenalties.cost, c, List.getElem?_eq_getElem hv,
      List.getElem?_eq_getElem hh]

private theorem extend_align (P : LinearPenalties) (xs ys : List α) (k h : ℤ)
    (f : ℕ) (hl : max 0 k ≤ h) (hu : h ≤ maxOffset xs ys k) (A : Alignment α)
    (ha : IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat)) :
    ∃ B, IsAlignment B (xs.take (extend xs ys k f h - k).toNat)
      (ys.take (extend xs ys k f h).toNat) ∧ P.cost B = P.cost A := by
  induction f generalizing h A with
  | zero => exact ⟨A, ha, rfl⟩
  | succ f ih =>
    rw [extend]
    split_ifs with he
    · have hm := lt_min_iff.mp he.1
      have hk : k ≤ h := le_trans (le_max_right _ _) hl
      have h0 : 0 ≤ h := le_trans (le_max_left _ _) hl
      have hv : (h - k).toNat < xs.length := by omega
      have hh : h.toNat < ys.length := by omega
      obtain ⟨B, hb, hc⟩ := append_pair P xs ys k h hl he.1 A ha
      have eq : xs[(h - k).toNat] = ys[h.toNat] := by
        simpa only [List.getElem?_eq_getElem hv, List.getElem?_eq_getElem hh,
          Option.some.injEq] using he.2
      have hc' : P.cost B = P.cost A := by
        simpa [LinearPenalties.columnCost, List.getElem?_eq_getElem hv,
          List.getElem?_eq_getElem hh, eq] using hc
      obtain ⟨C, hC, hcost⟩ := ih (h + 1) (by omega) (by omega) B hb
      exact ⟨C, hC, hcost.trans hc'⟩
    · exact ⟨A, ha, rfl⟩

private theorem slide_align (P : LinearPenalties) (xs ys : List α) (k h : ℤ)
    (hl : max 0 k ≤ h) (hu : h ≤ maxOffset xs ys k) (A : Alignment α)
    (ha : IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat)) :
    ∃ B, IsAlignment B (xs.take (slide xs ys k h - k).toNat)
      (ys.take (slide xs ys k h).toNat) ∧ P.cost B = P.cost A :=
  extend_align P xs ys k h _ hl hu A ha

private theorem mismatch_candidate (P : LinearPenalties) (xs ys : List α)
    (k h : ℤ) (hl : max 0 k ≤ h) (hu : h ≤ maxOffset xs ys k) (A : Alignment α)
    (ha : IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat)) :
    max 0 k ≤ min (h + 1) (maxOffset xs ys k) ∧
      ∃ B, IsAlignment B (xs.take (min (h + 1) (maxOffset xs ys k) - k).toNat)
        (ys.take (min (h + 1) (maxOffset xs ys k)).toNat) ∧
        P.cost B ≤ P.cost A + P.mismatch := by
  refine ⟨le_min (by omega) (hl.trans hu), ?_⟩
  by_cases he : h < maxOffset xs ys k
  · have hc : min (h + 1) (maxOffset xs ys k) = h + 1 := min_eq_left (by omega)
    rw [hc]
    obtain ⟨B, hb, hcost⟩ := append_pair P xs ys k h hl he A ha
    refine ⟨B, hb, ?_⟩
    rw [hcost]
    apply Nat.add_le_add_left
    have hm := lt_min_iff.mp he
    have hk : k ≤ h := le_trans (le_max_right _ _) hl
    have h0 : 0 ≤ h := le_trans (le_max_left _ _) hl
    have hv : (h - k).toNat < xs.length := by omega
    have hh : h.toNat < ys.length := by omega
    simp only [List.getElem?_eq_getElem hv, List.getElem?_eq_getElem hh,
      LinearPenalties.columnCost]
    split_ifs <;> omega
  · have hc : min (h + 1) (maxOffset xs ys k) = h := by omega
    rw [hc]
    exact ⟨A, ha, Nat.le_add_right _ _⟩

private theorem insertion_candidate (P : LinearPenalties) (xs ys : List α)
    (k h : ℤ) (hb : -(xs.length : ℤ) ≤ k ∧ k ≤ (ys.length : ℤ))
    (hl : max 0 (k - 1) ≤ h) (hu : h ≤ maxOffset xs ys (k - 1)) (A : Alignment α)
    (ha : IsAlignment A (xs.take (h - (k - 1)).toNat) (ys.take h.toNat)) :
    max 0 k ≤ min (h + 1) (maxOffset xs ys k) ∧
      ∃ B, IsAlignment B (xs.take (min (h + 1) (maxOffset xs ys k) - k).toNat)
        (ys.take (min (h + 1) (maxOffset xs ys k)).toNat) ∧
        P.cost B ≤ P.cost A + P.gap := by
  have h0 : 0 ≤ h := le_trans (le_max_left _ _) hl
  have hk : k - 1 ≤ h := le_trans (le_max_right _ _) hl
  have hm := le_min_iff.mp hu
  have ht : max 0 k ≤ maxOffset xs ys k := by
    dsimp [maxOffset]
    exact le_min (max_le (by omega) hb.2) (max_le (by omega) (by omega))
  refine ⟨le_min (max_le (by omega) (by omega)) ht, ?_⟩
  by_cases he : h < (ys.length : ℤ)
  · have hc : min (h + 1) (maxOffset xs ys k) = h + 1 := by
      simp only [maxOffset] at *
      omega
    rw [hc]
    have hh : h.toNat < ys.length := by omega
    have hhs : (h + 1).toNat = h.toNat + 1 := by omega
    have hvs : h + 1 - k = h - (k - 1) := by omega
    let c : Option α × Option α := (none, some ys[h.toNat])
    refine ⟨A ++ [c], ?_, ?_⟩
    · rw [hvs, hhs, List.take_succ_eq_append_getElem hh]
      simpa only [List.append_nil] using align_append A [c] _ _ [] [ys[h.toNat]] ha
        (by simp [IsAlignment, c])
    · simp [LinearPenalties.cost, LinearPenalties.columnCost, c]
  · have hY : h = (ys.length : ℤ) := by omega
    have hc : min (h + 1) (maxOffset xs ys k) = h := by
      simp only [maxOffset] at *
      omega
    rw [hc]
    have hv : (h - k).toNat < xs.length := by omega
    have hvs : (h - (k - 1)).toNat = (h - k).toNat + 1 := by omega
    rw [hvs, List.take_succ_eq_append_getElem hv] at ha
    exact remove_last_left P A xs[(h - k).toNat] _ _ ha

private theorem deletion_candidate (P : LinearPenalties) (xs ys : List α)
    (k h : ℤ) (hb : -(xs.length : ℤ) ≤ k ∧ k ≤ (ys.length : ℤ))
    (hl : max 0 (k + 1) ≤ h) (hu : h ≤ maxOffset xs ys (k + 1)) (A : Alignment α)
    (ha : IsAlignment A (xs.take (h - (k + 1)).toNat) (ys.take h.toNat)) :
    max 0 k ≤ min h (maxOffset xs ys k) ∧
      ∃ B, IsAlignment B (xs.take (min h (maxOffset xs ys k) - k).toNat)
        (ys.take (min h (maxOffset xs ys k)).toNat) ∧ P.cost B ≤ P.cost A + P.gap := by
  have h0 : 0 ≤ h := le_trans (le_max_left _ _) hl
  have hk : k + 1 ≤ h := le_trans (le_max_right _ _) hl
  have hm := le_min_iff.mp hu
  have ht : max 0 k ≤ maxOffset xs ys k := by
    dsimp [maxOffset]
    exact le_min (max_le (by omega) hb.2) (max_le (by omega) (by omega))
  refine ⟨le_min (max_le h0 (by omega)) ht, ?_⟩
  by_cases he : h ≤ (xs.length : ℤ) + k
  · have hc : min h (maxOffset xs ys k) = h := by
      simp only [maxOffset] at *
      omega
    rw [hc]
    have hv : (h - (k + 1)).toNat < xs.length := by omega
    have hvs : (h - k).toNat = (h - (k + 1)).toNat + 1 := by omega
    let c : Option α × Option α := (some xs[(h - (k + 1)).toNat], none)
    refine ⟨A ++ [c], ?_, ?_⟩
    · rw [hvs, List.take_succ_eq_append_getElem hv]
      simpa only [List.append_nil] using align_append A [c] _ _ [xs[(h - (k + 1)).toNat]] [] ha
        (by simp [IsAlignment, c])
    · simp [LinearPenalties.cost, LinearPenalties.columnCost, c]
  · have hc : min h (maxOffset xs ys k) = h - 1 := by
      simp only [maxOffset] at *
      omega
    rw [hc]
    have hh : (h - 1).toNat < ys.length := by omega
    have hhs : h.toNat = (h - 1).toNat + 1 := by omega
    have hvs : h - 1 - k = h - (k + 1) := by omega
    rw [hvs]
    rw [hhs, List.take_succ_eq_append_getElem hh] at ha
    exact remove_last_right P A ys[(h - 1).toNat] _ _ ha

private def Good (P : LinearPenalties) (xs ys : List α) (s : ℕ) (k h : ℤ) : Prop :=
  max 0 k ≤ h ∧ h ≤ maxOffset xs ys k ∧
    (∃ A, IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat) ∧ P.cost A ≤ s) ∧
    ¬(h < maxOffset xs ys k ∧ xs[(h - k).toNat]? = ys[h.toNat]?)

private theorem good_slide (P : LinearPenalties) (xs ys : List α) (s : ℕ) (k h : ℤ)
    (hl : max 0 k ≤ h) (hu : h ≤ maxOffset xs ys k)
    (ha : ∃ A, IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat) ∧ P.cost A ≤ s) :
    Good P xs ys s k (slide xs ys k h) := by
  obtain ⟨hb, hc⟩ := slide_bounds xs ys k h hu
  refine ⟨hl.trans hb, hc, ?_, slide_closed xs ys k h ((le_max_left _ _).trans hl) hu⟩
  obtain ⟨A, hA, hcost⟩ := ha
  obtain ⟨B, hB, hBcost⟩ := slide_align P xs ys k h hl hu A hA
  exact ⟨B, hB, hBcost ▸ hcost⟩

private theorem max_property (a b : Option ℤ) (R : ℤ → Prop)
    (ha : ∀ h, a = some h → R h) (hb : ∀ h, b = some h → R h) :
    ∀ h, max a b = some h → R h := by
  intro h hw
  cases a with
  | none =>
    cases b with
    | none => simp only [max, Option.max, reduceCtorEq] at hw
    | some b => exact hb h (by simpa only [max, Option.max] using hw)
  | some a =>
    cases b with
    | none => exact ha h (by simpa only [max, Option.max] using hw)
    | some b =>
      have he : max a b = h := by simpa only [max, Option.max, Option.some.injEq] using hw
      by_cases hab : a ≤ b
      · rw [max_eq_right hab] at he
        exact hb h (congrArg some he)
      · rw [max_eq_left (le_of_not_ge hab)] at he
        exact ha h (congrArg some he)

private theorem sound_good (P : LinearPenalties) (xs ys : List α) (s : ℕ)
    (k h : ℤ) (hw : wavefront P xs ys s k = some h) : Good P xs ys s k h := by
  induction s using Nat.strong_induction_on generalizing k h with
  | h s ih =>
    rw [recurrence] at hw
    by_cases hs : s = 0
    · subst s
      by_cases hk : k = 0
      · subst k
        simp only [ite_true, Option.some.injEq] at hw
        rw [← hw]
        apply good_slide P xs ys 0 0 0 (by simp)
        · simp [maxOffset]
        · exact ⟨[], by simp [IsAlignment], by simp [LinearPenalties.cost]⟩
      · simp [hk] at hw
    by_cases hk : k < -(xs.length : ℤ) ∨ (ys.length : ℤ) < k
    · simp [hs, hk] at hw
    simp only [ite_eq_right hs, ite_eq_right hk] at hw
    have hb : -(xs.length : ℤ) ≤ k ∧ k ≤ (ys.length : ℤ) := by omega
    let m := if P.mismatch ≤ s then (wavefront P xs ys (s - P.mismatch) k).map
      (· + 1) else none
    let i := if P.gap ≤ s then (wavefront P xs ys (s - P.gap) (k - 1)).map
      (· + 1) else none
    let d := if P.gap ≤ s then wavefront P xs ys (s - P.gap) (k + 1) else none
    let R (z : ℤ) := max 0 k ≤ min z (maxOffset xs ys k) ∧
      ∃ A, IsAlignment A (xs.take (min z (maxOffset xs ys k) - k).toNat)
        (ys.take (min z (maxOffset xs ys k)).toNat) ∧ P.cost A ≤ s
    have hm : ∀ z, m = some z → R z := by
      intro z hz
      dsimp [m] at hz
      by_cases hx : P.mismatch ≤ s
      · rw [ite_eq_left hx] at hz
        cases he : wavefront P xs ys (s - P.mismatch) k with
        | none => simp [he] at hz
        | some t =>
          simp only [he, Option.map_some, Option.some.injEq] at hz
          subst z
          have hp := P.mismatch_pos
          obtain ⟨hl, hu, ⟨A, hA, hc⟩, _⟩ := ih _ (by omega) k t he
          obtain ⟨hl', B, hB, hc'⟩ := mismatch_candidate P xs ys k t hl hu A hA
          exact ⟨hl', B, hB, by omega⟩
      · simp [hx] at hz
    have hi : ∀ z, i = some z → R z := by
      intro z hz
      dsimp [i] at hz
      by_cases hx : P.gap ≤ s
      · rw [ite_eq_left hx] at hz
        cases he : wavefront P xs ys (s - P.gap) (k - 1) with
        | none => simp [he] at hz
        | some t =>
          simp only [he, Option.map_some, Option.some.injEq] at hz
          subst z
          have hp := P.gap_pos
          obtain ⟨hl, hu, ⟨A, hA, hc⟩, _⟩ := ih _ (by omega) (k - 1) t he
          obtain ⟨hl', B, hB, hc'⟩ := insertion_candidate P xs ys k t hb hl hu A hA
          exact ⟨hl', B, hB, by omega⟩
      · simp [hx] at hz
    have hd : ∀ z, d = some z → R z := by
      intro z hz
      dsimp [d] at hz
      by_cases hx : P.gap ≤ s
      · rw [ite_eq_left hx] at hz
        have hp := P.gap_pos
        obtain ⟨hl, hu, ⟨A, hA, hc⟩, _⟩ := ih _ (by omega) (k + 1) z hz
        obtain ⟨hl', B, hB, hc'⟩ := deletion_candidate P xs ys k z hb hl hu A hA
        exact ⟨hl', B, hB, by omega⟩
      · simp [hx] at hz
    change (max m (max i d)).map (fun z => slide xs ys k (min z (maxOffset xs ys k))) =
      some h at hw
    cases he : max m (max i d) with
    | none => simp [he] at hw
    | some z =>
      simp only [he, Option.map_some, Option.some.injEq] at hw
      obtain ⟨hl, ha⟩ := max_property m (max i d) R hm (max_property i d R hi hd) z he
      rw [← hw]
      exact good_slide P xs ys s k _ hl (min_le_right _ _) ha

private theorem max_dominates_left (a b : Option ℤ) (z : ℤ) (hz : a = some z) :
    ∃ t, max a b = some t ∧ z ≤ t := by
  subst a
  cases b with
  | none => exact ⟨z, rfl, le_rfl⟩
  | some b => exact ⟨max z b, rfl, le_max_left _ _⟩

private theorem max_dominates_right (a b : Option ℤ) (z : ℤ) (hz : b = some z) :
    ∃ t, max a b = some t ∧ z ≤ t := by
  subst b
  cases a with
  | none => exact ⟨z, rfl, le_rfl⟩
  | some a => exact ⟨max a z, rfl, le_max_right _ _⟩

private theorem advance (P : LinearPenalties) (xs ys : List α) (s : ℕ) (k q t : ℤ)
    (hs : 0 < s) (hk : -(xs.length : ℤ) ≤ k ∧ k ≤ (ys.length : ℤ))
    (ht : t ≤ maxOffset xs ys k) (hq : t ≤ q)
    (hc :
      (if P.mismatch ≤ s then (wavefront P xs ys (s - P.mismatch) k).map
        (· + 1) else none) = some q ∨
      (if P.gap ≤ s then (wavefront P xs ys (s - P.gap) (k - 1)).map
        (· + 1) else none) = some q ∨
      (if P.gap ≤ s then wavefront P xs ys (s - P.gap) (k + 1) else none) = some q) :
    ∃ h', wavefront P xs ys s k = some h' ∧ t ≤ h' := by
  let m := if P.mismatch ≤ s then (wavefront P xs ys (s - P.mismatch) k).map
    (· + 1) else none
  let i := if P.gap ≤ s then (wavefront P xs ys (s - P.gap) (k - 1)).map
    (· + 1) else none
  let d := if P.gap ≤ s then wavefront P xs ys (s - P.gap) (k + 1) else none
  have he : ∃ z, max m (max i d) = some z ∧ q ≤ z := by
    rcases hc with hc | hc | hc
    · exact max_dominates_left m (max i d) q hc
    · obtain ⟨z, hz, hqz⟩ := max_dominates_left i d q hc
      obtain ⟨w, hw, hzw⟩ := max_dominates_right m (max i d) z hz
      exact ⟨w, hw, hqz.trans hzw⟩
    · obtain ⟨z, hz, hqz⟩ := max_dominates_right i d q hc
      obtain ⟨w, hw, hzw⟩ := max_dominates_right m (max i d) z hz
      exact ⟨w, hw, hqz.trans hzw⟩
  obtain ⟨z, hz, hqz⟩ := he
  refine ⟨slide xs ys k (min z (maxOffset xs ys k)), ?_, ?_⟩
  · rw [recurrence, ite_eq_right (by omega), ite_eq_right (by omega)]
    change (max m (max i d)).map _ = _
    rw [hz]
    rfl
  · exact (le_min (hq.trans hqz) ht).trans
      (slide_bounds xs ys k _ (min_le_right _ _)).1

omit [DecidableEq α] in
private theorem row_prefix (xs row tail : List α) (v : ℕ) (hv : v ≤ xs.length)
    (he : row ++ tail = xs.take v) : row = xs.take row.length ∧ row.length ≤ v := by
  have hn : row.length + tail.length = v := by
    simpa [List.length_take, Nat.min_eq_left hv] using congrArg List.length he
  have ht := congrArg (List.take row.length) he
  simp only [List.take_append_of_le_length (le_refl row.length), List.take_length,
    List.take_take, Nat.min_eq_left (by omega : row.length ≤ v)] at ht
  exact ⟨ht, by omega⟩

omit [DecidableEq α] in
private theorem row_last (xs row : List α) (a : α) (v : ℕ) (hv : v ≤ xs.length)
    (he : row ++ [a] = xs.take v) : xs[row.length]? = some a := by
  have hn : row.length + 1 = v := by
    simpa [List.length_take, Nat.min_eq_left hv] using congrArg List.length he
  have ht := congrArg (fun l => l[row.length]?) he
  simpa only [List.getElem?_append_right (le_refl row.length), Nat.sub_self,
    List.getElem?_cons_zero, List.getElem?_take, ite_eq_left (by omega : row.length < v)]
    using ht.symm

/-- Soundness: a wavefront offset is a valid cell of its diagonal, reachable by an alignment
of the corresponding prefixes with cost at most `s`. -/
theorem wavefront_sound (P : LinearPenalties) (xs ys : List α) (s : ℕ) (k h : ℤ)
    (hw : wavefront P xs ys s k = some h) :
    max 0 k ≤ h ∧ h ≤ maxOffset xs ys k ∧
      ∃ A, IsAlignment A (xs.take (h - k).toNat) (ys.take h.toNat) ∧ P.cost A ≤ s := by
  obtain ⟨hl, hu, ha, _⟩ := sound_good P xs ys s k h hw
  exact ⟨hl, hu, ha⟩

/-- Completeness: every alignment of a pair of prefixes is dominated on its diagonal by the
wavefront of its exact cost. -/
theorem wavefront_complete (P : LinearPenalties) (xs ys : List α) (v h : ℕ)
    (hv : v ≤ xs.length) (hh : h ≤ ys.length) (A : Alignment α)
    (hA : IsAlignment A (xs.take v) (ys.take h)) :
    ∃ h', wavefront P xs ys (P.cost A) ((h : ℤ) - v) = some h' ∧ (h : ℤ) ≤ h' := by
  induction A using List.reverseRecOn generalizing v h with
  | nil =>
    have hx := congrArg List.length hA.2.1
    have hy := congrArg List.length hA.2.2
    have hv0 : v = 0 := by simpa [List.length_take, Nat.min_eq_left hv] using hx.symm
    have hh0 : h = 0 := by simpa [List.length_take, Nat.min_eq_left hh] using hy.symm
    subst v; subst h
    refine ⟨slide xs ys 0 0, ?_, ?_⟩
    · simp [LinearPenalties.cost, recurrence]
    · exact (slide_bounds xs ys 0 0 (by simp [maxOffset])).1
  | append_singleton A c ih =>
    rcases c with ⟨a, b⟩
    have ht : ∀ c ∈ A, c ≠ (none, none) := fun c hc => hA.1 c (by simp [hc])
    have hx : A.filterMap Prod.fst ++ a.toList = xs.take v := by
      cases a <;> simpa [List.filterMap_append] using hA.2.1
    have hy : A.filterMap Prod.snd ++ b.toList = ys.take h := by
      cases b <;> simpa [List.filterMap_append] using hA.2.2
    let v₀ := (A.filterMap Prod.fst).length
    let h₀ := (A.filterMap Prod.snd).length
    obtain ⟨hx₀, hv₀⟩ := row_prefix xs (A.filterMap Prod.fst) a.toList v hv hx
    obtain ⟨hy₀, hh₀⟩ := row_prefix ys (A.filterMap Prod.snd) b.toList h hh hy
    have hA₀ : IsAlignment A (xs.take v₀) (ys.take h₀) := ⟨ht, hx₀, hy₀⟩
    obtain ⟨t, hw, hdom⟩ := ih v₀ h₀ (hv₀.trans hv) (hh₀.trans hh) hA₀
    have hvlen : v₀ + a.toList.length = v := by
      simpa [List.length_take, Nat.min_eq_left hv] using congrArg List.length hx
    have hhlen : h₀ + b.toList.length = h := by
      simpa [List.length_take, Nat.min_eq_left hh] using congrArg List.length hy
    have hk : -(xs.length : ℤ) ≤ (h : ℤ) - v ∧ (h : ℤ) - v ≤ (ys.length : ℤ) := by
      omega
    have hmax : (h : ℤ) ≤ maxOffset xs ys ((h : ℤ) - v) := by
      dsimp [maxOffset]
      omega
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hA.1 _ (by simp) rfl)
      | some b =>
        simp only [Option.toList_none, Option.toList_some, List.length_nil,
          List.length_singleton] at hvlen hhlen
        have hj : (h : ℤ) - v - 1 = (h₀ : ℤ) - v₀ := by omega
        have hp := P.gap_pos
        have hc : P.cost (A ++ [(none, some b)]) = P.cost A + P.gap := by
          simp [LinearPenalties.cost, List.map_append, List.sum_append,
            LinearPenalties.columnCost]
        rw [hc]
        apply advance P xs ys (P.cost A + P.gap) ((h : ℤ) - v) (t + 1) h
          (by omega) hk hmax (by omega)
        right; left
        simp [show P.gap ≤ P.cost A + P.gap by omega, hj, hw]
    | some a =>
      cases b with
      | none =>
        simp only [Option.toList_none, Option.toList_some, List.length_nil,
          List.length_singleton] at hvlen hhlen
        have hj : (h : ℤ) - v + 1 = (h₀ : ℤ) - v₀ := by omega
        have hp := P.gap_pos
        have hc : P.cost (A ++ [(some a, none)]) = P.cost A + P.gap := by
          simp [LinearPenalties.cost, List.map_append, List.sum_append,
            LinearPenalties.columnCost]
        rw [hc]
        apply advance P xs ys (P.cost A + P.gap) ((h : ℤ) - v) t h
          (by omega) hk hmax (by omega)
        right; right
        simp [show P.gap ≤ P.cost A + P.gap by omega, hj, hw]
      | some b =>
        simp only [Option.toList_some, List.length_singleton] at hvlen hhlen
        have hj : (h : ℤ) - v = (h₀ : ℤ) - v₀ := by omega
        by_cases hab : a = b
        · have hc : P.cost (A ++ [(some a, some b)]) = P.cost A := by
            simp [LinearPenalties.cost, List.map_append, List.sum_append,
              LinearPenalties.columnCost, hab]
          rw [hc, hj]
          by_cases he : (h : ℤ) ≤ t
          · exact ⟨t, hw, he⟩
          have ht₀ : t = (h₀ : ℤ) := by omega
          have hxlast := row_last xs (A.filterMap Prod.fst) a v hv hx
          have hylast := row_last ys (A.filterMap Prod.snd) b h hh hy
          obtain ⟨_, _, _, hclosed⟩ := sound_good P xs ys (P.cost A) _ t hw
          apply False.elim
          apply hclosed
          refine ⟨?_, ?_⟩
          · rw [← hj]
            omega
          · have htv : (t - ((h₀ : ℤ) - v₀)).toNat = v₀ := by omega
            have hth : t.toNat = h₀ := by omega
            rw [htv, hth]
            exact hxlast.trans (hab ▸ hylast.symm)
        · have hp := P.mismatch_pos
          have hc : P.cost (A ++ [(some a, some b)]) = P.cost A + P.mismatch := by
            simp [LinearPenalties.cost, List.map_append, List.sum_append,
              LinearPenalties.columnCost, hab]
          rw [hc]
          apply advance P xs ys (P.cost A + P.mismatch) ((h : ℤ) - v) (t + 1) h
            (by omega) hk hmax (by omega)
          left
          simp [show P.mismatch ≤ P.cost A + P.mismatch by omega, hj, hw]

/-- The wavefront algorithm is exact: the end cell is reached by some score `s' ≤ s` iff some
alignment of `xs` and `ys` costs at most `s`. Hence the least such `s` is the optimal cost. -/
theorem exists_wavefront_end_iff (P : LinearPenalties) (xs ys : List α) (s : ℕ) :
    (∃ s' ≤ s, wavefront P xs ys s' ((ys.length : ℤ) - xs.length) = some ys.length) ↔
      ∃ A, IsAlignment A xs ys ∧ P.cost A ≤ s := by
  constructor
  · rintro ⟨s', hs, hw⟩
    obtain ⟨_, _, A, hA, hc⟩ := wavefront_sound P xs ys s' _ _ hw
    refine ⟨A, ?_, hc.trans hs⟩
    have hv : ((ys.length : ℤ) - ((ys.length : ℤ) - xs.length)).toNat = xs.length := by
      omega
    simpa [hv] using hA
  · rintro ⟨A, hA, hc⟩
    obtain ⟨h', hw, hh⟩ := wavefront_complete P xs ys xs.length ys.length
      le_rfl le_rfl A (by simpa using hA)
    obtain ⟨_, hu, _⟩ := wavefront_sound P xs ys (P.cost A) _ h' hw
    have he : h' = (ys.length : ℤ) := by
      dsimp [maxOffset] at hu
      omega
    rw [he] at hw
    exact ⟨P.cost A, hc, hw⟩

end Wavefront

namespace LinearPenalties

variable (P : LinearPenalties) [DecidableEq α]

/-- The substitution score in the maximization convention of `nwScore`: `0` for a match and
`-mismatch` for a mismatch (the gap score is `-gap`). -/
def score (a b : α) : ℤ := if a = b then 0 else -(P.mismatch : ℤ)

/-- Scores are negated costs. -/
theorem alignmentScore_eq_neg_cost (A : Alignment α) :
    alignmentScore P.score (-(P.gap : ℤ)) A = -(P.cost A : ℤ) := by
  induction A with
  | nil => simp [alignmentScore, cost]
  | cons c A ih =>
      simp only [alignmentScore, cost, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
      rw [ih]
      rcases c with ⟨_ | a, _ | b⟩
      · simp [columnScore, columnCost]
      · simp only [columnScore, columnCost]; ring
      · simp only [columnScore, columnCost]; ring
      · by_cases hab : a = b
        · simp [columnScore, columnCost, score, hab]
        · simp only [columnScore, columnCost, score, hab, ite_false]; ring

end LinearPenalties

namespace Wavefront

variable [DecidableEq α]

/-- **The wavefront algorithm computes the optimal alignment cost**: the end cell is reached by
some score `s' ≤ s` iff `s` is at least the optimal Needleman–Wunsch cost. -/
theorem exists_wavefront_end_iff_nwScore (P : LinearPenalties) (xs ys : List α) (s : ℕ) :
    (∃ s' ≤ s, wavefront P xs ys s' ((ys.length : ℤ) - xs.length) = some ys.length) ↔
      -nwScore P.score (-(P.gap : ℤ)) xs ys ≤ s := by
  rw [exists_wavefront_end_iff]
  constructor
  · rintro ⟨A, hA, hcost⟩
    have := alignmentScore_le_nwScore P.score (-(P.gap : ℤ)) xs ys A hA
    rw [P.alignmentScore_eq_neg_cost] at this
    have : (P.cost A : ℤ) ≤ s := by exact_mod_cast hcost
    linarith
  · intro h
    obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore P.score (-(P.gap : ℤ)) xs ys
    rw [P.alignmentScore_eq_neg_cost] at hscore
    exact ⟨A, hA, by exact_mod_cast (show (P.cost A : ℤ) ≤ s by linarith)⟩

end Wavefront

end Cslib.Algorithms.Lean
