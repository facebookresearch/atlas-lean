/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadter

/-!
# Termination of the unpadded three-term Hofstadter sequence

The exact length for `N ≥ 14` and the finite computations for the smaller starts give the
termination part of Fox's Theorem 1.
-/

namespace MetaMathlibExt
namespace threeTermHofstadter_linear_dies

-- To keep the 1015-term computation tractable, store the prefix in one natural number,
-- with one base-2048 digit per term and the newest term in the least significant digit.
private def digit (words offset : ℕ) : ℕ := (words >>> (11 * offset)) % 2048

-- Offsets are one-based: for the next index n, offset d reads the term at n - d.
private def lookupPacked (size words offset : ℕ) : Option ℕ :=
  if 0 < offset ∧ offset ≤ size then some (digit words (offset - 1)) else none

private def nextPacked (size words : ℕ) : Option ℕ :=
  (lookupPacked size words 1).bind fun a =>
  (lookupPacked size words 2).bind fun b =>
  (lookupPacked size words 3).bind fun c =>
  (lookupPacked size words a).bind fun p =>
  (lookupPacked size words b).bind fun q =>
  (lookupPacked size words c).map fun r => p + q + r

-- A term that would overflow its digit makes the certificate fail, not report termination.
private def extendPacked : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, words => some words
  | fuel + 1, size, words => (nextPacked size words).bind fun v =>
    if v < 2048 then extendPacked fuel (size + 1) (words * 2048 + v) else none

private def packLinear : ℕ → ℕ
  | 0 => 0
  | n + 1 => packLinear n * 2048 + (n + 1)

private def Encodes (words : ℕ) (xs : Array ℤ) : Prop :=
  ∀ i < xs.size, xs[i]? = some (digit words (xs.size - (i + 1)) : ℤ)

private theorem digit_push_zero {value : ℕ} (words : ℕ) (hv : value < 2048) :
    digit (words * 2048 + value) 0 = value := by
  simp [digit, Nat.mod_eq_of_lt hv]

private theorem digit_push_succ {value : ℕ} (words offset : ℕ) (hv : value < 2048) :
    digit (words * 2048 + value) (offset + 1) = digit words offset := by
  unfold digit
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.mul_add, Nat.pow_add]
  change ((words * 2048 + value) / (2 ^ (11 * offset) * 2048)) % 2048 = _
  rw [Nat.mul_comm (2 ^ (11 * offset)) 2048, ← Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm words 2048, Nat.mul_add_div (by decide : 0 < 2048), Nat.div_eq_of_lt hv,
    Nat.add_zero]

private theorem encodes_push {xs : Array ℤ} {words value : ℕ} (h : Encodes words xs)
    (hv : value < 2048) : Encodes (words * 2048 + value) (xs.push (value : ℤ)) := by
  intro i hi
  rw [Array.size_push] at hi ⊢
  rw [Array.getElem?_push]
  split
  · subst i
    simp [digit_push_zero words hv]
  · have hin : i < xs.size := by omega
    rw [show xs.size + 1 - (i + 1) = (xs.size - (i + 1)) + 1 by omega,
      digit_push_succ words _ hv, h i hin]

private theorem encodes_linear (N : ℕ) (hN : N < 2048) :
    Encodes (packLinear N) ((List.range N).map fun i : ℕ => (i : ℤ) + 1).toArray := by
  induction N with
  | zero => simp [Encodes]
  | succ n ih =>
    rw [packLinear, List.range_succ, List.map_append]
    have hpush : (List.map (fun i : ℕ => (i : ℤ) + 1) (List.range n) ++ [(n : ℤ) + 1]).toArray =
        ((List.range n).map fun i : ℕ => (i : ℤ) + 1).toArray.push ((n + 1 : ℕ) : ℤ) := by
      simp
    rw [List.map_cons, List.map_nil, hpush]
    exact encodes_push (ih (by omega)) hN

private theorem lookup_eq {words : ℕ} {xs : Array ℤ} (h : Encodes words xs) (d : ℕ) :
    threeTermHofstadterLookup false xs ((xs.size : ℤ) + 1 - (d : ℤ)) =
      (lookupPacked xs.size words d).map (fun v : ℕ => (v : ℤ)) := by
  unfold lookupPacked threeTermHofstadterLookup
  by_cases h0 : d = 0
  · subst d
    simp only [Int.ofNat_zero, sub_zero, Nat.lt_irrefl, false_and, ite_false, Option.map_none]
    rw [ite_eq_right (by omega), show (((xs.size : ℤ) + 1 - 1).toNat) = xs.size by omega,
      Array.getElem?_eq_none (Nat.le_refl _)]
  by_cases hd : d ≤ xs.size
  · rw [ite_eq_right (by omega), ite_eq_left (show 0 < d ∧ d ≤ xs.size from ⟨by omega, hd⟩)]
    rw [show (((xs.size : ℤ) + 1 - (d : ℤ) - 1).toNat) = xs.size - d by omega,
      h (xs.size - d) (by omega), show xs.size - (xs.size - d + 1) = d - 1 by omega]
    rfl
  · have hbad : ¬ (0 < d ∧ d ≤ xs.size) := fun hh => hd hh.2
    rw [ite_eq_left (by omega), ite_eq_right hbad]
    rfl

private theorem next_eq {words : ℕ} {xs : Array ℤ} (h : Encodes words xs) :
    threeTermHofstadterNext false xs = (nextPacked xs.size words).map (fun v : ℕ => (v : ℤ)) := by
  unfold threeTermHofstadterNext nextPacked
  dsimp only
  erw [lookup_eq h 1, lookup_eq h 2, lookup_eq h 3]
  simp only [lookup_eq h, Option.bind_map, Option.map_bind, Option.map_map, Function.comp_def,
    Int.natCast_add]

private theorem extend_sound {words size k final : ℕ} {xs : Array ℤ} (h : Encodes words xs)
    (hsize : xs.size = size) (hext : extendPacked k size words = some final) :
    ∃ ys, threeTermHofstadterExtend false k xs = some ys ∧
      ys.size = size + k ∧ Encodes final ys := by
  induction k generalizing xs words size with
  | zero =>
    simp only [extendPacked, Option.some.injEq] at hext
    subst final
    exact ⟨xs, rfl, by simpa using hsize, h⟩
  | succ k ih =>
    unfold extendPacked at hext
    rw [← hsize] at hext ⊢
    cases hv : nextPacked xs.size words with
    | none => simp [hv] at hext
    | some v =>
      simp only [hv, Option.bind_some] at hext
      split at hext
      · rename_i hv'
        obtain ⟨ys, he, hs, hy⟩ := ih (encodes_push h hv') (Array.size_push ..) hext
        refine ⟨ys, ?_, by omega, hy⟩
        rw [threeTermHofstadterExtend, next_eq h, hv]
        exact he
      · contradiction

private theorem endsAfter_of_packed {N T : ℕ} (hN : N < 2048) (hT : N ≤ T)
    (check : (extendPacked (T - N) N (packLinear N)).any
      (fun final => (nextPacked T final).isNone) = true) :
    ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) T := by
  cases hf : extendPacked (T - N) N (packLinear N) with
  | none => simp [hf] at check
  | some final =>
    have hn : nextPacked T final = none := by simpa [hf] using check
    obtain ⟨ys, he, hs, hy⟩ := extend_sound (encodes_linear N hN) (by simp) hf
    have hs' : ys.size = T := by omega
    refine ⟨ys, ?_, hs', ?_⟩
    · simpa only [threeTermHofstadterPrefix, List.length_map, List.length_range] using he
    · rw [next_eq hy, hs', hn]
      rfl

set_option maxRecDepth 12000 in
set_option cbv.maxSteps 500000 in
set_option maxHeartbeats 1000000 in
-- The certificate computes 1005 new terms before checking the first unavailable term.
private theorem endsAfter_ten :
    ThreeTermHofstadterEndsAfter false ((List.range 10).map fun i : ℕ => (i : ℤ) + 1) 1015 :=
  endsAfter_of_packed (by decide) (by decide) (by cbv)

end threeTermHofstadter_linear_dies

open threeTermHofstadter_linear_dies

/-- **Death of the unpadded sequence from $1, \dots, N$ for $N = 3$, $4$ or $N \ge 10$.** Let
$N$ be a natural number with $N = 3$, $N = 4$ or $N \ge 10$, and let $B_N$ be the sequence with
initial conditions $B_N(i) = i$ for $1 \le i \le N$, continued without padding by the recurrence
$B_N(n) = B_N(n - B_N(n-1)) + B_N(n - B_N(n-2)) + B_N(n - B_N(n-3))$. Then $B_N$ dies: there is
a natural number $T$ such that $B_N(1), \dots, B_N(T)$ can be computed and $B_N(T + 1)$ cannot,
because the recurrence refers to a nonpositive index or to an index not yet computed.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1
(`jis-2024-24.7.4-thm-1`). -/
public theorem threeTermHofstadter_linear_dies {N : ℕ} (hN : N = 3 ∨ N = 4 ∨ 10 ≤ N) :
    ∃ T, ThreeTermHofstadterEndsAfter false ((List.range N).map fun i : ℕ => (i : ℤ) + 1) T := by
  rcases hN with rfl | rfl | hN
  · exact ⟨4, threeTermHofstadterEndsAfter_one_two_three⟩
  · exact ⟨5, endsAfter_of_packed (by decide) (by decide) (by cbv)⟩
  by_cases h : 14 ≤ N
  · exact ⟨N + 24, threeTermHofstadter_linear_length h⟩
  have hsmall : N = 10 ∨ N = 11 ∨ N = 12 ∨ N = 13 := by omega
  rcases hsmall with rfl | rfl | rfl | rfl
  · exact ⟨1015, endsAfter_ten⟩
  · exact ⟨117, endsAfter_of_packed (by decide) (by decide) (by cbv)⟩
  · exact ⟨45, endsAfter_of_packed (by decide) (by decide) (by cbv)⟩
  · exact ⟨73, endsAfter_of_packed (by decide) (by decide) (by cbv)⟩

end MetaMathlibExt
