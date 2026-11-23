/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadter

/-! # The two-cycle of the padded three-term Hofstadter-like recurrence -/

namespace MetaMathlibExt
namespace threeTermHofstadter_twoCycle

private abbrev seed (xs : Array ℤ) (M : ℤ) := ((xs.push 2).push M).push 2

private theorem lookup_push (xs : Array ℤ) (v j : ℤ) :
    threeTermHofstadterLookup true (xs.push v) j =
      if j = (xs.size : ℤ) + 1 then some v else threeTermHofstadterLookup true xs j := by
  by_cases hj : j ≤ 0
  · simp [threeTermHofstadterLookup, hj, show j ≠ (xs.size : ℤ) + 1 by omega]
  · simp only [threeTermHofstadterLookup, hj, ite_false, Array.getElem?_push]
    simp only [show ((j - 1).toNat = xs.size) ↔ j = (xs.size : ℤ) + 1 by omega]

private theorem lookup_nonpos (xs : Array ℤ) {j : ℤ} (hj : j ≤ 0) :
    threeTermHofstadterLookup true xs j = some 0 := by simp [threeTermHofstadterLookup, hj]

-- The two entries equal to 2 both select the middle entry M.
private theorem next_double (xs : Array ℤ) {M : ℤ} (hM : (xs.size : ℤ) + 5 ≤ M) :
    threeTermHofstadterNext true (seed xs M) = some (M + M) := by
  simp (disch := omega) only [threeTermHofstadterNext, seed, Array.size_push, Nat.cast_add,
    Nat.cast_one, lookup_push, ite_eq_left, ite_eq_right, lookup_nonpos, Option.bind_some,
    Option.map_some, add_zero]

-- Both large entries now select padded zeros, leaving just the previous 2.
private theorem next_two (xs : Array ℤ) {M : ℤ} (hM : (xs.size : ℤ) + 5 ≤ M) :
    threeTermHofstadterNext true ((seed xs M).push (M + M)) = some 2 := by
  simp (disch := omega) only [threeTermHofstadterNext, seed, Array.size_push, Nat.cast_add,
    Nat.cast_one, lookup_push, ite_eq_left, ite_eq_right, lookup_nonpos, Option.bind_some,
    Option.map_some, add_zero, zero_add]

/-- Read the last term after extending a prefix by the given number of steps. -/
private def lastAfter (xs : Array ℤ) (k : ℕ) : Option ℤ :=
  (threeTermHofstadterExtend true k xs).bind fun ys =>
    threeTermHofstadterLookup true ys (xs.size + k : ℕ)

private theorem lastAfter_succ {xs : Array ℤ} {v : ℤ}
    (hv : threeTermHofstadterNext true xs = some v) (k : ℕ) :
    lastAfter xs (k + 1) = lastAfter (xs.push v) k := by
  simp only [lastAfter, threeTermHofstadterExtend, hv, Array.size_push,
    Nat.add_right_comm xs.size 1 k, Nat.add_assoc]

private theorem lastAfter_push (xs : Array ℤ) (v : ℤ) : lastAfter (xs.push v) 0 = some v := by
  simp [lastAfter, threeTermHofstadterExtend, lookup_push]

-- Beyond a suffix 2, M, 2, the next two terms are 2M, 2. They give another
-- suffix of the same form, with a larger prefix and a doubled middle entry.
private theorem pairs (k : ℕ) (xs : Array ℤ) (M : ℤ) (hM : (xs.size : ℤ) + 5 ≤ M) :
    lastAfter (seed xs M) (2 * k + 1) = some (2 ^ (k + 1) * M) ∧
      lastAfter (seed xs M) (2 * k + 2) = some 2 := by
  induction k generalizing xs M with
  | zero =>
    simp only [Nat.zero_add, pow_one, two_mul M]
    constructor
    · rw [lastAfter_succ (next_double xs hM), lastAfter_push]
    · rw [lastAfter_succ (next_double xs hM), lastAfter_succ (next_two xs hM), lastAfter_push]
  | succ k ih =>
    let ys := (xs.push 2).push M
    have hbound : (ys.size : ℤ) + 5 ≤ M + M := by
      simp [ys]
      omega
    have shift (n : ℕ) : lastAfter (seed xs M) (n + 2) = lastAfter (seed ys (M + M)) n := by
      rw [lastAfter_succ (next_double xs hM), lastAfter_succ (next_two xs hM)]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega, shift, shift]
    obtain ⟨heven, hodd⟩ := ih ys (M + M) hbound
    exact ⟨by rwa [pow_succ _ (k + 1), mul_assoc, two_mul M], hodd⟩

end threeTermHofstadter_twoCycle

open threeTermHofstadter_twoCycle

/-- **Two-cycle lemma for the three-term Hofstadter-like recurrence.** Let $K \ge 1$ be a natural
number, let $M$ be an integer with $M \ge K + 5$, let $a_1, \dots, a_K$ be arbitrary integers,
and let $B$ be the padded three-term Hofstadter-like sequence with initial conditions
$a_1, \dots, a_K, 2, M, 2$. Then for every natural number $k$ the term $B(K + 2k + 1)$ is defined
and equals $2$, and for every $k \ge 1$ the term $B(K + 2k)$ is defined and equals $2^{k-1} M$.

Source: Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear
Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 4,
citing the author's thesis, Proposition 9.9 (`jis-2024-24.7.4-lem-4`). -/
public theorem threeTermHofstadter_twoCycle {K : ℕ} (hK : 1 ≤ K) {M : ℤ}
    (hM : (K : ℤ) + 5 ≤ M) (a : List ℤ) (ha : a.length = K) (k : ℕ) :
    threeTermHofstadterTerm true (a ++ [2, M, 2]) (K + 2 * k + 1) = some 2 ∧
      (1 ≤ k → threeTermHofstadterTerm true (a ++ [2, M, 2]) (K + 2 * k) =
        some (2 ^ (k - 1) * M)) := by
  subst K
  have hseed : (a ++ [2, M, 2]).toArray = seed a.toArray M := by
    apply Array.toList_inj.mp
    simp [seed]
  rcases k with _ | _ | k
  case zero | succ.zero =>
    have hinit (j : ℕ) (hj : j ≤ a.length + 3) :
        threeTermHofstadterTerm true (a ++ [2, M, 2]) j =
          threeTermHofstadterLookup true (seed a.toArray M) j := by
      rw [threeTermHofstadterTerm_of_le_length _ _ (by simpa using hj), hseed]
    simp (disch := omega) only [hinit, seed, lookup_push, Array.size_push, List.size_toArray,
      Nat.cast_add, Nat.cast_one, ite_eq_left, ite_eq_right]
    simp
  case succ.succ =>
    have hterm (n : ℕ) : threeTermHofstadterTerm true (a ++ [2, M, 2]) (a.length + 3 + n) =
        lastAfter (seed a.toArray M) n := by
      simp [threeTermHofstadterTerm, threeTermHofstadterPrefix, lastAfter, ← hseed]
    obtain ⟨heven, hodd⟩ := pairs k a.toArray M (by simpa using hM)
    constructor
    · simpa +arith only [← hterm] using hodd
    · intro _
      simpa +arith only [← hterm, Nat.add_one_sub_one] using heven

end MetaMathlibExt
