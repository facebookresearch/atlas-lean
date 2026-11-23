/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DistinctMultiplesInterval

/-!
# Diagonal and shifted intervals containing distinct multiples
-/

namespace MetaMathlibExt

/-- **An inequality between diagonal and shifted interval lengths.** For natural numbers $n$ and
$m$, let $f(n, m)$ be the least natural number $L$ such that the interval $(m, m + L]$ contains
distinct multiples of $1, \dots, n$. Then for all positive integers $k$ and $n$,
$kn + f(kn, kn) \le k^2 n + f(n, k^2 n)$.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Lemma 2
(`integers-2026-A7-lem-2`). -/
public theorem distinctMultiplesIntervalLength_mul_le {k n : ℕ} (hk : 0 < k)
    (hn : 0 < n) :
    k * n + distinctMultiplesIntervalLength (k * n) (k * n) ≤
      k ^ 2 * n + distinctMultiplesIntervalLength n (k ^ 2 * n) := by
  let L := distinctMultiplesIntervalLength n (k ^ 2 * n)
  change k * n + _ ≤ k ^ 2 * n + L
  have hbase : k * n ≤ k ^ 2 * n := by
    rw [Nat.mul_le_mul_right_iff hn, sq]
    exact Nat.le_mul_of_pos_left k hk
  suffices distinctMultiplesIntervalLength (k * n) (k * n) ≤ k ^ 2 * n + L - k * n by
    omega
  apply distinctMultiplesIntervalLength_le_iff.mpr
  obtain ⟨a, ha, hmem⟩ :=
    hasDistinctMultiplesInInterval_distinctMultiplesIntervalLength n (k ^ 2 * n)
  have htop (i : Fin (k * n)) : k * (i.val + 1) ≤ k ^ 2 * n := by
    rw [sq, Nat.mul_assoc]
    exact Nat.mul_le_mul_left k i.isLt
  -- The shifted witnesses lie above the scaled multiples, even at the dividing endpoint.
  refine ⟨fun i => if hi : i.val < n then a ⟨i.val, hi⟩ else k * (i.val + 1), ?_, ?_⟩
  · intro i j hij
    dsimp only at hij
    split at hij <;> split at hij
    · exact Fin.ext (congrArg (Fin.val (n := n)) (ha hij))
    · rename_i hi hj
      exact False.elim ((hmem ⟨i.val, hi⟩).1.not_ge (hij.le.trans (htop j)))
    · rename_i hi hj
      exact False.elim ((hmem ⟨j.val, hj⟩).1.not_ge (hij.ge.trans (htop i)))
    · exact Fin.ext (Nat.succ.inj (Nat.eq_of_mul_eq_mul_left hk hij))
  · intro i
    have hend : k * n + (k ^ 2 * n + L - k * n) = k ^ 2 * n + L := by omega
    rw [hend]
    dsimp only
    split
    · rename_i hi
      obtain ⟨hlo, hhi, hdvd⟩ := hmem ⟨i.val, hi⟩
      exact ⟨hbase.trans_lt hlo, hhi, hdvd⟩
    · rename_i hi
      exact ⟨Nat.mul_lt_mul_of_pos_left (by omega) hk,
        (htop i).trans (Nat.le_add_right _ _), dvd_mul_left _ _⟩

end MetaMathlibExt
