/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CoveringSystem
import Mathlib.Algebra.Ring.GeomSum

/-!
# A distinct covering system with moduli from 6 to 168

A covering system is *distinct* when no two of its classes share a modulus. Klein (Theorem 2)
exhibits a distinct covering system whose moduli all lie between `6` and `168` and include both;
the system, found by Ognian Trifonov, has the 58 classes listed in `TrifonovCovering.classes`.
This file proves that statement, `MetaMathlibExt.exists_distinct_covering_min_six_max_168`.

## Proof outline

The least common multiple of the moduli is `L = 2^5 · 3^3 · 5^2 · 7 · 11 = 1663200`, so it
suffices to check that the classes cover `0, 1, …, L - 1`. Checking these integers one at a time
is far too slow for the kernel, so the check is made on bitmasks instead. For `0 < m`,
`periodicMask m k = (2^(m k) - 1) / (2^m - 1)` has its set bits at `0, m, …, (k - 1) m`
(`testBit_periodicMask`), so when `m ∣ L` the set bits of `periodicMask m (L / m) <<< r` are
`r, r + m, …, r + L - m`. If the bitwise or `coverMask L cs` of these masks over a list `cs` of
classes is `2^L - 1`, every integer of `[0, L)` lies in one of the classes, and so does every
integer (`isCoveringSystem_of_coverMask_eq`). For Trifonov's system the kernel checks this
equality with its big-number arithmetic (`decide +kernel`, no `native_decide`).

## Main statements

* `MetaMathlibExt.TrifonovCovering.isCoveringSystem_of_coverMask_eq`: the bitmask criterion for
  a list of classes to cover the integers.
* `MetaMathlibExt.TrifonovCovering.isCoveringSystem_classes`: Trifonov's classes cover the
  integers.
* `MetaMathlibExt.exists_distinct_covering_min_six_max_168`: Klein's Theorem 2.

## References

* Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
  INTEGERS 26 (2026), Article A38; arXiv:2508.18062 (<https://arxiv.org/abs/2508.18062>),
  Theorem 2, proved in Section 7 by the covering system of Ognian Trifonov used here.
-/

namespace MetaMathlibExt

@[expose] public section

namespace TrifonovCovering

/-- `periodicMask m k = (2 ^ (m * k) - 1) / (2 ^ m - 1)`. For `0 < m` this is the sum of the
`2 ^ (m * j)` for `j < k`, so its binary digits equal to `1` are exactly those at the positions
`0, m, 2 * m, …, (k - 1) * m` (`testBit_periodicMask`). The closed form lets the kernel evaluate
it with one big-number division. -/
def periodicMask (m k : ℕ) : ℕ :=
  (2 ^ (m * k) - 1) / (2 ^ m - 1)

theorem periodicMask_zero (m : ℕ) : periodicMask m 0 = 0 := by
  simp [periodicMask]

theorem periodicMask_succ {m : ℕ} (hm : 0 < m) (k : ℕ) :
    periodicMask m (k + 1) = 2 ^ m * periodicMask m k + 1 := by
  have hgeom (k : ℕ) : periodicMask m k = ∑ j ∈ Finset.range k, (2 ^ m) ^ j := by
    rw [Nat.geomSum_eq (Nat.one_lt_two_pow hm.ne') k, ← pow_mul]
    rfl
  rw [hgeom, hgeom, Finset.sum_range_succ', Finset.mul_sum, pow_zero]
  simp only [pow_succ']

/-- For `0 < m`, bit `i` of `periodicMask m k` is set exactly when `i` is a multiple of `m`
below `m * k`. -/
theorem testBit_periodicMask {m : ℕ} (hm : 0 < m) (k i : ℕ) :
    (periodicMask m k).testBit i = decide (i % m = 0 ∧ i < m * k) := by
  induction k generalizing i with
  | zero => simp [periodicMask_zero]
  | succ k ih =>
    rw [periodicMask_succ hm, Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow hm.ne'),
      Nat.mul_succ]
    split_ifs with hi
    · rw [Nat.mod_eq_of_lt hi, Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero,
        decide_eq_true_iff]
      constructor
      · rintro rfl
        exact ⟨rfl, Nat.add_pos_right _ hm⟩
      · exact fun h => h.1
    · rw [ih, ← Nat.mod_eq_sub_mod (not_lt.1 hi)]
      congr 1
      apply propext
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, by omega⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, by omega⟩

/-- The bitmask of a list of classes modulo `L`: the bitwise or, over the pairs `(r, m)` of `cs`
(standing for the class `r mod m`), of `periodicMask m (L / m) <<< r`. A set bit `n` of this mask
lies in one of the classes (`exists_mem_of_testBit_coverMask`). -/
def coverMask (L : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | c :: cs => (periodicMask c.2 (L / c.2) <<< c.1) ||| coverMask L cs

/-- Every set bit `n` of `coverMask L cs` lies in a class `r mod m` of `cs` with `r ≤ n`. -/
theorem exists_mem_of_testBit_coverMask {L n : ℕ} {cs : List (ℕ × ℕ)}
    (h : (coverMask L cs).testBit n = true) : ∃ c ∈ cs, c.1 ≤ n ∧ c.2 ∣ n - c.1 := by
  induction cs with
  | nil => simp [coverMask] at h
  | cons c cs ih =>
    rw [coverMask, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff] at h
      rcases Nat.eq_zero_or_pos c.2 with h0 | hpos
      · simp [h0, periodicMask] at h
      · rw [testBit_periodicMask hpos, decide_eq_true_iff] at h
        exact ⟨c, List.mem_cons_self, h.1, Nat.dvd_of_mod_eq_zero h.2.1⟩
    · obtain ⟨d, hd, hd'⟩ := ih h
      exact ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

/-- **Bitmask criterion for covering systems.** Let `cs` be a list of pairs `(r, m)` of natural
numbers, standing for the classes `r mod m`, whose moduli all divide `L > 0`. If
`coverMask L cs = 2 ^ L - 1`, then every bit below `L` is set, so the classes cover the integers. -/
theorem isCoveringSystem_of_coverMask_eq {L : ℕ} (hL : 0 < L) {cs : List (ℕ × ℕ)}
    (hdvd : ∀ c ∈ cs, c.2 ∣ L) (h : coverMask L cs = 2 ^ L - 1) :
    Int.IsCoveringSystem (cs.map fun c => ((c.1 : ℤ), c.2)).toFinset := by
  intro z
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hzn : ((z % L).toNat : ℤ) = z % L := Int.toNat_of_nonneg (Int.emod_nonneg _ hL'.ne')
  have hnL : (z % L).toNat < L := by
    have := Int.emod_lt_of_pos z hL'
    omega
  have hbit : (coverMask L cs).testBit (z % L).toNat = true := by
    rw [h, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hnL
  obtain ⟨c, hc, hle, hdv⟩ := exists_mem_of_testBit_coverMask hbit
  refine ⟨((c.1 : ℤ), c.2), List.mem_toFinset.2 (List.mem_map_of_mem hc), ?_⟩
  have h₁ : z ≡ (z % L).toNat [ZMOD c.2] := by
    rw [hzn]
    exact (Int.mod_modEq z L).symm.of_dvd (Int.natCast_dvd_natCast.2 (hdvd c hc))
  exact h₁.trans (Int.natCast_modEq_iff.2 ((Nat.modEq_iff_dvd' hle).2 hdv)).symm

/-- Trifonov's covering system, as pairs `(r, m)` standing for the classes `r mod m`, listed in
the proof of Theorem 2 of Klein's paper (Section 7): 58 classes with distinct moduli between `6`
and `168`. -/
def classes : List (ℕ × ℕ) :=
  [(2, 6), (6, 7), (7, 8), (6, 9), (4, 10), (10, 11), (5, 12), (5, 14), (10, 15), (11, 16),
    (12, 18), (8, 20), (10, 21), (9, 22), (22, 24), (23, 25), (18, 27), (25, 28), (16, 30),
    (19, 32), (6, 33), (29, 35), (21, 36), (18, 40), (37, 42), (41, 44), (0, 45), (19, 48),
    (18, 50), (36, 54), (47, 55), (21, 56), (52, 60), (45, 63), (27, 66), (43, 70), (3, 72),
    (63, 75), (0, 77), (49, 80), (1, 84), (73, 88), (72, 90), (35, 96), (58, 100), (57, 105),
    (9, 108), (57, 110), (105, 112), (82, 120), (9, 126), (81, 132), (81, 135), (133, 140),
    (99, 144), (78, 150), (133, 154), (49, 168)]

/-- Trifonov's classes cover the integers. The least common multiple of their moduli is
`1663200 = 2^5 · 3^3 · 5^2 · 7 · 11`, and the kernel checks the bitmask equality of
`isCoveringSystem_of_coverMask_eq` for it. -/
theorem isCoveringSystem_classes :
    Int.IsCoveringSystem (classes.map fun c => ((c.1 : ℤ), c.2)).toFinset :=
  isCoveringSystem_of_coverMask_eq (L := 1663200) (by norm_num) (by decide +kernel)
    (by decide +kernel)

end TrifonovCovering

/-- **A distinct covering system with moduli from 6 to 168.** There is a distinct covering
system, that is, a finite set of congruences $x \equiv r \pmod m$ with $r \in \mathbb{Z}$,
$m \in \mathbb{N}$ and no two with the same modulus, such that every integer satisfies at least
one of them, whose moduli all lie between $6$ and $168$ and include both $6$ and $168$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 2 (`integers-2026-A38-thm-2`); the paper's witness is
due to Ognian Trifonov. -/
theorem exists_distinct_covering_min_six_max_168 :
    ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
      Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 6 ≤ c.2 ∧ c.2 ≤ 168) ∧
      (∃ c ∈ classes, c.2 = 6) ∧ ∃ c ∈ classes, c.2 = 168 := by
  have hmem {c : ℤ × ℕ} :
      c ∈ (TrifonovCovering.classes.map fun c => ((c.1 : ℤ), c.2)).toFinset ↔
        ∃ d ∈ TrifonovCovering.classes, ((d.1 : ℤ), d.2) = c := by
    rw [List.mem_toFinset, List.mem_map]
  refine ⟨_, TrifonovCovering.isCoveringSystem_classes, ?_, ?_,
    ⟨(2, 6), hmem.2 ⟨(2, 6), by decide, rfl⟩, rfl⟩,
    ⟨(49, 168), hmem.2 ⟨(49, 168), by decide, rfl⟩, rfl⟩⟩
  · rintro _ hx' _ hy' hxy
    obtain ⟨x, hx, rfl⟩ := hmem.1 hx'
    obtain ⟨y, hy, rfl⟩ := hmem.1 hy'
    have hnodup : (TrifonovCovering.classes.map Prod.snd).Nodup := by decide +kernel
    rw [List.inj_on_of_nodup_map hnodup hx hy hxy]
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := hmem.1 hc
    have hbounds : ∀ d ∈ TrifonovCovering.classes, 6 ≤ d.2 ∧ d.2 ≤ 168 := by decide +kernel
    exact hbounds d hd

end

end MetaMathlibExt
