/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Infix
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord

/-!
# Problems from the OEIS settled with Walnut

Statements from Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to
Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article
25.3.8 (arXiv:2503.04122): the theorem of Hajdu, Tijdeman, and Varga on
`(x-1)^c (x+1)^d` modulo `3`, Kimberling's conjecture on the anti-Tribonacci
sequence, and the greedy `3`-subsumfree sequences `S_{1,2,3}`, `S_{1,3,4}`,
`S_{1,4,5}`; the gaps between unsums of upper Wythoff numbers (Section 2, Lemmas 1-9)
and Zaslavsky's description of the anti-Fibonacci numbers (Theorem 11).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The least positive integer not in `s` (the source's `mex` over the positive integers, used
to build the anti-Tribonacci sequence), found among `1, …, |s| + 1`, where it must lie; see
`antiTribonacciMex_pos`, `antiTribonacciMex_notMem` and `antiTribonacciMex_le_of_notMem`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciMex (s : Finset ℕ) : ℕ :=
  ((List.range (s.card + 2)).find? fun m => decide (0 < m ∧ m ∉ s)).getD 0

/-- `antiTribonacciMex {1, 2, 3, 6} = 4`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_example : antiTribonacciMex {1, 2, 3, 6} = 4 := by
  decide +kernel

private theorem antiTribonacciMex_spec (s : Finset ℕ) :
    0 < antiTribonacciMex s ∧ antiTribonacciMex s ∉ s ∧
      ∀ m, 0 < m → m ∉ s → antiTribonacciMex s ≤ m := by
  have hex : ∃ m ∈ List.range (s.card + 2), 0 < m ∧ m ∉ s := by
    by_contra h
    push Not at h
    have hsub : Finset.Icc 1 (s.card + 1) ⊆ s := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      exact h m (List.mem_range.mpr (by omega)) (by omega)
    have := Finset.card_le_card hsub
    simp at this
  obtain ⟨m0, hm0, hp0⟩ := hex
  have hsome : ((List.range (s.card + 2)).find? fun m => decide (0 < m ∧ m ∉ s)).isSome :=
    List.find?_isSome.mpr ⟨m0, hm0, by simpa using hp0⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hval : antiTribonacciMex s = b := by unfold antiTribonacciMex; rw [hb]; rfl
  rw [List.find?_eq_some_iff_getElem] at hb
  obtain ⟨hpb, i, hi, hib, hmin⟩ := hb
  simp only [List.getElem_range] at hib
  subst hib
  simp only [decide_eq_true_eq] at hpb
  refine ⟨hval ▸ hpb.1, hval ▸ hpb.2, fun m hm hms => ?_⟩
  rw [hval]
  by_contra hlt
  push Not at hlt
  have := hmin m hlt
  simp [hm, hms] at this

/-- The `mex` value is positive.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_pos (s : Finset ℕ) : 0 < antiTribonacciMex s :=
  (antiTribonacciMex_spec s).1

/-- The `mex` value is not in `s`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_notMem (s : Finset ℕ) : antiTribonacciMex s ∉ s :=
  (antiTribonacciMex_spec s).2.1

/-- The `mex` value is at most every positive integer not in `s`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_le_of_notMem (s : Finset ℕ) {m : ℕ} (hm : 0 < m)
    (hms : m ∉ s) : antiTribonacciMex s ≤ m :=
  (antiTribonacciMex_spec s).2.2 m hm hms

/-- The anti-Tribonacci construction: entry `n` is `((A_{n+1}, B_{n+1}, C_{n+1},
D_{n+1}), U)` where `A_1, B_1, C_1, D_1 = 1, 2, 3, 6`, `U` is the set of all values
used so far, `A_{n+1}, B_{n+1}, C_{n+1}` are successive `mex` values and
`D_{n+1} = A_{n+1} + B_{n+1} + C_{n+1}`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciState : ℕ → (ℕ × ℕ × ℕ × ℕ) × Finset ℕ
  | 0 => ((1, 2, 3, 6), {1, 2, 3, 6})
  | n + 1 =>
    let s := (antiTribonacciState n).2
    let a := antiTribonacciMex s
    let b := antiTribonacciMex (insert a s)
    let c := antiTribonacciMex (insert b (insert a s))
    ((a, b, c, a + b + c), insert (a + b + c) (insert c (insert b (insert a s))))

/-- `A_n` (for `n ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciA (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.1

/-- `B_n` (for `n ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciB (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.2.1

/-- `C_n` (for `n ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciC (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.2.2.1

/-- The anti-Tribonacci numbers `D_n` (for `n ≥ 1`), OEIS A265389.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciD (n : ℕ) : ℕ := (antiTribonacciState (n - 1)).1.2.2.2

/-- The first anti-Tribonacci numbers are `6, 16, 27, 36`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciD_small :
    antiTribonacciD 1 = 6 ∧ antiTribonacciD 2 = 16 ∧ antiTribonacciD 3 = 27 ∧
      antiTribonacciD 4 = 36 := by
  decide +kernel

/-- The members below `m` of the greedy `3`-subsumfree sequence `S_{x,y,z}`: the start
values `x < y < z`, and every later number that is not a sum of three different
earlier members.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 6. -/
public def greedySubsumfreeBelow (x y z : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | m + 1 =>
    let s := greedySubsumfreeBelow x y z m
    if m = x ∨ m = y ∨ m = z ∨
        (z < m ∧ ¬ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a < b ∧ b < c ∧ a + b + c = m) then
      insert m s
    else s

/-- `S_{1,2,3}` starts `1, 2, 3, 4, 5, 13, 14, 15, 25`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 6. -/
public theorem greedySubsumfreeBelow_one_two_three :
    greedySubsumfreeBelow 1 2 3 26 = {1, 2, 3, 4, 5, 13, 14, 15, 25} := by
  decide +kernel

/-- Hajdu, Tijdeman, and Varga, as recalled by the source: if no coefficient of
`(x-1)^c (x+1)^d` is divisible by `3`, then `c + d + 1` is `3^j`, `2·3^j`, `3^i + 3^j`,
or `2·3^i + 3^j` for some `i > j ≥ 0`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 10 (`jis-2025-25.3.8-thm-10`), citing Hajdu, Tijdeman, and Varga. -/
public theorem_wanted coeff_not_dvd_three_shape (c d : ℕ)
    (h : ∀ k ≤ c + d,
      ¬ (3 : ℤ) ∣ (((Polynomial.X - 1) ^ c * (Polynomial.X + 1) ^ d : Polynomial ℤ)).coeff k) :
    ∃ i j : ℕ, j < i ∧ (c + d + 1 = 3 ^ j ∨ c + d + 1 = 2 * 3 ^ j ∨
      c + d + 1 = 3 ^ i + 3 ^ j ∨ c + d + 1 = 2 * 3 ^ i + 3 ^ j)

/-- Kimberling's conjecture: for every `n ≥ 1`, `0 ≤ 10n - 6 - 3A_n ≤ 2`,
`0 ≤ 10n - 2 - 3B_n ≤ 3`, `0 ≤ 10n + 1 - 3C_n ≤ 3`, and `0 ≤ 10n - 3 - D_n ≤ 2`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 12 (`jis-2025-25.3.8-thm-12`). -/
public theorem_wanted kimberling_antiTribonacci {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ 10 * (n : ℤ) - 6 - 3 * antiTribonacciA n ∧ 10 * (n : ℤ) - 6 - 3 * antiTribonacciA n ≤ 2) ∧
    (0 ≤ 10 * (n : ℤ) - 2 - 3 * antiTribonacciB n ∧ 10 * (n : ℤ) - 2 - 3 * antiTribonacciB n ≤ 3) ∧
    (0 ≤ 10 * (n : ℤ) + 1 - 3 * antiTribonacciC n ∧ 10 * (n : ℤ) + 1 - 3 * antiTribonacciC n ≤ 3) ∧
    (0 ≤ 10 * (n : ℤ) - 3 - antiTribonacciD n ∧ 10 * (n : ℤ) - 3 - antiTribonacciD n ≤ 2)

/-- For positive integers `z`: `z ∈ S_{1,2,3}` iff `z ∈ {1, 5, 13}` or
`z mod 23 ∈ {2, 3, 4, 14, 15}`; `z ∈ S_{1,3,4}` iff `z ∈ {1, 7, 19}` or
`z mod 33 ∈ {3, 4, 5, 6, 20, 21, 22}`; `z ∈ S_{1,4,5}` iff `z ∈ {1, 9, 25}` or
`z mod 43 ∈ {4, …, 8, 26, …, 29}`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 15 (`jis-2025-25.3.8-thm-15`). -/
public theorem_wanted mem_greedySubsumfree_iff {z : ℕ} (hz : 0 < z) :
    (z ∈ greedySubsumfreeBelow 1 2 3 (z + 1) ↔
      z ∈ ({1, 5, 13} : Finset ℕ) ∨ z % 23 ∈ ({2, 3, 4, 14, 15} : Finset ℕ)) ∧
    (z ∈ greedySubsumfreeBelow 1 3 4 (z + 1) ↔
      z ∈ ({1, 7, 19} : Finset ℕ) ∨ z % 33 ∈ ({3, 4, 5, 6, 20, 21, 22} : Finset ℕ)) ∧
    (z ∈ greedySubsumfreeBelow 1 4 5 (z + 1) ↔
      z ∈ ({1, 9, 25} : Finset ℕ) ∨ z % 43 ∈ ({4, 5, 6, 7, 8, 26, 27, 28, 29} : Finset ℕ))


/-- A positive integer `x` is an *unsum* (OEIS A260317) if it is not `p + q` for upper Wythoff
numbers `p < q`. As in the source, the upper Wythoff numbers are the positions of the letter
`b` in the Fibonacci word counted from one, so `p` is upper Wythoff iff `fibInf (p - 1) = true`
(`fibInf` codes `a` as `false`, `b` as `true`); see `upperWythoff_small` and
`isUpperWythoffUnsum_small`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2, defining unsums as the members of OEIS A260317. -/
public def IsUpperWythoffUnsum (x : ℕ) : Prop :=
  0 < x ∧ ¬ ∃ p < x, ∃ q < x, 0 < p ∧ p < q ∧ p + q = x ∧
    fibInf (p - 1) = true ∧ fibInf (q - 1) = true

/-- Being an unsum is decidable; the instance is classical (noncomputable). The structural
instance would evaluate `fibInf (q - 1)`, which builds the Fibonacci-word iterate
`fibWord (q + 1)` of Fibonacci-number length, so `decide` would exhaust memory at modest
inputs. Small values are decided through a fixed prefix of the Fibonacci word instead (see
`upperWythoff_small` and `isUpperWythoffUnsum_small`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable instance : DecidablePred IsUpperWythoffUnsum := Classical.decPred _

private theorem fibInf_eq_fibWord_seven {k : ℕ} (hk : k < 34) :
    fibInf k = (fibWord 7).getD k false := by
  have : (fibWord 7).length = 34 := by decide
  exact (fibInf_agrees 7 k (by omega)).symm

private def unsumCheck (x : ℕ) : Prop :=
  0 < x ∧ ¬ ∃ p < x, ∃ q < x, 0 < p ∧ p < q ∧ p + q = x ∧
    (fibWord 7).getD (p - 1) false = true ∧ (fibWord 7).getD (q - 1) false = true

private instance : DecidablePred unsumCheck := fun x => by
  unfold unsumCheck; infer_instance

private theorem isUpperWythoffUnsum_iff_check {x : ℕ} (hx : x ≤ 34) :
    IsUpperWythoffUnsum x ↔ unsumCheck x := by
  unfold IsUpperWythoffUnsum unsumCheck
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun ⟨p, hp, q, hq, hp0, hpq, hs, h1, h2⟩ => h ⟨p, hp, q, hq, hp0, hpq, hs, ?_, ?_⟩⟩
    · rwa [fibInf_eq_fibWord_seven (by omega)]
    · rwa [fibInf_eq_fibWord_seven (by omega)]
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun ⟨p, hp, q, hq, hp0, hpq, hs, h1, h2⟩ => h ⟨p, hp, q, hq, hp0, hpq, hs, ?_, ?_⟩⟩
    · rwa [← fibInf_eq_fibWord_seven (by omega)]
    · rwa [← fibInf_eq_fibWord_seven (by omega)]

/-- The upper Wythoff numbers below `30` are `2, 5, 7, 10, 13, 15, 18, 20, 23, 26, 28`, as
displayed in the source.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoff_small :
    (Finset.range 30).filter (fun p => 0 < p ∧ fibInf (p - 1) = true) =
      {2, 5, 7, 10, 13, 15, 18, 20, 23, 26, 28} := by
  have : (Finset.range 30).filter (fun p => 0 < p ∧ fibInf (p - 1) = true) =
      (Finset.range 30).filter (fun p => 0 < p ∧ (fibWord 7).getD (p - 1) false = true) := by
    refine Finset.filter_congr fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [fibInf_eq_fibWord_seven (by omega)]
  rw [this]
  decide +kernel

private theorem count_unsum_eq {n : ℕ} (hn : n ≤ 34) :
    Nat.count IsUpperWythoffUnsum n = Nat.count unsumCheck n := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [Finset.mem_range] at hx
  exact isUpperWythoffUnsum_iff_check (by omega)

/-- The unsums up to `21` are `1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 14, 16, 19, 21` (OEIS A260317).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem isUpperWythoffUnsum_small :
    (Finset.range 22).filter IsUpperWythoffUnsum =
      {1, 2, 3, 4, 5, 6, 8, 10, 11, 13, 14, 16, 19, 21} := by
  have : (Finset.range 22).filter IsUpperWythoffUnsum = (Finset.range 22).filter unsumCheck := by
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    exact isUpperWythoffUnsum_iff_check (by omega)
  rw [this]
  decide +kernel

/-- The `i`-th gap between consecutive unsums (counted from zero), `a(i + 2) - a(i + 1)` for the
unsums `a(1) < a(2) < ⋯` of OEIS A260317; this is OEIS A260311 shifted by one.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumGap (i : ℕ) : ℕ :=
  Nat.nth IsUpperWythoffUnsum (i + 1) - Nat.nth IsUpperWythoffUnsum i

private theorem nth_unsum {i n : ℕ} (hn : n ≤ 34) (h : unsumCheck n)
    (hc : Nat.count unsumCheck n = i) : Nat.nth IsUpperWythoffUnsum i = n := by
  rw [← hc, ← count_unsum_eq hn]
  exact Nat.nth_count ((isUpperWythoffUnsum_iff_check hn).mpr h)

/-- The first thirteen gaps between unsums are `1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumGap_small :
    (List.range 13).map upperWythoffUnsumGap = [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2] := by
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, upperWythoffUnsumGap]
  rw [nth_unsum (i := 0) (n := 1) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 1) (n := 2) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 2) (n := 3) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 3) (n := 4) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 4) (n := 5) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 5) (n := 6) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 6) (n := 8) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 7) (n := 10) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 8) (n := 11) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 9) (n := 13) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 10) (n := 14) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 11) (n := 16) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 12) (n := 19) (by omega) (by decide +kernel) (by decide +kernel),
    nth_unsum (i := 13) (n := 21) (by omega) (by decide +kernel) (by decide +kernel)]

/-- A *marker* is a gap index `i ≥ 10` with gap `2`: the source marks the entries `2` of
A260311 that follow the irregular prefix `1111122121` of length ten.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public def IsUpperWythoffUnsumMarker (i : ℕ) : Prop :=
  10 ≤ i ∧ upperWythoffUnsumGap i = 2

/-- The `j`-th marker (counted from zero) in increasing order.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumMarker (j : ℕ) : ℕ :=
  Nat.nth IsUpperWythoffUnsumMarker j

/-- The word of gaps strictly between the `j`-th and `(j + 1)`-th markers (both counted from
zero); the source writes the gap sequence after the prefix as
`2 W_1 2 W_1 2 W_2 2 W_2 2 W_3 2 ⋯`, so these words are `W_1, W_1, W_2, W_2, …`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumWord (j : ℕ) : List ℕ :=
  (List.range' (upperWythoffUnsumMarker j + 1)
    (upperWythoffUnsumMarker (j + 1) - upperWythoffUnsumMarker j - 1)).map upperWythoffUnsumGap

/-- The source's palindrome `W_i` (for `i ≥ 1`): the word between the `(2i - 2)`-th and
`(2i - 1)`-th markers.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public noncomputable def upperWythoffUnsumPalindrome (i : ℕ) : List ℕ :=
  upperWythoffUnsumWord (2 * i - 2)

private theorem gap_eq (i : ℕ) (h : i < 13) :
    upperWythoffUnsumGap i = [1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2].getD i 0 := by
  rw [← upperWythoffUnsumGap_small]
  simp [h]

/-- The first marker is gap index `10` and the second is `12`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumMarker_zero_one :
    upperWythoffUnsumMarker 0 = 10 ∧ upperWythoffUnsumMarker 1 = 12 := by
  have h10 : IsUpperWythoffUnsumMarker 10 := ⟨le_rfl, gap_eq 10 (by omega)⟩
  have h0 : upperWythoffUnsumMarker 0 = 10 := by
    unfold upperWythoffUnsumMarker
    rw [Nat.nth_zero]
    exact le_antisymm (Nat.sInf_le h10) (le_csInf ⟨10, h10⟩ fun i hi => hi.1)
  refine ⟨h0, ?_⟩
  have h12 : IsUpperWythoffUnsumMarker 12 := ⟨by omega, gap_eq 12 (by omega)⟩
  have h11 : ¬ IsUpperWythoffUnsumMarker 11 := fun h => by
    have := h.2
    rw [gap_eq 11 (by omega)] at this
    simp at this
  unfold upperWythoffUnsumMarker at h0 ⊢
  rw [Nat.nth_eq_sInf]
  refine le_antisymm (Nat.sInf_le ⟨h12, fun k hk => ?_⟩) (le_csInf ⟨12, h12, fun k hk => ?_⟩ ?_)
  · obtain rfl : k = 0 := by omega
    rw [h0]; omega
  · obtain rfl : k = 0 := by omega
    rw [h0]; omega
  · rintro x ⟨hx, hlt⟩
    have := hlt 0 (by omega)
    rw [h0] at this
    by_contra hx12
    obtain rfl : x = 11 := by omega
    exact h11 hx

/-- The first palindrome is `W_1 = 3`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 2. -/
public theorem upperWythoffUnsumPalindrome_one : upperWythoffUnsumPalindrome 1 = [3] := by
  obtain ⟨h0, h1⟩ := upperWythoffUnsumMarker_zero_one
  simp only [upperWythoffUnsumPalindrome, upperWythoffUnsumWord, Nat.reduceMul, Nat.sub_self,
    zero_add, h0, h1]
  simp [gap_eq 11 (by omega)]

/-- The tenth gap between unsums is the last gap equal to `1`: with gaps counted from zero,
gap `9` is `1` and no gap with index `≥ 10` is `1`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 1 (`jis-2025-25.3.8-lem-1`). -/
public theorem_wanted upperWythoffUnsumGap_ne_one :
    upperWythoffUnsumGap 9 = 1 ∧ ∀ i, 10 ≤ i → upperWythoffUnsumGap i ≠ 1

/-- For every word `W` between two consecutive markers, the digit sum of `W` plus two is a
Fibonacci number.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 2 (`jis-2025-25.3.8-lem-2`). -/
public theorem_wanted upperWythoffUnsumWord_sum_add_two_isFib (j : ℕ) :
    ∃ m, (upperWythoffUnsumWord j).sum + 2 = Nat.fib m

/-- The sums of the palindromes, each counted with its preceding marker `2` as in the source's
remark that adding the preceding digit `2` gives the Fibonacci numbers, are
`F_5, F_5, F_6, F_6, …`: the `j`-th word between markers has digit sum `F_(j/2 + 5) - 2`
(integer division). The bare digit sums are `3, 3, 6, 6, 11, …`, so the literal reading
without the marker fails at the first word (`3 ≠ F_5 = 5`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 3 (`jis-2025-25.3.8-lem-3`). -/
public theorem_wanted upperWythoffUnsumWord_sum_add_two (j : ℕ) :
    (upperWythoffUnsumWord j).sum + 2 = Nat.fib (j / 2 + 5)

/-- Each `W_i` is a palindrome.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 4 (`jis-2025-25.3.8-lem-4`). -/
public theorem_wanted upperWythoffUnsumPalindrome_reverse {i : ℕ} (hi : 1 ≤ i) :
    (upperWythoffUnsumPalindrome i).reverse = upperWythoffUnsumPalindrome i

/-- Each `W_i` starts and ends with digit `3`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 5 (`jis-2025-25.3.8-lem-5`). -/
public theorem_wanted upperWythoffUnsumPalindrome_head_getLast {i : ℕ} (hi : 1 ≤ i) :
    (upperWythoffUnsumPalindrome i).head? = some 3 ∧
      (upperWythoffUnsumPalindrome i).getLast? = some 3

/-- If a word between markers has the form `3V3`, then `3V` is a prefix of the next word
between markers; in particular the next word equals it if their digit sums agree.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 6 (`jis-2025-25.3.8-lem-6`). -/
public theorem_wanted upperWythoffUnsumWord_prefix_next {j : ℕ} {V : List ℕ}
    (h : upperWythoffUnsumWord j = 3 :: V ++ [3]) :
    (3 :: V) <+: upperWythoffUnsumWord (j + 1) ∧
      ((upperWythoffUnsumWord (j + 1)).sum = (upperWythoffUnsumWord j).sum →
        upperWythoffUnsumWord (j + 1) = upperWythoffUnsumWord j)

/-- `W_i` is a prefix of `W_(i+1)` iff `i` is odd (for `i ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 7 (`jis-2025-25.3.8-lem-7`). -/
public theorem_wanted upperWythoffUnsumPalindrome_isPrefix_succ_iff {i : ℕ} (hi : 1 ≤ i) :
    upperWythoffUnsumPalindrome i <+: upperWythoffUnsumPalindrome (i + 1) ↔ Odd i

/-- Writing `W_i = 3 V_i 3` (`V_i` is `W_i` with its first and last digit removed): for odd
`i ≥ 2`, `W_(i+1) = W_i 5 V_(i-1) 3`, and for even `i ≥ 2`, `W_(i+1) = 3 V_i 5 W_(i-1)`. In
particular `|W_(i+1)| = |W_i| + |W_(i-1)|` with `|W_1| = 1`, `|W_2| = 2`, and
`|W_i| = F_(i+1)`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 8 (`jis-2025-25.3.8-lem-8`). -/
public theorem_wanted upperWythoffUnsumPalindrome_succ :
    (∀ i, 2 ≤ i →
      (Odd i → upperWythoffUnsumPalindrome (i + 1) = upperWythoffUnsumPalindrome i ++
        5 :: (upperWythoffUnsumPalindrome (i - 1)).tail.dropLast ++ [3]) ∧
      (Even i → upperWythoffUnsumPalindrome (i + 1) =
        3 :: (upperWythoffUnsumPalindrome i).tail.dropLast ++
          5 :: upperWythoffUnsumPalindrome (i - 1)) ∧
      (upperWythoffUnsumPalindrome (i + 1)).length =
        (upperWythoffUnsumPalindrome i).length + (upperWythoffUnsumPalindrome (i - 1)).length) ∧
    (upperWythoffUnsumPalindrome 1).length = 1 ∧ (upperWythoffUnsumPalindrome 2).length = 2 ∧
    ∀ i, 1 ≤ i → (upperWythoffUnsumPalindrome i).length = Nat.fib (i + 1)

/-- Let `𝐕` be the Fibonacci word under the coding `a ↦ 5`, `b ↦ 3`. The palindromes `W_i`
converge to `3𝐕`: for every position `k` (counted from zero), `W_i` has digit `(3𝐕)[k]` at
position `k` for all large `i`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 9 (`jis-2025-25.3.8-lem-9`). -/
public theorem_wanted upperWythoffUnsumPalindrome_tendsto (k : ℕ) :
    ∃ N, ∀ i, N ≤ i → (upperWythoffUnsumPalindrome i)[k]? =
      some (if k = 0 then 3 else if fibInf (k - 1) = true then 3 else 5)

/-- The period-doubling word, the fixed point of `a ↦ ab`, `b ↦ aa`, as Walnut's `PD`: here
`a` is `1` and `b` is `0`. The source's prose says `a` is `0` and `b` is `1`, but its Walnut
definition `antifib` (`PD[k]=@1` gives `9 + 10k`) and its displayed anti-Fibonacci numbers
`0, 3, 9, 13, …` need `PD[0] = 1`. Entry `n` is the `n`-th iterate from `a`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def periodDoublingWord : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => (periodDoublingWord n).flatMap fun c => if c = 1 then [1, 0] else [1, 1]

/-- Letter `k` (counted from zero) of the period-doubling word, read from iterate
`Nat.log 2 k + 1`, which is guaranteed to contain index `k` and has length
`2 ^ (Nat.log 2 k + 1) ≤ 2k + 2`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def periodDoubling (k : ℕ) : ℕ := (periodDoublingWord (Nat.log 2 k + 1)).getD k 0

/-- The `n`-th iterate of the period-doubling substitution has length `2 ^ n`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem length_periodDoublingWord (n : ℕ) : (periodDoublingWord n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ L : List ℕ, (L.flatMap fun c => if c = 1 then [1, 0] else [1, 1]).length =
        2 * L.length := by
      intro L
      induction L with
      | nil => rfl
      | cons c L ihL =>
        simp only [List.flatMap_cons, List.length_append, ihL, List.length_cons]
        split_ifs <;> simp <;> omega
    rw [periodDoublingWord, h, ih, Nat.pow_succ, Nat.mul_comm]

private theorem periodDoublingWord_prefix_succ (n : ℕ) :
    periodDoublingWord n <+: periodDoublingWord (n + 1) := by
  induction n with
  | zero => exact ⟨[0], rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap fun c => if c = 1 then [1, 0] else [1, 1], ?_⟩
    change (periodDoublingWord n).flatMap (fun c => if c = 1 then [1, 0] else [1, 1]) ++ _ =
      (periodDoublingWord (n + 1)).flatMap (fun c => if c = 1 then [1, 0] else [1, 1])
    rw [← ht, List.flatMap_append]

private theorem periodDoublingWord_prefix {n m : ℕ} (h : n ≤ m) :
    periodDoublingWord n <+: periodDoublingWord m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (periodDoublingWord_prefix_succ _)

/-- `periodDoubling k` is letter `k` of every iterate of the period-doubling substitution
long enough to contain it.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem periodDoublingWord_getD {m k : ℕ} (hk : k < 2 ^ m) :
    (periodDoublingWord m).getD k 0 = periodDoubling k := by
  have hk' : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by decide) k
  unfold periodDoubling
  have key : ∀ {a b : ℕ}, a ≤ b → k < 2 ^ a →
      (periodDoublingWord a).getD k 0 = (periodDoublingWord b).getD k 0 := by
    intro a b hab hka
    have hp := periodDoublingWord_prefix hab
    have hla : k < (periodDoublingWord a).length := by
      rw [length_periodDoublingWord]; exact hka
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hla,
      List.getElem?_eq_getElem (lt_of_lt_of_le hla hp.length_le), Option.getD_some]
    exact hp.getElem hla
  rcases le_total m (Nat.log 2 k + 1) with h | h
  · exact key h hk
  · exact (key h hk').symm

/-- `PD` starts `1, 0, 1, 1, 1, 0, 1, 0`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem periodDoubling_small :
    (List.range 8).map periodDoubling = [1, 0, 1, 1, 1, 0, 1, 0] := by
  decide +kernel

/-- The anti-Fibonacci construction: entry `n` is `((A_(n+1), B_(n+1), C_(n+1)), U)` where
`A_1, B_1, C_1 = 1, 2, 3`, `U` is the set of values used so far, `A_(n+1), B_(n+1)` are the
next two missing positive integers, and `C_(n+1) = A_(n+1) + B_(n+1)`. The `C_n` are the
anti-Fibonacci numbers (OEIS A075326 without its initial `0`) and the missing numbers
`A_1, B_1, A_2, B_2, …` are the non-anti-Fibonacci numbers `Y_1, Y_2, …` (OEIS A249031).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciState : ℕ → (ℕ × ℕ × ℕ) × Finset ℕ
  | 0 => ((1, 2, 3), {1, 2, 3})
  | n + 1 =>
    let s := (antiFibonacciState n).2
    let a := antiTribonacciMex s
    let b := antiTribonacciMex (insert a s)
    ((a, b, a + b), insert (a + b) (insert b (insert a s)))

/-- `A_n = Y_(2n-1)` (for `n ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciA (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.1

/-- `B_n = Y_(2n)` (for `n ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciB (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.2.1

/-- The anti-Fibonacci numbers `X_n = C_n` (for `n ≥ 1`).

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiFibonacciC (n : ℕ) : ℕ := (antiFibonacciState (n - 1)).1.2.2

/-- The first anti-Fibonacci numbers are `3, 9, 13, 18` and the first non-anti-Fibonacci
numbers are `1, 2, 4, 5, 6, 7, 8, 10`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiFibonacci_small :
    (List.range 4).map (fun n => antiFibonacciC (n + 1)) = [3, 9, 13, 18] ∧
      (List.range 4).map (fun n => (antiFibonacciA (n + 1), antiFibonacciB (n + 1))) =
        [(1, 2), (4, 5), (6, 7), (8, 10)] := by
  decide +kernel

/-- Zaslavsky: `X_(2k+1) = 3 + 10k` and `X_(2k+2) = 8 + 10k + PD[k]`; `Y_(4k+1) = 5k + 1`,
`Y_(4k+2) = 5k + 2`, `Y_(4k+3) = 5k + 3 + PD[k]`, and `Y_(4k+4) = 5(k + 1)` (the source's
`Y_(4k) = 5k` for `k ≥ 1`; its `Y_0 = 0` is not a non-anti-Fibonacci number and is omitted).
`PD` is Walnut's period-doubling word (`PD[0] = 1`); with the prose encoding `a = 0` the
formulas give `X_2 = 8` and `Y_3 = 3`, but `X_2 = 9` and `Y_3 = 4`.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Theorem 11 (`jis-2025-25.3.8-thm-11`), due to Zaslavsky. -/
public theorem_wanted zaslavsky_antiFibonacci (k : ℕ) :
    antiFibonacciC (2 * k + 1) = 3 + 10 * k ∧
      antiFibonacciC (2 * k + 2) = 8 + 10 * k + periodDoubling k ∧
      antiFibonacciA (2 * k + 1) = 5 * k + 1 ∧ antiFibonacciB (2 * k + 1) = 5 * k + 2 ∧
      antiFibonacciA (2 * k + 2) = 5 * k + 3 + periodDoubling k ∧
      antiFibonacciB (2 * k + 2) = 5 * (k + 1)

end

end MetaMathlibExt
