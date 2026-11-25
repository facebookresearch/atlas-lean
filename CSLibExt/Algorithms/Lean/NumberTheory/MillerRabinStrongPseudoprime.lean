/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound
public import MathlibExt.NumberTheory.StrongPseudoprime

/-!
# Miller–Rabin non-witnesses are strong liars

Two definitions of the same notion live in different parts of the library:

* `Cslib.Algorithms.Lean.MillerRabin.witness a n`, the procedure `WITNESS(a, n)`, which
  computes `a^u mod n` (with `n - 1 = 2^t u`, `u` odd) and squares it `t` times, reporting a
  witness when a nontrivial square root of `1` appears or the last value is not `1`;
* `MetaMathlibExt.IsStrongPseudoprime n b`: `n` is odd and composite and
  `b^u = 1` or `b^(2^i u) = -1` for some `i < t`.

`witness_eq_false_iff` characterises the non-witnesses by the congruences, and
`isStrongPseudoprime_iff_witness_eq_false` identifies the two notions for odd composite `n` and
every natural base `a` (no range restriction: both sides depend only on `a mod n`). Rabin's
theorem in the number-theoretic language follows (`card_isStrongPseudoprime_le_quarter`): an odd
composite `n` is a strong pseudoprime to at most `(n - 1)/4` of the bases `1, …, n - 1`.

The witness condition computed by `WITNESS` is the condition of the Proposition in the note added
on 10 May 1978 to Rabin, *Probabilistic algorithm for testing primality*, J. Number Theory 12
(1980), p. 137 (attributed there to Knuth), in the form its proof establishes.

## Relation to `CSLibExt.Algorithms.Lean.NumberTheory.MillerRabinErrorBound`

This module builds on that one: `card_isStrongPseudoprime_le_quarter` is its
`card_nonwitnesses_le_quarter` restated. The private lemmas `natCast_eq_one_iff'`,
`natCast_eq_neg_one_iff'` and `pow_two_pow_mod'` restate that module's lemmas of the same names
without the prime, which are private there and so cannot be used here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MillerRabin

open Cslib.Algorithms.Lean TimeM ModularExponentiation

/-- Uniqueness of the decomposition `m = 2^k d` with `d` odd. -/
private theorem two_pow_mul_odd_inj :
    ∀ {k t d u : ℕ}, 2 ^ k * d = 2 ^ t * u → Odd d → Odd u → k = t ∧ d = u := by
  intro k
  induction k with
  | zero =>
      intro t d u h hd hu
      rcases t with _ | t
      · simpa using h
      · exfalso
        rw [pow_zero, one_mul] at h
        rw [h, pow_succ] at hd
        exact (Nat.not_even_iff_odd.2 hd) ⟨2 ^ t * u, by ring⟩
  | succ k ih =>
      intro t d u h hd hu
      rcases t with _ | t
      · exfalso
        rw [pow_zero, one_mul] at h
        rw [← h, pow_succ] at hu
        exact (Nat.not_even_iff_odd.2 hu) ⟨2 ^ k * d, by ring⟩
      · have h' : 2 ^ k * d = 2 ^ t * u := by
          rw [pow_succ, pow_succ] at h
          have : 2 * (2 ^ k * d) = 2 * (2 ^ t * u) := by linarith
          omega
        obtain ⟨h1, h2⟩ := ih h' hd hu
        exact ⟨by rw [h1], h2⟩

private theorem natCast_eq_one_iff' {n x : ℕ} (hn : 1 < n) : (x : ZMod n) = 1 ↔ x % n = 1 := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.one_mod_eq_one.2 (by omega)]

private theorem natCast_eq_neg_one_iff' {n x : ℕ} (hn : 1 < n) :
    (x : ZMod n) = -1 ↔ x % n = n - 1 := by
  have h : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [← h, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (show n - 1 < n by omega)]

private theorem pow_two_pow_mod' (n x i : ℕ) :
    (x * x % n) ^ (2 ^ i) % n = x ^ (2 ^ (i + 1)) % n := by
  rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← pow_two, ← pow_mul, ← pow_succ']

private theorem sub_one_mul_sub_one_mod {n : ℕ} (hn : 2 ≤ n) : (n - 1) * (n - 1) % n = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show (m + 1) * (m + 1) = (m + 2) * m + 1 by ring,
    Nat.mul_add_mod, Nat.one_mod_eq_one.2 (by omega)]

/-- **Converse for the squaring loop.** For `n > 2`, if the start `x < n` is `1`, or one of the
values `x^(2^i)` with `i < k` is `n - 1`, the loop reports no witness. Together with
`witnessLoop_eq_false_imp` this characterises the loop's *no witness* answer. -/
theorem witnessLoop_eq_false_of {n : ℕ} (hn : 2 < n) :
    ∀ k x, x < n → (x = 1 ∨ ∃ i < k, x ^ (2 ^ i) % n = n - 1) →
      (witnessLoop n k x).ret = false := by
  intro k
  induction k with
  | zero =>
      intro x _ h
      rcases h with rfl | ⟨i, hi, _⟩
      · simp [witnessLoop]
      · omega
  | succ k ih =>
      intro x hx h
      simp only [witnessLoop, ret_bind]
      split_ifs with hc
      · exfalso
        rcases h with rfl | ⟨i, hi, hxi⟩
        · exact hc.2.1 rfl
        · rcases i with _ | j
          · rw [pow_zero, pow_one, Nat.mod_eq_of_lt hx] at hxi
            exact hc.2.2 hxi
          · rw [← pow_two_pow_mod', hc.1, one_pow, Nat.one_mod_eq_one.2 (by omega)] at hxi
            omega
      · refine ih _ (Nat.mod_lt _ (by omega)) ?_
        rcases h with rfl | ⟨i, hi, hxi⟩
        · left; simp [Nat.one_mod_eq_one.2 (show n ≠ 1 by omega)]
        · rcases i with _ | j
          · rw [pow_zero, pow_one, Nat.mod_eq_of_lt hx] at hxi
            left
            rw [hxi]
            exact sub_one_mul_sub_one_mod (by omega)
          · right
            exact ⟨j, by omega, by rw [pow_two_pow_mod']; exact hxi⟩

/-- **The Miller–Rabin non-witnesses, by congruences.** For `n > 2`, with `n - 1 = 2^t u` and `u`
odd (`twoAdicSplit`), `WITNESS(a, n)` reports no witness if and only if `a^u ≡ 1 (mod n)` or
`a^(2^i u) ≡ -1 (mod n)` for some `i < t`. In the notation of Rabin (J. Number Theory 12
(1980), note added 10 May 1978, p. 137: `x₀ = a^u mod n`, `xᵢ = x_{i-1}² mod n`), these are the
bases for which the squaring chain reaches `1` either from the start or through `n - 1`. -/
theorem witness_eq_false_iff {n a : ℕ} (hn : 2 < n) :
    (witness a n).ret = false ↔
      (a ^ (twoAdicSplit (n - 1)).2 % n = 1 ∨
        ∃ i < (twoAdicSplit (n - 1)).1, a ^ (2 ^ i * (twoAdicSplit (n - 1)).2) % n = n - 1) := by
  refine ⟨witness_eq_false_imp (by omega), fun h => ?_⟩
  obtain ⟨_, hodd⟩ := twoAdicSplit_spec (n - 1) (by omega)
  have hu : 0 < (twoAdicSplit (n - 1)).2 := by omega
  simp only [witness, ret_bind]
  rw [modularExponentiation_correct a _ n hu (by omega)]
  refine witnessLoop_eq_false_of hn _ _ (Nat.mod_lt _ (by omega)) ?_
  rcases h with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, hi, ?_⟩
    rwa [← Nat.pow_mod, ← pow_mul, Nat.mul_comm]

/-- **Miller–Rabin non-witnesses are exactly the bases to which `n` is a strong pseudoprime.**
For an odd composite `n` and every natural `a`, `n` is a strong pseudoprime to the base
`a mod n` (`MetaMathlibExt.IsStrongPseudoprime`) if and only if the library's `witness a n`
(the procedure `WITNESS` of the Miller–Rabin test) reports no witness. This bridges the
number-theoretic and the algorithmic definitions; both sides depend only on `a mod n`. -/
theorem isStrongPseudoprime_iff_witness_eq_false {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime)
    (hodd : Odd n) (a : ℕ) :
    MetaMathlibExt.IsStrongPseudoprime n (a : ZMod n) ↔ (witness a n).ret = false := by
  have hn2 : 2 < n := by
    rcases hodd with ⟨m, rfl⟩
    rcases m with _ | m
    · omega
    · rcases m with _ | m
      · exact absurd Nat.prime_three hcomp
      · omega
  obtain ⟨hsplit, hu⟩ := twoAdicSplit_spec (n - 1) (by omega)
  set t := (twoAdicSplit (n - 1)).1
  set u := (twoAdicSplit (n - 1)).2
  rw [witness_eq_false_iff hn2, MetaMathlibExt.isStrongPseudoprime_iff]
  constructor
  · rintro ⟨-, -, -, k, d, hkd, hd, h⟩
    obtain ⟨rfl, rfl⟩ := two_pow_mul_odd_inj (hkd.symm.trans hsplit) hd
      (Nat.odd_iff.2 hu)
    rcases h with h | ⟨i, hi, h⟩
    · left
      rwa [← Nat.cast_pow, natCast_eq_one_iff' hn] at h
    · right
      refine ⟨i, hi, ?_⟩
      rwa [← Nat.cast_pow, natCast_eq_neg_one_iff' hn] at h
  · intro h
    refine ⟨hn, hcomp, hodd, t, u, hsplit, Nat.odd_iff.2 hu, ?_⟩
    rcases h with h | ⟨i, hi, h⟩
    · left
      rwa [← Nat.cast_pow, natCast_eq_one_iff' hn]
    · right
      refine ⟨i, hi, ?_⟩
      rwa [← Nat.cast_pow, natCast_eq_neg_one_iff' hn]

open Classical in
/-- **Rabin's `1/4` bound for strong pseudoprimes.** An odd composite `n` is a strong pseudoprime
(`MetaMathlibExt.IsStrongPseudoprime`) to at most `(n - 1)/4` of the bases `1, …, n - 1`.
This is the Proposition in the note added on 10 May 1978 to Rabin, *Probabilistic algorithm for
testing primality*, J. Number Theory 12 (1980), p. 137 (for odd composite `n > 4`, at least
`3(n - 1)/4` of the `1 ≤ x < n` are witnesses), deduced from his Theorem 1 (p. 130); the bound was
proved independently by Monier (1980; attribution taken from secondary sources). It is the
number-theoretic form of `card_nonwitnesses_le_quarter`. -/
theorem card_isStrongPseudoprime_le_quarter {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime)
    (hodd : Odd n) :
    ((Finset.Ioo 0 n).filter fun a : ℕ => MetaMathlibExt.IsStrongPseudoprime n (a : ZMod n)).card ≤
      (n - 1) / 4 := by
  have h : ((Finset.Ioo 0 n).filter fun a : ℕ =>
      MetaMathlibExt.IsStrongPseudoprime n (a : ZMod n)) = nonwitnesses n := by
    unfold nonwitnesses
    exact Finset.filter_congr fun a _ =>
      isStrongPseudoprime_iff_witness_eq_false hn hcomp hodd a
  rw [h]
  exact card_nonwitnesses_le_quarter hn (Nat.odd_iff.1 hodd) hcomp

end Cslib.Algorithms.Lean.MillerRabin
