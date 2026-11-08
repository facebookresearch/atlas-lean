/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sequences of the stable matching problem

Statements from Matvey Borodin, Aidan Duncan, Boyan Litchev, Jiahe Liu,
Veronika Moroz, Matthew Qian, Rohith Raghavan, Garima Rastogi, Michael Voigt,
and Tanya Khovanova, "Sequences of the Stable Matching Problem", *Journal of
Integer Sequences* 27 (2024), Article 24.2.2 (arXiv:2201.00645).

A preference profile for `n` men and `n` women is a pair `P` of families of
permutations: `P.1 i r` is the woman man `i` ranks at position `r` and
`P.2 j r` is the man woman `j` ranks at position `r`. Positions are zero-based,
so the paper's ranking `r + 1` (with `1` the favorite and `n` the least
favorite) is position `r` here. A matching is a permutation `μ` of `Fin n`:
man `i` is married to woman `μ i`.

The men-proposing Gale–Shapley algorithm is encoded by the number of women
each man has proposed to after `t` rounds (`gsProposals`). In that state a man
is provisionally engaged (`GSEngaged`) exactly when he has proposed at least
once and the woman he proposed to last ranks him above every man who has
proposed to her so far; this is the woman's held suitor in the paper's
description, since each woman keeps the best suitor proposed so far. In each
round every unengaged man proposes to his next choice, and the number of
rounds is the first `t` after which every man is engaged
(`galeShapleyRounds`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Matching.GaleShapley

set_option autoImplicit false

namespace MetaMathlibExt

namespace StableMatchingSequences

@[expose] public section

open Finset Nat

/-- A preference profile for `n` men and `n` women: `P.1 i r` is the woman man
`i` ranks at zero-based position `r`, and `P.2 j r` is the man woman `j` ranks
at position `r`.

Source: Borodin, Duncan, Litchev, Liu, Moroz, Qian, Raghavan, Rastogi, Voigt,
and Khovanova, *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2, Section 2. -/
abbrev PreferenceProfile (n : ℕ) : Type :=
  (Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))

variable {n : ℕ}

/-- The zero-based position at which man `i` ranks woman `j` (the paper's
ranking minus one).

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def manRank (P : PreferenceProfile n) (i j : Fin n) : ℕ :=
  ((P.1 i).symm j : ℕ)

/-- The zero-based position at which woman `j` ranks man `i` (the paper's
ranking minus one).

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def womanRank (P : PreferenceProfile n) (j i : Fin n) : ℕ :=
  ((P.2 j).symm i : ℕ)

/-- Man `i` and woman `j` are soulmates: each ranks the other first.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2.1. -/
def IsSoulmatePair (P : PreferenceProfile n) (i j : Fin n) : Prop :=
  manRank P i j = 0 ∧ womanRank P j i = 0

/-- The number of soulmate pairs of a profile (the paper's `k` in `F(k, n)`).

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4. -/
noncomputable def soulmatePairCount (P : PreferenceProfile n) : ℕ :=
  Nat.card {ij : Fin n × Fin n // IsSoulmatePair P ij.1 ij.2}

/-- The strict order on women induced by man `i`'s ranking: `a` before `b` when
`manRank P i a < manRank P i b`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def manPrefs (P : PreferenceProfile n) :
    MathlibExt.Combinatorics.Matching.GaleShapley.MPrefs (Fin n) (Fin n) := fun i =>
  { lt := fun a b => manRank P i a < manRank P i b
    irrefl := fun a => lt_irrefl _
    trans := fun h1 h2 => lt_trans h1 h2
    total := fun {a b} hab => by
      rcases lt_trichotomy (manRank P i a) (manRank P i b) with h | h | h
      · exact Or.inl h
      · exact absurd ((P.1 i).symm.injective (Fin.ext h)) hab
      · exact Or.inr h }

/-- The strict order on men induced by woman `j`'s ranking: `a` before `b` when
`womanRank P j a < womanRank P j b`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
def womanPrefs (P : PreferenceProfile n) :
    MathlibExt.Combinatorics.Matching.GaleShapley.WPrefs (Fin n) (Fin n) := fun j =>
  { lt := fun a b => womanRank P j a < womanRank P j b
    irrefl := fun a => lt_irrefl _
    trans := fun h1 h2 => lt_trans h1 h2
    total := fun {a b} hab => by
      rcases lt_trichotomy (womanRank P j a) (womanRank P j b) with h | h | h
      · exact Or.inl h
      · exact absurd ((P.2 j).symm.injective (Fin.ext h)) hab
      · exact Or.inr h }

/-- The matching `μ` (man `i` marries woman `μ i`) is stable: no man and woman
prefer each other to their spouses. This is the repository's Gale–Shapley
`IsStable` for the rank-induced preferences `manPrefs P` and `womanPrefs P`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
abbrev IsStableMatching (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n)) : Prop :=
  MathlibExt.Combinatorics.Matching.GaleShapley.IsStable (manPrefs P) (womanPrefs P) μ

/-- Stability in terms of ranks: no man `i` and woman `j` rank each other above
their spouses `μ i` and `μ.symm j`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem isStableMatching_iff (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n)) :
    IsStableMatching P μ ↔ ∀ i j : Fin n,
      ¬ (manRank P i j < manRank P i (μ i) ∧ womanRank P j i < womanRank P j (μ.symm j)) :=
  Iff.rfl

/-- Man `i` and his wife `μ i` form a hell-couple: they are married and rank
each other last.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 6.1. -/
def IsHellCouple (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  manRank P i (μ i) = n - 1 ∧ womanRank P (μ i) i = n - 1

/-- The number `L_n` of Latin squares of order `n`: families of `n` rows, each
a permutation of `Fin n`, whose columns are also injective.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4.2 (OEIS A002860). -/
noncomputable def latinSquareCount (n : ℕ) : ℕ :=
  Nat.card {M : Fin n → Equiv.Perm (Fin n) // ∀ r : Fin n, Function.Injective fun i => M i r}

/-- In the men-proposing Gale–Shapley state where each man `i'` has proposed to
his first `p i'` women, man `i` is provisionally engaged: he has proposed at
least once, and the woman at his last proposed position `r` ranks him weakly
above every man who has proposed to her so far.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2 (description of the
Gale–Shapley algorithm). -/
def GSEngaged (P : PreferenceProfile n) (p : Fin n → ℕ) (i : Fin n) : Prop :=
  ∃ r : Fin n, r.val + 1 = p i ∧
    ∀ i' r' : Fin n, r'.val < p i' → P.1 i' r' = P.1 i r →
      womanRank P (P.1 i r) i ≤ womanRank P (P.1 i r) i'

open Classical in
/-- The number of women each man has proposed to after `t` rounds of the
men-proposing Gale–Shapley algorithm: in each round every man who is not
provisionally engaged proposes to his next choice.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
noncomputable def gsProposals (P : PreferenceProfile n) : ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun i =>
      if GSEngaged P (gsProposals P t) i then gsProposals P t i else gsProposals P t i + 1

/-- The number of rounds of the men-proposing Gale–Shapley algorithm: the first
`t` after which every man is provisionally engaged.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
noncomputable def galeShapleyRounds (P : PreferenceProfile n) : ℕ :=
  sInf {t : ℕ | ∀ i : Fin n, GSEngaged P (gsProposals P t) i}

/-- Before the first round no man has proposed.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem gsProposals_zero (P : PreferenceProfile n) : gsProposals P 0 = fun _ => 0 := rfl

open Classical in
/-- One Gale–Shapley round: engaged men keep their count, the others propose
once more.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem gsProposals_succ (P : PreferenceProfile n) (t : ℕ) (i : Fin n) :
    gsProposals P (t + 1) i =
      if GSEngaged P (gsProposals P t) i then gsProposals P t i
      else gsProposals P t i + 1 := rfl

/-- With no people the algorithm takes zero rounds.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 2. -/
theorem galeShapleyRounds_of_zero (P : PreferenceProfile 0) : galeShapleyRounds P = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl fun i => i.elim0)

/-- A profile has at most `n` soulmate pairs: a man's soulmate is his first
choice.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4. -/
theorem soulmatePairCount_le (P : PreferenceProfile n) : soulmatePairCount P ≤ n := by
  have h : Function.Injective
      (fun x : {ij : Fin n × Fin n // IsSoulmatePair P ij.1 ij.2} => x.1.1) := by
    rintro ⟨⟨i, j⟩, hj, -⟩ ⟨⟨i', j'⟩, hj', -⟩ (rfl : i = i')
    have : (P.1 i).symm j = (P.1 i).symm j' := Fin.ext (hj.trans hj'.symm)
    simp [(P.1 i).symm.injective this]
  simpa [soulmatePairCount] using Nat.card_le_card_of_injective _ h

/-- There is one Latin square of order zero.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Section 4.2 (OEIS A002860). -/
theorem latinSquareCount_zero : latinSquareCount 0 = 1 := by
  rw [latinSquareCount, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
    ⟨⟨fun i => i.elim0, fun r => r.elim0⟩⟩⟩

/-- If all men rank the women in the same order, the men-proposing
Gale–Shapley algorithm ends in exactly `n` rounds.

Source: Borodin, Duncan, Litchev, Liu, Moroz, Qian, Raghavan, Rastogi, Voigt,
and Khovanova, *Sequences of the Stable Matching Problem*, Journal of Integer
Sequences 27 (2024), Article 24.2.2, Proposition 1
(`jis-2024-24.2.2-prop-1`). -/
public theorem_wanted galeShapleyRounds_of_same_taste (P : PreferenceProfile n)
    (h : ∀ i i' : Fin n, P.1 i = P.1 i') :
    galeShapleyRounds P = n

/-- For `n ≥ 1`, the men-proposing Gale–Shapley algorithm ends in one round if
and only if every woman is the first choice of exactly one man.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 2
(`jis-2024-24.2.2-prop-2`). -/
public theorem_wanted galeShapleyRounds_eq_one_iff (P : PreferenceProfile n) (hn : 0 < n) :
    galeShapleyRounds P = 1 ↔ ∀ j : Fin n, ∃! i : Fin n, P.1 i ⟨0, hn⟩ = j

/-- The number of disjoint profiles (profiles in which every pair of mutual
positions `(r, s)` is realized by exactly one man-woman pair) is at most
`(n²)!` and divisible by `(n!)²`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 3
(`jis-2024-24.2.2-prop-3`). -/
public theorem_wanted disjoint_profiles_card_le_and_dvd (n : ℕ) :
    Nat.card {P : PreferenceProfile n //
        Function.Bijective fun ij : Fin n × Fin n => ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)} ≤
        (n ^ 2)! ∧
      (n ! ) ^ 2 ∣ Nat.card {P : PreferenceProfile n //
        Function.Bijective fun ij : Fin n × Fin n => ((P.1 ij.1).symm ij.2, (P.2 ij.2).symm ij.1)}

/-- The paper's `S(k, n)`: fix a group of `k` men and `k` women and ignore their
preferences; the remaining `n - k` men (here the men `k, …, n - 1`) and
`n - k` women (the women `k, …, n - 1`), each ranking all `n` people of the
other gender, have no soulmate pair among themselves in exactly
`∑_{i=0}^{n-k} (-1)^i C(n-k, i)² ((n-1)!)^{2i} i! (n!)^{2n-2k-2i}` ways.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Lemma 4
(`jis-2024-24.2.2-lem-4`). -/
public theorem_wanted outside_no_soulmates_card (n k : ℕ) :
    (Nat.card {MW : (Fin (n - k) → Equiv.Perm (Fin n)) × (Fin (n - k) → Equiv.Perm (Fin n)) //
        ∀ a b : Fin (n - k),
          ¬ (((MW.1 a).symm ⟨k + b.val, by have := b.isLt; omega⟩ : ℕ) = 0 ∧
            ((MW.2 b).symm ⟨k + a.val, by have := a.isLt; omega⟩ : ℕ) = 0)} : ℤ) =
      ∑ i ∈ range (n - k + 1),
        (-1 : ℤ) ^ i * ((n - k).choose i : ℤ) ^ 2 * ((n - 1)! : ℤ) ^ (2 * i) * (i ! : ℤ) *
          (n ! : ℤ) ^ (2 * n - 2 * k - 2 * i)

/-- The number `F(k, n)` of preference profiles with exactly `k` soulmate pairs
is `C(n, k)² k! ((n-1)!)^{2k} S(k, n)`, with `S(k, n)` the inclusion-exclusion
sum of Lemma 4.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 6
(`jis-2024-24.2.2-thm-6`). -/
public theorem_wanted soulmate_profiles_card (n k : ℕ) :
    (Nat.card {P : PreferenceProfile n // soulmatePairCount P = k} : ℤ) =
      (n.choose k : ℤ) ^ 2 * (k ! : ℤ) * ((n - 1)! : ℤ) ^ (2 * k) *
        ∑ i ∈ range (n - k + 1),
          (-1 : ℤ) ^ i * ((n - k).choose i : ℤ) ^ 2 * ((n - 1)! : ℤ) ^ (2 * i) * (i ! : ℤ) *
            (n ! : ℤ) ^ (2 * n - 2 * k - 2 * i)

/-- A profile with `n - 1` soulmate pairs has exactly one stable matching, and
the men-proposing Gale–Shapley algorithm ends in `j` rounds, where `j` is the
(one-based) ranking the man outside the soulmate pairs gives his wife.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 7
(`jis-2024-24.2.2-prop-7`). -/
public theorem_wanted unique_stable_matching_of_soulmatePairCount_eq_pred
    (P : PreferenceProfile n) (h : soulmatePairCount P = n - 1) :
    (∃! μ : Equiv.Perm (Fin n), IsStableMatching P μ) ∧
      ∀ μ : Equiv.Perm (Fin n), IsStableMatching P μ →
        ∀ i : Fin n, (∀ j : Fin n, ¬ IsSoulmatePair P i j) →
          galeShapleyRounds P = manRank P i (μ i) + 1

/-- The number of profiles whose men's preferences form a Latin square and that
have exactly `k` soulmate pairs is `L_n C(n, k) (n-1)^{n-k} ((n-1)!)^n`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 8
(`jis-2024-24.2.2-thm-8`). -/
public theorem_wanted men_latin_soulmate_profiles_card (n k : ℕ) :
    Nat.card {P : PreferenceProfile n //
        (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = k} =
      latinSquareCount n * n.choose k * (n - 1) ^ (n - k) * ((n - 1)!) ^ n

/-- The number of profiles whose men's and women's preferences both form Latin
squares and that have exactly `k` soulmate pairs is
`(L_n² / n!) C(n, k) ∑_{i=0}^{n-k} (-1)^i (n-k)!/i!`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Theorem 9
(`jis-2024-24.2.2-thm-9`). -/
public theorem_wanted mutually_latin_soulmate_profiles_card (n k : ℕ) :
    (Nat.card {P : PreferenceProfile n //
        (∀ r : Fin n, Function.Injective fun i => P.1 i r) ∧
          (∀ r : Fin n, Function.Injective fun j => P.2 j r) ∧ soulmatePairCount P = k} : ℚ) =
      (latinSquareCount n : ℚ) ^ 2 / (n ! : ℚ) * (n.choose k : ℚ) *
        ∑ i ∈ range (n - k + 1), (-1 : ℚ) ^ i * ((n - k)! : ℚ) / (i ! : ℚ)

/-- A stable matching has at most one hell-couple.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 12
(`jis-2024-24.2.2-prop-12`). -/
public theorem_wanted hellCouple_subsingleton (P : PreferenceProfile n)
    (μ : Equiv.Perm (Fin n)) (hμ : IsStableMatching P μ) :
    {i : Fin n | IsHellCouple P μ i}.Subsingleton

/-- If some stable matching contains a hell-couple, every stable matching
contains that couple.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 13
(`jis-2024-24.2.2-prop-13`). -/
public theorem_wanted hellCouple_mem_all_stable (P : PreferenceProfile n)
    (μ ν : Equiv.Perm (Fin n)) (hμ : IsStableMatching P μ) (hν : IsStableMatching P ν)
    (i : Fin n) (hi : IsHellCouple P μ i) :
    ν i = μ i

/-- The number of profiles with at least one pair of outcasts (a man and a
woman ranked last by every other person of the opposite gender) is
`n⁴ ((n-1)!)^{2n}` for `n ≠ 2` and `14` for `n = 2`.

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 14
(`jis-2024-24.2.2-prop-14`). -/
public theorem_wanted outcast_profiles_card (n : ℕ) :
    Nat.card {P : PreferenceProfile n // ∃ i j : Fin n,
        (∀ i' : Fin n, i' ≠ i → manRank P i' j = n - 1) ∧
          (∀ j' : Fin n, j' ≠ j → womanRank P j' i = n - 1)} =
      if n = 2 then 14 else n ^ 4 * ((n - 1)!) ^ (2 * n)

end

end StableMatchingSequences

end MetaMathlibExt
