/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The harmonic count for signed inversion sequences

The three pattern sets of Mansour and Safadi's Lemma 3 have the same avoidance count
`n! (1 + H_n)`. Only zeros can be barred. Splitting by the last letter gives the same
recurrence for each of the three ways to forbid a pair of signs on two zeros.
-/

namespace MetaMathlibExt

open Nat

namespace signedInvSeq_wilf_and_count_b0b1_b0b0_0b1

private abbrev Entry := ℕ × Bool

private abbrev patterns (a b : Bool) : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, a, b⟩, ⟨.lt, false, true⟩}

private structure Valid (a b : Bool) {n : ℕ} (e : Fin n → Entry) : Prop where
  bound : ∀ i, (e i).1 ≤ i.val
  barred : ∀ i, (e i).2 = true → (e i).1 = 0
  zeros : ∀ ⦃i j⦄, i < j → e i = (0, a) → e j ≠ (0, b)

private abbrev Word (a b : Bool) (n : ℕ) := {e : Fin n → Entry // Valid a b e}

private theorem pair_iff (a b : Bool) (x y : Entry) :
    ⟨compare x.1 y.1, x.2, y.2⟩ ∉ patterns a b ↔
      (y.2 = true → y.1 ≤ x.1) ∧ (x.2 = a → y.2 = b → x.1 ≠ y.1) := by
  cases a <;> cases b <;> cases x.2 <;> cases y.2 <;>
    simp [patterns, SignedPattern2.mk.injEq, compare_lt_iff_lt, and_comm]

private theorem valid_iff {n : ℕ} (a b : Bool) (hab : a = true ∨ b = true)
    (e : Fin n → Entry) :
    ((∀ i, (e i).1 ≤ i.val) ∧ ∀ p ∈ patterns a b, ¬ SignedInvSeqContains e p) ↔
      Valid a b e := by
  constructor
  · rintro ⟨bound, avoids⟩
    have pairs {i j : Fin n} (h : i < j) := (pair_iff a b (e i) (e j)).mp
      (fun hm => avoids _ hm ⟨i, j, h, rfl, rfl, rfl⟩)
    refine ⟨bound, ?_, ?_⟩
    · intro i hi
      cases n with
      | zero => exact i.elim0
      | succ n =>
        have h0 := Nat.eq_zero_of_le_zero (bound 0)
        rcases (Fin.zero_le i).eq_or_lt with he | hlt
        · exact he ▸ h0
        · exact Nat.eq_zero_of_le_zero (((pairs hlt).1 hi).trans h0.le)
    · intro i j hij hi hj
      have h := (pairs hij).2
      simp [hi, hj] at h
  · rintro h
    refine ⟨h.bound, ?_⟩
    rintro p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair_iff a b (e i) (e j)).mpr ?_
    · cases p
      simpa only [ho, hs, ht] using hm
    constructor
    · intro hj
      simp [h.barred j hj]
    · intro hi hj he
      have hz : (e i).1 = 0 := hab.elim (fun ha => h.barred i (hi.trans ha))
        (fun hb => he.trans (h.barred j (hj.trans hb)))
      exact h.zeros hij (Prod.ext hz hi) (Prod.ext (he.symm.trans hz) hj)

private theorem count_eq_card (a b : Bool) (hab : a = true ∨ b = true) (n : ℕ) :
    signedInvAvoidCount (patterns a b) n = Nat.card (Word a b n) :=
  Nat.card_congr (Equiv.subtypeEquivRight (valid_iff a b hab))

private instance wordFinite (a b : Bool) (n : ℕ) : Finite (Word a b n) :=
  Finite.of_injective
    (fun (w : Word a b n) (i : Fin n) =>
      ((⟨(w.val i).1, Nat.lt_succ_of_le (w.property.bound i)⟩ : Fin (i.val + 1)), (w.val i).2))
    (by
      intro v w h
      apply Subtype.ext
      funext i
      exact Prod.ext (congrArg (fun f => (f i).1.val) h) (congrArg (fun f => (f i).2) h))

-- For each magnitude, this is the unique possible letter other than (0, s).
private def letter (s : Bool) (k : ℕ) : Entry := (k, if k = 0 then !s else false)

private theorem letter_ne (s : Bool) (k : ℕ) : letter s k ≠ (0, s) := by
  cases s <;> by_cases hk : k = 0 <;> simp [letter, hk]

private theorem letter_barred (s : Bool) (k : ℕ) : (letter s k).2 = true → k = 0 := by
  by_cases hk : k = 0 <;> simp [letter, hk]

private theorem letter_eq {s : Bool} {x : Entry} (hz : x.2 = true → x.1 = 0)
    (hne : x ≠ (0, s)) : letter s x.1 = x := by
  rcases x with ⟨k, t⟩
  cases s <;> cases t <;> cases k <;> simp_all [letter]

private def init {a b : Bool} {n : ℕ} (w : Word a b (n + 1)) : Word a b n :=
  ⟨fun i => w.val i.castSucc, fun i => w.property.bound i.castSucc,
    fun i => w.property.barred i.castSucc,
    fun {_ _} h => w.property.zeros (Fin.castSucc_lt_castSucc_iff.mpr h)⟩

private def snoc {a b : Bool} {n : ℕ} (w : Word a b n) (x : Entry) (hx : x.1 ≤ n)
    (hz : x.2 = true → x.1 = 0) (hp : ∀ i, w.val i = (0, a) → x ≠ (0, b)) :
    Word a b (n + 1) := by
  refine ⟨Fin.snoc w.val x, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases <;> simp_all [w.property.bound]
  · intro i
    induction i using Fin.lastCases <;> simp_all [w.property.barred]
  · intro i j
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hp i
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact fun h => (j.castSucc_lt_last.not_gt h).elim
      | cast i => simpa using w.property.zeros (i := i) (j := j)

private abbrev LastZero (b : Bool) {a : Bool} {n : ℕ} (w : Word a b (n + 1)) :=
  w.val (Fin.last n) = (0, b)

-- Appending an ordinary last letter gives one extension for each possible magnitude.
private def ordinaryEquiv (a b : Bool) (n : ℕ) :
    Word a b n × Fin (n + 1) ≃ {w : Word a b (n + 1) // ¬ LastZero b w} where
  toFun := fun ⟨w, k⟩ =>
    ⟨snoc w (letter b k) (Nat.le_of_lt_succ k.isLt) (letter_barred b k)
      (fun _ _ => letter_ne b k), by simpa [LastZero, snoc] using letter_ne b k⟩
  invFun w := (init w.val, ⟨(w.val.val (Fin.last n)).1,
    Nat.lt_succ_of_le (w.val.property.bound (Fin.last n))⟩)
  left_inv := by
    rintro ⟨w, k⟩
    apply Prod.ext
    · exact Subtype.ext (funext fun i => by simp [init, snoc])
    · apply Fin.ext
      simp [snoc, letter]
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | cast i => simp [snoc, init]
    | last => simpa [snoc] using letter_eq (w.val.property.barred (Fin.last n)) w.property

private abbrev Unsigned (n : ℕ) := (i : Fin n) → Fin (i.val + 1)

-- When the last letter is (0, b), all earlier zeros have sign !a.
private def signedPrefix (a b : Bool) {n : ℕ} (f : Unsigned n) : Word a b n :=
  ⟨fun i => letter a (f i), fun i => Nat.le_of_lt_succ (f i).isLt,
    fun i => letter_barred a (f i), fun {i _} _ h => (letter_ne a (f i) h).elim⟩

private def zeroEquiv (a b : Bool) (n : ℕ) :
    Unsigned n ≃ {w : Word a b (n + 1) // LastZero b w} where
  toFun f := ⟨snoc (signedPrefix a b f) (0, b) (Nat.zero_le _) (fun _ => rfl)
    (fun i h => (letter_ne a (f i) h).elim), by simp [LastZero, snoc]⟩
  invFun w i := ⟨(w.val.val i.castSucc).1, Nat.lt_succ_of_le (w.val.property.bound i.castSucc)⟩
  left_inv f := by
    funext i
    apply Fin.ext
    simp [snoc, signedPrefix, letter]
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | last => simpa [snoc] using w.property.symm
    | cast i =>
      have hne : w.val.val i.castSucc ≠ (0, a) := fun he =>
        w.val.property.zeros i.castSucc_lt_last he w.property
      simpa [snoc, signedPrefix] using letter_eq (w.val.property.barred i.castSucc) hne

private theorem recurrence (a b : Bool) (n : ℕ) :
    Nat.card (Word a b (n + 1)) = (n + 1) * Nat.card (Word a b n) + n ! := by
  classical
  rw [← Nat.card_congr (Equiv.sumCompl (LastZero b (a := a) (n := n))), Nat.card_sum,
    ← Nat.card_congr (zeroEquiv a b n), ← Nat.card_congr (ordinaryEquiv a b n),
    Nat.card_prod, Nat.card_fin, Nat.card_pi]
  simp only [Nat.card_fin]
  rw [Fin.prod_univ_eq_prod_range fun i => i + 1, Finset.prod_range_add_one_eq_factorial]
  ac_rfl

private theorem count (a b : Bool) (hab : a = true ∨ b = true) (n : ℕ) :
    (signedInvAvoidCount (patterns a b) n : ℚ) = n ! * (1 + harmonic n) := by
  induction n with
  | zero => simp [signedInvAvoidCount_zero]
  | succ n ih =>
    rw [count_eq_card a b hab, recurrence, ← count_eq_card a b hab, Nat.cast_add, Nat.cast_mul,
      ih, factorial_succ, Nat.cast_mul, harmonic_succ]
    push_cast
    field_simp
    ring

end signedInvSeq_wilf_and_count_b0b1_b0b0_0b1

open signedInvSeq_wilf_and_count_b0b1_b0b0_0b1 in
/-- **Mansour–Safadi Lemma 3 (signed patterns 0̄1̄, 0̄0̄, 01̄).** A signed inversion sequence of
length $n$ is a word $e_1 \cdots e_n$ with $e_k \in \{0, \bar 0, 1, \bar 1, \dots, k - 1,
\overline{k - 1}\}$. It avoids a length-2 signed pattern $\tau_1\tau_2$ (one of $00$, $01$, $10$,
each letter possibly barred) when no $i < j$ have $|e_i|$, $|e_j|$ in the same order as $|\tau_1|$,
$|\tau_2|$ with $e_i$, $e_j$ barred exactly when $\tau_1$, $\tau_2$ are. Write $\bar I_n(B)$ for the
set of signed inversion sequences of length $n$ that avoid every pattern in $B$. Let
$B_1 = \{\bar 0\bar 1, \bar 0\bar 0, 0\bar 1\}$, $B_2 = \{\bar 0\bar 1, \bar 0 0, 0\bar 1\}$ and
$B_3 = \{\bar 0\bar 1, 0\bar 1, 0\bar 0\}$. For every $n \ge 0$,
$|\bar I_n(B_1)| = |\bar I_n(B_2)| = |\bar I_n(B_3)| = n!\,(1 + H_n)$, where
$H_n = \sum_{k=1}^{n} 1/k$ is the $n$th harmonic number.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 3 (`integers-2026-A74-lem-3`). -/
public theorem signedInvSeq_wilf_and_count_b0b1_b0b0_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩} ∧
    ∀ n, (signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩} n : ℚ) =
        n ! * (1 + harmonic n) := by
  have h₁ := count true true (Or.inl rfl)
  have h₂ := count true false (Or.inl rfl)
  have h₃ := count false true (Or.inr rfl)
  have hset : patterns false true =
      {⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩} := by decide
  rw [← hset]
  refine ⟨funext fun n => ?_, funext fun n => ?_, h₁⟩
  · exact_mod_cast (h₁ n).trans (h₂ n).symm
  · exact_mod_cast (h₂ n).trans (h₃ n).symm

end MetaMathlibExt
