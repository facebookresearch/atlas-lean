/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux

/-!
# First-down and last-up Motzkin prefixes

`motzkinFirstDownFamily_equiv_lastUpEvenFamily` equates the two prefix families by showing
that their cardinalities satisfy the same recurrence in the length.

## References

* Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*,
  Journal of Integer Sequences 28 (2025), Article 25.8.1, pp. 1–11, Lemma 6 (p. 6).
-/

namespace MetaMathlibExt
namespace motzkinFirstDownFamily_equiv_lastUpEvenFamily

private abbrev Word (n : ℕ) := Fin n → Fin 3

-- Starting above zero lets us remove the first step of a prefix.
private def Good {n : ℕ} (a : ℤ) (p : Word n) : Prop :=
  ∀ m ≤ n, 0 ≤ a + motzkinPrefixHeight p m

private theorem prefix_iff {n : ℕ} (p : Word n) (h : ℤ) :
    IsMotzkinPrefix n h p ↔ Good 0 p ∧ motzkinPrefixHeight p n = h := by
  simp only [isMotzkinPrefix_iff, Good, zero_add, motzkinPrefixHeight_total]
  exact and_congr_left' (forall_congr' fun m => forall_congr' fun hm => by
    rw [motzkinPrefixHeight_prefix_sum p hm])

private theorem good_cons {n : ℕ} (a : ℤ) (x : Fin 3) (p : Word n) :
    Good a (Fin.cons x p) ↔ 0 ≤ a ∧ Good (a + motzkinStep x) p := by
  constructor
  · intro h
    refine ⟨by simpa [motzkinPrefixHeight_zero] using h 0 (by omega), fun m hm => ?_⟩
    simpa only [motzkinPrefixHeight_cons_succ, add_assoc] using h (m + 1) (by omega)
  · rintro ⟨ha, h⟩ (_ | m) hm
    · simpa only [motzkinPrefixHeight_zero, add_zero] using ha
    · simpa only [motzkinPrefixHeight_cons_succ, add_assoc] using h m (by omega)

private theorem good_snoc {n : ℕ} (x : Fin 3) (p : Word n) :
    Good 0 (Fin.snoc p x) ↔ Good 0 p ∧ 0 ≤ motzkinPrefixHeight p n + motzkinStep x := by
  constructor
  · intro h
    refine ⟨fun m hm => ?_, ?_⟩
    · simpa only [motzkinPrefixHeight_snoc_of_le p x hm] using h m (by omega)
    · simpa only [zero_add, motzkinPrefixHeight_snoc_succ] using h _ (le_refl _)
  · rintro ⟨h, hx⟩ m hm
    obtain hmn | rfl := Nat.lt_or_eq_of_le hm
    · simpa only [motzkinPrefixHeight_snoc_of_le p x (Nat.le_of_lt_succ hmn)] using h m (by omega)
    · simpa only [zero_add, motzkinPrefixHeight_snoc_succ] using hx

private theorem first_cons {n : ℕ} (x : Fin 3) (p : Word n) :
    FirstNonupStepDown _ (Fin.cons x p) ↔ x = 0 ∨ x = 2 ∧ FirstNonupStepDown n p := by
  constructor
  · rintro ⟨i, hi, hj⟩
    cases i using Fin.cases with
    | zero => exact Or.inl (by simpa using hi)
    | succ i =>
      exact Or.inr ⟨by simpa using hj 0 (Fin.succ_pos i), i, by simpa using hi,
        fun j h => by simpa using hj j.succ (Fin.succ_lt_succ_iff.mpr h)⟩
  · rintro (rfl | ⟨rfl, i, hi, hj⟩)
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨i.succ, by simpa using hi, ?_⟩
      intro j
      cases j using Fin.cases with
      | zero => simp
      | succ j => simpa only [Fin.cons_succ, Fin.succ_lt_succ_iff] using hj j

private theorem last_snoc {n : ℕ} (x : Fin 3) (p : Word n) :
    LastNonflatStepUp _ (Fin.snoc p x) ↔ x = 2 ∨ x = 1 ∧ LastNonflatStepUp n p := by
  constructor
  · rintro ⟨i, hi, hj⟩
    cases i using Fin.lastCases with
    | last => exact Or.inl (by simpa using hi)
    | cast i =>
      exact Or.inr ⟨by simpa using hj _ i.castSucc_lt_last, i, by simpa using hi,
        fun j h => by simpa using hj j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr h)⟩
  · rintro (rfl | ⟨rfl, i, hi, hj⟩)
    · exact ⟨Fin.last n, by simp, fun j h => (not_lt_of_ge (Fin.le_last j) h).elim⟩
    · refine ⟨i.castSucc, by simpa using hi, ?_⟩
      intro j
      cases j using Fin.lastCases with
      | last => simp
      | cast j => simpa only [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff] using hj j

private theorem height_le {n : ℕ} (p : Word n) : motzkinPrefixHeight p n ≤ n := by
  rw [← motzkinPrefixHeight_total]
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      have := (p i).isLt
      rw [motzkinStep_eq_sub_one]
      omega
    _ = _ := by simp

private theorem height_first {n : ℕ} (p : Word n) (h : FirstNonupStepDown n p) :
    motzkinPrefixHeight p n + 2 ≤ n := by
  induction n with
  | zero => exact Fin.elim0 h.choose
  | succ n ih =>
    obtain ⟨⟨x, p⟩, rfl⟩ := (Fin.consEquiv (n := n) (fun _ => Fin 3)).surjective p
    change FirstNonupStepDown _ (Fin.cons x p) at h
    change motzkinPrefixHeight (Fin.cons x p) _ + 2 ≤ _
    rw [motzkinPrefixHeight_cons_succ]
    rcases (first_cons x p).mp h with rfl | ⟨rfl, hp⟩
    · have := height_le p
      rw [motzkinStep_values.1]
      omega
    · have := ih p hp
      rw [motzkinStep_values.2.2]
      omega

open scoped Classical in
private noncomputable def count {n : ℕ} (P : Word n → Prop) : ℕ :=
  ∑ p, if P p then 1 else 0

private theorem count_cons {n : ℕ} (P : Word (n + 1) → Prop) :
    count P = count (fun p => P (Fin.cons 0 p)) + count (fun p => P (Fin.cons 1 p)) +
      count (fun p => P (Fin.cons 2 p)) := by
  classical
  unfold count
  rw [← (Fin.consEquiv (n := n) (fun _ => Fin 3)).sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  rfl

private theorem count_snoc {n : ℕ} (P : Word (n + 1) → Prop) :
    count P = count (fun p => P (Fin.snoc p 0)) + count (fun p => P (Fin.snoc p 1)) +
      count (fun p => P (Fin.snoc p 2)) := by
  classical
  unfold count
  rw [← (Fin.snocEquiv (n := n) (fun _ => Fin 3)).sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  rfl

private noncomputable abbrev total (n : ℕ) (a : ℤ) := count (n := n) (Good a)

private noncomputable abbrev firstDown (n : ℕ) (a : ℤ) :=
  count (fun p => Good a p ∧ FirstNonupStepDown n p)

private theorem total_succ (n : ℕ) {a : ℤ} (ha : 0 ≤ a) :
    total (n + 1) a = total n (a - 1) + total n a + total n (a + 1) := by
  rw [total, count_cons]
  simp only [good_cons, ha, true_and, motzkinStep_values, add_zero, sub_eq_add_neg]

private theorem first_succ (n : ℕ) {a : ℤ} (ha : 0 ≤ a) :
    firstDown (n + 1) a = total n (a - 1) + firstDown n (a + 1) := by
  rw [firstDown, count_cons]
  simp only [good_cons, first_cons, ha, true_and]
  simp only [motzkinStep_values, sub_eq_add_neg, add_zero, Fin.reduceEq, true_or, false_or,
    false_and, and_true, and_false]
  simp [count, total, firstDown]

-- A first flat after a run of ups can be replaced by an extra up and a down.
-- The single all-up word accounts for the constant term.
private theorem first_add (n : ℕ) {a : ℤ} (ha : 0 ≤ a) :
    firstDown (n + 1) a + firstDown n a + 1 = total n a + total n (a - 1) := by
  induction n generalizing a with
  | zero =>
    rw [first_succ 0 ha]
    simp [firstDown, total, count, firstNonupStepDown_iff, Good,
      motzkinPrefixHeight_zero, ha, add_comm]
  | succ n ih =>
    rw [first_succ (n + 1) ha, first_succ n ha, total_succ n ha]
    have h := ih (a := a + 1) (by omega)
    rw [add_sub_cancel_right] at h
    omega

private def AtParity {n : ℕ} (r : ℤ) (p : Word n) : Prop :=
  Good 0 p ∧ motzkinPrefixHeight p n % 2 = r

private def LastUp {n : ℕ} (p : Word n) : Prop :=
  AtParity 0 p ∧ 2 ≤ motzkinPrefixHeight p n ∧ LastNonflatStepUp n p

private theorem nonneg_end {n : ℕ} {p : Word n} (h : Good 0 p) : 0 ≤ motzkinPrefixHeight p n := by
  simpa only [zero_add] using h n (le_refl _)

-- From an odd height either vertical step gives an even height, and a flat preserves parity.
private theorem parity_snoc {n : ℕ} (p : Word n) :
    (AtParity 0 (Fin.snoc p 0) ↔ AtParity 1 p) ∧
    (AtParity 0 (Fin.snoc p 1) ↔ AtParity 0 p) ∧
    (AtParity 0 (Fin.snoc p 2) ↔ AtParity 1 p) := by
  by_cases hg : Good 0 p
  · have := nonneg_end hg
    simp only [AtParity, good_snoc, motzkinPrefixHeight_snoc_succ, motzkinStep_values,
      hg, true_and, add_zero]
    omega
  · simp [AtParity, good_snoc, hg]

private theorem lastUp_snoc {n : ℕ} (p : Word n) :
    ¬LastUp (Fin.snoc p 0) ∧ (LastUp (Fin.snoc p 1) ↔ LastUp p) ∧
    (LastUp (Fin.snoc p 2) ↔ AtParity 1 p) := by
  simp only [LastUp, (parity_snoc p).1, (parity_snoc p).2.1, (parity_snoc p).2.2,
    motzkinPrefixHeight_snoc_succ, last_snoc, motzkinStep_values, Fin.reduceEq, add_zero]
  simp only [false_and, or_self, true_and, false_or, true_or, and_false, not_false_eq_true,
    and_true]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  have := nonneg_end h.1
  have := h.2
  omega

private noncomputable abbrev parityCount (n : ℕ) (r : ℤ) := count (n := n) (AtParity r)

private noncomputable abbrev lastUp (n : ℕ) := count (n := n) LastUp

private theorem even_succ (n : ℕ) :
    parityCount (n + 1) 0 = parityCount n 1 + parityCount n 0 + parityCount n 1 := by
  rw [parityCount, count_snoc]
  simp only [(parity_snoc _).1, (parity_snoc _).2.1, (parity_snoc _).2.2]

private theorem lastUp_succ (n : ℕ) :
    lastUp (n + 1) = lastUp n + parityCount n 1 := by
  rw [lastUp, count_snoc]
  simp only [(lastUp_snoc _).1, (lastUp_snoc _).2.1, (lastUp_snoc _).2.2]
  simp [count, lastUp, parityCount]

-- Both counts grow by the odd-height count, twice for even prefixes and once for last-up.
private theorem even_eq (n : ℕ) : parityCount n 0 = 2 * lastUp n + 1 := by
  induction n with
  | zero => simp [parityCount, lastUp, count, LastUp, AtParity, Good, motzkinPrefixHeight_zero]
  | succ n ih =>
    rw [even_succ, lastUp_succ]
    omega

private theorem parity_partition (n : ℕ) :
    total n 0 = parityCount n 0 + parityCount n 1 := by
  classical
  unfold total parityCount count
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold AtParity
  by_cases hg : Good 0 p <;> simp only [hg, true_and, false_and, ite_true, ite_false, add_zero]
  split_ifs <;> omega

private theorem counts_eq (n : ℕ) : firstDown n 0 = lastUp n := by
  induction n with
  | zero =>
    simp [firstDown, lastUp, count, firstNonupStepDown_iff, LastUp, motzkinPrefixHeight_zero]
  | succ n ih =>
    have h := first_add n (a := 0) (by decide)
    have neg : total n (-1) = 0 := by
      have bad (p : Word n) : ¬Good (-1) p := by
        intro hp
        have h₀ := hp 0 (Nat.zero_le _)
        rw [motzkinPrefixHeight_zero, add_zero] at h₀
        omega
      simp [total, count, bad]
    rw [show (0 : ℤ) - 1 = -1 by decide, neg, add_zero, parity_partition, even_eq] at h
    rw [lastUp_succ]
    omega

-- In either indexed family the word determines the index from its final height.
private def firstEquiv (n : ℕ) : MotzkinFirstDownFamily n ≃
    {p : Word n // Good 0 p ∧ FirstNonupStepDown n p} where
  toFun := fun ⟨⟨k, p⟩, _, hp, hf⟩ => ⟨p, ((prefix_iff p k).mp hp).1, hf⟩
  invFun := fun ⟨p, hg, hf⟩ => ⟨⟨(motzkinPrefixHeight p n).toNat, p⟩, by
    have := nonneg_end hg
    have := height_first p hf
    exact ⟨by omega, (prefix_iff p _).mpr ⟨hg, by omega⟩, hf⟩⟩
  left_inv := by
    rintro ⟨⟨k, p⟩, _, hp, _⟩
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    change (motzkinPrefixHeight p n).toNat = k
    rw [((prefix_iff p k).mp hp).2, Int.toNat_natCast]
  right_inv _ := rfl

private def lastEquiv (n : ℕ) : MotzkinLastUpEvenFamily n ≃ {p : Word n // LastUp p} where
  toFun := fun ⟨⟨k, p⟩, hk, _, hp, hu⟩ => ⟨p, by
    obtain ⟨hg, he⟩ := (prefix_iff p _).mp hp
    exact ⟨⟨hg, by omega⟩, by omega, hu⟩⟩
  invFun := fun ⟨p, ⟨hg, he⟩, hpos, hu⟩ => ⟨⟨(motzkinPrefixHeight p n).toNat / 2, p⟩, by
    have := height_le p
    exact ⟨by omega, by omega, (prefix_iff p _).mpr ⟨hg, by omega⟩, hu⟩⟩
  left_inv := by
    rintro ⟨⟨k, p⟩, _, _, hp, _⟩
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    change (motzkinPrefixHeight p n).toNat / 2 = k
    have he : motzkinPrefixHeight p n = 2 * (k : ℤ) := ((prefix_iff p _).mp hp).2
    omega
  right_inv _ := rfl

private theorem card_words {n : ℕ} (P : Word n → Prop) [Fintype {p // P p}] :
    Fintype.card {p // P p} = count P := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, count]

end motzkinFirstDownFamily_equiv_lastUpEvenFamily

open motzkinFirstDownFamily_equiv_lastUpEvenFamily

/-- **A bijection between first-down and even-height last-up Motzkin prefixes.** Use the steps
$U = (1,1)$, $F = (1,0)$ and $D = (1,-1)$, and call a word in these steps a Motzkin prefix if
none of its initial segments ends below height $0$. For every natural number $n$ there is a
bijection between the set of pairs $(k, p)$, where $k$ is a natural number with $k + 2 \le n$ and
$p$ is a Motzkin prefix of length $n$ ending at height $k$ whose first step other than $U$ exists
and is $D$, and the set of pairs $(k, p)$, where $k$ is a natural number with
$1 \le k \le \lfloor n/2 \rfloor$ and $p$ is a Motzkin prefix of length $n$ ending at height $2k$
that contains a $U$ after which every step is $F$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 6 (`jis-2025-25.8.1-lem-6`).
-/
public theorem motzkinFirstDownFamily_equiv_lastUpEvenFamily (n : ℕ) :
    Nonempty (MotzkinFirstDownFamily n ≃ MotzkinLastUpEvenFamily n) := by
  classical
  refine ⟨(firstEquiv n).trans ((Fintype.equivOfCardEq ?_).trans (lastEquiv n).symm)⟩
  simpa only [card_words] using counts_eq n

end MetaMathlibExt
