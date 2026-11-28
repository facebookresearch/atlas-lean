/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import all MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC3
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Interval.Finset.Fin

/-!
# Three signed pattern sets with twice the factorial count

For `n ≥ 1`, each of the three six-pattern sets in Theorem 17 has `2 * n!` avoiders of
length `n`. Each set permits at most one bar. In the first and third sets the bar, if
present, is at the last minimum or last maximum, respectively. In the second set the
one-bar count is `(n - 1)!` for each possible barred magnitude, by a recurrence that
separates a bar at the final position from a bar in the prefix.

## References

* Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed
  Patterns*, INTEGERS 26 (2026), Article A74, pp. 1–74, Theorem 17 (p. 56).
  <https://math.colgate.edu/~integers/aa74/aa74.pdf>
* Toufik Mansour and Amir Safadi, *Inversion sequences and signed permutations*, Discrete
  Mathematics Letters 14 (2024), pp. 13–20, §1, for the signed Lehmer correspondence used in
  the paper's proof. The proof here counts directly in the inversion-sequence model.
* `MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC3`, for
  `count_eq_card`, `avoidersFinite` and `unbarredEquiv` (in the namespace for class C3).
-/

namespace MetaMathlibExt

open Nat

namespace SignedInvTwoFactorial

open signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1
  (Entry Avoiders WithBar Unbarred count_eq_card avoidersFinite unbarredEquiv)

attribute [local instance] avoidersFinite

-- With one bar, the two relations prescribe its permitted neighbors on the left and right.
private def Allowed (before after : ℕ → ℕ → Prop) (x y : Entry) : Prop :=
  match x.2, y.2 with
  | false, false => True
  | false, true => before x.1 y.1
  | true, false => after x.1 y.1
  | true, true => False

private abbrev Digits (n : ℕ) := (i : Fin n) → Fin (i.val + 1)

private def BarPosition {n : ℕ} (before after : ℕ → ℕ → Prop) (a : Digits n) (k : Fin n) : Prop :=
  (∀ j < k, before (a j).val (a k).val) ∧ (∀ j, k < j → after (a k).val (a j).val)

private abbrev Pointed (before after : ℕ → ℕ → Prop) (n : ℕ) :=
  {p : Fin n × Digits n // BarPosition before after p.2 p.1}

private def mark {n : ℕ} (a : Digits n) (k : Fin n) (i : Fin n) : Entry :=
  ((a i).val, decide (i = k))

private theorem mark_allowed {n : ℕ} {before after : ℕ → ℕ → Prop} {a : Digits n} {k : Fin n} :
    (∀ ⦃i j⦄, i < j → Allowed before after (mark a k i) (mark a k j)) ↔
      BarPosition before after a k := by
  constructor
  · intro h
    exact ⟨fun j hj => by simpa [Allowed, mark, hj.ne] using h hj,
      fun j hj => by simpa [Allowed, mark, hj.ne'] using h hj⟩
  · rintro ⟨hbefore, hafter⟩ i j hij
    by_cases hi : i = k
    · subst i
      simpa [Allowed, mark, hij.ne'] using hafter j hij
    · by_cases hj : j = k
      · subst j
        simpa [Allowed, mark, hi] using hbefore i hij
      · simp [Allowed, mark, hi, hj]

private noncomputable def pointedEquiv (before after : ℕ → ℕ → Prop) (n : ℕ) :
    Pointed before after n ≃ WithBar (Allowed before after) n := by
  classical
  let f : Pointed before after n → WithBar (Allowed before after) n := fun p =>
    ⟨⟨mark p.val.2 p.val.1, fun i => Nat.le_of_lt_succ (p.val.2 i).isLt,
      mark_allowed.mpr p.property⟩, fun h => by simpa [mark] using h p.val.1⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    have he : mark p.val.2 p.val.1 = mark q.val.2 q.val.1 :=
      congrArg (fun e : WithBar (Allowed before after) n => e.val.val) hpq
    apply Subtype.ext
    refine Prod.ext ?_ (funext fun i => Fin.ext ?_)
    · simpa [mark] using congrArg (fun e : Fin n → Entry => (e p.val.1).2) he |>.symm
    · exact congrArg (fun e : Fin n → Entry => (e i).1) he
  · intro e
    have hex : ∃ k, (e.val.val k).2 = true := by
      simpa [Unbarred, Bool.not_eq_false] using e.property
    obtain ⟨k, hk⟩ := hex
    let a : Digits n := fun i => ⟨(e.val.val i).1, Nat.lt_succ_of_le (e.val.property.1 i)⟩
    have he : mark a k = e.val.val := by
      funext i
      refine Prod.ext rfl ?_
      by_cases hi : i = k
      · simpa [mark, hi] using hk.symm
      · have hplain : (e.val.val i).2 = false := by
          by_contra h
          have hb : (e.val.val i).2 = true := by
            simpa only [Bool.not_eq_false] using h
          rcases lt_or_gt_of_ne hi with hik | hki
          · simpa [Allowed, hb, hk] using e.val.property.2 hik
          · simpa [Allowed, hb, hk] using e.val.property.2 hki
        simp [mark, hi, hplain]
    exact ⟨⟨(k, a), mark_allowed.mp (he.symm ▸ e.val.property.2)⟩,
      Subtype.ext (Subtype.ext he)⟩

private theorem card_digits (n : ℕ) : Nat.card (Digits n) = n ! := by
  rw [Nat.card_pi]
  simp only [Nat.card_fin]
  rw [Fin.prod_univ_eq_prod_range fun i => i + 1, Finset.prod_range_add_one_eq_factorial]

-- A last maximizer has weak inequalities on its left and strict inequalities on its right.
private theorem existsUnique_last_max {α : Type*} [LinearOrder α] {n : ℕ} (f : Fin (n + 1) → α) :
    ∃! k, (∀ j < k, f j ≤ f k) ∧ (∀ j, k < j → f j < f k) := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  let s := Finset.univ.filter fun i => f i = f m
  have hs : s.Nonempty := ⟨m, by simp [s]⟩
  let k := s.max' hs
  have hk : f k = f m := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hle (j : Fin (n + 1)) : f j ≤ f k := hk ▸ hm j (Finset.mem_univ j)
  have hright (j : Fin (n + 1)) (hj : k < j) : f j < f k := by
    refine (hle j).lt_of_ne fun he => ?_
    exact hj.not_ge (s.le_max' j (by simp [s, he.trans hk]))
  refine ⟨k, ⟨fun j _ => hle j, hright⟩, fun j hj => ?_⟩
  rcases lt_trichotomy j k with h | h | h
  · exact ((hj.2 k h).not_ge (hle j)).elim
  · exact h
  · exact ((hright j h).not_ge (hj.1 k h)).elim

private theorem card_pointed_of_unique {before after : ℕ → ℕ → Prop} {n : ℕ}
    (h : ∀ a : Digits n, ∃! k, BarPosition before after a k) :
    Nat.card (Pointed before after n) = n ! := by
  rw [← card_digits n]
  apply Nat.card_congr
  refine Equiv.ofBijective (fun p : Pointed before after n => p.val.2) ⟨?_, ?_⟩
  · rintro ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩ (hab : a = b)
    subst b
    exact Subtype.ext (Prod.ext ((h a).unique hi hj) rfl)
  · intro a
    obtain ⟨k, hk, -⟩ := h a
    exact ⟨⟨(k, a), hk⟩, rfl⟩

private theorem count_of_pointed (B : Finset SignedPattern2) (before after : ℕ → ℕ → Prop)
    (pair : ∀ x y : Entry, ⟨compare x.1 y.1, x.2, y.2⟩ ∉ B ↔ Allowed before after x y)
    (n : ℕ) (h : Nat.card (Pointed before after n) = n !) :
    signedInvAvoidCount B n = 2 * n ! := by
  classical
  rw [count_eq_card B _ pair,
    ← Nat.card_congr (Equiv.sumCompl (fun e : Avoiders (Allowed before after) n => Unbarred e.val)),
    Nat.card_sum, Nat.card_congr (unbarredEquiv (fun _ _ => trivial) n), card_digits,
    ← Nat.card_congr (pointedEquiv before after n), h, two_mul]

private def MiddleSpec {n : ℕ} (b : ℕ) (a : Digits n) : Prop :=
  ∃ k, (a k).val = b ∧ BarPosition (· ≠ ·) (· < ·) a k

private abbrev Middle (b n : ℕ) := {a : Digits n // MiddleSpec b a}

private abbrev Omits (b n : ℕ) := {a : Digits n // ∀ i, (a i).val ≠ b}

private theorem card_omits_digit (b i : ℕ) :
    Nat.card {x : Fin (i + 1) // x.val ≠ b} = if b ≤ i then i else i + 1 := by
  split_ifs with h
  · let k : Fin (i + 1) := ⟨b, Nat.lt_succ_of_le h⟩
    let e : {x : Fin (i + 1) // x ≠ k} ≃ {x : Fin (i + 1) // x.val ≠ b} :=
      Equiv.subtypeEquivRight fun x => not_congr (Fin.ext_iff (a := x) (b := k))
    rw [Nat.card_congr e.symm, ← Nat.card_congr (finSuccAboveEquiv k), Nat.card_fin]
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by have := x.isLt; omega), Nat.card_fin]

-- If `b` fits at the last position, forbidding it leaves exactly the length of the prefix
-- many choices there. If it does not fit anywhere the word is unrestricted.
private theorem card_omits (n b : ℕ) (hb : b ≤ n + 1) :
    Nat.card (Omits b (n + 1)) = b * n ! := by
  let e : Omits b (n + 1) ≃ ((i : Fin (n + 1)) → {x : Fin (i.val + 1) // x.val ≠ b}) :=
    Equiv.subtypePiEquivPi (β := fun i : Fin (n + 1) => Fin (i.val + 1))
      (p := fun _ x => x.val ≠ b)
  rw [Nat.card_congr e, Nat.card_pi]
  simp_rw [card_omits_digit]
  induction n with
  | zero =>
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl | rfl <;> simp
  | succ n ih =>
    by_cases h : b ≤ n + 1
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ite_eq_left h]
      rw [ih h, Nat.factorial_succ]
      ac_rfl
    · have he : b = n + 2 := by omega
      subst b
      have hn (i : Fin (n + 2)) : ¬ n + 2 ≤ i.val := Nat.not_le_of_gt i.isLt
      simp only [ite_eq_right (hn _)]
      rw [Fin.prod_univ_eq_prod_range fun i => i + 1, Finset.prod_range_add_one_eq_factorial,
        Nat.factorial_succ (n + 1)]

private theorem middle_snoc_iff {n b : ℕ} (a : Digits n) (x : Fin (n + 1)) :
    MiddleSpec b (Fin.snoc a x) ↔
      (x.val = b ∧ ∀ i, (a i).val ≠ b) ∨ (b < x.val ∧ MiddleSpec b a) := by
  constructor
  · rintro ⟨k, hk, hbefore, hafter⟩
    induction k using Fin.lastCases with
    | last =>
      have hx : x.val = b := by simpa using hk
      exact Or.inl ⟨hx, fun i => by
        simpa [hx] using hbefore i.castSucc (Fin.castSucc_lt_last i)⟩
    | cast k =>
      have hk' : (a k).val = b := by simpa using hk
      refine Or.inr ⟨by simpa [hk'] using hafter (Fin.last n) (Fin.castSucc_lt_last k),
        k, hk', ?_, ?_⟩
      · intro i hi
        simpa using hbefore i.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hi)
      · intro i hi
        simpa using hafter i.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hi)
  · rintro (⟨hx, ha⟩ | ⟨hx, k, hk, hbefore, hafter⟩)
    · refine ⟨Fin.last n, by simpa using hx, ?_, fun j hj => ((Fin.le_last j).not_gt hj).elim⟩
      intro i hi
      induction i using Fin.lastCases with
      | last => exact (lt_irrefl _ hi).elim
      | cast i => simpa [hx] using ha i
    · refine ⟨k.castSucc, by simpa using hk, ?_, ?_⟩
      · intro i hi
        induction i using Fin.lastCases with
        | last => exact ((Fin.le_last k.castSucc).not_gt hi).elim
        | cast i => simpa using hbefore i (Fin.castSucc_lt_castSucc_iff.mp hi)
      · intro i hi
        induction i using Fin.lastCases with
        | last => simpa [hk] using hx
        | cast i => simpa using hafter i (Fin.castSucc_lt_castSucc_iff.mp hi)

-- The two summands correspond to a bar at the last digit and a bar in the prefix.
private noncomputable def middleSnocEquiv {n b : ℕ} (hb : b ≤ n) :
    Omits b n ⊕ ({x : Fin (n + 1) // b < x.val} × Middle b n) ≃ Middle b (n + 1) := by
  let k : Fin (n + 1) := ⟨b, Nat.lt_succ_of_le hb⟩
  refine Equiv.ofBijective (Sum.elim
    (fun a : Omits b n => ⟨Fin.snoc a.val k, (middle_snoc_iff _ _).mpr (Or.inl ⟨rfl, a.property⟩)⟩)
    (fun p : {x : Fin (n + 1) // b < x.val} × Middle b n =>
      ⟨Fin.snoc p.2.val p.1.val, (middle_snoc_iff _ _).mpr (Or.inr ⟨p.1.property, p.2.property⟩)⟩))
    ⟨?_, ?_⟩
  · rintro (a | ⟨x, a⟩) (a' | ⟨x', a'⟩) he
    all_goals simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Fin.snoc_inj] at he
    · exact congrArg Sum.inl (Subtype.ext he.1)
    · exact ((show b < x'.val.val from x'.property).ne (congrArg Fin.val he.2)).elim
    · exact ((show b < x.val.val from x.property).ne' (congrArg Fin.val he.2)).elim
    · exact congrArg Sum.inr (Prod.ext (Subtype.ext he.2) (Subtype.ext he.1))
  · intro a
    have he : Fin.snoc (Fin.init a.val) (a.val (Fin.last n)) = a.val := Fin.snoc_init_self _
    rcases (middle_snoc_iff _ _).mp (he.symm ▸ a.property) with ⟨hx, ha⟩ | ⟨hx, ha⟩
    · have hk : a.val (Fin.last n) = k := Fin.ext hx
      refine ⟨Sum.inl ⟨Fin.init a.val, ha⟩, Subtype.ext ?_⟩
      change Fin.snoc (Fin.init a.val) k = a.val
      rw [← hk, Fin.snoc_init_self]
    · exact ⟨Sum.inr (⟨a.val (Fin.last n), hx⟩, ⟨Fin.init a.val, ha⟩), Subtype.ext he⟩

private theorem card_above {n b : ℕ} (hb : b ≤ n) :
    Nat.card {x : Fin (n + 1) // b < x.val} = n - b := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let k : Fin (n + 1) := ⟨b, Nat.lt_succ_of_le hb⟩
  have he : (Finset.univ.filter fun x : Fin (n + 1) => b < x.val) = Finset.Ioi k := by
    ext x
    simp [Fin.lt_def, k]
  rw [he, Fin.card_Ioi]
  simp [k]

private theorem card_middle (n b : ℕ) (hb : b ≤ n) : Nat.card (Middle b (n + 1)) = n ! := by
  rw [← Nat.card_congr (middleSnocEquiv hb), Nat.card_sum, Nat.card_prod, card_above hb]
  induction n with
  | zero =>
    have h : b = 0 := by omega
    subst b
    simp only [Nat.sub_self, zero_mul, add_zero, Nat.factorial_zero]
    have ha (a : Digits 0) : ∀ i, (a i).val ≠ 0 := fun i => i.elim0
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv ha), card_digits, Nat.factorial_zero]
  | succ n ih =>
    rw [card_omits n b hb]
    by_cases h : b ≤ n
    · have hprefix := ih h
      rw [← Nat.card_congr (middleSnocEquiv h), Nat.card_sum, Nat.card_prod, card_above h,
        hprefix, ← Nat.add_mul, Nat.factorial_succ]
      congr 1
      omega
    · have he : b = n + 1 := by omega
      subst b
      simp [Nat.factorial_succ]

private noncomputable def pointedMiddleEquiv (n : ℕ) :
    Pointed (· ≠ ·) (· < ·) n ≃ (Σ b : Fin n, Middle b.val n) := by
  let f : Pointed (· ≠ ·) (· < ·) n → (Σ b : Fin n, Middle b.val n) := fun p =>
    ⟨⟨(p.val.2 p.val.1).val, (p.val.2 p.val.1).isLt.trans_le p.val.1.isLt⟩,
      ⟨p.val.2, p.val.1, rfl, p.property⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨⟨i, a⟩, hi⟩ ⟨⟨j, a'⟩, hj⟩ he
    have ha : a = a' := congrArg (fun s : Σ b : Fin n, Middle b.val n => s.2.val) he
    subst a'
    have hb : (a i).val = (a j).val := congrArg (fun s : Σ b : Fin n, Middle b.val n => s.1.val) he
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    change i = j
    rcases lt_trichotomy i j with h | h | h
    · exact ((hi.2 j h).ne hb).elim
    · exact h
    · exact ((hj.2 i h).ne hb.symm).elim
  · rintro ⟨b, a, k, hk, hp⟩
    let p : Pointed (· ≠ ·) (· < ·) n := ⟨(k, a), hp⟩
    have he : (f p).1 = b := Fin.ext hk
    refine ⟨p, Sigma.ext he ?_⟩
    subst b
    exact heq_of_eq (Subtype.ext rfl)

private theorem card_pointed_middle (n : ℕ) :
    Nat.card (Pointed (· ≠ ·) (· < ·) (n + 1)) = (n + 1)! := by
  classical
  rw [Nat.card_congr (pointedMiddleEquiv (n + 1)), Nat.card_sigma]
  simp only [card_middle n _ (Nat.le_of_lt_succ (Fin.isLt _)), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Nat.factorial_succ]

end SignedInvTwoFactorial

open SignedInvTwoFactorial in
/-- **Three six-pattern sets with 2 · n! avoiders (Theorem 17).** Write a length-2 signed pattern
as $\tau_1\tau_2$, where $00$, $01$ and $10$ record whether $|\tau_1|$ is equal to, smaller than
or larger than $|\tau_2|$ and a bar marks a barred letter, and write $|\bar I_n(A)|$ for the
number of signed inversion sequences of length $n$ avoiding every pattern of a set $A$ of such
patterns. For every $n \ge 1$ and each of the three sets
$A = \lbrace \bar 1\bar 0, \bar 1 0, \bar 0\bar 1, \bar 0\bar 0, \bar 0 0, 0\bar 1 \rbrace$,
$\lbrace \bar 1\bar 0, \bar 1 0, \bar 0\bar 1, \bar 0\bar 0, \bar 0 0, 0\bar 0 \rbrace$ and
$\lbrace \bar 1\bar 0, \bar 0\bar 1, \bar 0\bar 0, \bar 0 0, \bar 0 1, 1\bar 0 \rbrace$, we have
$|\bar I_n(A)| = 2 \cdot n!$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 17 (`integers-2026-A74-thm-17`). -/
public theorem signedInvAvoidCount_eq_two_mul_factorial :
    ∀ n, 1 ≤ n →
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n = 2 * n ! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} n = 2 * n ! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} n = 2 * n ! := by
  rintro (_ | n) hn
  · omega
  have hmin (a : Digits (n + 1)) : ∃! k, BarPosition (· ≥ ·) (· < ·) a k :=
    existsUnique_last_max (α := ℕᵒᵈ) (fun i => OrderDual.toDual (a i).val)
  have hmax (a : Digits (n + 1)) : ∃! k, BarPosition (· ≤ ·) (· > ·) a k :=
    existsUnique_last_max (fun i => (a i).val)
  refine ⟨count_of_pointed _ _ _ ?_ _ (card_pointed_of_unique hmin),
    count_of_pointed _ _ _ ?_ _ (card_pointed_middle n),
    count_of_pointed _ _ _ ?_ _ (card_pointed_of_unique hmax)⟩
  all_goals
    intro x y
    cases hx : x.2 <;> cases hy : y.2 <;>
      simp [Allowed, hx, hy, SignedPattern2.mk.injEq, compare_lt_iff_lt, compare_gt_iff_gt] <;>
        omega

end MetaMathlibExt
