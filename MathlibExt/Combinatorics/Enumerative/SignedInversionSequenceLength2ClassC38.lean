/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import Mathlib.Logic.Equiv.Sum

/-!
# Signed inversion sequences in class C38

The two pattern sets in class C38 have the same avoiders. Decomposing them by their
last entry gives the recurrence for their common generating function.
-/

namespace MetaMathlibExt

namespace signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01

private abbrev Entry := ℕ × Bool

private abbrev patterns (b : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, b⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.lt, false, false⟩}

private abbrev Bounded {n : ℕ} (e : Fin n → Entry) := ∀ i, (e i).1 ≤ i

-- A barred entry is zero, and an unbarred entry bounds all later magnitudes.
private structure Valid {n : ℕ} (e : Fin n → Entry) : Prop where
  bound : Bounded e
  bar : ∀ i, (e i).2 = true → (e i).1 = 0
  decreasing : ∀ i j, i < j → (e i).2 = false → (e j).1 ≤ (e i).1

private abbrev Word (n : ℕ) := {e : Fin n → Entry // Valid e}

private theorem valid_iff {n : ℕ} (e : Fin n → Entry) (b : Bool) :
    Valid e ↔ Bounded e ∧ ∀ p ∈ patterns b, ¬ SignedInvSeqContains e p := by
  have pair (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns b ↔
        (((e i).2 = false ∨ (e j).2 = true) → (e j).1 ≤ (e i).1) ∧
        ((e i).2 = true → (e j).2 = b → (e i).1 ≤ (e j).1) := by
    cases (e i).2 <;> cases (e j).2 <;> cases b <;>
      simp [patterns, SignedPattern2.mk.injEq, compare_lt_iff_lt, compare_gt_iff_gt,
        le_antisymm_iff, and_comm]
  constructor
  · rintro h
    refine ⟨h.bound, ?_⟩
    rintro p hp ⟨i, j, hij, hcmp, hi, hj⟩
    apply (pair i j).mpr ?_ (by simpa only [hcmp, hi, hj] using hp)
    constructor
    · rintro (hplain | hbar)
      · exact h.decreasing i j hij hplain
      · simp [h.bar j hbar]
    · intro hbar _
      simp [h.bar i hbar]
  · rintro ⟨bound, avoids⟩
    have hpair (i j : Fin n) (hij : i < j) :=
      (pair i j).mp fun hp => avoids _ hp ⟨i, j, hij, rfl, rfl, rfl⟩
    refine ⟨bound, ?_, fun i j hij hi => (hpair i j hij).1 (Or.inl hi)⟩
    intro j hj
    cases n with
    | zero => exact j.elim0
    | succ n =>
      have h0 : (e 0).1 = 0 := Nat.le_zero.mp (bound 0)
      rcases (Fin.zero_le j).eq_or_lt with h | h
      · simpa [← h] using h0
      · exact Nat.le_zero.mp ((hpair 0 j h).1 (Or.inr hj) |>.trans h0.le)

private theorem count_eq (b : Bool) (n : ℕ) :
    signedInvAvoidCount (patterns b) n = Nat.card (Word n) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun e => (valid_iff e b).symm)

private instance wordFinite (n : ℕ) : Finite (Word n) :=
  Finite.of_injective
    (fun (w : Word n) (i : Fin n) =>
      ((⟨(w.val i).1, Nat.lt_succ_of_le (w.property.bound i)⟩ : Fin (i.val + 1)), (w.val i).2))
    (by
      intro u v h
      apply Subtype.ext
      funext i
      exact Prod.ext (congrArg (fun w => (w i).1.val) h) (congrArg (fun w => (w i).2) h))

private abbrev last {n : ℕ} (w : Word (n + 1)) := w.val (Fin.last n)

private abbrev Plain (n : ℕ) := {w : Word (n + 1) // (last w).2 = false}

private def appendZero {n : ℕ} (w : Word n) (b : Bool) : Word (n + 1) := by
  refine ⟨Fin.snoc w.val (0, b), ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using w.property.bound i
  · intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using w.property.bar i
  · intro i j hij
    induction j using Fin.lastCases with
    | last => simp
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact (not_lt_of_ge (Fin.le_last _) hij).elim
      | cast i =>
        simpa using w.property.decreasing i j (Fin.castSucc_lt_castSucc_iff.mp hij)

private def dropLast {n : ℕ} (w : Word (n + 1)) : Word n :=
  ⟨Fin.init w.val, fun i => w.property.bound i.castSucc, fun i => w.property.bar i.castSucc,
    fun i j h => w.property.decreasing i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr h)⟩

private theorem drop_append {n : ℕ} (w : Word n) (b : Bool) : dropLast (appendZero w b) = w := by
  apply Subtype.ext
  exact Fin.init_snoc (α := fun _ => Entry) (0, b) w.val

private theorem append_drop {n : ℕ} (w : Word (n + 1)) (b : Bool) (h : last w = (0, b)) :
    appendZero (dropLast w) b = w := by
  apply Subtype.ext
  change Fin.snoc (Fin.init w.val) (0, b) = w.val
  rw [← h, Fin.snoc_init_self]

-- Split off words ending in a barred zero.
private theorem card_by_sign (n : ℕ) :
    Nat.card (Word (n + 1)) = Nat.card (Plain n) + Nat.card (Word n) := by
  classical
  let equiv : {w : Word (n + 1) // ¬ (last w).2 = false} ≃ Word n :=
    { toFun := fun w => dropLast w.val
      invFun := fun w => ⟨appendZero w true, by simp [last, appendZero]⟩
      left_inv := fun w => by
        have hb : (last w.val).2 = true := by simpa using w.property
        exact Subtype.ext (append_drop _ _ (Prod.ext (w.val.property.bar _ hb) hb))
      right_inv := fun w => drop_append w true }
  rw [← Nat.card_congr (Equiv.sumCompl (fun w : Word (n + 1) => (last w).2 = false)),
    Nat.card_sum, Nat.card_congr equiv]

private def liftEntry (x : Entry) : Entry := (if x.2 then 0 else x.1 + 1, x.2)

private def lowerEntry (x : Entry) : Entry := (x.1 - 1, x.2)

-- Prepending a barred zero makes room to increase every unbarred magnitude by one.
private def raiseWord {n : ℕ} (w : Word n) : Word (n + 1) := by
  refine ⟨Fin.cons (0, true) (fun i => liftEntry (w.val i)), ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      cases hb : (w.val i).2 <;> simp [liftEntry, hb, w.property.bound]
  · intro i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp [liftEntry]
  · intro i
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      intro j
      induction j using Fin.cases with
      | zero => simp
      | succ j =>
        intro hij hi
        have h := w.property.decreasing i j (Fin.succ_lt_succ_iff.mp hij) hi
        cases hj : (w.val j).2 <;> simp [liftEntry, hj, show (w.val i).2 = false from hi, h]

private def lowerTail {n : ℕ} (w : Word (n + 1)) : Word n :=
  ⟨fun i => lowerEntry (w.val i.succ),
    fun i => Nat.sub_le_of_le_add (w.property.bound i.succ),
    fun i hi => by simp [lowerEntry, w.property.bar i.succ hi],
    fun i j hij hi => Nat.sub_le_sub_right
      (w.property.decreasing i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) hi) 1⟩

private theorem lower_raise {n : ℕ} (w : Word n) : lowerTail (raiseWord w) = w := by
  apply Subtype.ext
  funext i
  simp only [lowerTail, raiseWord, Fin.cons_succ]
  refine Prod.ext ?_ rfl
  cases hb : (w.val i).2 <;> simp [lowerEntry, liftEntry, hb, w.property.bar i]

-- If the word ends in a positive value, every unbarred value is positive.
private theorem raise_lower {n : ℕ} (w : Word (n + 1)) (h : 0 < (last w).1) :
    raiseWord (lowerTail w) = w := by
  have pos (i : Fin (n + 1)) (hi : (w.val i).2 = false) : 0 < (w.val i).1 := by
    rcases (Fin.le_last i).lt_or_eq with hlt | rfl
    · exact h.trans_le (w.property.decreasing i _ hlt hi)
    · exact h
  have hz : (w.val 0).1 = 0 := Nat.le_zero.mp (w.property.bound 0)
  apply Subtype.ext
  funext i
  induction i using Fin.cases with
  | zero =>
    have hb : (w.val 0).2 = true := by
      cases hb : (w.val 0).2
      · exact ((pos 0 hb).ne' hz).elim
      · rfl
    exact Prod.ext hz.symm hb.symm
  | succ i =>
    simp only [lowerTail, raiseWord, Fin.cons_succ]
    refine Prod.ext ?_ rfl
    cases hb : (w.val i.succ).2
    · simp [lowerEntry, liftEntry, hb, Nat.sub_add_cancel (pos _ hb)]
    · simp [lowerEntry, liftEntry, hb, w.property.bar _ hb]

-- A word ending in an unbarred zero extends an arbitrary word. A word ending
-- in a positive value is obtained by raising a shorter word ending unbarred.
private theorem card_plain (n : ℕ) :
    Nat.card (Plain (n + 1)) = Nat.card (Word (n + 1)) + Nat.card (Plain n) := by
  classical
  let zeroLast (w : Plain (n + 1)) := (last w.val).1 = 0
  let zeroEquiv : {w // zeroLast w} ≃ Word (n + 1) :=
    { toFun := fun w => dropLast w.val.val
      invFun := fun w => ⟨⟨appendZero w false, by simp [last, appendZero]⟩,
        by simp [zeroLast, last, appendZero]⟩
      left_inv := fun w => Subtype.ext (Subtype.ext (append_drop _ _
        (Prod.ext w.property w.val.property)))
      right_inv := fun w => drop_append w false }
  have raised (w : Word (n + 1)) : last (raiseWord w) = liftEntry (last w) :=
    Fin.cons_succ (α := fun _ => Entry) (0, true) (fun i => liftEntry (w.val i)) (Fin.last n)
  let posEquiv : {w // ¬ zeroLast w} ≃ Plain n :=
    { toFun := fun w => ⟨lowerTail w.val.val, w.val.property⟩
      invFun := fun w => ⟨⟨raiseWord w.val, by rw [raised]; exact w.property⟩, by
        change (last (raiseWord w.val)).1 ≠ 0
        simp [raised, liftEntry, w.property]⟩
      left_inv := fun w => Subtype.ext (Subtype.ext
        (raise_lower w.val.val (Nat.pos_of_ne_zero w.property)))
      right_inv := fun w => Subtype.ext (lower_raise w.val) }
  rw [← Nat.card_congr (Equiv.sumCompl zeroLast), Nat.card_sum,
    Nat.card_congr zeroEquiv, Nat.card_congr posEquiv]

private theorem recurrence (n : ℕ) :
    signedInvAvoidCount (patterns true) (n + 2) + signedInvAvoidCount (patterns true) n =
      3 * signedInvAvoidCount (patterns true) (n + 1) := by
  simp only [count_eq]
  change Nat.card (Word (n + 1 + 1)) + Nat.card (Word n) = 3 * Nat.card (Word (n + 1))
  have hs := card_by_sign n
  have ht := card_by_sign (n + 1)
  have hp := card_plain n
  omega

end signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01

open PowerSeries
open signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01 in
/-- **Signed inversion sequences avoiding $\{\bar1\bar0, \bar0\bar1, 0\bar1, 01\}$.** For a set $B$
of length-2 signed patterns (a bar marks a barred letter), let $|\bar I_n(B)|$ be the number of
signed inversion sequences of length $n$ avoiding every pattern of $B$, and let
$F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n \in \mathbb{Q}[[x]]$. Let
$B = \{\bar1\bar0, \bar0\bar1, 0\bar1, 01\}$ and $C = \{\bar10, \bar0\bar1, 0\bar1, 01\}$. Then
$|\bar I_n(B)| = |\bar I_n(C)|$ for every $n \ge 0$, and $(1 - 3x + x^2) F_B(x) = 1 - x$, that is,
$F_B(x) = (1 - x)/(1 - 3x + x^2)$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C38) (`integers-2026-A74-thm-3`). -/
public theorem signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    (1 - 3 * X + X ^ 2) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - X := by
  constructor
  · funext n
    exact (count_eq true n).trans (count_eq false n).symm
  · let F := signedInvAvoidGF (patterns true)
    change (1 - 3 * X + X ^ 2) * F = 1 - X
    have expand : (1 - 3 * X + X ^ 2) * F = F - (X * F + X * F + X * F) + X * (X * F) := by
      ring
    rw [expand]
    ext n
    rcases n with _ | _ | n
    · norm_num only [map_add, map_sub, coeff_zero_X_mul, F, coeff_signedInvAvoidGF,
        signedInvAvoidCount_zero, coeff_one, coeff_X, ite_true, ite_false]
    · norm_num [coeff_succ_X_mul, coeff_zero_X_mul, F, coeff_signedInvAvoidGF,
        signedInvAvoidCount_one, signedInvAvoidCount_zero, coeff_one, coeff_X]
    · simp only [map_add, map_sub, coeff_succ_X_mul, F, coeff_signedInvAvoidGF, coeff_one, coeff_X,
        Nat.succ_ne_zero, Nat.succ.injEq, ite_false, sub_zero]
      have h : (signedInvAvoidCount (patterns true) (n + 2) : ℚ) +
          signedInvAvoidCount (patterns true) n =
            3 * signedInvAvoidCount (patterns true) (n + 1) := by
        exact_mod_cast recurrence n
      linarith

end MetaMathlibExt
