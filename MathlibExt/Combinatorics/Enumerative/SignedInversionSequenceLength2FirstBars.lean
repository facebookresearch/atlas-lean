/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2

/-!
# Wilf-equivalence by copying bars from first occurrences

Mansour and Safadi's four-pattern Wilf-equivalence follows by copying the sign of the first
occurrence of each magnitude to every occurrence. The inverse removes bars from repetitions.
-/

namespace MetaMathlibExt

namespace signedInvSeq_wilf_b1b0_b10_b0b0_0b0

variable {n : ℕ}

private abbrev patterns (single : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, single⟩, ⟨.eq, false, true⟩}

-- In both classes, a bar forbids every smaller magnitude to its right.
-- For a repeated magnitude the later sign is unbarred on the left and agrees on the right.
private theorem avoids_iff (single : Bool) (e : Fin n → ℕ × Bool) :
    (∀ p ∈ patterns single, ¬ SignedInvSeqContains e p) ↔ ∀ i j, i < j →
      ((e i).2 = true → (e i).1 ≤ (e j).1) ∧
      ((e i).1 = (e j).1 → (e j).2 = ((e i).2 && !single)) := by
  have pair (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns single ↔
        ((e i).2 = true → (e i).1 ≤ (e j).1) ∧
        ((e i).1 = (e j).1 → (e j).2 = ((e i).2 && !single)) := by
    cases single <;> cases hi : (e i).2 <;> cases hj : (e j).2 <;>
      simp [patterns, SignedPattern2.mk.injEq, compare_gt_iff_gt]
  constructor
  · intro h i j hij
    exact (pair i j).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair i j).mpr (h i j hij)
    simpa only [ho, hs, ht] using hm

private noncomputable def first (e : Fin n → ℕ × Bool) (i : Fin n) : Fin n :=
  WellFoundedLT.min {j | (e j).1 = (e i).1} ⟨i, rfl⟩

private theorem first_value (e : Fin n → ℕ × Bool) (i : Fin n) :
    (e (first e i)).1 = (e i).1 :=
  wellFounded_lt.min_mem {j | (e j).1 = (e i).1} ⟨i, rfl⟩

private theorem first_le (e : Fin n → ℕ × Bool) {i j : Fin n} (h : (e i).1 = (e j).1) :
    first e j ≤ i :=
  WellFoundedLT.min_le (s := {k | (e k).1 = (e j).1}) h

private theorem first_eq (e : Fin n → ℕ × Bool) {i j : Fin n} (h : (e i).1 = (e j).1) :
    first e i = first e j := by
  simp only [first, h]

-- Retain the first sign at all occurrences, or only at the first one.
private noncomputable def mark (single : Bool) (e : Fin n → ℕ × Bool) (i : Fin n) : ℕ × Bool :=
  ((e i).1, (e (first e i)).2 && (!single || decide (first e i = i)))

private theorem mark_avoids (s t : Bool) (e : Fin n → ℕ × Bool)
    (h : ∀ p ∈ patterns s, ¬ SignedInvSeqContains e p) :
    ∀ p ∈ patterns t, ¬ SignedInvSeqContains (mark t e) p := by
  rw [avoids_iff] at h ⊢
  intro i j hij
  constructor
  · intro hi
    have hb := (Bool.and_eq_true_iff.mp hi).1
    have hle := (h (first e i) j ((first_le e (i := i) rfl).trans_lt hij)).1 hb
    change (e i).1 ≤ (e j).1
    simpa only [first_value] using hle
  · intro heq
    have hf := first_eq e heq
    have hne := ((first_le e heq).trans_lt hij).ne
    cases t <;> simp [mark, hf, hne]

private theorem mark_twice (s t : Bool) (e : Fin n → ℕ × Bool) :
    mark s (mark t e) = mark s e := by
  funext i
  have hf := first_eq e (first_value e i)
  change ((e i).1, (mark t e (first e i)).2 && (!s || decide (first e i = i))) = _
  simp [mark, hf]

private theorem mark_self (s : Bool) (e : Fin n → ℕ × Bool)
    (h : ∀ p ∈ patterns s, ¬ SignedInvSeqContains e p) : mark s e = e := by
  funext i
  refine Prod.ext (by rfl) ?_
  rcases (first_le e (i := i) rfl).lt_or_eq with hlt | hfirst
  · have hs := ((avoids_iff s e).mp h _ _ hlt).2 (first_value e i)
    cases s <;> simp_all [mark, hlt.ne]
  · simp [mark, hfirst]

end signedInvSeq_wilf_b1b0_b10_b0b0_0b0

open signedInvSeq_wilf_b1b0_b10_b0b0_0b0 in
/-- **Mansour–Safadi Theorem 9: a Wilf-equivalence of four-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar0, 0\bar0\} \sim \{\bar1\bar0, \bar10, \bar00, 0\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 9 (`integers-2026-A74-thm-9`). -/
public theorem signedInvSeq_wilf_b1b0_b10_b0b0_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩} := by
  funext n
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨mark false e.val, e.property.1, mark_avoids true false _ e.property.2⟩
    invFun := fun e => ⟨mark true e.val, e.property.1, mark_avoids false true _ e.property.2⟩
    left_inv := fun e => Subtype.ext ((mark_twice _ _ _).trans (mark_self _ _ e.property.2))
    right_inv := fun e => Subtype.ext ((mark_twice _ _ _).trans (mark_self _ _ e.property.2)) }

end MetaMathlibExt
