/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import all MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import all MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC3
import all MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2FirstBars

/-!
# Wilf-equivalence by filling a suffix of bars at each magnitude

For each magnitude, the bijection keeps its first bar and toggles all later occurrences of
that magnitude. Thus a single bar becomes a barred suffix and a barred suffix becomes a
single bar. A new bar still has no smaller magnitude to its right: it has the same magnitude
as an earlier bar. This gives a direct bijection for the three-pattern classes in Lemma 9,
using the bar toggle of Theorem 13 rather than the generating trees of Lemma 9.

## References

* Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2 Signed
  Patterns*, INTEGERS 26 (2026), Article A74, pp. 1–74, Lemma 9 and Theorem 13.
  <https://math.colgate.edu/~integers/aa74/aa74.pdf>
* Toufik Mansour and Amir Safadi, *Inversion sequences and signed permutations*, Discrete
  Mathematics Letters 14 (2024), pp. 13–20, §§1–2, for signed inversion sequence avoidance and the
  generating-tree method used in the original proof of Lemma 9.
-/

namespace MetaMathlibExt

namespace signedInvSeq_wilf_b1b0_b10_b0b0

open signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 (Seen toggle seen_toggle toggle_involutive)

variable {n : ℕ}

-- Drop the extra unbarred-then-barred equal-value pattern from the four-pattern family.
private abbrev suffixPatterns (single : Bool) : Finset SignedPattern2 :=
  (signedInvSeq_wilf_b1b0_b10_b0b0_0b0.patterns single).erase ⟨.eq, false, true⟩

private theorem suffix_pair_iff (single : Bool) (x y : ℕ × Bool) :
    ⟨compare x.1 y.1, x.2, y.2⟩ ∉ suffixPatterns single ↔
      (x.2 = true → x.1 ≤ y.1) ∧ (x.2 = true → x.1 = y.1 → y.2 ≠ single) := by
  cases single <;> cases x.2 <;> cases y.2 <;>
    simp [suffixPatterns, signedInvSeq_wilf_b1b0_b10_b0b0_0b0.patterns,
      SignedPattern2.mk.injEq, compare_gt_iff_gt]

private theorem suffix_avoids_iff (single : Bool) (e : Fin n → ℕ × Bool) :
    (∀ p ∈ suffixPatterns single, ¬ SignedInvSeqContains e p) ↔
      (∀ i j, i < j → (e i).2 = true → (e i).1 ≤ (e j).1) ∧
      (∀ i, Seen e i → (e i).2 ≠ single) := by
  rw [signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1.avoids_iff _ _ (suffix_pair_iff single)]
  constructor
  · intro h
    exact ⟨fun _ _ hij ↦ (h hij).1, fun _ ⟨_, hij, hi, heq⟩ ↦ (h hij).2 hi heq⟩
  · rintro ⟨hright, hsign⟩ i j hij
    exact ⟨hright i j hij, fun hi heq ↦ hsign j ⟨i, hij, hi, heq⟩⟩

private theorem toggle_suffix_avoids (single : Bool) (e : Fin n → ℕ × Bool)
    (h : ∀ p ∈ suffixPatterns single, ¬ SignedInvSeqContains e p) :
    ∀ p ∈ suffixPatterns (!single), ¬ SignedInvSeqContains (toggle e) p := by
  obtain ⟨hright, hsign⟩ := (suffix_avoids_iff single e).mp h
  apply (suffix_avoids_iff _ _).mpr
  constructor
  · intro i j hij hi
    change (e i).1 ≤ (e j).1
    by_cases hseen : Seen e i
    · obtain ⟨k, hki, hk, hval⟩ := hseen
      exact hval ▸ hright k j (hki.trans hij) hk
    · exact hright i j hij (by simpa [toggle, hseen] using hi)
  · intro i hi
    have hseen := (seen_toggle e i).mp hi
    simpa [toggle, hseen] using hsign i hseen

private theorem suffix_count_eq :
    signedInvAvoidCount (suffixPatterns true) = signedInvAvoidCount (suffixPatterns false) := by
  funext n
  apply Nat.card_congr
  exact {
    toFun := fun e ↦ ⟨toggle e.val, e.property.1, toggle_suffix_avoids true _ e.property.2⟩
    invFun := fun e ↦ ⟨toggle e.val, e.property.1, toggle_suffix_avoids false _ e.property.2⟩
    left_inv := fun e ↦ Subtype.ext (toggle_involutive e.val)
    right_inv := fun e ↦ Subtype.ext (toggle_involutive e.val) }

end signedInvSeq_wilf_b1b0_b10_b0b0

/-- **Mansour–Safadi Lemma 9: a Wilf-equivalence of three-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar0\} \sim \{\bar1\bar0, \bar10, \bar00\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 9 (`integers-2026-A74-lem-9`). -/
public theorem signedInvSeq_wilf_b1b0_b10_b0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, false⟩} := by
  have hp (b : Bool) : signedInvSeq_wilf_b1b0_b10_b0b0.suffixPatterns b =
      {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, b⟩} := by
    cases b <;> decide
  simpa only [hp] using signedInvSeq_wilf_b1b0_b10_b0b0.suffix_count_eq

end MetaMathlibExt
