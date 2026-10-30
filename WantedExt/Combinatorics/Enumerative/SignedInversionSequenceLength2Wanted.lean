/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Signed inversion sequences avoiding sets of length-2 signed patterns

Statements from Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of
Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74.

A signed inversion sequence of length `n` is `e₁ ⋯ eₙ` with `e_{i+1} ∈ {0, 0̄, 1, 1̄, …, i, ī}`;
here it is `e : Fin n → ℕ × Bool` with `(e i).1 ≤ i` (zero-based positions), the second
component recording a bar. A length-2 signed pattern is one of `00`, `01`, `10` with each letter
possibly barred (twelve patterns); `e` contains it when some `i < j` has `|e_i| |e_j|`
order-isomorphic to `|τ₁| |τ₂|` and `e_i`, `e_j` barred exactly when `τ₁`, `τ₂` are. `Ī_n(B)` is
the set of length-`n` signed inversion sequences avoiding every pattern of `B`, `B ∼ C`
(Wilf-equivalence) means `|Ī_n(B)| = |Ī_n(C)|` for all `n ≥ 0`, and
`F_B(x) = ∑_{n ≥ 0} |Ī_n(B)| xⁿ`. In the declarations, the paper's pattern `1̄0` is
`⟨.gt, true, false⟩`, `0̄1̄` is `⟨.lt, true, true⟩`, `00̄` is `⟨.eq, false, true⟩`, and so on.
-/

namespace MetaMathlibExt

open Nat PowerSeries

@[expose] public section

/-- A length-2 signed pattern `τ₁τ₂`: `ord` is the comparison of `|τ₁|` with `|τ₂|` (`.eq` for
`00`, `.lt` for `01`, `.gt` for `10`), and `bar₁`, `bar₂` say whether `τ₁`, `τ₂` are barred.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
structure SignedPattern2 where
  /-- The comparison of `|τ₁|` with `|τ₂|`. -/
  ord : Ordering
  /-- Whether the first letter is barred. -/
  bar₁ : Bool
  /-- Whether the second letter is barred. -/
  bar₂ : Bool
deriving DecidableEq, Fintype

/-- There are twelve length-2 signed patterns.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 5 (`binom 12 k` sets of `k`
patterns). -/
theorem card_signedPattern2 : Fintype.card SignedPattern2 = 12 := by decide

/-- The signed inversion sequence `e` (values `(e i).1`, bars `(e i).2`) contains the length-2
signed pattern `p`: some positions `i < j` have `|e_i| |e_j|` order-isomorphic to `p` and the
bars of `e_i`, `e_j` equal those of `p`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
def SignedInvSeqContains {n : ℕ} (e : Fin n → ℕ × Bool) (p : SignedPattern2) : Prop :=
  ∃ i j : Fin n, i < j ∧ compare (e i).1 (e j).1 = p.ord ∧ (e i).2 = p.bar₁ ∧ (e j).2 = p.bar₂

/-- `|Ī_n(B)|`: the number of signed inversion sequences of length `n` avoiding every pattern
of `B`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
noncomputable def signedInvAvoidCount (B : Finset SignedPattern2) (n : ℕ) : ℕ :=
  Nat.card {e : Fin n → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ B, ¬ SignedInvSeqContains e p}

/-- The empty sequence is the only signed inversion sequence of length `0`, and it avoids every
pattern: `|Ī_0(B)| = 1`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
theorem signedInvAvoidCount_zero (B : Finset SignedPattern2) : signedInvAvoidCount B 0 = 1 := by
  rw [signedInvAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e e' => Subtype.ext (funext fun i => i.elim0)⟩, ⟨⟨fun i => i.elim0, ?_⟩⟩⟩
  exact ⟨fun i => i.elim0, fun _ _ ⟨i, _⟩ => i.elim0⟩

/-- The signed inversion sequences of length `1` are `0` and `0̄`, and both avoid every length-2
pattern: `|Ī_1(B)| = 2`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
theorem signedInvAvoidCount_one (B : Finset SignedPattern2) : signedInvAvoidCount B 1 = 2 := by
  have hpat : ∀ (e : Fin 1 → ℕ × Bool) (p : SignedPattern2), ¬ SignedInvSeqContains e p := by
    rintro e p ⟨i, j, hij, -⟩
    exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl j)
  let f : {e : Fin 1 → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ B, ¬ SignedInvSeqContains e p} ≃
      Bool :=
    { toFun := fun e => (e.1 0).2
      invFun := fun b => ⟨fun _ => (0, b), fun i => Nat.zero_le _, fun p _ => hpat _ p⟩
      left_inv := fun e => by
        refine Subtype.ext (funext fun i => ?_)
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        have h0 : (e.1 0).1 = 0 := Nat.le_zero.mp (e.2.1 0)
        exact Prod.ext h0.symm rfl
      right_inv := fun b => rfl }
  rw [signedInvAvoidCount, Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_bool]

/-- The paper's generating function `F_B(x) = ∑_{n ≥ 0} |Ī_n(B)| xⁿ` in `ℚ⟦X⟧`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 2. -/
noncomputable def signedInvAvoidGF (B : Finset SignedPattern2) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (signedInvAvoidCount B n : ℚ)

/-- The coefficients of `F_B` are the counts: `[xⁿ] F_B = |Ī_n(B)|`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 2. -/
theorem coeff_signedInvAvoidGF (B : Finset SignedPattern2) (n : ℕ) :
    coeff n (signedInvAvoidGF B) = (signedInvAvoidCount B n : ℚ) := by
  simp [signedInvAvoidGF]

/-- `sw_k`: the number of Wilf-equivalence classes among the sets of `k` length-2 signed
patterns, i.e. the number of distinct counting functions `n ↦ |Ī_n(B)|` with `|B| = k`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1. -/
noncomputable def signedWilfClassCount (k : ℕ) : ℕ :=
  Set.ncard ((fun B => signedInvAvoidCount B) '' {B : Finset SignedPattern2 | B.card = k})

/-- `sw_0 = 1`: the empty set is the only set of no patterns.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1 (definition of `sw_k`). -/
theorem signedWilfClassCount_zero : signedWilfClassCount 0 = 1 := by
  have : {B : Finset SignedPattern2 | B.card = 0} = {∅} := by
    ext B
    simp
  rw [signedWilfClassCount, this, Set.image_singleton, Set.ncard_singleton]

/-- **Lemma 1.** `{0̄1̄, 0̄0, 01}` ∼ `{0̄1̄, 0̄1, 01}`, and `F_{0̄1̄, 0̄0, 01}(x) = (1 - x) / (1 -
3x + x²)`, stated after clearing the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 1 (`integers-2026-A74-lem-1`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b00_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, false⟩} ∧
    (1 - 3 * X + X ^ 2) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, false⟩} = 1 - X

/-- **Lemma 2.** `{0̄0̄, 0̄0, 01̄}` ∼ `{0̄0, 0̄1, 01̄}`, and `|Ī_n(0̄0̄, 0̄0, 01̄)| = 1 +
∑_{j=0}^{n-1} (2j + 1) j!`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 2 (`integers-2026-A74-lem-2`). -/
public theorem_wanted signedInvSeq_wilf_and_count_b0b0_b00_0b1 :
    signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n =
        1 + ∑ j ∈ Finset.range n, (2 * j + 1) * j !

/-- **Lemma 3.** `{0̄1̄, 0̄0̄, 01̄}` ∼ `{0̄1̄, 0̄0, 01̄}` ∼ `{0̄1̄, 01̄, 00̄}`, and `|Ī_n(0̄1̄,
0̄0̄, 01̄)| = n! (1 + H_n)` with `H_n` the `n`th harmonic number.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 3 (`integers-2026-A74-lem-3`). -/
public theorem_wanted signedInvSeq_wilf_and_count_b0b1_b0b0_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩} ∧
    ∀ n, (signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩} n : ℚ) =
        n ! * (1 + harmonic n)

/-- **Lemma 4.** `{0̄1̄, 0̄0̄, 0̄1}` ∼ `{0̄1̄, 0̄0, 0̄1}`, and `|Ī_n(0̄1̄, 0̄0̄, 0̄1)| = ∑_{j=0}^{n}
j! (j + 1)^(n-j)`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 4 (`integers-2026-A74-lem-4`). -/
public theorem_wanted signedInvSeq_wilf_and_count_b0b1_b0b0_b01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} n =
        ∑ j ∈ Finset.range (n + 1), j ! * (j + 1) ^ (n - j)

/-- **Lemma 5.** `{1̄0̄, 0̄1̄, 01}` ∼ `{1̄0, 0̄1̄, 01}`, and `F_{1̄0̄, 0̄1̄, 01}(x) = 1 + x(1-x)² /
((1-2x)(1-3x+x²)) + x(1-x+x²) / ((1-2x)(1-x)²)`, stated after multiplying by the unit
`(1-2x)(1-3x+x²)(1-x)²`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 5 (`integers-2026-A74-lem-5`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, false⟩} ∧
    (1 - 2 * X) * (1 - 3 * X + X ^ 2) * (1 - X) ^ 2 * signedInvAvoidGF {⟨.gt, true, true⟩,
        ⟨.lt, true, true⟩, ⟨.lt, false, false⟩} =
      (1 - 2 * X) * (1 - 3 * X + X ^ 2) * (1 - X) ^ 2 + X * (1 - X) ^ 4 +
        X * (1 - X + X ^ 2) * (1 - 3 * X + X ^ 2)

/-- **Lemma 6.** `{1̄0̄, 0̄0̄, 0̄1}` ∼ `{1̄0̄, 0̄0, 0̄1}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 6 (`integers-2026-A74-lem-6`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_b01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩}

/-- **Lemma 7.** `{1̄0, 0̄1̄, 0̄0̄}` ∼ `{1̄0, 0̄1̄, 0̄0}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 7 (`integers-2026-A74-lem-7`). -/
public theorem_wanted signedInvSeq_wilf_b10_b0b1_b0b0 :
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩}

/-- **Lemma 8.** For each of the eight sets `B` in parts (i)–(vii) (`{1̄0̄, 0̄1̄, 0̄0̄}`, `{1̄0̄,
0̄1̄, 0̄0}`, `{1̄0̄, 0̄1̄, 01̄}`, `{1̄0, 0̄1̄, 01̄}`, `{1̄0, 0̄0, 0̄1}`, `{1̄0̄, 0̄1̄, 00̄}`,
`{1̄0, 0̄0, 01̄}`, `{1̄0, 00̄, 01̄}`), `|Ī_n(B)| = (n + 1)!` for all `n ≥ 0`. The unbarred `I_n`
printed in parts (iii) and (iv) is read as `Ī_n`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 8 (`integers-2026-A74-lem-8`). -/
public theorem_wanted signedInvAvoidCount_eq_factorial_succ :
    ∀ n,
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n = (n + 1)! ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, false, true⟩, ⟨.lt, false, true⟩} n = (n + 1)!

/-- **Lemma 9.** `{1̄0̄, 1̄0, 0̄0̄}` ∼ `{1̄0̄, 1̄0, 0̄0}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 9 (`integers-2026-A74-lem-9`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, false⟩}

/-- **Lemma 10.** `{1̄0̄, 0̄0̄, 10̄}` ∼ `{1̄0̄, 00̄, 10̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Lemma 10 (`integers-2026-A74-lem-10`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

/-- **Theorem 1.** `sw_3 = 93`, `sw_4 = 195`, `239 ≤ sw_5 ≤ 240`, `sw_6 = 190`, `sw_7 = 107`, `sw_8
= 49`, `sw_9 = 22`, `sw_10 = 8`, `sw_11 = 3` and `sw_12 = 1`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1 (`integers-2026-A74-thm-1`). -/
public theorem_wanted signedWilfClassCount_three_to_twelve :
    signedWilfClassCount 3 = 93 ∧ signedWilfClassCount 4 = 195 ∧
    239 ≤ signedWilfClassCount 5 ∧ signedWilfClassCount 5 ≤ 240 ∧
    signedWilfClassCount 6 = 190 ∧ signedWilfClassCount 7 = 107 ∧ signedWilfClassCount 8 = 49 ∧
    signedWilfClassCount 9 = 22 ∧ signedWilfClassCount 10 = 8 ∧ signedWilfClassCount 11 = 3 ∧
    signedWilfClassCount 12 = 1

/-- The equivalence `{1̄0̄, 1̄0, 0̄0̄, 0̄0, 00}` ∼ `{1̄0̄, 1̄0, 0̄1̄, 01̄, 00}` (Class 141 of Table
6), which the paper states remains to be shown to settle `sw_5 = 239`. Open in the source.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1, closing remark
(`integers-2026-A74-thm-1`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b0_b00_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.lt, false, true⟩, ⟨.eq, false, false⟩}

/-- **Theorem 2.** `sw_3 = 93`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 2 (`integers-2026-A74-thm-2`). -/
public theorem_wanted signedWilfClassCount_three :
    signedWilfClassCount 3 = 93

/-- **Theorem 10.** `sw_4 = 195`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 10 (`integers-2026-A74-thm-10`). -/
public theorem_wanted signedWilfClassCount_four :
    signedWilfClassCount 4 = 195

/-- **Theorem 11.** `239 ≤ sw_5 ≤ 240`, `sw_6 = 190`, `sw_7 = 107`, `sw_8 = 49`, `sw_9 = 22`, `sw_10
= 8`, `sw_11 = 3` and `sw_12 = 1`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 11 (`integers-2026-A74-thm-11`). -/
public theorem_wanted signedWilfClassCount_five_to_twelve :
    239 ≤ signedWilfClassCount 5 ∧ signedWilfClassCount 5 ≤ 240 ∧
    signedWilfClassCount 6 = 190 ∧ signedWilfClassCount 7 = 107 ∧ signedWilfClassCount 8 = 49 ∧
    signedWilfClassCount 9 = 22 ∧ signedWilfClassCount 10 = 8 ∧ signedWilfClassCount 11 = 3 ∧
    signedWilfClassCount 12 = 1

/-- **Theorem 3, class C2.** `{0̄0̄, 0̄0, 0̄1, 01}` ∼ `{0̄0̄, 0̄1, 00̄, 01}`, and `F(x) = 1 + 2 ∑_{k
≥ 1} xᵏ / ∏_{i=1}^{k} (1 - ix)`; each coefficient `[xⁿ]` is compared with the partial sum
through index `n`, which carries all of `[xⁿ]`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C2) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b0_b00_b01_01 :
    signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩}) =
      coeff n (1 + 2 * ∑ k ∈ Finset.Icc 1 n, X ^ k * ∏ i ∈ Finset.Icc 1 k, (1 - (i : ℚ⟦X⟧) * X)⁻¹)

/-- **Theorem 3, class C3.** `{0̄1̄, 0̄0̄, 0̄1, 01̄}` ∼ `{0̄1̄, 0̄0, 0̄1, 01̄}` ∼ `{0̄0̄, 0̄0, 01̄,
00̄}`, and `F(x) = ∑_{k ≥ 0} (∑_{i=0}^{k} i!) xᵏ`, stated as `|Ī_n(B)| = ∑_{i=0}^{n} i!`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C3) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} n =
      ∑ i ∈ Finset.range (n + 1), i !

/-- **Theorem 3, class C4.** `{0̄1̄, 0̄0̄, 0̄0, 01̄}` ∼ `{0̄1̄, 0̄0̄, 01̄, 00̄}` ∼ `{0̄1̄, 0̄0, 01̄,
00̄}` ∼ `{0̄0, 0̄1, 01̄, 00̄}`, and `F(x) = 1 + 2 ∑_{k ≥ 1} k! xᵏ`, stated as `|Ī_{n+1}(B)| = 2
(n + 1)!` (the constant term `|Ī_0(B)| = 1` holds for every `B`, `signedInvAvoidCount_zero`).

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C4) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_b00_0b1 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩} ∧
    ∀ n, signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, true⟩} (n + 1) = 2 * (n + 1)!

/-- **Theorem 3, class C12.** `{0̄1̄, 0̄0̄, 01̄, 01}` ∼ `{0̄1̄, 0̄1, 01̄, 00}` ∼ `{0̄1̄, 0̄1, 00̄,
00}`, and `F(x) = (1 + x²) / (1 - x)²`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C12) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_0b1_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    ((1 - X) ^ 2) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      1 + X ^ 2

/-- **Theorem 3, class C15.** `{0̄1̄, 0̄0̄, 0̄1, 01}` ∼ `{0̄1̄, 0̄0, 0̄1, 00}` ∼ `{0̄1̄, 0̄0̄, 01̄,
00}` ∼ `{0̄1̄, 0̄0̄, 00̄, 00}` ∼ `{0̄1̄, 0̄1, 01̄, 01}` ∼ `{0̄0̄, 0̄0, 01̄, 00}` ∼ `{0̄0̄, 0̄0,
00̄, 00}`, and `F(x) = 1 / (1 - 2x)`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C15) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    (1 - 2 * X) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      1

/-- **Theorem 3, class C16.** `{0̄1̄, 0̄0, 01̄, 01}` ∼ `{0̄1̄, 0̄1, 00̄, 01}`, and `F(x) = (1 - 3x +
2x² - x³) / ((1 - x)²(1 - 3x + x²))`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C16) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b0b1_b00_0b1_01 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ((1 - X) ^ 2 * (1 - 3 * X + X ^ 2)) * signedInvAvoidGF {⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - 3 * X + 2 * X ^ 2 - X ^ 3

/-- **Theorem 3, class C21.** `{0̄1̄, 0̄1, 01̄, 00̄}` ∼ `{0̄0̄, 0̄1, 01̄, 00̄}`. The printed
generating function `1/(1 - x)² + ∑_{j ≥ 0} j! xʲ` is false (its constant term is `2`, while
`|Ī_0(B)| = 1`) and is omitted.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C21) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_b0b1_b01_0b1_0b0 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩}

/-- **Theorem 3, class C23.** `{1̄0̄, 0̄1̄, 0̄1, 00}` ∼ `{1̄0, 0̄0̄, 01̄, 01}`, and `F(x) = (1 - x +
2x²) / (1 - x)³`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C23) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b01_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ((1 - X) ^ 3) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, false⟩} =
      1 - X + 2 * X ^ 2

/-- **Theorem 3, class C25.** `{1̄0̄, 0̄0̄, 01̄, 01}` ∼ `{1̄0, 0̄1̄, 0̄1, 00}`, and `F(x) = (1 - x +
x²) / ((1 - x)(1 - 2x))`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C25) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b0_0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩} ∧
    ((1 - X) * (1 - 2 * X)) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - X + X ^ 2

/-- **Theorem 3, class C30.** `{1̄0̄, 0̄1̄, 0̄0̄, 00}` ∼ `{1̄0̄, 0̄1̄, 0̄1, 01}` ∼ `{1̄0, 0̄1̄, 0̄1,
01}` ∼ `{1̄0, 0̄0̄, 01̄, 00}` ∼ `{0̄0̄, 0̄1, 00, 10̄}`, and `F(x) = (1 - 2x + 2x²) / ((1 - x)²(1
- 2x))`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C30) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b0b0_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, false⟩,
          ⟨.gt, false, true⟩} ∧
    ((1 - X) ^ 2 * (1 - 2 * X)) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, false, false⟩} =
      1 - 2 * X + 2 * X ^ 2

/-- **Theorem 3, class C32.** `{1̄0̄, 0̄1̄, 0̄0, 01}` ∼ `{1̄0, 0̄1̄, 0̄0, 01}`, and `F(x) = (1 - 4x
+ 5x² - 3x³) / ((1 - x)(1 - 2x)(1 - 3x + x²))`, stated after multiplying by the unit
denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C32) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b00_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    ((1 - X) * (1 - 2 * X) * (1 - 3 * X + X ^ 2)) * signedInvAvoidGF {⟨.gt, true, true⟩,
        ⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, false⟩} =
      1 - 4 * X + 5 * X ^ 2 - 3 * X ^ 3

/-- **Theorem 3, class C38.** `{1̄0̄, 0̄1̄, 01̄, 01}` ∼ `{1̄0, 0̄1̄, 01̄, 01}`, and `F(x) = (1 - x)
/ (1 - 3x + x²)`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C38) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    (1 - 3 * X + X ^ 2) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.lt, false, false⟩} =
      1 - X

/-- **Theorem 3, class C39.** `{1̄0̄, 0̄0̄, 0̄0, 01}` ∼ `{1̄0̄, 0̄1, 01̄, 01}`, and `F(x) = (1 - 3x
+ 2x² + 2x³ - (1 - 3x + 2x²)√(1 - 4x)) / (2x(1 - x)²(1 - 2x))`; `√(1 - 4x)` is the power series
`S` with constant term `1` and `S² = 1 - 4x`, and the identity is stated after multiplying by
`2x(1 - x)²(1 - 2x)`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C39) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b0_b00_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.lt, false, false⟩} ∧
    ∀ S : ℚ⟦X⟧, constantCoeff S = 1 → S ^ 2 = 1 - 4 * X →
      2 * X * (1 - X) ^ 2 * (1 - 2 * X) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, false, false⟩} =
        1 - 3 * X + 2 * X ^ 2 + 2 * X ^ 3 - (1 - 3 * X + 2 * X ^ 2) * S

/-- **Theorem 3, class C41.** `{1̄0̄, 0̄0̄, 01̄, 00}` ∼ `{1̄0, 0̄0̄, 0̄0, 01}`, and `F(x) = 1/(1 -
x) + 1/(1 - x) ∑_{j ≥ 1} xʲ / (1 - (j + 1)x)`; each coefficient `[xⁿ]` is compared with the
partial sum through index `n`, which carries all of `[xⁿ]`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C41) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b0_0b1_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.lt, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩}) =
      coeff n ((1 - X)⁻¹ + (1 - X)⁻¹ * ∑ j ∈ Finset.Icc 1 n, X ^ j * (1 - ((j + 1 : ℕ) : ℚ⟦X⟧) *
            X)⁻¹)

/-- **Theorem 3, class C45.** `{1̄0̄, 0̄0̄, 0̄1, 01}` ∼ `{1̄0̄, 0̄0, 0̄1, 00}`. The printed
generating function `C(x)` is not defined in the paper and is omitted.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C45) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_b01_01 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, false⟩}

/-- **Theorem 3, class C46.** `{1̄0̄, 0̄1̄, 0̄0, 00}` ∼ `{1̄0̄, 0̄1̄, 00̄, 00}` ∼ `{1̄0, 0̄1̄, 00̄,
00}`, and `F(x) = 1/(1 - x) + 1/(1 - x) ∑_{j ≥ 1} xʲ(1 - jx) / ∏_{i=1}^{j+1} (1 - ix)`; each
coefficient `[xⁿ]` is compared with the partial sum through index `n`, which carries all of
`[xⁿ]`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C46) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b00_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.eq, false, false⟩}) =
      coeff n ((1 - X)⁻¹ + (1 - X)⁻¹ * ∑ j ∈ Finset.Icc 1 n, X ^ j * (1 - (j : ℚ⟦X⟧) * X) * ∏ i ∈
            Finset.Icc 1 (j + 1), (1 - (i : ℚ⟦X⟧) * X)⁻¹)

/-- **Theorem 3, class C50.** `{1̄0̄, 0̄1̄, 0̄1, 01̄}` ∼ `{1̄0, 0̄1̄, 0̄1, 01̄}`, and `F(x) = (1 -
x)/(1 - 2x) ∑_{j ≥ 0} j! xʲ`, stated after multiplying by the unit denominator.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C50) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_b01_0b1 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.lt, false, true⟩} ∧
    (1 - 2 * X) * signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.lt, false, true⟩} =
      (1 - X) * PowerSeries.mk fun j => (j ! : ℚ)

/-- **Theorem 3, class C60.** `{1̄0̄, 0̄1̄, 01̄, 00}` ∼ `{1̄0, 0̄1̄, 01̄, 00}`, and `F(x) = ∑_{j ≥
0} xʲ / ∏_{i=1}^{j+1} (1 - ix)`; each coefficient `[xⁿ]` is compared with the partial sum
through index `n`, which carries all of `[xⁿ]`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 3 (C60) (`integers-2026-A74-thm-3`). -/
public theorem_wanted signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, false⟩} ∧
    ∀ n, coeff n (signedInvAvoidGF {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩}) =
      coeff n (∑ j ∈ Finset.range (n + 1), X ^ j * ∏ i ∈ Finset.Icc 1 (j + 1), (1 - (i : ℚ⟦X⟧) *
            X)⁻¹)

/-- **Theorem 4.** `{0̄1̄, 0̄0̄, 0̄1, 00̄}` ∼ `{0̄1̄, 0̄0, 0̄1, 00̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 4 (`integers-2026-A74-thm-4`). -/
public theorem_wanted signedInvSeq_wilf_b0b1_b0b0_b01_0b0 :
    signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, true⟩}

/-- **Theorem 5.** `{1̄0̄, 0̄0̄, 0̄1, 00̄}` ∼ `{1̄0̄, 0̄0, 0̄1, 00̄}`; `{1̄0, 0̄1̄, 0̄0̄, 00̄}` ∼
`{1̄0, 0̄1̄, 0̄0, 00̄}`; `{1̄0̄, 0̄0̄, 0̄1, 10̄}` ∼ `{1̄0̄, 0̄0, 0̄1, 10̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 5 (`integers-2026-A74-thm-5`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b0_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
          ⟨.gt, false, true⟩}

/-- **Theorem 6.** `{1̄0, 0̄0, 01̄, 00}` ∼ `{1̄0, 01̄, 00̄, 00}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 6 (`integers-2026-A74-thm-6`). -/
public theorem_wanted signedInvSeq_wilf_b10_b00_0b1_00 :
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩,
          ⟨.eq, false, false⟩}

/-- **Theorem 7.** `{1̄0̄, 0̄1̄, 0̄0̄, 0̄0}` ∼ `{1̄0̄, 0̄1̄, 0̄0̄, 00̄}` ∼ `{1̄0̄, 0̄1̄, 0̄0, 00̄}`
∼ `{1̄0, 0̄0, 01̄, 00̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 7 (`integers-2026-A74-thm-7`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b0b0_b00 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩}

/-- **Theorem 8.** `{1̄0̄, 0̄1̄, 0̄0̄, 10̄}` ∼ `{1̄0̄, 0̄1̄, 00̄, 10̄}`; `{1̄0̄, 0̄0̄, 0̄0, 10̄}` ∼
`{1̄0̄, 0̄0, 00̄, 10̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 8 (`integers-2026-A74-thm-8`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
          ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩,
          ⟨.gt, false, true⟩}

/-- **Theorem 9.** `{1̄0̄, 1̄0, 0̄0̄, 00̄}` ∼ `{1̄0̄, 1̄0, 0̄0, 00̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 9 (`integers-2026-A74-thm-9`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b0_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩}

/-- **Theorem 12.** `{1̄0̄, 0̄1̄, 0̄0, 0̄1, 00̄}` ∼ `{1̄0̄, 0̄1̄, 0̄0̄, 0̄1, 00̄}`; `{1̄0̄, 1̄0,
0̄1̄, 0̄0, 00̄}` ∼ `{1̄0̄, 1̄0, 0̄1̄, 0̄0̄, 00̄}`; `{1̄0̄, 0̄1̄, 0̄0̄, 0̄0, 10̄}` ∼ `{1̄0̄,
0̄1̄, 0̄0, 00̄, 10̄}`; `{1̄0̄, 1̄0, 0̄1̄, 0̄0, 00}` ∼ `{1̄0̄, 1̄0, 0̄1̄, 00̄, 00}`. The printed
third set of the first chain, `{1̄0̄, 0̄1̄, 0̄1, 00̄, 10̄}`, is omitted: it has `|Ī_2| = 5`
against `4` for the first two sets.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 12 (`integers-2026-A74-thm-12`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b00_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, true, true⟩, ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, false⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, false, true⟩, ⟨.eq, false, false⟩}

/-- **Theorem 13.** `{1̄0̄, 0̄1̄, 0̄0, 0̄1, 10̄}` ∼ `{1̄0̄, 0̄1̄, 0̄0̄, 0̄1, 10̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 13 (`integers-2026-A74-thm-13`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, true, false⟩, ⟨.gt, false, true⟩}

/-- **Theorem 14.** `{1̄0, 0̄1̄, 01̄, 00̄, 10̄}` ∼ `{1̄0̄, 0̄1̄, 01̄, 00̄, 10̄}` ∼ `{1̄0̄, 1̄0,
0̄0̄, 0̄0, 00̄}` ∼ `{1̄0̄, 0̄0̄, 01̄, 00̄, 10̄}` ∼ `{1̄0̄, 0̄1̄, 0̄0̄, 01̄, 10̄}` ∼ `{1̄0, 0̄1̄,
0̄0̄, 01̄, 10̄}` ∼ `{1̄0̄, 1̄0, 0̄0̄, 0̄0, 0̄1}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 14 (`integers-2026-A74-thm-14`). -/
public theorem_wanted signedInvSeq_wilf_b10_b0b1_0b1_0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} ∧
    signedInvAvoidCount {⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.lt, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, true, false⟩}

/-- **Theorem 15.** `{1̄0̄, 0̄0, 0̄1, 00̄, 10̄}` ∼ `{1̄0̄, 0̄0̄, 0̄1, 00̄, 10̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 15 (`integers-2026-A74-thm-15`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b00_b01_0b0_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩,
        ⟨.eq, false, true⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩,
          ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

/-- **Theorem 16.** `{1̄0̄, 1̄0, 0̄1̄, 0̄0, 0̄1, 00̄}` ∼ `{1̄0̄, 1̄0, 0̄1̄, 0̄0̄, 0̄1, 00̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 16 (`integers-2026-A74-thm-16`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩}

/-- **Theorem 17.** For `A` any of `{1̄0̄, 1̄0, 0̄1̄, 0̄0̄, 0̄0, 01̄}`, `{1̄0̄, 1̄0, 0̄1̄, 0̄0̄,
0̄0, 00̄}`, `{1̄0̄, 0̄1̄, 0̄0̄, 0̄0, 0̄1, 10̄}`, `|Ī_n(A)| = 2 · n!` for all `n ≥ 1`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 17 (`integers-2026-A74-thm-17`). -/
public theorem_wanted signedInvAvoidCount_eq_two_mul_factorial :
    ∀ n, 1 ≤ n →
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} n = 2 * n ! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} n = 2 * n ! ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} n = 2 * n !

/-- **Theorem 18.** `{1̄0̄, 1̄0, 0̄1̄, 0̄0̄, 0̄0, 0̄1, 10̄}` ∼ `{1̄0̄, 1̄0, 0̄0̄, 0̄0, 0̄1, 00̄,
10̄}`.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 18 (`integers-2026-A74-thm-18`). -/
public theorem_wanted signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
          ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

end

end MetaMathlibExt
