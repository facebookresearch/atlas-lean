/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Signed inversion sequences avoiding sets of length-2 signed patterns

This module defines signed pattern avoidance and proves the Wilf-equivalences
of Theorems 13 and 16 from Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding
a Set of Length-2 Signed Patterns*, INTEGERS 26 (2026), Article A74.

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

/-- **Length-2 signed pattern.** A length-2 signed pattern is a word $\tau_1\tau_2$ whose
underlying word $|\tau_1||\tau_2|$ is $00$, $01$ or $10$ and each of whose letters may be barred,
for example $\bar10$ or $0\bar1$. It is given by the comparison of $|\tau_1|$ with $|\tau_2|$
(equal for $00$, less for $01$, greater for $10$) together with whether $\tau_1$ is barred and
whether $\tau_2$ is barred.

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

/-- **Number of length-2 signed patterns.** There are exactly twelve length-2 signed patterns.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 5 (`binom 12 k` sets of `k`
patterns). -/
theorem card_signedPattern2 : Fintype.card SignedPattern2 = 12 := by decide

/-- **Containment of a length-2 signed pattern.** Let $e = e_1 \cdots e_n$ be a sequence whose
entries are natural numbers $|e_i|$, each barred or not, and let $\tau_1\tau_2$ be a length-2
signed pattern. Then $e$ contains $\tau_1\tau_2$ if there are positions $i < j$ such that $|e_i|$
is equal to, smaller than or larger than $|e_j|$ exactly as $|\tau_1|$ is equal to, smaller than
or larger than $|\tau_2|$, and $e_i$ and $e_j$ are barred exactly when $\tau_1$ and $\tau_2$ are.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
def SignedInvSeqContains {n : ℕ} (e : Fin n → ℕ × Bool) (p : SignedPattern2) : Prop :=
  ∃ i j : Fin n, i < j ∧ compare (e i).1 (e j).1 = p.ord ∧ (e i).2 = p.bar₁ ∧ (e j).2 = p.bar₂

/-- **Number of signed inversion sequences avoiding a set of patterns.** A signed inversion
sequence of length $n$ is a word $e_1 \cdots e_n$ in which each entry $e_i$ is a natural number
$|e_i| \le i - 1$, either barred or not; that is, $e_i \in \lbrace 0, \bar 0, 1, \bar 1, \dots,
i - 1, \overline{i - 1} \rbrace$. For a finite set $B$ of length-2 signed patterns and $n \ge 0$,
$|\bar I_n(B)|$ is the number of signed inversion sequences of length $n$ that contain no pattern
of $B$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
noncomputable def signedInvAvoidCount (B : Finset SignedPattern2) (n : ℕ) : ℕ :=
  Nat.card {e : Fin n → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧ ∀ p ∈ B, ¬ SignedInvSeqContains e p}

/-- **Signed inversion sequences of length zero.** The empty sequence is the only signed inversion
sequence of length $0$, and it contains no pattern, so for every finite set $B$ of length-2 signed
patterns the number $|\bar I_0(B)|$ of signed inversion sequences of length $0$ avoiding every
pattern of $B$ is $1$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Introduction. -/
theorem signedInvAvoidCount_zero (B : Finset SignedPattern2) : signedInvAvoidCount B 0 = 1 := by
  rw [signedInvAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e e' => Subtype.ext (funext fun i => i.elim0)⟩, ⟨⟨fun i => i.elim0, ?_⟩⟩⟩
  exact ⟨fun i => i.elim0, fun _ _ ⟨i, _⟩ => i.elim0⟩

/-- **Signed inversion sequences of length one.** The signed inversion sequences of length $1$ are
$0$ and $\bar 0$, and neither contains a length-2 signed pattern, so for every finite set $B$ of
length-2 signed patterns the number $|\bar I_1(B)|$ of signed inversion sequences of length $1$
avoiding every pattern of $B$ is $2$.

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

/-- **Generating function of signed inversion sequences avoiding a set of patterns.** For a finite
set $B$ of length-2 signed patterns, $F_B(x) = \sum_{n \ge 0} |\bar I_n(B)| x^n$ is the formal
power series with rational coefficients whose coefficient of $x^n$ is the number $|\bar I_n(B)|$
of signed inversion sequences of length $n$ avoiding every pattern of $B$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 2. -/
noncomputable def signedInvAvoidGF (B : Finset SignedPattern2) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (signedInvAvoidCount B n : ℚ)

/-- **Coefficients of the avoidance generating function.** For a finite set $B$ of length-2
signed patterns and $m \ge 0$, let $|\bar I_m(B)|$ be the number of signed inversion sequences of
length $m$ avoiding every pattern of $B$, and let $F_B(x) = \sum_{m \ge 0} |\bar I_m(B)| x^m$ be
their generating function, a formal power series with rational coefficients. Then for every
$n \ge 0$ the coefficient of $x^n$ in $F_B(x)$ is $|\bar I_n(B)|$, viewed as a rational number.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Section 2. -/
theorem coeff_signedInvAvoidGF (B : Finset SignedPattern2) (n : ℕ) :
    coeff n (signedInvAvoidGF B) = (signedInvAvoidCount B n : ℚ) := by
  simp [signedInvAvoidGF]

/-- **Number of signed Wilf classes.** For $k \ge 0$, $\mathrm{sw}_k$ is the number of
Wilf-equivalence classes among the sets of $k$ length-2 signed patterns, that is, the number of
distinct counting functions $n \mapsto |\bar{I}_n(B)|$ (for $n \ge 0$) over all sets $B$ of exactly
$k$ length-2 signed patterns, where $|\bar{I}_n(B)|$ is the number of signed inversion sequences of
length $n$ avoiding every pattern of $B$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1. -/
noncomputable def signedWilfClassCount (k : ℕ) : ℕ :=
  Set.ncard ((fun B => signedInvAvoidCount B) '' {B : Finset SignedPattern2 | B.card = k})

/-- **The empty pattern set forms one signed Wilf class.** The number $\mathrm{sw}_0$ of
Wilf-equivalence classes among the sets of $0$ length-2 signed patterns is $1$: the empty set is
the only set of no patterns.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 1 (definition of `sw_k`). -/
theorem signedWilfClassCount_zero : signedWilfClassCount 0 = 1 := by
  have : {B : Finset SignedPattern2 | B.card = 0} = {∅} := by
    ext B
    simp
  rw [signedWilfClassCount, this, Set.image_singleton, Set.ncard_singleton]

namespace signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0

variable {n : ℕ}

private abbrev patterns (b : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, b⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩}

/-- An earlier barred entry has the same magnitude as the entry at `i`. -/
private def Seen (e : Fin n → ℕ × Bool) (i : Fin n) : Prop :=
  ∃ j < i, (e j).2 = true ∧ (e j).1 = (e i).1

-- The four common patterns say precisely that every barred entry is a maximum.
-- The fifth prescribes the bar on each later occurrence of its magnitude.
private theorem avoids_iff (e : Fin n → ℕ × Bool) (b : Bool) :
    (∀ p ∈ patterns b, ¬ SignedInvSeqContains e p) ↔
      (∀ i, (e i).2 = true → ∀ j, (e j).1 ≤ (e i).1) ∧
      (∀ i, Seen e i → (e i).2 ≠ b) := by
  let pair (i j : Fin n) : SignedPattern2 := ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩
  have noPair : (∀ p ∈ patterns b, ¬ SignedInvSeqContains e p) ↔
      ∀ i j, i < j → pair i j ∉ patterns b := by
    constructor
    · intro h i j hij hm
      exact h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
    · rintro h ⟨ord, s, t⟩ hm ⟨i, j, hij, ho, hs, ht⟩
      exact h i j hij (by simpa only [pair, ho, hs, ht] using hm)
  have pair_iff (i j : Fin n) : pair i j ∉ patterns b ↔
      ((e i).2 = true → (e j).1 ≤ (e i).1) ∧
      ((e j).2 = true → (e i).1 ≤ (e j).1) ∧
      ((e i).2 = true → (e i).1 = (e j).1 → (e j).2 ≠ b) := by
    cases hi : (e i).2 <;> cases hj : (e j).2 <;>
      simp [pair, patterns, hi, hj, SignedPattern2.mk.injEq, compare_lt_iff_lt,
        compare_gt_iff_gt] <;> grind
  simp_rw [noPair, pair_iff]
  constructor
  · intro h
    constructor
    · intro i hi j
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (h i j hij).1 hi
      · exact le_rfl
      · exact (h j i hji).2.1 hi
    · rintro j ⟨i, hij, hi, heq⟩
      exact (h i j hij).2.2 hi heq
  · rintro ⟨hmax, hseen⟩ i j hij
    exact ⟨fun hi => hmax i hi j, fun hj => hmax j hj i,
      fun hi heq => hseen j ⟨i, hij, hi, heq⟩⟩

/-- Toggle the bar at every occurrence of a magnitude after its first barred occurrence. -/
private noncomputable def toggle (e : Fin n → ℕ × Bool) (i : Fin n) : ℕ × Bool := by
  classical
  exact ((e i).1, if Seen e i then !(e i).2 else (e i).2)

private theorem seen_toggle (e : Fin n → ℕ × Bool) (i : Fin n) :
    Seen (toggle e) i ↔ Seen e i := by
  constructor
  · rintro ⟨j, hji, hj, heq⟩
    by_cases h : Seen e j
    · obtain ⟨k, hkj, hk, hval⟩ := h
      exact ⟨k, hkj.trans hji, hk, hval.trans heq⟩
    · exact ⟨j, hji, by simpa [toggle, h] using hj, heq⟩
  · intro h
    -- The first barred occurrence of this magnitude keeps its bar.
    obtain ⟨j, ⟨hji, hj, heq⟩, hmin⟩ := wellFounded_lt.has_min
      {j : Fin n | j < i ∧ (e j).2 = true ∧ (e j).1 = (e i).1} h
    have hfirst : ¬ Seen e j := by
      rintro ⟨k, hkj, hk, hval⟩
      exact hmin k ⟨hkj.trans hji, hk, hval.trans heq⟩ hkj
    exact ⟨j, hji, by simpa [toggle, hfirst] using hj, heq⟩

private theorem toggle_involutive : Function.Involutive (toggle (n := n)) := by
  classical
  intro e
  funext i
  refine Prod.ext (by rfl) ?_
  change (if Seen (toggle e) i then !(toggle e i).2 else (toggle e i).2) = _
  rw [seen_toggle]
  by_cases h : Seen e i <;> simp [toggle, h]

private theorem toggle_avoids (e : Fin n → ℕ × Bool) (b : Bool)
    (h : ∀ p ∈ patterns b, ¬ SignedInvSeqContains e p) :
    ∀ p ∈ patterns (!b), ¬ SignedInvSeqContains (toggle e) p := by
  obtain ⟨hmax, hbar⟩ := (avoids_iff e b).mp h
  apply (avoids_iff _ _).mpr
  constructor
  · intro i hi j
    by_cases hseen : Seen e i
    · obtain ⟨k, _, hk, heq⟩ := hseen
      exact heq ▸ hmax k hk j
    · exact hmax i (by simpa [toggle, hseen] using hi) j
  · intro i hi
    have hseen := (seen_toggle e i).mp hi
    simpa [toggle, hseen] using hbar i hseen

end signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0

open signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 in
/-- **Mansour–Safadi Theorem 13: a Wilf-equivalence of five-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar0\bar1, \bar00, \bar01, 1\bar0\} \sim
\{\bar1\bar0, \bar0\bar1, \bar0\bar0, \bar01, 1\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 13 (`integers-2026-A74-thm-13`). -/
theorem signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, false⟩,
        ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
          ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} := by
  funext n
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨toggle e.val, e.property.1, toggle_avoids _ false e.property.2⟩
    invFun := fun e => ⟨toggle e.val, e.property.1, toggle_avoids _ true e.property.2⟩
    left_inv := fun e => Subtype.ext (toggle_involutive e.val)
    right_inv := fun e => Subtype.ext (toggle_involutive e.val) }

namespace signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0

open signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 (Seen toggle)

private abbrev patterns (b : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, b⟩,
    ⟨.lt, true, false⟩, ⟨.eq, false, true⟩}

variable {n : ℕ}

-- After a bar the magnitude is constant. At equal magnitudes the earlier sign
-- determines the later sign, according to which equal-letter pattern is forbidden.
private theorem avoids_iff (e : Fin n → ℕ × Bool) (b : Bool) :
    (∀ p ∈ patterns b, ¬ SignedInvSeqContains e p) ↔ ∀ i j, i < j →
      ((e i).2 = true → (e i).1 = (e j).1) ∧
      ((e i).1 = (e j).1 → (e j).2 = ((e i).2 && !b)) := by
  have pair_iff (i j : Fin n) :
      ⟨compare (e i).1 (e j).1, (e i).2, (e j).2⟩ ∉ patterns b ↔
        ((e i).2 = true → (e i).1 = (e j).1) ∧
        ((e i).1 = (e j).1 → (e j).2 = ((e i).2 && !b)) := by
    cases hi : (e i).2 <;> cases hj : (e j).2 <;> cases b <;>
      simp [patterns, SignedPattern2.mk.injEq, compare_gt_iff_gt, compare_lt_iff_lt] <;> omega
  constructor
  · intro h i j hij
    exact (pair_iff i j).mp fun hm => h _ hm ⟨i, j, hij, rfl, rfl, rfl⟩
  · rintro h p hm ⟨i, j, hij, ho, hs, ht⟩
    apply (pair_iff i j).mpr (h i j hij)
    simpa only [ho, hs, ht] using hm

private theorem toggle_avoids (e : Fin n → ℕ × Bool) (b : Bool)
    (h : ∀ p ∈ patterns b, ¬ SignedInvSeqContains e p) :
    ∀ p ∈ patterns (!b), ¬ SignedInvSeqContains (toggle e) p := by
  rw [avoids_iff] at h ⊢
  intro i j hij
  classical
  by_cases heq : (e i).1 = (e j).1
  · -- At equal magnitudes a bar has been seen by j exactly when it has been seen at or before i.
    have hseen : Seen e j ↔ Seen e i ∨ (e i).2 = true := by
      constructor
      · rintro ⟨k, hkj, hk, hval⟩
        rcases lt_trichotomy k i with hki | rfl | hik
        · exact Or.inl ⟨k, hki, hk, hval.trans heq.symm⟩
        · exact Or.inr hk
        · have hsign := (h i k hik).2 (heq.trans hval.symm)
          exact Or.inr (Bool.and_eq_true_iff.mp (hsign.symm.trans hk)).1
      · rintro (⟨k, hki, hk, hval⟩ | hi)
        · exact ⟨k, hki.trans hij, hk, hval.trans heq⟩
        · exact ⟨i, hij, hi, heq⟩
    have earlier : Seen e i → (e i).2 = !b := by
      rintro ⟨k, hki, hk, hval⟩
      simpa [hk] using (h k i hki).2 hval
    have later := (h i j hij).2 heq
    refine ⟨fun _ => heq, fun _ => ?_⟩
    simp only [toggle, hseen, later]
    by_cases hs : Seen e i <;> cases hi : (e i).2 <;> cases b <;> simp_all
  · -- A barred entry at or before i would force the magnitudes at i and j to agree.
    have hi : (e i).2 = false := Bool.eq_false_iff.mpr fun hb => heq ((h i j hij).1 hb)
    have hs : ¬ Seen e i := by
      rintro ⟨k, hki, hk, hval⟩
      exact heq (hval.symm.trans ((h k j (hki.trans hij)).1 hk))
    simp [toggle, hi, hs, heq]

end signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0

open signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 (toggle toggle_involutive) in
open signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0 in
/-- **Mansour–Safadi Theorem 16: a Wilf-equivalence of six-pattern sets.** Length-2 signed
patterns are written as in the paper, a bar marking a barred letter, and $B \sim C$ means that
for every $n \ge 0$ the number $|\bar I_n(B)|$ of signed inversion sequences of length $n$
avoiding every pattern of $B$ equals $|\bar I_n(C)|$. Then
$\{\bar1\bar0, \bar10, \bar0\bar1, \bar00, \bar01, 0\bar0\} \sim
\{\bar1\bar0, \bar10, \bar0\bar1, \bar0\bar0, \bar01, 0\bar0\}$.

Source: Toufik Mansour and Amir Safadi, *Signed Inversion Sequences Avoiding a Set of Length-2
Signed Patterns*, INTEGERS 26 (2026), Article A74, Theorem 16 (`integers-2026-A74-thm-16`). -/
theorem signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0 :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} =
      signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
          ⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩} := by
  funext n
  apply Nat.card_congr
  exact {
    toFun := fun e => ⟨toggle e.val, e.property.1, toggle_avoids _ false e.property.2⟩
    invFun := fun e => ⟨toggle e.val, e.property.1, toggle_avoids _ true e.property.2⟩
    left_inv := fun e => Subtype.ext (toggle_involutive e.val)
    right_inv := fun e => Subtype.ext (toggle_involutive e.val) }

end

end MetaMathlibExt
