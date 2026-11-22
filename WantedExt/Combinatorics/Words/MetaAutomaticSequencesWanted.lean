/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
public import MathlibExt.Combinatorics.InfiniteWord.WordFactorComplexity
public import MathlibExt.Combinatorics.Words.CobhamUniformMorphism
public import MathlibExt.Combinatorics.Words.RegularSequence

namespace MetaMathlibExt

open Filter Asymptotics

@[expose] public section

/-- **Thue–Morse quarto sequence.** The Thue–Morse quarto sequence
$\mathcal{Q} : \mathbb{N} \to \{0, 1\}$ (OEIS A298952, with $\mathcal{Q}(0) = 0$) is given by
$\mathcal{Q}(0) = 0$, $\mathcal{Q}(1) = 1$ and, for every $m \ge 2$, writing $m = 4n + r$ with
$n \ge 0$ and $0 \le r \le 3$: $\mathcal{Q}(m) = \mathcal{Q}(n)$ if $r = 0$,
$\mathcal{Q}(m) = 1 - \mathcal{Q}(n)$ if $r = 1$, $\mathcal{Q}(m) = \mathcal{Q}(2n)$ if $r = 2$,
and $\mathcal{Q}(m) = 1 - \mathcal{Q}(2n)$ if $r = 3$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2 (definition of `𝒬`). -/
public def thueMorseQuarto : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => thueMorseQuarto ((n + 2) / 4)
    | 1 => !thueMorseQuarto ((n + 2) / 4)
    | 2 => thueMorseQuarto (2 * ((n + 2) / 4))
    | _ => !thueMorseQuarto (2 * ((n + 2) / 4))
termination_by n => n
decreasing_by all_goals omega

/-- **The meta-automatic sequence $\mathcal{M}_1$.** The sequence
$\mathcal{M}_1 : \mathbb{N} \to \{0, 1\}$ (OEIS A392736) is defined by $\mathcal{M}_1(0) = 0$,
$\mathcal{M}_1(1) = 1$, the recurrences $\mathcal{M}_1(4n) = \mathcal{M}_1(n)$ and
$\mathcal{M}_1(4n+1) = 1 - \mathcal{M}_1(n)$ for every $n \ge 1$, and the recurrences
$\mathcal{M}_1(4n+2) = \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$ and
$\mathcal{M}_1(4n+3) = 1 - \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$ for every $n \ge 0$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3 (definition of `ℳ₁`). -/
public def metaAutomaticOne : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => metaAutomaticOne ((n + 2) / 4)
    | 1 => !metaAutomaticOne ((n + 2) / 4)
    | 2 => if metaAutomaticOne ((n + 2) / 4) then metaAutomaticOne (2 * ((n + 2) / 4))
        else metaAutomaticOne (2 * ((n + 2) / 4) + 1)
    | _ => !(if metaAutomaticOne ((n + 2) / 4) then metaAutomaticOne (2 * ((n + 2) / 4))
        else metaAutomaticOne (2 * ((n + 2) / 4) + 1))
termination_by n => n
decreasing_by all_goals omega

/-- **The meta-automatic sequence $\mathcal{M}_2$.** The meta-automatic sequence
$\mathcal{M}_2 : \mathbb{N} \to \{0, 1\}$ (OEIS A391614) is defined by $\mathcal{M}_2(0) = 0$,
$\mathcal{M}_2(1) = 1$, $\mathcal{M}_2(4n) = \mathcal{M}_2(2n + \mathcal{M}_2(n))$ and
$\mathcal{M}_2(4n+1) = 1 - \mathcal{M}_2(4n)$ for $n \ge 1$, and
$\mathcal{M}_2(4n+2) = \mathcal{M}_2(2n + 1 - \mathcal{M}_2(n))$ and
$\mathcal{M}_2(4n+3) = 1 - \mathcal{M}_2(4n+2)$ for $n \ge 0$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4 (definition of `ℳ₂`). -/
public def metaAutomaticTwo : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4) + 1)
        else metaAutomaticTwo (2 * ((n + 2) / 4))
    | 1 => !(if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4) + 1)
        else metaAutomaticTwo (2 * ((n + 2) / 4)))
    | 2 => if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4))
        else metaAutomaticTwo (2 * ((n + 2) / 4) + 1)
    | _ => !(if metaAutomaticTwo ((n + 2) / 4) then metaAutomaticTwo (2 * ((n + 2) / 4))
        else metaAutomaticTwo (2 * ((n + 2) / 4) + 1))
termination_by n => n
decreasing_by all_goals omega

/-- **First sixteen terms of the Thue–Morse quarto sequence.** The values
$\mathcal{Q}(0), \mathcal{Q}(1), \ldots, \mathcal{Q}(15)$ of the Thue–Morse quarto sequence
$\mathcal{Q}$ are $0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1$, in this order.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2. -/
public theorem thueMorseQuarto_small : (List.range 16).map thueMorseQuarto =
    [false, true, false, true, true, false, false, true, false, true, true, false, true,
      false, false, true] := by
  simp [List.range_succ, thueMorseQuarto]

/-- **First sixteen terms of $\mathcal{M}_1$.** Writing the values of the meta-automatic sequence
$\mathcal{M}_1$ as $0$ and $1$, the terms $\mathcal{M}_1(0), \dots, \mathcal{M}_1(15)$ are
$0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3. -/
public theorem metaAutomaticOne_small : (List.range 16).map metaAutomaticOne =
    [false, true, true, false, true, false, true, false, true, false, true, false, false,
      true, false, true] := by
  simp [List.range_succ, metaAutomaticOne]

/-- **First sixteen terms of $\mathcal{M}_2$.** The first sixteen terms
$\mathcal{M}_2(0), \mathcal{M}_2(1), \ldots, \mathcal{M}_2(15)$ of the meta-automatic sequence
$\mathcal{M}_2$ are $0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4. -/
public theorem metaAutomaticTwo_small : (List.range 16).map metaAutomaticTwo =
    [false, true, true, false, false, true, true, false, true, false, false, true, true,
      false, false, true] := by
  simp [List.range_succ, metaAutomaticTwo]

/-- **Recurrences of the Thue–Morse quarto sequence.** The Thue–Morse quarto sequence
$\mathcal{Q}$ satisfies $\mathcal{Q}(4n) = \mathcal{Q}(n)$ and
$\mathcal{Q}(4n+1) = 1 - \mathcal{Q}(n)$ for every $n \ge 1$, and
$\mathcal{Q}(4n+2) = \mathcal{Q}(2n)$ and $\mathcal{Q}(4n+3) = 1 - \mathcal{Q}(2n)$ for every
$n \ge 0$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2. -/
public theorem thueMorseQuarto_rec (n : ℕ) :
    (1 ≤ n → thueMorseQuarto (4 * n) = thueMorseQuarto n) ∧
      (1 ≤ n → thueMorseQuarto (4 * n + 1) = !thueMorseQuarto n) ∧
      thueMorseQuarto (4 * n + 2) = thueMorseQuarto (2 * n) ∧
      thueMorseQuarto (4 * n + 3) = !thueMorseQuarto (2 * n) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, thueMorseQuarto]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n + 1 = k + 2 := ⟨4 * n - 1, by omega⟩
    rw [hk, thueMorseQuarto]
    simp only [show (k + 2) % 4 = 1 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, thueMorseQuarto]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, thueMorseQuarto]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega]

/-- **Recurrences of the meta-automatic sequence $\mathcal{M}_1$.** Reading the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, for every $n \ge 1$ we have
$\mathcal{M}_1(4n) = \mathcal{M}_1(n)$ and $\mathcal{M}_1(4n+1) = 1 - \mathcal{M}_1(n)$, and for
every $n \in \mathbb{N}$ we have $\mathcal{M}_1(4n+2) = \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$
and $\mathcal{M}_1(4n+3) = 1 - \mathcal{M}_1(2n + 1 - \mathcal{M}_1(n))$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 3, equations (6) and (7). -/
public theorem metaAutomaticOne_rec (n : ℕ) :
    (1 ≤ n → metaAutomaticOne (4 * n) = metaAutomaticOne n) ∧
      (1 ≤ n → metaAutomaticOne (4 * n + 1) = !metaAutomaticOne n) ∧
      metaAutomaticOne (4 * n + 2) =
        metaAutomaticOne (2 * n + 1 - (metaAutomaticOne n).toNat) ∧
      metaAutomaticOne (4 * n + 3) =
        !metaAutomaticOne (2 * n + 1 - (metaAutomaticOne n).toNat) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, metaAutomaticOne]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n + 1 = k + 2 := ⟨4 * n - 1, by omega⟩
    rw [hk, metaAutomaticOne]
    simp only [show (k + 2) % 4 = 1 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, metaAutomaticOne]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
    cases metaAutomaticOne n <;> simp
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, metaAutomaticOne]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega]
    cases metaAutomaticOne n <;> simp

/-- **Recurrences of $\mathcal{M}_2$.** The meta-automatic sequence $\mathcal{M}_2$, read as
taking values in $\{0, 1\}$, satisfies $\mathcal{M}_2(4n) = \mathcal{M}_2(2n + \mathcal{M}_2(n))$
and $\mathcal{M}_2(4n+1) = 1 - \mathcal{M}_2(4n)$ for every $n \ge 1$, and
$\mathcal{M}_2(4n+2) = \mathcal{M}_2(2n + 1 - \mathcal{M}_2(n))$ and
$\mathcal{M}_2(4n+3) = 1 - \mathcal{M}_2(4n+2)$ for every $n \ge 0$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4, equations (9) and (10). -/
public theorem metaAutomaticTwo_rec (n : ℕ) :
    (1 ≤ n → metaAutomaticTwo (4 * n) =
        metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) ∧
      (1 ≤ n → metaAutomaticTwo (4 * n + 1) = !metaAutomaticTwo (4 * n)) ∧
      metaAutomaticTwo (4 * n + 2) =
        metaAutomaticTwo (2 * n + 1 - (metaAutomaticTwo n).toNat) ∧
      metaAutomaticTwo (4 * n + 3) = !metaAutomaticTwo (4 * n + 2) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, metaAutomaticTwo]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
    cases metaAutomaticTwo n <;> simp
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, show k + 2 + 1 = (k + 1) + 2 by omega, metaAutomaticTwo, metaAutomaticTwo]
    simp only [show (k + 1 + 2) % 4 = 1 by omega, show (k + 1 + 2) / 4 = n by omega,
      show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, metaAutomaticTwo]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
    cases metaAutomaticTwo n <;> simp
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, metaAutomaticTwo, metaAutomaticTwo]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega,
      show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]

/-- **Right-special factors.** Let $a$ be an infinite binary word and $n$ a natural number. The
right-special factors of $a$ of length $n$ are the binary words $u$ of length $n$ such that both
$u0$ and $u1$ are factors of $a$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 5 (definition of `RS_a(n)`). -/
public def rightSpecialFactors (a : ℕ → Bool) (n : ℕ) : Set (Fin n → Bool) :=
  {u | ∀ b : Bool, (Fin.snoc (α := fun _ => Bool) u b) ∈ InfiniteWord.factorSet a (n + 1)}

/-- **The all-zero word has no right-special factors.** For every natural number $n$, the
infinite binary word $000\cdots$ has no right-special factors of length $n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 5. -/
public theorem rightSpecialFactors_const_false (n : ℕ) :
    rightSpecialFactors (fun _ => false) n = ∅ := by
  ext u
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hu
  obtain ⟨i, hi⟩ := hu true
  have := congrFun hi (Fin.last n)
  simp at this

/-- **Allouche–Shallit criterion for automatic sequences.** Let $A$ be a finite set,
$U : \mathbb{N} \to A$ a sequence and $q \ge 2$ a natural number. Let $t, a, b, n_0$ be natural
numbers, let $P$ be the set of pairs $(i, j')$ of natural numbers with $i \le t$, $j' < q^i$ and
$(i, j') \ne (0, 0)$, and for each natural number $j$ let $f_j$ map families of elements of $A$
indexed by the disjoint union of $\{0, 1, \dots, a + b\}$ and $P$ to $A$. Suppose that for all
$n \ge n_0$ and $j < q^{t+1}$, $U(q^{t+1} n + j)$ is the value of $f_j$ at the family sending
$k \in \{0, \dots, a + b\}$ to $U(n + k - a)$ and $(i, j') \in P$ to $U(q^i n + j')$, where
$n + k - a$ is read as $0$ when it is negative. Then $U$ is $q$-automatic.

The arguments $U(n - a), \dots, U(n + b)$ are truncated only when $n < a$, which is harmless
since only large $n$ matter; the paper notes that the order of the arguments plays no role.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 2, quoting Allouche and Shallit
(2012), Theorem 2.2 (`jis-2026-26.4.1-thm-2`). -/
public theorem_wanted isKAutomaticSequence_of_digit_recurrence {A : Type} [Fintype A]
    (U : ℕ → A) (q : ℕ) (hq : 2 ≤ q) (t a b n₀ : ℕ)
    (f : ℕ → ((Fin (a + b + 1) ⊕
      {p : ℕ × ℕ // p.1 ≤ t ∧ p.2 < q ^ p.1 ∧ p ≠ (0, 0)}) → A) → A)
    (hf : ∀ n, n₀ ≤ n → ∀ j, j < q ^ (t + 1) →
      U (q ^ (t + 1) * n + j) =
        f j (Sum.elim (fun i => U (n + i - a)) (fun p => U (q ^ p.1.1 * n + p.1.2)))) :
    IsKAutomaticSequence q U

/-- **Nested indices in balanced binary sequences.** Let $a : \mathbb{N} \to \{0, 1\}$ satisfy
$a(2n) + a(2n+1) = 1$ for every $n \in \mathbb{N}$, and write $\oplus$ for addition modulo $2$.
Then for every $n \in \mathbb{N}$, $a(2n + a(n)) = a(2n) \oplus a(n)$ and
$a(2n + 1 - a(n)) = a(2n+1) \oplus a(n)$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 5 (`jis-2026-26.4.1-lem-5`). -/
public theorem_wanted balanced_nested_xor (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1) (n : ℕ) :
    a (2 * n + (a n).toNat) = xor (a (2 * n)) (a n) ∧
      a (2 * n + 1 - (a n).toNat) = xor (a (2 * n + 1)) (a n)

/-- **Balanced sequences with a nested doubling recurrence are eventually alternating.** Let
$a : \mathbb{N} \to \{0, 1\}$ satisfy $a(2n) + a(2n+1) = 1$ for every $n \in \mathbb{N}$.
(a) If $a(2n) = a(n + a(n))$ for every $n$, then $a(0) = 0$, and $a(2n) = 0$ and
$a(2n+1) = 1$ for every $n \ge 2$. (b) If $a(2n) = a(n + 1 - a(n))$ for every $n$, then
$a(0) = 1$, and $a(2n) = 1$ and $a(2n+1) = 0$ for every $n \ge 2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 6 (`jis-2026-26.4.1-lem-6`). -/
public theorem_wanted balanced_dyadic_nested_eventually_periodic (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1) :
    ((∀ n, a (2 * n) = a (n + (a n).toNat)) →
        a 0 = false ∧ ∀ n, 2 ≤ n → a (2 * n) = false ∧ a (2 * n + 1) = true) ∧
      ((∀ n, a (2 * n) = a (n + 1 - (a n).toNat)) →
        a 0 = true ∧ ∀ n, 2 ≤ n → a (2 * n) = true ∧ a (2 * n + 1) = false)

/-- **Thue–Morse quarto sequence from the Thue–Morse sequence.** Let $\mathcal{Q}$ be the
Thue–Morse quarto sequence and $t$ the Thue–Morse sequence, and let $d(0) = 0$ and
$d(n) = \lfloor \log_2 n \rfloor \bmod 2$ for $n \ge 1$. Then for every $n \ge 0$,
$\mathcal{Q}(n) = t(n) \oplus d(n)$, where $\oplus$ is addition modulo $2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 8 (`jis-2026-26.4.1-prop-8`). -/
public theorem_wanted thueMorseQuarto_eq_xor (n : ℕ) :
    thueMorseQuarto n = xor (thueMorse n) (decide (Nat.log 2 n % 2 = 1))

/-- **The meta-automatic sequence $\mathcal{M}_1$ is balanced.** Reading the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, we have
$\mathcal{M}_1(2n) + \mathcal{M}_1(2n+1) = 1$ for every $n \in \mathbb{N}$.

The paper's lemma also asserts that $\mathcal{M}_1$ is well defined; here that is part of the
definition of $\mathcal{M}_1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 10 (`jis-2026-26.4.1-lem-10`). -/
public theorem_wanted metaAutomaticOne_balanced (n : ℕ) :
    (metaAutomaticOne (2 * n)).toNat + (metaAutomaticOne (2 * n + 1)).toNat = 1

/-- **Joint recurrence for $\mathcal{M}_1$ and its nested companion.** Read the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, write $\oplus$ for addition modulo $2$,
and let $b(m) = \mathcal{M}_1(2m + 1 - \mathcal{M}_1(m))$ for every $m \in \mathbb{N}$. Then for
every $n \ge 1$, with $x = \mathcal{M}_1(n)$ and $y = b(n)$, the pairs
$s(k) = (\mathcal{M}_1(k), b(k))$ satisfy $s(4n) = (x, y)$, $s(4n+1) = (1 \oplus x, x \oplus y)$,
$s(4n+2) = (y, 1 \oplus x)$ and $s(4n+3) = (1 \oplus y, 1 \oplus x \oplus y)$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 12 (`jis-2026-26.4.1-lem-12`). -/
public theorem_wanted metaAutomaticOne_pair_closure (b : ℕ → Bool)
    (hb : ∀ m, b m = metaAutomaticOne (2 * m + 1 - (metaAutomaticOne m).toNat))
    (n : ℕ) (hn : 1 ≤ n) :
    (metaAutomaticOne (4 * n), b (4 * n)) = (metaAutomaticOne n, b n) ∧
      (metaAutomaticOne (4 * n + 1), b (4 * n + 1)) =
        (!metaAutomaticOne n, xor (metaAutomaticOne n) (b n)) ∧
      (metaAutomaticOne (4 * n + 2), b (4 * n + 2)) = (b n, !metaAutomaticOne n) ∧
      (metaAutomaticOne (4 * n + 3), b (4 * n + 3)) =
        (!b n, !xor (metaAutomaticOne n) (b n))

/-- **An automaton for the meta-automatic sequence $\mathcal{M}_1$.** The meta-automatic sequence
$\mathcal{M}_1$ is $4$-automatic. Moreover, let $\delta$ be the transition map on the states
$\{0, 1, 2, 3\}$ and the digits $\{0, 1, 2, 3\}$ given by $\delta(0, \cdot) = 0112$,
$\delta(1, \cdot) = 1230$, $\delta(2, \cdot) = 2301$ and $\delta(3, \cdot) = 3023$, where the
symbol at position $d$ (counted from $0$) of the word listed for $q$ is $\delta(q, d)$. For every
$n \in \mathbb{N}$, let $q_n$ be the state reached by starting in state $0$ and reading the
base-$4$ digits of $n$ with $\delta$, most significant digit first (no digits when $n = 0$).
Then, reading the values of $\mathcal{M}_1$ as $0$ and $1$, $\mathcal{M}_1(n) = q_n \bmod 2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 13 (`jis-2026-26.4.1-thm-13`). -/
public theorem_wanted metaAutomaticOne_dfao :
    IsKAutomaticSequence 4 metaAutomaticOne ∧
      ∀ n, metaAutomaticOne n = decide (((Nat.digits 4 n).reverse.foldl
        (fun q d => ([[0, 1, 1, 2], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 2, 3]].getD q []).getD d 0)
        0) % 2 = 1)

/-- **$\mathcal{M}_1$ as a coding of a uniform morphism fixed point.** Let $\sigma$ be the
$4$-uniform morphism on $\{0, 1, 2, 3\}$ with $\sigma(0) = 0112$, $\sigma(1) = 1230$,
$\sigma(2) = 2301$ and $\sigma(3) = 3023$, and write $\sigma(c)_r$ for the letter of $\sigma(c)$
at position $r$, counted from $0$. There is a sequence $w : \mathbb{N} \to \mathbb{N}$ with
$w(0) = 0$ and $w(4n + r) = \sigma(w(n))_r$ for all $n \in \mathbb{N}$ and $r < 4$, such that,
reading the values of the meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$,
$\mathcal{M}_1(n) = w(n) \bmod 2$ for every $n \in \mathbb{N}$. In other words, $\mathcal{M}_1$
is the image of the fixed point of $\sigma$ starting with $0$ under the coding $0, 2 \mapsto 0$,
$1, 3 \mapsto 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Corollary 16 (`jis-2026-26.4.1-cor-16`). -/
public theorem_wanted metaAutomaticOne_morphism_coding :
    ∃ w : ℕ → ℕ, w 0 = 0 ∧
      (∀ n r, r < 4 → w (4 * n + r) =
        ([[0, 1, 1, 2], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 2, 3]].getD (w n) []).getD r 0) ∧
      ∀ n, metaAutomaticOne n = decide (w n % 2 = 1)

/-- **$\mathcal{M}_2$ is balanced.** For every natural number $n$, the meta-automatic sequence
$\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(2n) + \mathcal{M}_2(2n+1) = 1$.

The well-definedness of $\mathcal{M}_2$, also part of the source theorem, holds because its
defining recursion terminates.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 18 (`jis-2026-26.4.1-thm-18`). -/
public theorem_wanted metaAutomaticTwo_balanced (n : ℕ) :
    (metaAutomaticTwo (2 * n)).toNat + (metaAutomaticTwo (2 * n + 1)).toNat = 1

/-- **Recovering the even and odd terms of $\mathcal{M}_2$.** For every natural number $n$, let
$x = \mathcal{M}_2(n)$ and $y = \mathcal{M}_2(2n + \mathcal{M}_2(n))$, where $\mathcal{M}_2$ is the
meta-automatic sequence with values in $\{0, 1\}$. Then $\mathcal{M}_2(2n) = x \oplus y$ and
$\mathcal{M}_2(2n+1) = x \oplus y \oplus 1$, where $\oplus$ is addition modulo $2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 19 (`jis-2026-26.4.1-lem-19`). -/
public theorem_wanted metaAutomaticTwo_recover (n : ℕ) :
    metaAutomaticTwo (2 * n) = xor (metaAutomaticTwo n)
        (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) ∧
      metaAutomaticTwo (2 * n + 1) = !xor (metaAutomaticTwo n)
        (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat))

/-- **Pair recurrence and $4$-automaticity of $\mathcal{M}_2$.** Read the meta-automatic
sequence $\mathcal{M}_2$ as taking values in $\{0, 1\}$, write $\oplus$ for addition modulo $2$,
and let $s(n) = (\mathcal{M}_2(n), \mathcal{M}_2(2n + \mathcal{M}_2(n)))$. For every $n \ge 0$,
writing $s(n) = (x, y)$, we have $s(4n) = (y, x \oplus y)$, $s(4n+1) = (y \oplus 1, x \oplus y)$,
$s(4n+2) = (y \oplus 1, x \oplus y \oplus 1)$ and $s(4n+3) = (y, x \oplus y \oplus 1)$.
Moreover, $\mathcal{M}_2$ is $4$-automatic, and it is computed by a four-state automaton: there
are maps $\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ and
$\tau : \{0, 1, 2, 3\} \to \{0, 1\}$ such that for every $n$, $\mathcal{M}_2(n) = \tau(q)$, where
$q$ is the state reached from the state $0$ by reading the base-$4$ digits of $n$ with $\delta$,
most significant digit first (for $n = 0$ no digit is read, so $q = 0$).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 20 (`jis-2026-26.4.1-thm-20`). -/
public theorem_wanted metaAutomaticTwo_affine (s : ℕ → Bool × Bool)
    (hs : ∀ m, s m = (metaAutomaticTwo m,
      metaAutomaticTwo (2 * m + (metaAutomaticTwo m).toNat))) :
    (∀ n, s (4 * n) = ((s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 1) = (!(s n).2, xor (s n).1 (s n).2) ∧
      s (4 * n + 2) = (!(s n).2, !xor (s n).1 (s n).2) ∧
      s (4 * n + 3) = ((s n).2, !xor (s n).1 (s n).2)) ∧
    IsKAutomaticSequence 4 metaAutomaticTwo ∧
    ∃ δ : Fin 4 → Fin 4 → Fin 4, ∃ τ : Fin 4 → Bool, ∀ n,
      metaAutomaticTwo n = τ ((Nat.digits 4 n).reverse.foldl (fun q d => δ q (Fin.ofNat 4 d)) 0)

/-- **A four-state automaton computing $\mathcal{M}_2$.** Let
$\delta : \{0, 1, 2, 3\} \times \{0, 1, 2, 3\} \to \{0, 1, 2, 3\}$ be the map for which the word
$\delta(q, 0)\,\delta(q, 1)\,\delta(q, 2)\,\delta(q, 3)$ is $0132$ for $q = 0$, $2310$ for $q = 1$,
$3201$ for $q = 2$ and $1023$ for $q = 3$. For every natural number $n$, the meta-automatic
sequence $\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(n) = q \bmod 2$, where $q$ is the state reached from the state $0$ by reading the
base-$4$ digits of $n$ with $\delta$, most significant digit first (for $n = 0$ no digit is read,
so $q = 0$).

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 22 (`jis-2026-26.4.1-thm-22`). -/
public theorem_wanted metaAutomaticTwo_dfao (n : ℕ) :
    metaAutomaticTwo n = decide (((Nat.digits 4 n).reverse.foldl
      (fun q d => ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD q []).getD d 0)
      0) % 2 = 1)

/-- **$\mathcal{M}_2$ as a coding of a uniform morphic word.** Let $\sigma$ be the $4$-uniform
morphism on $\{0, 1, 2, 3\}$ with $\sigma(0) = 0132$, $\sigma(1) = 2310$, $\sigma(2) = 3201$ and
$\sigma(3) = 1023$. There is a sequence $w$ with values in $\{0, 1, 2, 3\}$ such that $w(0) = 0$,
$w(4n + r)$ is the letter of $\sigma(w(n))$ in position $r$ (counting from $0$) for all $n \ge 0$
and $0 \le r < 4$, and, for every $n$, the meta-automatic sequence $\mathcal{M}_2$ satisfies
$\mathcal{M}_2(n) = 1$ if $w(n)$ is odd and $\mathcal{M}_2(n) = 0$ if $w(n)$ is even. Thus
$w$ is the fixed point of $\sigma$ starting with $0$, and $\mathcal{M}_2$ is its image under the
coding $0, 2 \mapsto 0$ and $1, 3 \mapsto 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Corollary 23 (`jis-2026-26.4.1-cor-23`). -/
public theorem_wanted metaAutomaticTwo_morphism_coding :
    ∃ w : ℕ → ℕ, w 0 = 0 ∧
      (∀ n r, r < 4 → w (4 * n + r) =
        ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD (w n) []).getD r 0) ∧
      ∀ n, metaAutomaticTwo n = decide (w n % 2 = 1)

/-- **Digit formula for $\mathcal{M}_2$.** For a natural number $n$ and $k \ge 0$, let
$d_k = \lfloor n / 4^k \rfloor \bmod 4$ be the $k$-th base-$4$ digit of $n$, and write
$d_k = 2 j_k + i_k$ with $i_k, j_k \in \{0, 1\}$. Let $c_k = i_k + j_k$ if $k \equiv 0 \pmod 3$,
$c_k = j_k$ if $k \equiv 1 \pmod 3$, and $c_k = i_k$ if $k \equiv 2 \pmod 3$. Then the
meta-automatic sequence $\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(n) = (c_0 + c_1 + \cdots + c_n) \bmod 2$.

The digits $d_k$ with $k > n$ vanish, so the sum runs over all base-$4$ digits of $n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 25 (`jis-2026-26.4.1-thm-25`). -/
public theorem_wanted metaAutomaticTwo_digit_formula (n : ℕ) :
    metaAutomaticTwo n = decide ((∑ k ∈ Finset.range (n + 1),
      (if k % 3 = 0 then n / 4 ^ k % 4 % 2 + n / 4 ^ k % 4 / 2
        else if k % 3 = 1 then n / 4 ^ k % 4 / 2 else n / 4 ^ k % 4 % 2)) % 2 = 1)

/-- **$\mathcal{M}_2$ is the Thue–Morse sequence along a binary digit mask.** For a natural
number $m$ with binary digits $b_i = \lfloor m / 2^i \rfloor \bmod 2$, let $q(m)$ be the sum of
$b_i 2^i$ over the $i \le m$ with $i \not\equiv 2 \pmod 3$, that is, the number obtained from $m$
by setting its binary digits in the positions $i \equiv 2 \pmod 3$ to zero. Then for every natural
number $n$, the meta-automatic sequence $\mathcal{M}_2$ and the Thue–Morse sequence $t$ satisfy
$\mathcal{M}_2(n) = t(q(n))$. Moreover, writing the base-$4$ digits of $n$ as
$d_k = \lfloor n / 4^k \rfloor \bmod 4 = 2 j_k + i_k$ with $i_k, j_k \in \{0, 1\}$, we have
$q(n) = \sum_{k=0}^{n} d'_k 4^k$, where $d'_k = d_k$ if $k \equiv 0 \pmod 3$, $d'_k = 2 j_k$ if
$k \equiv 1 \pmod 3$, and $d'_k = i_k$ if $k \equiv 2 \pmod 3$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 26 (`jis-2026-26.4.1-thm-26`). -/
public theorem_wanted metaAutomaticTwo_eq_thueMorse_mask (q : ℕ → ℕ)
    (hq : ∀ m, q m = ∑ i ∈ (Finset.range (m + 1)).filter (fun i => i % 3 ≠ 2),
      m / 2 ^ i % 2 * 2 ^ i) (n : ℕ) :
    metaAutomaticTwo n = thueMorse (q n) ∧
      q n = ∑ k ∈ Finset.range (n + 1),
        (if k % 3 = 0 then n / 4 ^ k % 4
          else if k % 3 = 1 then 2 * (n / 4 ^ k % 4 / 2) else n / 4 ^ k % 4 % 2) * 4 ^ k

/-- **First difference of the factor complexity of a binary word.** Let $a$ be an infinite word
over $\{0, 1\}$, let $p_a$ be its factor complexity, and let $\mathrm{RS}_a(n)$ be the set of
right-special factors of $a$ of length $n$. Then for every $n \ge 1$,
$p_a(n+1) = p_a(n) + \#\mathrm{RS}_a(n)$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 27 (`jis-2026-26.4.1-lem-27`). -/
public theorem_wanted wordFactorComplexity_succ_eq_add_rightSpecial (a : ℕ → Bool) (n : ℕ)
    (hn : 1 ≤ n) :
    wordFactorComplexity a (n + 1) = wordFactorComplexity a n + (rightSpecialFactors a n).ncard

/-- **Right-special factor counts of automatic sequences are regular.** Let $k$ be a natural
number and $a$ an infinite binary word that is $k$-automatic, and for each $n$ let
$\mathrm{RS}_a(n)$ be the set of right-special factors of $a$ of length $n$. Then the integer
sequence $n \mapsto \#\mathrm{RS}_a(n)$ is $k$-regular. Moreover, for every natural number $C$
with $\#\mathrm{RS}_a(n) \le C$ for all $n$, the sequence $n \mapsto \#\mathrm{RS}_a(n)$, taken
with values in $\{0, 1, \ldots, C\}$, is $k$-automatic.

The source also states that this sequence is effectively computable from any automaton for
$a$; that algorithmic claim is not part of this statement.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 28 (`jis-2026-26.4.1-lem-28`). -/
public theorem_wanted rightSpecial_count_regular (k : ℕ) (a : ℕ → Bool)
    (ha : IsKAutomaticSequence k a) :
    IsKRegularSequence k (fun n => ((rightSpecialFactors a n).ncard : ℤ)) ∧
      ∀ C : ℕ, (∀ n, (rightSpecialFactors a n).ncard ≤ C) →
        IsKAutomaticSequence k (fun n => Fin.ofNat (C + 1) (rightSpecialFactors a n).ncard)

/-- **Factors of the Thue–Morse word are closed under complement.** For every natural number
$n$, if a binary word $v$ of length $n$ is a factor of the Thue–Morse sequence, then so is the
word obtained from $v$ by exchanging $0$ and $1$ in every position.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 29 (`jis-2026-26.4.1-lem-29`). -/
public theorem_wanted thueMorse_factor_complement (n : ℕ) (v : Fin n → Bool)
    (hv : v ∈ InfiniteWord.factorSet thueMorse n) :
    (fun i => !v i) ∈ InfiniteWord.factorSet thueMorse n

/-- **Factor complexity of the Thue–Morse Quarto word versus Thue–Morse.** Let $\mathcal{Q}$ be
the Thue–Morse Quarto sequence and $t$ the Thue–Morse sequence, with factor complexities
$p_{\mathcal{Q}}$ and $p_t$. For every natural number $n$, let $J_n$ be the set of length-$n$
factors of $\mathcal{Q}$ that are not factors of $t$. Then $p_{\mathcal{Q}}(n) = p_t(n) + |J_n|$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 30 (`jis-2026-26.4.1-prop-30`). -/
public theorem_wanted thueMorseQuarto_complexity_eq (n : ℕ) :
    wordFactorComplexity thueMorseQuarto n = wordFactorComplexity thueMorse n +
      (InfiniteWord.factorSet thueMorseQuarto n \ InfiniteWord.factorSet thueMorse n).ncard

/-- **Factor complexity of the Thue–Morse Quarto word at powers of two.** Let $\mathcal{Q}$ be
the Thue–Morse Quarto sequence and $t$ the Thue–Morse sequence, with factor complexities
$p_{\mathcal{Q}}$ and $p_t$, and for a natural number $n$ let $J_n$ be the set of length-$n$
factors of $\mathcal{Q}$ that are not factors of $t$. Then for every natural number $k \ge 4$,
$p_{\mathcal{Q}}(2^k) = 13 \cdot 2^{k-2} - 2$, $p_{\mathcal{Q}}(2^k) = p_t(2^k) + 2^{k-2}$ and
$|J_{2^k}| = 2^{k-2}$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 31 (`jis-2026-26.4.1-thm-31`). -/
public theorem_wanted thueMorseQuarto_complexity_two_pow (k : ℕ) (hk : 4 ≤ k) :
    wordFactorComplexity thueMorseQuarto (2 ^ k) = 13 * 2 ^ (k - 2) - 2 ∧
      wordFactorComplexity thueMorseQuarto (2 ^ k) =
        wordFactorComplexity thueMorse (2 ^ k) + 2 ^ (k - 2) ∧
      (InfiniteWord.factorSet thueMorseQuarto (2 ^ k) \
        InfiniteWord.factorSet thueMorse (2 ^ k)).ncard = 2 ^ (k - 2)

/-- **Factor complexity and right-special factors of the Thue–Morse Quarto word.** Let
$\mathcal{Q}$ be the Thue–Morse Quarto sequence, $p_{\mathcal{Q}}$ its factor complexity and
$\mathrm{RS}_{\mathcal{Q}}(n)$ its set of right-special factors of length $n$. Let $n \ge 16$ and
$k = \lfloor \log_2 n \rfloor$, so that $2^k \le n < 2^{k+1}$. Then
$p_{\mathcal{Q}}(n) = 13 \cdot 2^{k-2} - 2$ if $n = 2^k$,
$p_{\mathcal{Q}}(n) = 4n - 3 \cdot 2^{k-2} - 4$ if $2^k < n \le 2^k + 2^{k-1}$,
$p_{\mathcal{Q}}(n) = 3n + 3 \cdot 2^{k-2} - 3$ if $2^k + 2^{k-1} < n \le 2^k + 3 \cdot 2^{k-2}$,
and $p_{\mathcal{Q}}(n) = 2n + 5 \cdot 2^{k-1} - 2$ if $2^k + 3 \cdot 2^{k-2} < n$. Moreover
$\#\mathrm{RS}_{\mathcal{Q}}(n) = p_{\mathcal{Q}}(n+1) - p_{\mathcal{Q}}(n)$, and
$\#\mathrm{RS}_{\mathcal{Q}}(n)$ equals $4$ if $2^k < n \le 3 \cdot 2^{k-1}$, $3$ if
$3 \cdot 2^{k-1} < n \le 7 \cdot 2^{k-2}$, and $2$ if $7 \cdot 2^{k-2} < n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 33 (`jis-2026-26.4.1-prop-33`). -/
public theorem_wanted thueMorseQuarto_complexity_formula (n : ℕ) (hn : 16 ≤ n) :
    (n = 2 ^ Nat.log 2 n →
        (wordFactorComplexity thueMorseQuarto n : ℤ) = 13 * 2 ^ (Nat.log 2 n - 2) - 2) ∧
      (2 ^ Nat.log 2 n < n ∧ n ≤ 2 ^ Nat.log 2 n + 2 ^ (Nat.log 2 n - 1) →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          4 * n - 3 * 2 ^ (Nat.log 2 n - 2) - 4) ∧
      (2 ^ Nat.log 2 n + 2 ^ (Nat.log 2 n - 1) < n ∧
          n ≤ 2 ^ Nat.log 2 n + 3 * 2 ^ (Nat.log 2 n - 2) →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          3 * n + 3 * 2 ^ (Nat.log 2 n - 2) - 3) ∧
      (2 ^ Nat.log 2 n + 3 * 2 ^ (Nat.log 2 n - 2) < n →
        (wordFactorComplexity thueMorseQuarto n : ℤ) =
          2 * n + 5 * 2 ^ (Nat.log 2 n - 1) - 2) ∧
      ((rightSpecialFactors thueMorseQuarto n).ncard : ℤ) =
        wordFactorComplexity thueMorseQuarto (n + 1) - wordFactorComplexity thueMorseQuarto n ∧
      (2 ^ Nat.log 2 n < n ∧ n ≤ 3 * 2 ^ (Nat.log 2 n - 1) →
        (rightSpecialFactors thueMorseQuarto n).ncard = 4) ∧
      (3 * 2 ^ (Nat.log 2 n - 1) < n ∧ n ≤ 7 * 2 ^ (Nat.log 2 n - 2) →
        (rightSpecialFactors thueMorseQuarto n).ncard = 3) ∧
      (7 * 2 ^ (Nat.log 2 n - 2) < n → (rightSpecialFactors thueMorseQuarto n).ncard = 2)

/-- **The meta-automatic sequences have linear factor complexity.** Let $p_{\mathcal{M}_1}$ and
$p_{\mathcal{M}_2}$ be the factor complexities of the meta-automatic sequences $\mathcal{M}_1$
and $\mathcal{M}_2$. Then $p_{\mathcal{M}_1}(n) = \Theta(n)$ and $p_{\mathcal{M}_2}(n) = \Theta(n)$
as $n \to \infty$: for each $i \in \{1, 2\}$ there are real constants $c, C > 0$ with
$c n \le p_{\mathcal{M}_i}(n) \le C n$ for all sufficiently large $n$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 34 (`jis-2026-26.4.1-prop-34`). -/
public theorem_wanted metaAutomatic_complexity_isTheta :
    (fun n : ℕ => (wordFactorComplexity metaAutomaticOne n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ)) ∧
      (fun n : ℕ => (wordFactorComplexity metaAutomaticTwo n : ℝ)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ))

/-- **Factor complexity of $\mathcal{M}_2$ at powers of two.** Let $p(n)$ be the factor
complexity of the meta-automatic sequence $\mathcal{M}_2$, and let $k \ge 3$. If $3 \mid k$, then
$p(2^k) = 5 \cdot 2^{k-1} - 2$; if $3 \nmid k$, then $p(2^k) = 3 \cdot 2^k - 2$. Moreover,
$p(2^{k+3}) = 8\, p(2^k) + 14$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 36 (`jis-2026-26.4.1-prop-36`). -/
public theorem_wanted metaAutomaticTwo_complexity_two_pow (k : ℕ) (hk : 3 ≤ k) :
    (3 ∣ k → wordFactorComplexity metaAutomaticTwo (2 ^ k) = 5 * 2 ^ (k - 1) - 2) ∧
      (¬ 3 ∣ k → wordFactorComplexity metaAutomaticTwo (2 ^ k) = 3 * 2 ^ k - 2) ∧
      wordFactorComplexity metaAutomaticTwo (2 ^ (k + 3)) =
        8 * wordFactorComplexity metaAutomaticTwo (2 ^ k) + 14

/-- **Factor complexity of $\mathcal{M}_2$.** Let $p(n)$ be the factor complexity of the
meta-automatic sequence $\mathcal{M}_2$. Then $p(1) = 2$, and for every $n \ge 2$, writing
$k = \lfloor \log_2 n \rfloor$ (so that $2^k \le n < 2^{k+1}$), the following hold.
If $k \equiv 0 \pmod 3$, then $p(n) = 2n + 2^{k-1} - 2$ when $n \le 2^k + 1$,
$p(n) = 4n - (3 \cdot 2^{k-1} + 4)$ when $2^k + 1 \le n \le 7 \cdot 2^{k-2} + 1$, and
$p(n) = 2n + 2^{k+1} - 2$ when $n \ge 7 \cdot 2^{k-2} + 1$.
If $k \equiv 1 \pmod 3$, then $p(n) = 2n + 2^k - 2$ when $n \le 2^k + 1$,
$p(n) = 4n - (2^k + 4)$ when $2^k + 1 \le n \le 3 \cdot 2^{k-1} + 1$, and
$p(n) = 2n + 2^{k+1} - 2$ when $n \ge 3 \cdot 2^{k-1} + 1$.
If $k \equiv 2 \pmod 3$, then $p(n) = 2n + 2^k - 2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 37 (`jis-2026-26.4.1-prop-37`). -/
public theorem_wanted metaAutomaticTwo_complexity_formula :
    wordFactorComplexity metaAutomaticTwo 1 = 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      (Nat.log 2 n % 3 = 0 →
        (n ≤ 2 ^ Nat.log 2 n + 1 → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n - 1) - 2)) ∧
        (2 ^ Nat.log 2 n + 1 ≤ n ∧ n ≤ 7 * 2 ^ (Nat.log 2 n - 2) + 1 →
          (wordFactorComplexity metaAutomaticTwo n : ℤ) =
            4 * n - (3 * 2 ^ (Nat.log 2 n - 1) + 4)) ∧
        (7 * 2 ^ (Nat.log 2 n - 2) + 1 ≤ n → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n + 1) - 2))) ∧
      (Nat.log 2 n % 3 = 1 →
        (n ≤ 2 ^ Nat.log 2 n + 1 → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ Nat.log 2 n - 2)) ∧
        (2 ^ Nat.log 2 n + 1 ≤ n ∧ n ≤ 3 * 2 ^ (Nat.log 2 n - 1) + 1 →
          (wordFactorComplexity metaAutomaticTwo n : ℤ) = 4 * n - (2 ^ Nat.log 2 n + 4)) ∧
        (3 * 2 ^ (Nat.log 2 n - 1) + 1 ≤ n → (wordFactorComplexity metaAutomaticTwo n : ℤ) =
          2 * n + (2 ^ (Nat.log 2 n + 1) - 2))) ∧
      (Nat.log 2 n % 3 = 2 →
        (wordFactorComplexity metaAutomaticTwo n : ℤ) = 2 * n + (2 ^ Nat.log 2 n - 2))

end

end MetaMathlibExt
