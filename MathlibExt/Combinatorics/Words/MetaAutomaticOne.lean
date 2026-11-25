/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
import MathlibExt.Combinatorics.Words.BalancedNestedXor

/-!
# The first meta-automatic sequence

The defining recurrence pairs each even-indexed value with its Boolean complement. With the nested
companion $b(m) = \mathcal{M}_1(2m + 1 - \mathcal{M}_1(m))$, the pair $(\mathcal{M}_1(n), b(n))$
determines the pairs at $4n, \dots, 4n + 3$ for every $n \ge 1$ (`metaAutomaticOne_pair_closure`).
-/

namespace MetaMathlibExt

@[expose] public section

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

/-- **The meta-automatic sequence $\mathcal{M}_1$ is balanced.** Reading the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, we have
$\mathcal{M}_1(2n) + \mathcal{M}_1(2n+1) = 1$ for every $n \in \mathbb{N}$.

The paper's lemma also asserts that $\mathcal{M}_1$ is well defined; here that is part of the
definition of $\mathcal{M}_1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 10 (`jis-2026-26.4.1-lem-10`). -/
public theorem metaAutomaticOne_balanced (n : ℕ) :
    (metaAutomaticOne (2 * n)).toNat + (metaAutomaticOne (2 * n + 1)).toNat = 1 := by
  have complement (b : Bool) : b.toNat + (!b).toNat = 1 := by cases b <;> rfl
  by_cases hn : n = 0
  · simp [hn, metaAutomaticOne]
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = 4 * k ∨ 2 * n = 4 * k + 2 := ⟨n / 2, by omega⟩
  obtain ⟨h₀, h₁, h₂, h₃⟩ := metaAutomaticOne_rec k
  rcases hk with hk | hk
  · rw [hk, h₀ (by omega), h₁ (by omega)]
    exact complement _
  · rw [hk, h₂, h₃]
    exact complement _

/-- **Joint recurrence for $\mathcal{M}_1$ and its nested companion.** Read the values of the
meta-automatic sequence $\mathcal{M}_1$ as $0$ and $1$, write $\oplus$ for addition modulo $2$,
and let $b(m) = \mathcal{M}_1(2m + 1 - \mathcal{M}_1(m))$ for every $m \in \mathbb{N}$. Then for
every $n \ge 1$, with $x = \mathcal{M}_1(n)$ and $y = b(n)$, the pairs
$s(k) = (\mathcal{M}_1(k), b(k))$ satisfy $s(4n) = (x, y)$, $s(4n+1) = (1 \oplus x, x \oplus y)$,
$s(4n+2) = (y, 1 \oplus x)$ and $s(4n+3) = (1 \oplus y, 1 \oplus x \oplus y)$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 12 (`jis-2026-26.4.1-lem-12`). -/
public theorem metaAutomaticOne_pair_closure (b : ℕ → Bool)
    (hb : ∀ m, b m = metaAutomaticOne (2 * m + 1 - (metaAutomaticOne m).toNat))
    (n : ℕ) (hn : 1 ≤ n) :
    (metaAutomaticOne (4 * n), b (4 * n)) = (metaAutomaticOne n, b n) ∧
      (metaAutomaticOne (4 * n + 1), b (4 * n + 1)) =
        (!metaAutomaticOne n, xor (metaAutomaticOne n) (b n)) ∧
      (metaAutomaticOne (4 * n + 2), b (4 * n + 2)) = (b n, !metaAutomaticOne n) ∧
      (metaAutomaticOne (4 * n + 3), b (4 * n + 3)) =
        (!b n, !xor (metaAutomaticOne n) (b n)) := by
  -- `balanced_nested_xor` (the source's Lemma 5) for the balanced `ℳ₁` turns nested terms into
  -- XORs of two terms.
  have hxor (m : ℕ) : metaAutomaticOne (2 * m + 1 - (metaAutomaticOne m).toNat) =
      xor (metaAutomaticOne (2 * m + 1)) (metaAutomaticOne m) :=
    (balanced_nested_xor metaAutomaticOne metaAutomaticOne_balanced m).2
  have hb' (m : ℕ) : b m = xor (metaAutomaticOne (2 * m + 1)) (metaAutomaticOne m) :=
    (hb m).trans (hxor m)
  have hodd (m : ℕ) : metaAutomaticOne (2 * m + 1) = !metaAutomaticOne (2 * m) := by
    have h := metaAutomaticOne_balanced m
    cases he : metaAutomaticOne (2 * m) <;> simpa [he] using h
  -- The first coordinates are the defining recurrences at `n`.
  obtain ⟨r0, r1, r2, r3⟩ := metaAutomaticOne_rec n
  have e0 : metaAutomaticOne (4 * n) = metaAutomaticOne n := r0 hn
  have e1 : metaAutomaticOne (4 * n + 1) = !metaAutomaticOne n := r1 hn
  have e2 : metaAutomaticOne (4 * n + 2) = b n := r2.trans (hb n).symm
  have e3 : metaAutomaticOne (4 * n + 3) = !b n := r3.trans (congrArg Bool.not (hb n).symm)
  -- The second coordinates use the recurrences at `2n` and `2n + 1`.
  obtain ⟨-, s1, -, s3⟩ := metaAutomaticOne_rec (2 * n)
  obtain ⟨-, s5, -, s7⟩ := metaAutomaticOne_rec (2 * n + 1)
  have f0 : b (4 * n) = b n := by
    rw [hb' (4 * n), hb' n, show 2 * (4 * n) + 1 = 4 * (2 * n) + 1 by omega, s1 (by omega),
      e0, hodd n]
  have f1 : b (4 * n + 1) = xor (metaAutomaticOne n) (b n) := by
    rw [hb' (4 * n + 1), show 2 * (4 * n + 1) + 1 = 4 * (2 * n) + 3 by omega, s3, hxor (2 * n),
      show 2 * (2 * n) + 1 = 4 * n + 1 by omega, e1, hb' n, hodd n]
    cases metaAutomaticOne n <;> cases metaAutomaticOne (2 * n) <;> rfl
  have f2 : b (4 * n + 2) = !metaAutomaticOne n := by
    rw [hb' (4 * n + 2), show 2 * (4 * n + 2) + 1 = 4 * (2 * n + 1) + 1 by omega,
      s5 (by omega), e2, hb' n]
    cases metaAutomaticOne n <;> cases metaAutomaticOne (2 * n + 1) <;> rfl
  have f3 : b (4 * n + 3) = !xor (metaAutomaticOne n) (b n) := by
    rw [hb' (4 * n + 3), show 2 * (4 * n + 3) + 1 = 4 * (2 * n + 1) + 3 by omega, s7,
      hxor (2 * n + 1), show 2 * (2 * n + 1) + 1 = 4 * n + 3 by omega, e3, hb' n]
    cases metaAutomaticOne n <;> cases metaAutomaticOne (2 * n + 1) <;> rfl
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  exact ⟨rfl, rfl, rfl, rfl⟩

end

end MetaMathlibExt
