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
# The second meta-automatic sequence

The recurrence for the second meta-automatic sequence gives complementary values
at indices `2 * n` and `2 * n + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

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

/-- **First sixteen terms of $\mathcal{M}_2$.** The first sixteen terms
$\mathcal{M}_2(0), \mathcal{M}_2(1), \ldots, \mathcal{M}_2(15)$ of the meta-automatic sequence
$\mathcal{M}_2$ are $0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 4. -/
public theorem metaAutomaticTwo_small : (List.range 16).map metaAutomaticTwo =
    [false, true, true, false, false, true, true, false, true, false, false, true, true,
      false, false, true] := by
  simp [List.range_succ, metaAutomaticTwo]

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

/-- **$\mathcal{M}_2$ is balanced.** For every natural number $n$, the meta-automatic sequence
$\mathcal{M}_2$, read as taking values in $\{0, 1\}$, satisfies
$\mathcal{M}_2(2n) + \mathcal{M}_2(2n+1) = 1$.

The well-definedness of $\mathcal{M}_2$, also part of the source theorem, holds because its
defining recursion terminates.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 18 (`jis-2026-26.4.1-thm-18`). -/
public theorem metaAutomaticTwo_balanced (n : ℕ) :
    (metaAutomaticTwo (2 * n)).toNat + (metaAutomaticTwo (2 * n + 1)).toNat = 1 := by
  have h : metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) := by
    by_cases hn : n = 0
    · simp [hn, metaAutomaticTwo]
    obtain ⟨k, hk | hk⟩ : ∃ k, 2 * n = 4 * k ∨ 2 * n = 4 * k + 2 := ⟨n / 2, by omega⟩
    · rw [hk]
      exact (metaAutomaticTwo_rec k).2.1 (by omega)
    · rw [hk]
      exact (metaAutomaticTwo_rec k).2.2.2
  rw [h]
  cases metaAutomaticTwo (2 * n) <;> rfl

/-- **Recovering the even and odd terms of $\mathcal{M}_2$.** For every natural number $n$, let
$x = \mathcal{M}_2(n)$ and $y = \mathcal{M}_2(2n + \mathcal{M}_2(n))$, where $\mathcal{M}_2$ is the
meta-automatic sequence with values in $\{0, 1\}$. Then $\mathcal{M}_2(2n) = x \oplus y$ and
$\mathcal{M}_2(2n+1) = x \oplus y \oplus 1$, where $\oplus$ is addition modulo $2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 19 (`jis-2026-26.4.1-lem-19`). -/
public theorem metaAutomaticTwo_recover (n : ℕ) :
    metaAutomaticTwo (2 * n) = xor (metaAutomaticTwo n)
        (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) ∧
      metaAutomaticTwo (2 * n + 1) = !xor (metaAutomaticTwo n)
        (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) := by
  have hy := (balanced_nested_xor metaAutomaticTwo metaAutomaticTwo_balanced n).1
  have heven : metaAutomaticTwo (2 * n) = xor (metaAutomaticTwo n)
      (metaAutomaticTwo (2 * n + (metaAutomaticTwo n).toNat)) := by
    rw [hy, Bool.xor_comm (metaAutomaticTwo (2 * n)), ← Bool.xor_assoc]
    simp
  have hodd : metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) := by
    have h := metaAutomaticTwo_balanced n
    cases he : metaAutomaticTwo (2 * n) <;> simpa [he] using h
  exact ⟨heven, hodd.trans (congrArg Bool.not heven)⟩

end

end MetaMathlibExt
