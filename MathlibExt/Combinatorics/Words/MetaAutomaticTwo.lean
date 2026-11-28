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
at indices `2 * n` and `2 * n + 1`. The sequence is also the parity coding of
a four-letter morphism fixed point.

## References

* John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer
  Sequences 29 (2026), Article 26.4.1, pp. 1–23. Section 4 defines the sequence and proves
  balance and recovery (Theorem 18 and Lemma 19); Corollary 23 gives the morphic coding.
  The proof below uses the balanced XOR identities of Lemma 5 to verify the transition
  table of Theorem 22 directly from the recurrence.
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

private theorem metaAutomaticTwo_odd_eq_not_even (n : ℕ) :
    metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) := by
  obtain ⟨heven, hodd⟩ := metaAutomaticTwo_recover n
  exact hodd.trans (congrArg Bool.not heven.symm)

-- The first bit of each of the four successor states is determined by the nested selector.
private theorem metaAutomaticTwo_four_terms (n : ℕ) :
    let y := xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n))
    metaAutomaticTwo (4 * n) = y ∧ metaAutomaticTwo (4 * n + 1) = !y ∧
      metaAutomaticTwo (4 * n + 2) = !y ∧ metaAutomaticTwo (4 * n + 3) = y := by
  dsimp only
  by_cases hn : n = 0
  · subst n
    simpa [List.range_succ] using congrArg (List.take 4) metaAutomaticTwo_small
  obtain ⟨h₀, h₁, h₂, h₃⟩ := metaAutomaticTwo_rec n
  obtain ⟨heven, hodd⟩ := balanced_nested_xor metaAutomaticTwo metaAutomaticTwo_balanced n
  have hfirst : metaAutomaticTwo (4 * n) = xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n)) :=
    (h₀ (by omega)).trans (heven.trans (Bool.xor_comm _ _))
  have hthird : metaAutomaticTwo (4 * n + 2) =
      !xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n)) := by
    rw [h₂, hodd, metaAutomaticTwo_odd_eq_not_even n]
    cases metaAutomaticTwo n <;> cases metaAutomaticTwo (2 * n) <;> rfl
  exact ⟨hfirst, (h₁ (by omega)).trans (congrArg Bool.not hfirst), hthird,
    h₃.trans (by rw [hthird, Bool.not_not])⟩

-- The terms at doubled successor indices come from the blocks at `2 * n` and `2 * n + 1`.
private theorem metaAutomaticTwo_double_four_terms (n : ℕ) :
    metaAutomaticTwo (2 * (4 * n)) = metaAutomaticTwo n ∧
      metaAutomaticTwo (2 * (4 * n + 1)) = !metaAutomaticTwo n ∧
      metaAutomaticTwo (2 * (4 * n + 2)) = metaAutomaticTwo n ∧
      metaAutomaticTwo (2 * (4 * n + 3)) = !metaAutomaticTwo n := by
  obtain ⟨h₀, _, h₂, _⟩ := metaAutomaticTwo_four_terms n
  obtain ⟨heven₀, _, heven₂, _⟩ := metaAutomaticTwo_four_terms (2 * n)
  obtain ⟨hodd₀, _, hodd₂, _⟩ := metaAutomaticTwo_four_terms (2 * n + 1)
  have hxor : xor (metaAutomaticTwo (2 * n)) (metaAutomaticTwo (4 * n)) = metaAutomaticTwo n ∧
      xor (metaAutomaticTwo (2 * n + 1)) (metaAutomaticTwo (4 * n + 2)) = metaAutomaticTwo n := by
    rw [h₀, h₂, metaAutomaticTwo_odd_eq_not_even n]
    cases metaAutomaticTwo n <;> cases metaAutomaticTwo (2 * n) <;> exact ⟨rfl, rfl⟩
  rw [show 2 * (4 * n) = 4 * (2 * n) by omega,
    show 2 * (4 * n + 1) = 4 * (2 * n) + 2 by omega,
    show 2 * (4 * n + 2) = 4 * (2 * n + 1) by omega,
    show 2 * (4 * n + 3) = 4 * (2 * n + 1) + 2 by omega,
    heven₀, heven₂, hodd₀, hodd₂, show 2 * (2 * n) = 4 * n by omega,
    show 2 * (2 * n + 1) = 4 * n + 2 by omega, hxor.1, hxor.2]
  exact ⟨rfl, rfl, rfl, rfl⟩

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
public theorem metaAutomaticTwo_morphism_coding :
    ∃ w : ℕ → ℕ, w 0 = 0 ∧
      (∀ n r, r < 4 → w (4 * n + r) =
        ([[0, 1, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1], [1, 0, 2, 3]].getD (w n) []).getD r 0) ∧
      ∀ n, metaAutomaticTwo n = decide (w n % 2 = 1) := by
  -- The nested term is the high bit by Lemma 5; the sequence value is the low bit.
  let w : ℕ → ℕ := fun n =>
    2 * (xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n))).toNat + (metaAutomaticTwo n).toNat
  refine ⟨w, by simp [w, metaAutomaticTwo], ?_, ?_⟩
  · intro n r hr
    obtain ⟨h₀, h₁, h₂, h₃⟩ := metaAutomaticTwo_four_terms n
    obtain ⟨h₀', h₁', h₂', h₃'⟩ := metaAutomaticTwo_double_four_terms n
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr' with rfl | rfl | rfl | rfl <;>
      cases hx : metaAutomaticTwo n <;> cases hy : metaAutomaticTwo (2 * n) <;> simp [w, *]
  · intro n
    have hparity (lo hi : Bool) : lo = decide ((2 * hi.toNat + lo.toNat) % 2 = 1) := by
      cases lo <;> cases hi <;> rfl
    exact hparity _ _

end

end MetaMathlibExt
