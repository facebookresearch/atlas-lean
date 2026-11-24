/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.RatResidue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Göbel sequences

The recurrence for the rational $(k,l)$-Göbel sequence propagates a congruence
for the index times the sequence value up to the first multiple of the prime.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The (k, l)-Göbel sequence.** For natural numbers $k$ and $l$, the $(k, l)$-Göbel sequence
is the sequence of rational numbers $g_{k,l}(n)$, $n \ge 0$, given by $g_{k,l}(0) = 0$,
$g_{k,l}(1) = l$ and, for $n \ge 1$,
$$g_{k,l}(n + 1) = \frac{g_{k,l}(n) \bigl(n + g_{k,l}(n)^{k-1}\bigr)}{n + 1},$$
where $k - 1$ is truncated subtraction, so the exponent is $0$ when $k = 0$.

The paper indexes from $n = 1$ and takes $k, l \ge 2$ (Lemma 5 also admits $k, l \ge 1$); the
value at $n = 0$ is a convention and plays no role.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public def gobelSequence (k l : ℕ) : ℕ → ℚ
  | 0 => 0
  | 1 => l
  | n + 2 => gobelSequence k l (n + 1) * ((n + 1 : ℚ) + gobelSequence k l (n + 1) ^ (k - 1))
      / (n + 2)

/-- **Initial value of the $(k, l)$-Göbel sequence.** For all natural numbers $k$ and $l$, the
$(k, l)$-Göbel sequence $g_{k,l}$ satisfies $g_{k,l}(1) = l$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public theorem gobelSequence_one (k l : ℕ) : gobelSequence k l 1 = l := rfl

/-- **Recursion for the (k, l)-Göbel sequence.** For all natural numbers $k$, $l$ and $n \ge 1$,
the $(k, l)$-Göbel sequence $g_{k,l}$ satisfies, in $\mathbb{Q}$,
$$(n + 1)\, g_{k,l}(n + 1) = g_{k,l}(n) \bigl(n + g_{k,l}(n)^{k-1}\bigr),$$
where $k - 1$ is truncated subtraction, so the exponent is $0$ when $k = 0$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Definition 1. -/
public theorem gobelSequence_succ (k l n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℚ) * gobelSequence k l (n + 1)
      = gobelSequence k l n * ((n : ℚ) + gobelSequence k l n ^ (k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  change (↑(m + 1) + 1 : ℚ) * (gobelSequence k l (m + 1) *
      ((m + 1 : ℚ) + gobelSequence k l (m + 1) ^ (k - 1)) / (m + 2)) = _
  have h : (m + 2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Göbel's original sequence.** The $(2, 2)$-Göbel sequence $g_{2,2}$ satisfies
$g_{2,2}(2) = 3$, $g_{2,2}(3) = 5$, $g_{2,2}(4) = 10$ and $g_{2,2}(5) = 28$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Section 1. -/
public theorem gobelSequence_two_two_small :
    gobelSequence 2 2 2 = 3 ∧ gobelSequence 2 2 3 = 5 ∧ gobelSequence 2 2 4 = 10 ∧
      gobelSequence 2 2 5 = 28 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gobelSequence]

namespace gobelSequence_mul_index_congr

private abbrev ValAtLeast (p s : ℕ) (x : ℚ) : Prop :=
  x = 0 ∨ (s : ℤ) ≤ padicValRat p x

variable {p s : ℕ} [Fact p.Prime] {x y : ℚ}

private theorem valAtLeast_add (hx : ValAtLeast p s x) (hy : ValAtLeast p s y) :
    ValAtLeast p s (x + y) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · simpa using Or.inr hx
  apply or_iff_not_imp_left.mpr
  exact fun h => (le_min hx hy).trans (padicValRat.min_le_padicValRat_add h)

private theorem valAtLeast_natCast_mul (m : ℕ) (hx : ValAtLeast p s x) :
    ValAtLeast p s (m * x) := by
  apply or_iff_not_imp_left.mpr
  intro h
  obtain ⟨hm, hx'⟩ := mul_ne_zero_iff.mp h
  rw [padicValRat.mul hm hx']
  exact le_add_of_nonneg_of_le (zero_le_padicValRat_of_nat m) (hx.resolve_left hx')

private theorem valAtLeast_of_natCast_mul {m : ℕ} (hm : 0 < m) (hmp : m < p)
    (hx : ValAtLeast p s (m * x)) : ValAtLeast p s x := by
  apply or_iff_not_imp_left.mpr
  intro hx'
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h := hx.resolve_left (mul_ne_zero hm' hx')
  simpa [padicValRat.mul hm' hx', padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hm hmp)]
    using h

end gobelSequence_mul_index_congr

open gobelSequence_mul_index_congr

set_option linter.unusedVariables false in
/-- **Propagation of a congruence along the $(k, l)$-Göbel sequence.** Let $p$ be a prime, let
$k, l, r \ge 2$ be natural numbers, let $g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $a, b$ be
natural numbers with $1 \le a < p$ and $b < p$. For rational numbers $x, y$ write
$x \equiv y \pmod{p^r}$ when $x = y$ or $\nu_p(x - y) \ge r$, where $\nu_p$ is the $p$-adic
valuation on $\mathbb{Q}$. If $g_{k,l}(a) \equiv b p^{r-1} \pmod{p^r}$, then
$n \, g_{k,l}(n) \equiv a b p^{r-1} \pmod{p^r}$ for every natural number $n$ with $a \le n < p$.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 20 (`jis-2024-24.8.1-lem-20`). -/
public theorem gobelSequence_mul_index_congr (p : ℕ) (hp : p.Prime) (k l r a b : ℕ)
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hr : 2 ≤ r) (ha₁ : 1 ≤ a) (hap : a < p) (hbp : b < p)
    (hg : gobelSequence k l a - b * (p : ℚ) ^ (r - 1) = 0 ∨
      (r : ℤ) ≤ padicValRat p (gobelSequence k l a - b * (p : ℚ) ^ (r - 1)))
    (n : ℕ) (han : a ≤ n) (hnp : n < p) :
    n * gobelSequence k l n - a * b * (p : ℚ) ^ (r - 1) = 0 ∨
      (r : ℤ) ≤ padicValRat p (n * gobelSequence k l n - a * b * (p : ℚ) ^ (r - 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  let c : ℚ := a * b * (p : ℚ) ^ (r - 1)
  have hc : ValAtLeast p (r - 1) c := by
    dsimp [c]
    rw [mul_assoc]
    apply valAtLeast_natCast_mul
    apply valAtLeast_natCast_mul
    exact Or.inr (by simp [padicValRat.pow, padicValRat.self hp.one_lt])
  change ValAtLeast p r (n * gobelSequence k l n - c)
  induction n, han using Nat.le_induction with
  | base =>
    simpa only [c, mul_sub, mul_assoc] using valAtLeast_natCast_mul a hg
  | succ n han ih =>
    have hdiff := ih (Nat.lt_of_succ_lt hnp)
    -- The weighted term has valuation at least r - 1, and n is a unit at p.
    have hng : ValAtLeast p (r - 1) (n * gobelSequence k l n) := by
      have hweak : ValAtLeast p (r - 1) (n * gobelSequence k l n - c) :=
        hdiff.imp_right (fun h => le_trans (by omega) h)
      simpa only [sub_add_cancel] using valAtLeast_add hweak hc
    have hpow : ValAtLeast p r (gobelSequence k l n ^ k) := by
      rcases valAtLeast_of_natCast_mul (by omega) (Nat.lt_of_succ_lt hnp) hng with h | h
      · exact Or.inl (by simp [h, show k ≠ 0 by omega])
      · right
        rw [padicValRat.pow]
        calc
          (r : ℤ) ≤ 2 * ((r - 1 : ℕ) : ℤ) := by omega
          _ ≤ (k : ℤ) * padicValRat p (gobelSequence k l n) := by
            gcongr
            omega
    -- The increment of the weighted sequence is the kth power of the current term.
    rw [Nat.cast_succ, gobelSequence_succ k l n (by omega), mul_add, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ k), mul_comm (gobelSequence k l n) (n : ℚ),
      add_sub_right_comm]
    exact valAtLeast_add hdiff hpow

end

end MetaMathlibExt
