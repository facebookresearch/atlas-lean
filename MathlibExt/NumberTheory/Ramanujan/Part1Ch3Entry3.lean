/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Defs.Filter
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9Odd
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4HarmonicPoissonAsymptotic

end Entry10Example4HarmonicPoissonAsymptotic

namespace Entry3

noncomputable def sector (ε : ℝ) : Set ℂ :=
  {z : ℂ | -Real.pi + ε ≤ Complex.arg z ∧ Complex.arg z ≤ Real.pi - ε}

noncomputable def fCoeff (x : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-x) * ∑' (k : ℕ), (((k + 1 : ℕ) : ℂ) ^ j * x ^ (k + 1) / (Nat.factorial k : ℂ))

noncomputable def psi (x z : ℂ) : ℂ :=
  ∑' (j : ℕ), if ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = (0 : ℂ) then (0 : ℂ) else
      ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)))

/-- **Entry 3 coefficients as generalized Bell values.** Let $F$ be Ramanujan's generalized Bell
function. For every complex number $x$ and every natural number $j$, let
$f(x, j) = e^{-x} \sum_{k=0}^{\infty} \frac{(k+1)^j x^{k+1}}{k!}$. Then
$f(x, j) = F(0, 1, x; j)$. -/
theorem fCoeff_eq_generalizedBellGenerating (x : ℂ) (j : ℕ) :
    fCoeff x j =
      Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x j := by
  unfold fCoeff
    Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating
  congr 1
  apply tsum_congr
  intro k
  simp only [zero_add, one_mul]

/-- The Entry 9 product with `a = 0, b = 1` coincides with the Entry 3 product. -/
private lemma prod_entry9_eq (z : ℂ) (j : ℕ) :
    (∏ r ∈ Finset.range (j + 1), (z + (0 : ℂ) + (1 : ℂ) * ((r : ℂ) + 1)))
      = ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) := by
  apply Finset.prod_congr rfl
  intro r _
  have hcast : (((r + 1 : ℕ)) : ℂ) = (r : ℂ) + 1 := by push_cast; ring
  rw [hcast]
  ring

/-- **Ramanujan's factorial series as the Entry 9 product series at $a = 0$, $b = 1$.** Let $P$ be
Ramanujan's Entry 9(i) product series. For all complex numbers $x$ and $z$, let
$\psi(x, z) = \sum_{j=0}^{\infty} t_j$, where $t_j = \frac{(-1)^j x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$
when the product in the denominator is nonzero and $t_j = 0$ otherwise. Then
$\psi(x, z) = P(0, 1, x; z)$.

Since division by zero is taken to give zero, the case distinction in $t_j$ changes nothing. -/
theorem psi_eq_entry9_P (x z : ℂ) :
    psi x z = Entry9Odd.entry9_P 0 1 x z := by
  unfold psi Entry9Odd.entry9_P
  apply tsum_congr
  intro j
  have hprod := prod_entry9_eq z j
  by_cases h : ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = 0
  · have h2 : ∏ r ∈ Finset.range (j + 1), (z + (0 : ℂ) + (1 : ℂ) * ((r : ℂ) + 1)) = 0 :=
      hprod.trans h
    rw [ite_eq_left h, h2]
    simp
  · rw [ite_eq_right h, ← hprod]

/-- **Asymptotic expansion of Ramanujan's factorial series, for every $x$.** Let $x$ be a complex
number. For natural numbers $j$ let
$f(x, j) = e^{-x} \sum_{k=0}^{\infty} \frac{(k+1)^j x^{k+1}}{k!}$, and for complex $z$ let
$\psi(x, z) = \sum_{j=0}^{\infty} t_j$, where
$t_j = \frac{(-1)^j x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$ when the denominator is nonzero and
$t_j = 0$ otherwise. Let $\varepsilon$ be a real number with $0 < \varepsilon < \pi$, and let
$S_\varepsilon$ be the set of complex $z$ whose principal argument satisfies
$-\pi + \varepsilon \le \arg z \le \pi - \varepsilon$. Then for every natural number $N$,
$$\psi(x, z) - \sum_{j=0}^{N} \frac{(-1)^j f(x, j)}{z^{j+1}} = O\left(\frac{1}{z^{N+2}}\right)$$
as $|z| \to \infty$ with $z \in S_\varepsilon$. -/
theorem ramanujan_part1_ch3_entry3_general (x : ℂ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < Real.pi) (N : ℕ) :
    Asymptotics.IsBigO (Filter.cocompact ℂ ⊓ Filter.principal (sector ε))
      (fun z : ℂ => psi x z - ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
      (fun z : ℂ => (1 : ℂ) / z ^ (N + 2)) := by
  have h9 :=
    Entry9Odd.ramanujan_part1_ch3_entry9_odd 0 1 x one_ne_zero ε hε_pos hε_lt N
  have hfun : (fun z : ℂ => (z + (0 : ℂ)) / (1 : ℂ)) = id := by
    funext z
    simp
  have hfilter :
      Filter.comap (fun z : ℂ => (z + (0 : ℂ)) / (1 : ℂ))
          (Filter.cocompact ℂ ⊓ Filter.principal
            {w : ℂ | -Real.pi + ε ≤ Complex.arg w ∧ Complex.arg w ≤ Real.pi - ε})
        = Filter.cocompact ℂ ⊓ Filter.principal (sector ε) := by
    rw [hfun, Filter.comap_id]
    rfl
  rw [hfilter] at h9
  have hsum : ∀ z : ℂ, (Finset.sum (Finset.range (N + 1)) (fun k : ℕ =>
      ((-1 : ℂ) ^ k *
        Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x k)
        / z ^ (k + 1)))
      = ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)) := by
    intro z
    apply Finset.sum_congr rfl
    intro j _
    simp only [fCoeff_eq_generalizedBellGenerating]
  have hLHS :
      (fun z : ℂ => psi x z -
        ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
      = fun z : ℂ => -((Finset.sum (Finset.range (N + 1)) (fun k : ℕ =>
          ((-1 : ℂ) ^ k *
            Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x k)
            / z ^ (k + 1)) - Entry9Odd.entry9_P 0 1 x z)) := by
    funext z
    rw [← psi_eq_entry9_P, hsum z]
    ring
  rw [hLHS]
  exact h9.neg_left

/-- **Ramanujan's asymptotic expansion of a factorial series.** Let $x$ be a nonzero complex
number. For natural numbers $j$ let
$f(x, j) = e^{-x} \sum_{k=0}^{\infty} \frac{(k+1)^j x^{k+1}}{k!}$, and for complex $z$ let
$\psi(x, z) = \sum_{j=0}^{\infty} t_j$, where
$t_j = \frac{(-1)^j x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$ when the denominator is nonzero and
$t_j = 0$ otherwise. Let $\varepsilon$ be a real number with $0 < \varepsilon < \pi$, and let
$S_\varepsilon$ be the set of complex $z$ whose principal argument satisfies
$-\pi + \varepsilon \le \arg z \le \pi - \varepsilon$. Then for every natural number $N$,
$$\psi(x, z) - \sum_{j=0}^{N} \frac{(-1)^j f(x, j)}{z^{j+1}} = O\left(\frac{1}{z^{N+2}}\right)$$
as $|z| \to \infty$ with $z \in S_\varepsilon$.

The hypothesis $x \neq 0$ is not needed for the proof; it is kept to match the source.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 3, printed p. 47 / PDF p.
    57.
-/
theorem ramanujan_part1_ch3_entry3 (x : ℂ)
    (hx : x ≠ 0) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < Real.pi) (N : ℕ) :
    Asymptotics.IsBigO (Filter.cocompact ℂ ⊓ Filter.principal (sector ε))
      (fun z : ℂ => psi x z - ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
      (fun z : ℂ => (1 : ℂ) / z ^ (N + 2)) := by
  have _ : x ≠ 0 := hx
  exact ramanujan_part1_ch3_entry3_general x ε hε_pos hε_lt N

end Entry3

namespace Entry3Fsummable

end Entry3Fsummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
