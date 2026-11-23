/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-accessibility of primes

`OPG-1797` (Open Problem Garden, node 1797): is the set of prime
numbers 2-accessible?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.PrimeTwoAccessibilityWanted

/-- **Monochromatic finite sequences.** Given a colouring $c : \mathbb{N} \to \{0, \dots, r - 1\}$
of the natural numbers with $r$ colours, a finite sequence $x_0, \dots, x_{k-1}$ of natural
numbers is monochromatic when all its terms have the same colour: $c(x_i) = c(x_j)$ for all
$i, j < k$.

Source: `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
formalizes "monochromatic sequence" from the definition of `r`-accessible. -/
def IsMonochromatic {r k : ℕ} (c : ℕ → Fin r) (x : Fin k → ℕ) : Prop :=
  ∀ i j, c (x i) = c (x j)

/-- **Finite $S$-diffsequences.** For a set $S$ of natural numbers, a finite sequence
$x_0, \dots, x_{k-1}$ of natural numbers is an $S$-diffsequence when each term is the previous
one plus an element of $S$: for every $i$ with $i + 1 < k$ there is $d \in S$ with
$x_{i+1} = x_i + d$.

Source: `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
formalizes "`S`-diffsequence", i.e. `x_{i+1} - x_i ∈ S`,
stated additively as `x (i+1) = x i + d` with `d ∈ S`. -/
def IsSDiffSequence (S : Set ℕ) {k : ℕ} (x : Fin k → ℕ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < k), ∃ d ∈ S, x ⟨i + 1, h⟩ = x ⟨i, by omega⟩ + d

/-- **$r$-accessible sets of natural numbers.** A set $S \subseteq \mathbb{N}$ is $r$-accessible
when for every colouring $c : \mathbb{N} \to \{0, \dots, r - 1\}$ with $r$ colours and every
length $k \ne 1$ there is a sequence $x_0, \dots, x_{k-1}$ of natural numbers that is
monochromatic for $c$ and is an $S$-diffsequence: for each $i$ with $i + 1 < k$ there is
$d \in S$ with $x_{i+1} = x_i + d$.

Source: `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
`S` is `r`-accessible if for every `r`-coloring of `ℕ` and every
`k ∈ ℕ \ {1}` there is a monochromatic `S`-diffsequence of length `k`. -/
def IsRAccessible (r : ℕ) (S : Set ℕ) : Prop :=
  ∀ (c : ℕ → Fin r) (k : ℕ), k ≠ 1 → ∃ x : Fin k → ℕ,
    IsMonochromatic c x ∧ IsSDiffSequence S x

/-- **2-accessibility of the primes.** The statement that the set of prime numbers is
$2$-accessible: for every colouring $c : \mathbb{N} \to \{0, 1\}$ of the natural numbers with two
colours and every length $k \ne 1$ there is a sequence $x_0, \dots, x_{k-1}$ of natural numbers,
all of the same colour, such that each difference $x_{i+1} - x_i$ is a prime number. Open Problem
Garden question OPG-1797 asks whether this holds.

Source: `OPG-1797` (Open Problem Garden, node 1797,
http://www.openproblemgarden.org/op/2_accessibility_of_primes):
"Is the set of prime numbers 2-accessible?" -/
def conjecture : Prop :=
  IsRAccessible 2 { n | Nat.Prime n }

/--
**The primes are 2-accessible.** The set of prime numbers is $2$-accessible: for every colouring
$c : \mathbb{N} \to \{0, 1\}$ of the natural numbers with two colours and every length $k \ne 1$
there is a sequence $x_0, \dots, x_{k-1}$ of natural numbers, all of the same colour, such that
each difference $x_{i+1} - x_i$ is a prime number.

Quester proves this as a special case of Theorem 1 of the paper, using the
Frantzikinakis–Host–Kra recurrence theorem along shifted primes.

Source: Oscar Quester, The
Primes are 2-Accessible, arXiv preprint (2026), arXiv:2606.00410,
https://arxiv.org/abs/2606.00410; Nikos Frantzikinakis, Bernard Host, Bryna Kra, The polynomial
multidimensional Szemeredi theorem along shifted primes, Israel J. Math. 194 (2013), 331-348,
arXiv:1009.1484, https://arxiv.org/abs/1009.1484. Moved from
`OpenConjectures/Combinatorics/PrimeTwoAccessibility`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PrimeTwoAccessibilityWanted
