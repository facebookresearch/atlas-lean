/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Interval
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Monochromatic solutions of linear equations with at least three colours

Statements from Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using
at Least Three Colors*, INTEGERS 25 (2025), Article A88 (preprint arXiv:2501.17136, from
which the definitions are taken).

An equation `a₁x₁ + ⋯ + aₖxₖ = 0` is given by its coefficient vector `a : Fin k → ℤ`.

* Over a finite abelian group `G` the paper measures colourings by the expected proportion of
  monochromatic solutions of a probabilistic colouring (its equation (2.1)), so
  `IsUncommonOverFiniteGroup G a r` asks for weights `w c x ≥ 0` with `∑_c w c x = 1` whose
  monochromatic weight `∑_c ∑_{x ∈ sol} ∏_i w c (xᵢ)` is below the uniform value
  `r^{1-k} · #sol`. Deterministic colourings would not do: on `ℤ/2` the equation
  `x₁ + x₂ + x₃ = 0` has `4` solutions and every deterministic `3`-colouring has at least one
  monochromatic solution, a proportion `≥ 1/4 > 1/9`.
* Over the integers an equation is `r`-common if every `r`-colouring of `[n]` has at least
  `(1 - o(1)) r^{1-k}` times the number of solutions in `[n]^k` monochromatic, and
  `IsUncommonOverIntegers a r` is the negation of that.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Canceling partition.** Let $a_1, \dots, a_k$ be integers, the coefficients of the
linear equation $a_1x_1 + \cdots + a_kx_k = 0$. The equation has a canceling partition when
its indices split into pairs of distinct indices $i, j$ with $a_i + a_j = 0$; precisely,
when there is a permutation $\sigma$ of the indices $1, \dots, k$ such that for every $i$
we have $\sigma(\sigma(i)) = i$, $\sigma(i) \ne i$ and $a_i + a_{\sigma(i)} = 0$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1 (definition of canceling
partition). -/
public def HasCancelingPartition {k : ℕ} (a : Fin k → ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), (∀ i, σ (σ i) = i) ∧ (∀ i, σ i ≠ i) ∧ ∀ i, a i + a (σ i) = 0

/-- **A canceling partition for $x_1 + 2x_2 - x_3 - 2x_4 = 0$.** The equation
$x_1 + 2x_2 - x_3 - 2x_4 = 0$, with coefficient vector $(1, 2, -1, -2)$, has a canceling
partition.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem hasCancelingPartition_one_two_neg_one_neg_two :
    HasCancelingPartition (![1, 2, -1, -2] : Fin 4 → ℤ) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide, by decide, by decide⟩

/-- **The equation $x_1 + x_2 = 0$ has no canceling partition.** The equation
$x_1 + x_2 = 0$, with coefficient vector $(1, 1)$, has no canceling partition.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem not_hasCancelingPartition_one_one : ¬ HasCancelingPartition (![1, 1] : Fin 2 → ℤ) := by
  rintro ⟨σ, -, -, hsum⟩
  have h1 : ∀ j : Fin 2, (![1, 1] : Fin 2 → ℤ) j = 1 := by decide
  have h := hsum 0
  rw [h1, h1] at h
  omega

/-- **Uncommon equations over a finite abelian group.** Let $G$ be a finite abelian group,
let $a_1, \dots, a_k$ be integers, let $r$ be a natural number, and let $S \subseteq G^k$ be
the set of solutions of $a_1x_1 + \cdots + a_kx_k = 0$. The equation is $r$-uncommon over
$G$ when there are functions $w_1, \dots, w_r \colon G \to \mathbb{R}$ with $w_c(x) \ge 0$ for
all $c$ and $x$, and $w_1(x) + \cdots + w_r(x) = 1$ for every $x \in G$, such that

$$r^{k-1} \sum_{c=1}^{r} \sum_{(x_1, \dots, x_k) \in S} \prod_{i=1}^{k} w_c(x_i) < |S|,$$

where $r^{k-1}$ is read as $1$ when $k = 0$.

The functions $w_c$ form a fractional $r$-colouring of $G$, and the double sum is its
weighted count of monochromatic solutions. For $k \ge 1$ the condition says that this count
is below $r^{1-k}|S|$, its value for the uniform weights $w_c(x) = 1/r$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2 (equation (2.1)). -/
public def IsUncommonOverFiniteGroup (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k : ℕ} (a : Fin k → ℤ) (r : ℕ) : Prop :=
  ∃ w : Fin r → G → ℝ, (∀ c x, 0 ≤ w c x) ∧ (∀ x, ∑ c, w c x = 1) ∧
    (r : ℝ) ^ (k - 1) *
        ∑ c, ∑ x ∈ univ.filter (fun x : Fin k → G => ∑ i, a i • x i = 0), ∏ i, w c (x i) <
      ((univ.filter (fun x : Fin k → G => ∑ i, a i • x i = 0)).card : ℝ)

/-- **No equation is 1-uncommon over a finite abelian group.** For every finite abelian group
$G$, every $k \ge 0$ and all integers $a_1, \dots, a_k$, the equation
$a_1 x_1 + \dots + a_k x_k = 0$ is not $1$-uncommon over $G$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2. -/
public theorem not_isUncommonOverFiniteGroup_one (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k : ℕ} (a : Fin k → ℤ) : ¬ IsUncommonOverFiniteGroup G a 1 := by
  rintro ⟨w, -, hw, hlt⟩
  have h1 : ∀ x, w 0 x = 1 := fun x => by simpa using hw x
  simp [h1] at hlt

/-- **Uncommon equations over the integers.** Let $a_1, \dots, a_k$ be integers and let $r$
be a natural number. For each $n$, write $[n]$ for the set of integers $1, \dots, n$ and
$S_n$ for the set of solutions $(x_1, \dots, x_k) \in [n]^k$ of
$a_1x_1 + \cdots + a_kx_k = 0$; for a colouring $\chi$ of the integers with $r$ colours, let
$M_\chi(n)$ be the number of solutions in $S_n$ whose entries all have the same colour.
The equation is $r$-uncommon over the integers when there is $\varepsilon > 0$ such that
for infinitely many $n$ some such colouring $\chi$ satisfies
$r^{k-1} M_\chi(n) < (1 - \varepsilon)|S_n|$, where $r^{k-1}$ is read as $1$ when $k = 0$.

For $k \ge 1$ this says that the equation is not $r$-common: it is not the case that every
$r$-colouring of $[n]$ has at least $(1 - o(1)) r^{1-k}|S_n|$ monochromatic solutions.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1 (`r`-common over the integers). -/
public def IsUncommonOverIntegers {k : ℕ} (a : Fin k → ℤ) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in Filter.atTop, ∃ χ : ℤ → Fin r,
    (r : ℝ) ^ (k - 1) *
        (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
          (fun x => ∑ i, a i * x i = 0 ∧ ∀ i j, χ (x i) = χ (x j))).card : ℝ) <
      (1 - ε) *
        (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
          (fun x => ∑ i, a i * x i = 0)).card : ℝ)

/-- **No equation is 1-uncommon over the integers.** For every $k \ge 0$ and all integers
$a_1, \dots, a_k$, the equation $a_1 x_1 + \dots + a_k x_k = 0$ is not $1$-uncommon over the
integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem not_isUncommonOverIntegers_one {k : ℕ} (a : Fin k → ℤ) :
    ¬ IsUncommonOverIntegers a 1 := by
  rintro ⟨ε, hε, h⟩
  obtain ⟨n, χ, hlt⟩ := h.exists
  simp only [Nat.cast_one, one_pow, one_mul] at hlt
  rw [Finset.filter_congr
    (fun x _ => and_iff_left (fun i j => Subsingleton.elim (χ (x i)) (χ (x j))))] at hlt
  have h0 : (0 : ℝ) ≤ _ := Nat.cast_nonneg
    (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
      (fun x => ∑ i, a i * x i = 0)).card)
  nlinarith

/-- **Uncommonness of odd-length equations over finite abelian groups.** Let $G$ be a
nontrivial finite abelian group, let $m \ge 1$, and let $a_1, \dots, a_{2m+1}$ be integers
each coprime to the order $|G|$. Then for every $r \ge 3$ the equation
$a_1x_1 + \cdots + a_{2m+1}x_{2m+1} = 0$ is $r$-uncommon over $G$.

Since $|G| \ge 2$, coprimality forces every $a_i$ to be nonzero.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Theorem 1 (`integers-2025-A88-thm-1`). -/
public theorem_wanted isUncommonOverFiniteGroup_of_odd (G : Type*) [AddCommGroup G]
    [Fintype G] [DecidableEq G] [Nontrivial G] (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ)
    (hcop : ∀ i, Nat.Coprime (a i).natAbs (Fintype.card G)) (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverFiniteGroup G a r

/-- **Uncommonness of odd-length equations over the integers.** Let $m \ge 1$ and let
$a_1, \dots, a_{2m+1}$ be nonzero integers, at least one negative and at least one positive.
Then for every $r \ge 3$ the equation $a_1x_1 + \cdots + a_{2m+1}x_{2m+1} = 0$ is
$r$-uncommon over the integers.

The sign condition excludes equations such as $x_1 + x_2 + x_3 = 0$, which have no solutions
in positive integers and for which the proportion of monochromatic solutions is undefined.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 1 (`integers-2025-A88-cor-1`). -/
public theorem_wanted isUncommonOverIntegers_of_odd (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ) (ha : ∀ i, a i ≠ 0) (hsign : ∃ i j, a i < 0 ∧ 0 < a j)
    (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r

/-- **Two-colour uncommonness over the integers extends to more colours.** Let
$k \ge 3$ and let $a_1, \dots, a_k$ be nonzero integers. If the equation
$a_1x_1 + \cdots + a_kx_k = 0$ is $2$-uncommon over the integers, then it is $r$-uncommon
over the integers for every $r \ge 3$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Theorem 2 (`integers-2025-A88-thm-2`). -/
public theorem_wanted isUncommonOverIntegers_of_two (k : ℕ) (hk : 3 ≤ k) (a : Fin k → ℤ)
    (ha : ∀ i, a i ≠ 0) (h2 : IsUncommonOverIntegers a 2) (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r

/-- **Uncommonness of even-length equations without a canceling partition.** Let $m \ge 2$
and let $a_1, \dots, a_{2m}$ be nonzero integers, at least one negative and at least one
positive, such that the equation $a_1x_1 + \cdots + a_{2m}x_{2m} = 0$ has no canceling
partition. Then this equation is $r$-uncommon over the integers for every $r \ge 2$.

The sign condition excludes equations such as $x_1 + x_2 + x_3 + x_4 = 0$, which has no
canceling partition and no solutions in positive integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 2 (`integers-2025-A88-cor-2`). -/
public theorem_wanted isUncommonOverIntegers_of_not_hasCancelingPartition (m : ℕ)
    (hm : 2 ≤ m) (a : Fin (2 * m) → ℤ) (ha : ∀ i, a i ≠ 0)
    (hsign : ∃ i j, a i < 0 ∧ 0 < a j) (hcan : ¬ HasCancelingPartition a) (r : ℕ)
    (hr : 2 ≤ r) :
    IsUncommonOverIntegers a r

/-- **Uncommonness of $x + 2y - z - 2w = 0$ over the integers.** For every $r \ge 2$,
the equation $x + 2y - z - 2w = 0$ is $r$-uncommon over the integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 2 (`integers-2025-A88-cor-2`). -/
public theorem_wanted isUncommonOverIntegers_one_two_neg_one_neg_two (r : ℕ) (hr : 2 ≤ r) :
    IsUncommonOverIntegers (![1, 2, -1, -2] : Fin 4 → ℤ) r

end

end MetaMathlibExt
