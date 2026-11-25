/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive

/-!
# Ehrhart series and unimodality

The Ehrhart function counts lattice points in dilates. Its generating series determines
the $h^*$-polynomial, whose coefficients can be tested for unimodality.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ehrhart function.** For a finite index set $\iota$, a set $P \subseteq \mathbb{R}^\iota$
and a natural number $t$, the Ehrhart function $L_P(t)$ is the number of integer vectors
$x \in \mathbb{Z}^\iota$ lying in the dilate $tP = \{t y : y \in P\}$, with the convention that
$L_P(t) = 0$ when there are infinitely many such vectors.

No boundedness of $P$ is needed for the definition. On $\mathbb{R}^d$ it agrees with the
lattice-point enumerator of $P$ at the real dilate $t$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public noncomputable def ehrhart {ι : Type*} [Fintype ι]
    (P : Set (ι → ℝ)) (t : ℕ) : ℕ :=
  Set.ncard {x : ι → ℤ | IsLatticePoint (polytopeDilate t P) x}

/-- **The $h^*$-polynomial.** Let $P \subseteq \mathbb{R}^n$, with coordinates indexed by a finite
set of size $n$, and let $L_P(t)$ be the number of lattice points of the dilate
$tP = \{t y : y \in P\}$ (taken to be $0$ if there are infinitely many). A polynomial
$h \in \mathbb{Z}[z]$ is an $h^*$-polynomial of $P$ when
$$\Big(\sum_{t \ge 0} L_P(t)\, z^t\Big) (1 - z)^{n+1} = h(z)$$
as formal power series with integer coefficients.

The exponent uses the ambient dimension $n$, which is $\dim P$ when $P$ is full dimensional, and
$h^*$ is characterised by this identity rather than by the explicit formula for weighted simplices.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public def IsHStarPolynomial {ι : Type*} [Fintype ι]
    (P : Set (ι → ℝ)) (h : Polynomial ℤ) : Prop :=
  PowerSeries.mk (fun t => (ehrhart P t : ℤ)) *
      (1 - PowerSeries.X) ^ (Fintype.card ι + 1) = (h : PowerSeries ℤ)

/-- **Unimodal polynomials.** A polynomial $p = \sum_k a_k z^k \in \mathbb{Z}[z]$ of degree $n$
(with $n = 0$ for $p = 0$) is unimodal when there is an index $t \le n$ such that
$a_0 \le a_1 \le \dots \le a_t$ and $a_t \ge a_{t+1} \ge \dots \ge a_n$.

The paper considers polynomials with nonnegative coefficients; the order condition itself is
stated over $\mathbb{Z}$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def IsUnimodal (p : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, t ≤ p.natDegree ∧
    (∀ i j : ℕ, i ≤ j → j ≤ t → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → j ≤ p.natDegree → p.coeff j ≤ p.coeff i)

end

end MetaMathlibExt
