/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexCoefficients
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexEhrhart
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexIDP
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexOneSupported
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive
public import MathlibExt.Geometry.LatticePointEnumerator

/-!
# The integer decomposition property and weighted projective space simplices (statements)

Statement-only targets from Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and
Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, for the
simplices `Δ_(1,q) = conv(e_1, …, e_n, -∑ q_i e_i)`. IDP, reflexivity, the Ehrhart function and
the `h*`-polynomial are defined geometrically (not by the paper's number-theoretic criteria), so
Theorems 1, 4 and 5 relate independent notions.
-/

namespace MetaMathlibExt

open Filter

@[expose] public section

/-! ## Basic geometric and enumerative definitions -/

/-- **$h^*$-unimodal polytopes.** Let $P \subseteq \mathbb{R}^n$, with coordinates indexed by a
finite set of size $n$, and let $L_P(t)$ be the number of lattice points of the dilate
$tP = \{t y : y \in P\}$ (taken to be $0$ if there are infinitely many). Then $P$ is
$h^*$-unimodal when there is a unimodal polynomial $h \in \mathbb{Z}[z]$ with
$$\Big(\sum_{t \ge 0} L_P(t)\, z^t\Big) (1 - z)^{n+1} = h(z)$$
as formal power series, that is, an $h^*$-polynomial of $P$ that is unimodal.

The identity determines $h$, so this says that the $h^*$-polynomial of $P$ exists and is unimodal;
it is not built from the explicit formula for weighted simplices.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def IsHStarUnimodal {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∃ h : Polynomial ℤ, IsHStarPolynomial P h ∧ IsUnimodal h

/-! ## Weight and support notation -/

/-- **The integer $\ell$ of support data.** For tuples $r = (r_1, \dots, r_d)$ and
$x = (x_1, \dots, x_d)$ of natural numbers, let $L = \operatorname{lcm}(r_1, \dots, r_d)$, with
$L = 1$ when $d = 0$. Then $\ell(r, x)$ is the natural-number quotient
$\lfloor (1 + \sum_{i=1}^{d} x_i r_i) / L \rfloor$, taken to be $0$ when $L = 0$.

Under the reflexivity hypothesis of the results that use $\ell$, $L$ divides
$1 + \sum_i x_i r_i$, so the division is exact.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public def setupEll {d : ℕ} (r x : Fin d → ℕ) : ℕ :=
  (1 + ∑ i, x i * r i) / weightLcm (List.ofFn r)

/-- **The $h^*$ formula of a weight vector.** For a list $q = (q_1, \dots, q_n)$ of natural
numbers, put $|q| = q_1 + \dots + q_n$ and define the weight statistic
$w(q,b) = b - \sum_{i=1}^n \lfloor q_i b / (1 + |q|) \rfloor$. The $h^*$ formula of $q$ is the
integer polynomial $\sum_{b=0}^{|q|} z^{w(q,b)}$.

The polynomial is defined separately from the Ehrhart-series condition. For positive weights,
Theorem 2.2 of Braun, Davis, and Solus identifies it as the Ehrhart numerator.

Source: Benjamin Braun, Robert Davis, and Liam Solus, *Detecting the integer decomposition
property and Ehrhart unimodality in reflexive simplices*, Adv. in Appl. Math. 100 (2018),
122–142, Theorem 2.2; restated by Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and
Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*,
INTEGERS 24 (2024), Article A60, Theorem 5. -/
public noncomputable def hStarFormula (q : List ℕ) : Polynomial ℤ :=
  ∑ b ∈ Finset.range (q.sum + 1), Polynomial.X ^ weightStatistic q b

/-- **The exponent $u(\alpha)$ of support data.** For tuples $r = (r_1, \dots, r_d)$ and
$x = (x_1, \dots, x_d)$ of natural numbers and a natural number $\alpha$, let $\ell = \ell(r, x)$
be the integer of the support data and $s_1, \dots, s_d$ its complementary factors. Then
$u(\alpha) = \alpha \ell - \sum_{i=1}^{d} x_i \lfloor \alpha / s_i \rfloor$, computed in the
natural numbers: the subtraction is truncated at $0$, and $\lfloor \alpha / s_i \rfloor$ is
taken to be $0$ when $s_i = 0$.

The results that use $u$ assume valid support data and reflexivity.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 6. -/
public def setupU {d : ℕ} (r x : Fin d → ℕ) (α : ℕ) : ℕ :=
  α * setupEll r x - ∑ i, x i * (α / setupS r i)

/-- **The polynomial $g_r^x$.** For tuples $r = (r_1, \dots, r_d)$ and $x = (x_1, \dots, x_d)$
of natural numbers, let $L = \operatorname{lcm}(r_1, \dots, r_d)$, with $L = 1$ when $d = 0$, and
let $u(\alpha)$ be the exponent of the support data $(r, x)$ at $\alpha$. Then $g_r^x$ is the
polynomial with integer coefficients $g_r^x(z) = \sum_{\alpha = 0}^{L - 1} z^{u(\alpha)}$, which
is $0$ when $L = 0$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 6. -/
public noncomputable def setupG {d : ℕ} (r x : Fin d → ℕ) : Polynomial ℤ :=
  ∑ α ∈ Finset.range (weightLcm (List.ofFn r)), Polynomial.X ^ setupU r x α

/-- **IDP-necessary condition.** A vector of natural-number weights $q = (q_1, \dots, q_n)$
satisfies the IDP-necessary condition when $1 + \sum_{i=1}^n (q_i \bmod q_j) = q_j$ for every
$j$, where $q_i \bmod q_j$ is the remainder of $q_i$ on division by $q_j$ (with the convention
$q_i \bmod 0 = q_i$).

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public def SatisfiesIDPNecessary {n : ℕ} (q : Fin n → ℕ) : Prop :=
  ∀ j, 1 + ∑ i, q i % q j = q j

/-! ## Theorems 1--9 -/

/-- **Reflexivity criterion in support form.** Let $d \ge 1$, let $r_1, \dots, r_d$ be pairwise
distinct natural numbers with $r_i \ge 1$, and let $x_1, \dots, x_d$ be natural numbers with
$x_i \ge 1$. Let $q = (r_1^{x_1}, \dots, r_d^{x_d})$ be the weight vector in which each $r_i$ is
repeated $x_i$ times, in this order. The weighted projective simplex with weights $q$ is
reflexive if and only if $\operatorname{lcm}(r_1, \dots, r_d)$ divides
$1 + \sum_{i=1}^d x_i r_i$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public theorem_wanted reflexive_support_iff_lcm_dvd {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x) :
    IsReflexive (weightedSimplexList (expandSupport r x)) ↔
      weightLcm (List.ofFn r) ∣ 1 + ∑ i, x i * r i

/-- **Affine free sum.** For sets $P \subseteq \mathbb{R}^n$ and $Q \subseteq \mathbb{R}^m$ and a
point $v \in \mathbb{R}^m$, the affine free sum $P *_v Q \subseteq \mathbb{R}^n \times \mathbb{R}^m$
is the convex hull of $(P \times \{0\}) \cup (\{0\} \times (Q - v))$, where
$Q - v = \{y - v : y \in Q\}$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def affineFreeSum {n m : ℕ} (P : Set (Fin n → ℝ)) (Q : Set (Fin m → ℝ))
    (v : Fin m → ℝ) : Set (Sum (Fin n) (Fin m) → ℝ) :=
  convexHull ℝ
    (Set.image (fun p => Sum.elim p (fun _ => 0)) P ∪
      Set.image (fun q => Sum.elim (fun _ => 0) (q - v)) Q)

/-- **Negative weight vertex.** For natural-number weights $q = (q_1, \dots, q_n)$, the negative
weight vertex is the point $v_0 = -\sum_{i=1}^n q_i e_i$ of $\mathbb{R}^n$, whose $i$th coordinate
is $-q_i$; here $e_1, \dots, e_n$ is the standard basis of $\mathbb{R}^n$.

The weighted projective simplex with weights $q$ is the convex hull of $e_1, \dots, e_n$ and $v_0$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def negativeWeightVertex {n : ℕ} (q : Fin n → ℕ) : Fin n → ℝ :=
  fun i => -(q i : ℝ)

/-- **Affine free sums of IDP weighted simplices at the negative weight vertex of a reflexive
summand are IDP.** Let $q = (q_1, \dots, q_n)$ and $p = (p_1, \dots, p_m)$ be tuples of natural
numbers, let $\Delta_{(1,q)} \subseteq \mathbb{R}^n$ and $\Delta_{(1,p)} \subseteq \mathbb{R}^m$
be the weighted projective space simplices of $q$ and $p$, and let $v_0 = -\sum_{i=1}^m p_i e_i$
be the negative weight vertex of $\Delta_{(1,p)}$, where $e_1, \dots, e_m$ is the standard basis
of $\mathbb{R}^m$. Let
$\Delta_{(1,q)} \ast_{v_0} \Delta_{(1,p)} \subseteq \mathbb{R}^n \times \mathbb{R}^m$ be the
affine free sum, the convex hull of
$(\Delta_{(1,q)} \times \{0\}) \cup (\{0\} \times (\Delta_{(1,p)} - v_0))$. If $\Delta_{(1,p)}$ is
reflexive and has the integer decomposition property and $\Delta_{(1,q)}$ has the integer
decomposition property, then $\Delta_{(1,q)} \ast_{v_0} \Delta_{(1,p)}$ has the integer
decomposition property.

Lattice points of $\mathbb{R}^n \times \mathbb{R}^m$ are the points of
$\mathbb{Z}^n \times \mathbb{Z}^m$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public theorem_wanted affineFreeSum_idp {n m : ℕ} (q : Fin n → ℕ) (p : Fin m → ℕ)
    (hpRef : IsReflexive (weightedSimplex p)) (hpIDP : HasIDP (weightedSimplex p))
    (hqIDP : HasIDP (weightedSimplex q)) :
    HasIDP (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p))

/-- **Affine free sums of weighted simplices at the negative weight vertex preserve reflexivity,
IDP and $h^\ast$-unimodality.** Let $q = (q_1, \dots, q_n)$ and $p = (p_1, \dots, p_m)$ be tuples
of natural numbers, let $\Delta_{(1,q)} \subseteq \mathbb{R}^n$ and
$\Delta_{(1,p)} \subseteq \mathbb{R}^m$ be the weighted projective space simplices of $q$ and $p$,
and let $v_0 = -\sum_{i=1}^m p_i e_i$ be the negative weight vertex of $\Delta_{(1,p)}$, where
$e_1, \dots, e_m$ is the standard basis of $\mathbb{R}^m$. Let
$\Delta_{(1,q)} \ast_{v_0} \Delta_{(1,p)} \subseteq \mathbb{R}^n \times \mathbb{R}^m$ be the
affine free sum, the convex hull of
$(\Delta_{(1,q)} \times \{0\}) \cup (\{0\} \times (\Delta_{(1,p)} - v_0))$. If $\Delta_{(1,q)}$
and $\Delta_{(1,p)}$ are both reflexive, both have the integer decomposition property and are
both $h^*$-unimodal, then $\Delta_{(1,q)} \ast_{v_0} \Delta_{(1,p)}$ is reflexive, has the
integer decomposition property and is $h^*$-unimodal.

Lattice points of $\mathbb{R}^n \times \mathbb{R}^m$ are the points of
$\mathbb{Z}^n \times \mathbb{Z}^m$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public theorem_wanted affineFreeSum_reflexive_idp_hStarUnimodal {n m : ℕ}
    (q : Fin n → ℕ) (p : Fin m → ℕ)
    (hqRef : IsReflexive (weightedSimplex q)) (hpRef : IsReflexive (weightedSimplex p))
    (hqIDP : HasIDP (weightedSimplex q)) (hpIDP : HasIDP (weightedSimplex p))
    (hqUni : IsHStarUnimodal (weightedSimplex q))
    (hpUni : IsHStarUnimodal (weightedSimplex p)) :
    IsReflexive (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p)) ∧
    HasIDP (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p)) ∧
    IsHStarUnimodal (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p))

/-- **Finitely many reflexive IDP multiplicity vectors.** Let $r_1 < r_2 < \dots < r_d$ be
positive integers such that $r_j \nmid r_d$ for some $j < d$. Then there are only finitely
many vectors $x = (x_1, \dots, x_d)$ of positive integers for which the weighted projective
simplex $\Delta_{(1,q)}$ is reflexive and has the integer decomposition property, where
$q = (r_1^{x_1}, \dots, r_d^{x_d})$ consists of $x_1$ copies of $r_1$, then $x_2$ copies of
$r_2$, and so on, ending with $x_d$ copies of $r_d$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 3. -/
public theorem_wanted finite_idp_reflexive_multiplicities {d : ℕ} (r : Fin d → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hrinc : StrictMono r)
    (hndvd : ∃ j : Fin d, ∃ h : j.val + 1 < d,
      ¬r j ∣ r ⟨d - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) (by omega)⟩) :
    {x : Fin d → ℕ | (∀ i, 1 ≤ x i) ∧
      IsReflexive (weightedSimplexList (expandSupport r x)) ∧
      HasIDP (weightedSimplexList (expandSupport r x))}.Finite

/-- **Floor criterion for IDP of reflexive weighted simplices.** Let $q = (q_1, \dots, q_n)$ be
positive integers such that the weighted simplex
$\Delta_{(1,q)} = \operatorname{conv}(e_1, \dots, e_n, -\sum_i q_i e_i) \subseteq \mathbb{R}^n$ is
reflexive, and for each $j$ write $S_j = \sum_{i \ne j} q_i$. Then $\Delta_{(1,q)}$ has the
integer decomposition property if and only if the following holds for every $j$: for every
integer $b$ with $1 \le b < q_j$ and

$$b \lfloor (1 + S_j) / q_j \rfloor - \sum_{i \ne j} \lfloor b q_i / q_j \rfloor \ge 2$$

there is an integer $c$ with $1 \le c < b$ such that
$\lfloor b q_i / q_j \rfloor - \lfloor c q_i / q_j \rfloor = \lfloor (b - c) q_i / q_j \rfloor$
for every $i \ne j$ and

$$c \lfloor (1 + S_j) / q_j \rfloor - \sum_{i \ne j} \lfloor c q_i / q_j \rfloor = 1.$$

All differences are taken in the natural numbers, truncated at $0$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 4. -/
public theorem_wanted idp_reflexive_floor_characterization {n : ℕ} (q : Fin n → ℕ)
    (hq : ∀ i, 1 ≤ q i) (href : IsReflexive (weightedSimplex q)) :
    HasIDP (weightedSimplex q) ↔
      ∀ j, ∀ b : ℕ, 1 ≤ b → b < q j →
        2 ≤ b * ((1 + ∑ i ∈ Finset.univ.erase j, q i) / q j) -
          ∑ i ∈ Finset.univ.erase j, b * q i / q j →
        ∃ c : ℕ, 1 ≤ c ∧ c < b ∧
          (∀ i ∈ Finset.univ.erase j,
            b * q i / q j - c * q i / q j = (b - c) * q i / q j) ∧
          c * ((1 + ∑ i ∈ Finset.univ.erase j, q i) / q j) -
            ∑ i ∈ Finset.univ.erase j, c * q i / q j = 1

/-- **A necessary condition for IDP reflexive weighted simplices.** Let $q = (q_1, \dots, q_n)$
be natural numbers. If the weighted simplex
$\Delta_{(1,q)} = \operatorname{conv}(e_1, \dots, e_n, -\sum_i q_i e_i) \subseteq \mathbb{R}^n$ is
reflexive and has the integer decomposition property, then
$1 + \sum_{i=1}^n (q_i \bmod q_j) = q_j$ for every $j$.

Here $a \bmod b$ is the remainder of $a$ on division by $b$, with the convention $a \bmod 0 = a$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public theorem_wanted idp_reflexive_implies_necessary {n : ℕ} (q : Fin n → ℕ)
    (href : IsReflexive (weightedSimplex q)) (hidp : HasIDP (weightedSimplex q)) :
    SatisfiesIDPNecessary q

/-- **The $h^*$-polynomial of a weighted projective space simplex.** Let $q = (q_1, \dots, q_n)$
be a list of positive integers, let $\Delta_{(1,q)} \subset \mathbb{R}^n$ be the weighted
projective space simplex, and let $L(t)$ be the number of lattice points in its $t$-th dilate
$t \Delta_{(1,q)}$. Then, as formal power series over $\mathbb{Z}$,
$$\Big(\sum_{t \ge 0} L(t) z^t\Big)(1 - z)^{n+1} = \sum_{b=0}^{q_1 + \cdots + q_n} z^{w(q,b)},$$
where $w(q, b) = b - \sum_{i=1}^{n} \lfloor q_i b / (1 + q_1 + \cdots + q_n) \rfloor$ is the
weight statistic.

Source: Benjamin Braun, Robert Davis, and Liam Solus, *Detecting the integer decomposition
property and Ehrhart unimodality in reflexive simplices*, Adv. in Appl. Math. 100 (2018),
122–142, Theorem 2.2; restated by Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and
Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*,
INTEGERS 24 (2024), Article A60, Theorem 5. -/
public theorem_wanted weightedSimplex_hStar_formula (q : List ℕ) (hq : ∀ a ∈ q, 1 ≤ a) :
    IsHStarPolynomial (weightedSimplexList q) (hStarFormula q)

/-- **Geometric factorization of the $h^*$ formula.** Let $d \ge 1$, let $r_1, \dots, r_d$ be
pairwise distinct positive integers, let $x_1, \dots, x_d$ be positive integers, and let
$q = (r_1^{x_1}, \dots, r_d^{x_d})$ be the list in which each $r_i$ is repeated $x_i$ times.
Suppose that the weighted simplex $\Delta_{(1,q)}$, the convex hull of the standard basis vectors
and $-q$, is reflexive. Put $L = \operatorname{lcm}(r_1, \dots, r_d)$,
$\ell = \lfloor (1 + \sum_i x_i r_i) / L \rfloor$, $s_i = L / r_i$ and
$u(\alpha) = \alpha \ell - \sum_i x_i \lfloor \alpha / s_i \rfloor$, and let
$g_r^x(z) = \sum_{0 \le \alpha < L} z^{u(\alpha)}$. Then the $h^*$ formula of $q$ equals
$(\sum_{0 \le t < \ell} z^t) \, g_r^x(z)$.

The subtraction in $u(\alpha)$ is truncated at $0$, as in the natural numbers. Reflexivity
supplies exactness of $\ell$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 6. -/
public theorem_wanted hStar_geometric_factorization {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x)
    (href : IsReflexive (weightedSimplexList (expandSupport r x))) :
    hStarFormula (expandSupport r x) =
      (∑ t ∈ Finset.range (setupEll r x), Polynomial.X ^ t) * setupG r x

/-- **Multiplicity bounds for IDP reflexive weighted simplices.** Let $r_1 < r_2 < \dots < r_d$
be positive integers, let $x_1, \dots, x_d$ be positive integers, and let
$q = (r_1^{x_1}, \dots, r_d^{x_d})$ be the weight vector in which each $r_i$ is repeated $x_i$
times. Suppose the weighted projective space simplex $\Delta_{(1,q)}$ is reflexive and has the
integer decomposition property. Then $x_i \le \lfloor r_{i+1} / r_i \rfloor$ for every $i < d$,
and for every $j < d$ with $r_j \nmid r_d$ we have $x_d \le \lfloor r_j / (r_d \bmod r_j) \rfloor$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 7. -/
public theorem_wanted idp_reflexive_multiplicity_bounds {d : ℕ} (r x : Fin d → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r)
    (href : IsReflexive (weightedSimplexList (expandSupport r x)))
    (hidp : HasIDP (weightedSimplexList (expandSupport r x))) :
    (∀ i : Fin d, ∀ h : i.val + 1 < d,
      x i ≤ r ⟨i.val + 1, h⟩ / r i) ∧
    (∀ j : Fin d, ∀ h : j.val + 1 < d,
      let last : Fin d := ⟨d - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) (by omega)⟩
      ¬r j ∣ r last → x last ≤ r j / (r last % r j))

/-- **IDP reflexive two-supported weighted simplices.** Let $r = (r_1, r_2)$ and
$x = (x_1, x_2)$ be pairs of positive integers with $r_1 < r_2$, and let
$q = (r_1^{x_1}, r_2^{x_2})$ be the weight vector consisting of $r_1$ repeated $x_1$ times
followed by $r_2$ repeated $x_2$ times. The weighted projective space simplex $\Delta_{(1,q)}$ is
reflexive and has the integer decomposition property if and only if
$1 + \sum_{i=1}^{2} x_i (r_i \bmod r_j) = r_j$ for $j = 1, 2$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 8. -/
public theorem_wanted two_supported_idp_reflexive_iff_necessary (r x : Fin 2 → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r) :
    (IsReflexive (weightedSimplexList (expandSupport r x)) ∧
      HasIDP (weightedSimplexList (expandSupport r x))) ↔
      SatisfiesSupportIDPNecessary r x

/-- **Support triples of the three-supported classification.** For a case index $c \in \mathbb{N}$,
natural numbers $k, s$ and a triple $x = (x_1, x_2, x_3)$ of natural numbers, the support triple
$F_c(k, s; x) \in \mathbb{N}^3$ is defined case by case, and $k, s$ enter only when $c \ge 7$.
For $c = 0$ it is $(1, 1 + x_1, (1 + x_1)(1 + x_2))$. For $c = 1$ it is
$(1 + x_2, 1 + x_1(1 + x_2), (1 + x_1(1 + x_2))(1 + x_2))$. For $c = 2$ it is
$((1 + x_2)(1 + x_3), 1 + x_1(1 + x_2)(1 + x_3), (1 + x_1(1 + x_2)(1 + x_3))(1 + x_2))$.
For $c = 3$ it is $(1, (1 + x_1)(1 + x_3), (1 + x_1)(1 + x_2(1 + x_3)))$. For $c = 4$ it is
$(1 + (1 + x_3)x_2, (1 + x_3)(1 + x_1(1 + (1 + x_3)x_2)),
(1 + (1 + (1 + x_3)x_2)x_1)(1 + (1 + x_3)x_2))$. For $c = 5$ it is
$((1 + x_3)(1 + (1 + x_3)x_2), (1 + x_3)(1 + x_1(1 + x_3)(1 + (1 + x_3)x_2)),
(1 + (1 + x_3)(1 + (1 + x_3)x_2)x_1)(1 + (1 + x_3)x_2))$. For $c = 6$ it is
$(1 + x_3, (1 + x_3)(1 + x_1(1 + x_3)), (1 + (1 + x_3)x_1)(1 + (1 + x_3)x_2))$. For every
$c \ge 7$ it is
$(1 + kx_2, (skx_2 + s + k)(1 + x_1(1 + kx_2)), (1 + x_1(1 + kx_2))(1 + x_2(skx_2 + s + k)))$.

The cases $c = 0, \dots, 6$ are forms (i)–(vii) of the source's Theorem 9 and $c \ge 7$ is form
(viii).

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public def threeSupportFamily (case k s : ℕ) (x : Fin 3 → ℕ) : Fin 3 → ℕ :=
  match case with
  | 0 => ![1, 1 + x 0, (1 + x 0) * (1 + x 1)]
  | 1 => ![1 + x 1, 1 + x 0 * (1 + x 1),
      (1 + x 0 * (1 + x 1)) * (1 + x 1)]
  | 2 => ![(1 + x 1) * (1 + x 2),
      1 + x 0 * (1 + x 1) * (1 + x 2),
      (1 + x 0 * (1 + x 1) * (1 + x 2)) * (1 + x 1)]
  | 3 => ![1, (1 + x 0) * (1 + x 2),
      (1 + x 0) * (1 + x 1 * (1 + x 2))]
  | 4 => ![1 + (1 + x 2) * x 1,
      (1 + x 2) * (1 + x 0 * (1 + (1 + x 2) * x 1)),
      (1 + (1 + (1 + x 2) * x 1) * x 0) * (1 + (1 + x 2) * x 1)]
  | 5 => ![(1 + x 2) * (1 + (1 + x 2) * x 1),
      (1 + x 2) * (1 + x 0 * (1 + x 2) * (1 + (1 + x 2) * x 1)),
      (1 + (1 + x 2) * (1 + (1 + x 2) * x 1) * x 0) *
        (1 + (1 + x 2) * x 1)]
  | 6 => ![1 + x 2, (1 + x 2) * (1 + x 0 * (1 + x 2)),
      (1 + (1 + x 2) * x 0) * (1 + (1 + x 2) * x 1)]
  | _ => ![1 + k * x 1,
      (s * k * x 1 + s + k) * (1 + x 0 * (1 + k * x 1)),
      (1 + x 0 * (1 + k * x 1)) * (1 + x 1 * (s * k * x 1 + s + k))]

/-- **Classification of three-supported vectors satisfying the necessary condition.** For
$c, k, s \in \mathbb{N}$ and $x \in \mathbb{N}^3$, write $F_c(k, s; x)$ for the support triple of
case $c$ with parameters $k, s$ in the three-supported classification. Let $r = (r_1, r_2, r_3)$
and $x = (x_1, x_2, x_3)$ be triples of positive integers with $r_1 < r_2 < r_3$, and suppose that
$1 + \sum_{i=1}^{3} x_i (r_i \bmod r_j) = r_j$ for every $j$ (the support form of the IDP
necessary condition). Then either $r = F_c(0, 0; x)$ for some $c \in \{0, \dots, 6\}$, or there
are integers $k, s \ge 1$ with $x_3 = skx_2 + s - k + 1$ and $r = F_7(k, s; x)$.

Only this direction is stated: the case $c = 7$ with $x = (1, 1, 2)$, $k = 2$, $s = 1$ gives
$r = (3, 20, 24)$, which fails the necessary condition.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public theorem_wanted three_supported_classification (r x : Fin 3 → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r) :
    SatisfiesSupportIDPNecessary r x →
      (∃ c : Fin 7, r = threeSupportFamily c.val 0 0 x) ∨
      (∃ k s : ℕ, 1 ≤ k ∧ 1 ≤ s ∧ x 2 = s * k * x 1 + s - k + 1 ∧
        r = threeSupportFamily 7 k s x)

/-- **Cases (i)–(vii) of the three-support family give IDP reflexive simplices.** Let
$x = (x_1, x_2, x_3)$ be positive integers, and let $r = (r_1, r_2, r_3)$ be the support triple
of any one of the first seven cases, (i)–(vii), of the three-support family with parameters $x$.
Let $q = (r_1^{x_1}, r_2^{x_2}, r_3^{x_3})$ be the list in which each $r_i$ is repeated $x_i$
times. Then the weighted simplex $\Delta_{(1,q)}$, the convex hull of the standard basis vectors
and $-q$, is reflexive and has the integer decomposition property.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public theorem_wanted first_seven_three_supported_families_are_idp (x : Fin 3 → ℕ)
    (hxpos : ∀ i, 1 ≤ x i) (c : Fin 7) :
    IsReflexive (weightedSimplexList (expandSupport (threeSupportFamily c.val 0 0 x) x)) ∧
    HasIDP (weightedSimplexList (expandSupport (threeSupportFamily c.val 0 0 x) x))

/-- **Case (viii) of the three-supported classification is reflexive but not IDP.** Let
$x_1, x_2, x_3$ and $k, s$ be positive integers with $x_3 = skx_2 + s - k + 1$, and put
$r_1 = 1 + kx_2$, $r_2 = (skx_2 + s + k)(1 + x_1(1 + kx_2))$ and
$r_3 = (1 + x_1(1 + kx_2))(1 + x_2(skx_2 + s + k))$. Suppose that
$1 + \sum_{i=1}^{3} x_i (r_i \bmod r_j) = r_j$ for $j = 1, 2, 3$. Let $q$ be the weight vector
$(r_1^{x_1}, r_2^{x_2}, r_3^{x_3})$, consisting of $x_1$ copies of $r_1$, then $x_2$ copies of
$r_2$, then $x_3$ copies of $r_3$. Then the weighted projective simplex $\Delta_{(1,q)}$ is
reflexive and does not have the integer decomposition property.

The hypothesis $1 + \sum_i x_i (r_i \bmod r_j) = r_j$ is kept because the equation for $x_3$
alone need not imply it.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public theorem_wanted eighth_three_supported_family_is_not_idp (x : Fin 3 → ℕ) (k s : ℕ)
    (hxpos : ∀ i, 1 ≤ x i) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hx3 : x 2 = s * k * x 1 + s - k + 1)
    (hnecessary : SatisfiesSupportIDPNecessary (threeSupportFamily 7 k s x) x) :
    IsReflexive (weightedSimplexList (expandSupport (threeSupportFamily 7 k s x) x)) ∧
    ¬HasIDP (weightedSimplexList (expandSupport (threeSupportFamily 7 k s x) x))

/-! ## Reflexive stabilizations and Theorems 10--13 -/

/-- **Higher reflexive stabilizations.** For a list of natural-number weights
$q = (q_1, \dots, q_n)$ and a natural number $m$, the $m$th reflexive stabilization of $q$ is the
list $\mathrm{rs}(q, m) = (1^k, q_1, \dots, q_n)$ obtained by prepending $k$ entries equal to $1$,
where $k = \mathrm{rsn}(q) + (m - 1) \operatorname{lcm}(q)$. Here $\mathrm{rsn}(q)$ is the
reflexive stabilization number of $q$, $\operatorname{lcm}(q)$ is the least common multiple of
the weights (equal to $1$ for the empty list), and the subtraction $m - 1$ is truncated at $0$,
so $\mathrm{rs}(q, 0) = \mathrm{rs}(q, 1)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public noncomputable def reflexiveStabilizationAt (q : List ℕ) (m : ℕ) : List ℕ :=
  List.replicate (reflexiveStabilizationNumber q + (m - 1) * weightLcm q) 1 ++ q

/-- **Higher reflexive stabilizations are not IDP.** Let $q = (q_1, \dots, q_n)$ be a nonempty
list of integers with $q_i \ge 2$ for all $i$, and let $m \ge 2$. Let $\operatorname{rsn}(q)$ be
the least $k$ for which the weighted simplex of $(1^k, q)$, the list $q$ preceded by $k$ ones, is
reflexive, and let
$\operatorname{rs}(q,m) = (1^{\operatorname{rsn}(q) + (m-1)\operatorname{lcm}(q)}, q)$ be the
$m$th reflexive stabilization. Then the weighted simplex $\Delta_{(1,\operatorname{rs}(q,m))}$,
the convex hull of the standard basis vectors and $-\operatorname{rs}(q,m)$, does not have the
integer decomposition property.

Nonemptiness is the paper's $q \in \mathbb{Z}^n_{\ge 1}$, $n \ge 1$: for the empty list,
$\operatorname{rs}((),2) = (1)$ gives the interval $[-1,1]$, which has IDP.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public theorem_wanted higher_reflexive_stabilizations_not_idp (q : List ℕ)
    (hne : q ≠ []) (hq : ∀ a ∈ q, 2 ≤ a) (m : ℕ) (hm : 2 ≤ m) :
    ¬HasIDP (weightedSimplexList (reflexiveStabilizationAt q m))

/-- **Large reflexive stabilizations of weights at least $2$ with lcm at least $3$ are not
$h^\ast$-unimodal.** Let $q = (q_1, \dots, q_n)$ be a list of natural numbers with $q_i \ge 2$
for every $i$ and $\operatorname{lcm}(q) \ge 3$. For $m \in \mathbb{N}$ let
$\operatorname{rs}(q, m)$ be the $m$th reflexive stabilization of $q$, let
$\Delta_{(1,\operatorname{rs}(q,m))}$ be its weighted projective space simplex, and let
$h_m \in \mathbb{Z}[z]$ be the $h^\ast$ formula of $\operatorname{rs}(q, m)$. Then for all
sufficiently large $m$, the simplex $\Delta_{(1,\operatorname{rs}(q,m))}$ is not
$h^\ast$-unimodal, and the coefficient of $z^k$ in $h_m$ is $1$ or $2$ for every $k$ with
$0 \le k \le \deg h_m$.

The hypothesis $\operatorname{lcm}(q) \ge 3$ is the journal version's. The arXiv version omits
it, and then $q = (2)$ is a counterexample: its stabilizations have $h^\ast$-vector
$(1, \dots, 1, 2, 1, \dots, 1)$, which is unimodal.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 11. -/
public theorem_wanted stabilization_eventually_not_unimodal_coefficients_one_or_two
    (q : List ℕ) (hq : ∀ a ∈ q, 2 ≤ a) (hlcm : 3 ≤ weightLcm q) :
    ∀ᶠ m in atTop,
      ¬IsHStarUnimodal (weightedSimplexList (reflexiveStabilizationAt q m)) ∧
      ∀ k : ℕ, k ≤ (hStarFormula (reflexiveStabilizationAt q m)).natDegree →
        (hStarFormula (reflexiveStabilizationAt q m)).coeff k = 1 ∨
          (hStarFormula (reflexiveStabilizationAt q m)).coeff k = 2

/-- **The first reflexive stabilization adds one monomial to the $h^*$-formula.** Let
$q = (q_1, \dots, q_n)$ be a list of natural numbers whose reflexive stabilization number is
$1$, so that its first reflexive stabilization is $\operatorname{rs}(q) = (1, q_1, \dots, q_n)$.
For a list $p = (p_1, \dots, p_m)$ of natural numbers put $|p| = p_1 + \dots + p_m$, let
$\ell(p) = \lfloor (1 + |p|) / \operatorname{lcm}(p) \rfloor$ (taken to be $0$ when
$\operatorname{lcm}(p) = 0$), let
$w(p, b) = b - \sum_{i=1}^{m} \lfloor p_i b / (1 + |p|) \rfloor$ be its weight statistic, and let
$h_p(z) = \sum_{b=0}^{|p|} z^{w(p, b)} \in \mathbb{Z}[z]$ be its explicit $h^*$-formula. Suppose
that $\ell(\operatorname{rs}(q)) = 1$. Then $h_{\operatorname{rs}(q)}(z) = h_q(z) + z^{n+1}$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public theorem_wanted stabilization_hStar_add_monomial (q : List ℕ)
    (hrsn : reflexiveStabilizationNumber q = 1)
    (hell : listEll (reflexiveStabilization q) = 1) :
    hStarFormula (reflexiveStabilization q) =
      hStarFormula q + Polynomial.X ^ (q.length + 1)

/-- **Lattice points of the cone over a polytope.** For a set $P \subseteq \mathbb{R}^n$, a pair
$(t, w)$ with $t \in \mathbb{N}$ and $w \in \mathbb{Z}^n$ is a lattice point of the cone over $P$
when $w$ is a lattice point of the dilate $tP = \{t y : y \in P\}$.

For a convex polytope $P$ the slice of the cone over $P$ at height $t$ is $tP$, so this describes
the lattice points of the cone height by height, as in the definition of the integer
decomposition property.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def IsConeLatticePoint {n : ℕ} (P : Set (Fin n → ℝ))
    (a : ℕ × (Fin n → ℤ)) : Prop := IsLatticePoint (polytopeDilate a.1 P) a.2

/-- **Hilbert basis elements of the cone over a polytope.** Let $P \subseteq \mathbb{R}^n$. A pair
$a = (t, w)$ with $t \in \mathbb{N}$ and $w \in \mathbb{Z}^n$ is a Hilbert basis element of the
cone over $P$ when $a$ is a lattice point of that cone (that is, $w$ is a lattice point of
$tP = \{t y : y \in P\}$), $a \ne 0$, and $a$ is irreducible: whenever $a = b + c$ with $b$ and
$c$ lattice points of the cone over $P$, we have $b = 0$ or $c = 0$.

For a lattice polytope the cone is pointed, and its irreducible lattice points are exactly the
minimal generating set, the Hilbert basis, of the monoid of lattice points of the cone.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def IsHilbertBasisElement {n : ℕ} (P : Set (Fin n → ℝ))
    (a : ℕ × (Fin n → ℤ)) : Prop :=
  IsConeLatticePoint P a ∧ a ≠ 0 ∧
    ∀ b c : ℕ × (Fin n → ℤ), IsConeLatticePoint P b → IsConeLatticePoint P c →
      a = b + c → b = 0 ∨ c = 0

/-- **Hilbert basis of the cone over a polytope.** For $P \subseteq \mathbb{R}^n$, call a pair
$(t, w) \in \mathbb{N} \times \mathbb{Z}^n$ a cone lattice point of $P$ when $w$ is a lattice point
of the dilate $tP = \{t y : y \in P\}$. The Hilbert basis of $P$ is the set of nonzero cone
lattice points $a$ of $P$ that are irreducible: whenever $a = b + c$ with $b$ and $c$ cone
lattice points of $P$, one of $b$ and $c$ is zero.

For a nonempty lattice polytope $P$ the cone lattice points form a positive monoid, whose
irreducible nonzero elements are exactly its minimal generating set, so this is then an equivalent
formulation of the usual Hilbert basis.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def hilbertBasis {n : ℕ} (P : Set (Fin n → ℝ)) : Set (ℕ × (Fin n → ℤ)) :=
  {a | IsHilbertBasisElement P a}

/-- **Homogenized vertices of a weighted simplex.** For weights $q = (q_1, \dots, q_n)$, the
homogenized vertex set is the subset of $\mathbb{N} \times \mathbb{Z}^n$ consisting of the
point $(1, -q) = (1, (-q_1, \dots, -q_n))$ and the points $(1, e_i)$ for $i = 1, \dots, n$, where
$e_i$ is the $i$th standard basis vector.

For the weights $q(n)$ of Theorem 13 this is the set $V(n)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def homogenizedWeightedVertices {n : ℕ} (q : Fin n → ℕ) :
    Set (ℕ × (Fin n → ℤ)) :=
  {(1, fun i => -(q i : ℤ))} ∪ Set.range (fun i : Fin n => (1, Pi.single i (1 : ℤ)))

/-- **Exceptional Hilbert basis columns.** Let $n \ge 1$. Write $t_0, \dots, t_8$ for the
integer triples $(0,0,0)$, $(0,0,-1)$, $(0,-1,-1)$, $(0,-1,-2)$, $(0,-2,-3)$, $(-1,-3,-5)$,
$(-1,-4,-6)$, $(-2,-7,-10)$ and $(-3,-10,-15)$. For $j = 0, \dots, 8$ the $j$th exceptional
column is the pair $(h_j, v_j)$, where the height $h_j$ is $1$ for $j \le 6$ and $2$ for
$j = 7, 8$, and $v_j \in \mathbb{Z}^{2n+2}$ has its first $2n-1$ coordinates equal to $0$ and
its last three coordinates equal to $t_j$.

The source prints $t_5$ as $(0, -3, -5)$, a point outside the cone; it is $(-1, -3, -5)$ here.
For $n = 0$ the vector $v_j \in \mathbb{Z}^2$ consists of the first and third entries of $t_j$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def exceptionalHilbertColumn (n : ℕ) (j : Fin 9) :
    ℕ × (Fin (2 * n + 2) → ℤ) :=
  let triples : Fin 9 → Fin 3 → ℤ := ![
    ![0, 0, 0], ![0, 0, -1], ![0, -1, -1], ![0, -1, -2], ![0, -2, -3],
    ![-1, -3, -5], ![-1, -4, -6], ![-2, -7, -10], ![-3, -10, -15]]
  (if j.val < 7 then 1 else 2, fun i =>
    if i.val < 2 * n - 1 then 0
    else if _h0 : i.val = 2 * n - 1 then triples j 0
    else if _h1 : i.val = 2 * n then triples j 1
    else triples j 2)

/-- **Hilbert basis of $\Delta_{(1,q(n))}$.** Let $n \ge 2$ and let
$q(n) = (1^{2n-1}, 3n, 10n, 15n)$, that is, $2n - 1$ ones followed by $3n$, $10n$, $15n$. Write
lattice points of the cone over the weighted projective simplex
$\Delta_{(1,q(n))} \subseteq \mathbb{R}^{2n+2}$ as pairs $(k, w)$ with height $k \in \mathbb{N}$
and $w \in \mathbb{Z}^{2n+2}$. The Hilbert basis of this cone is exactly the set of homogenized
vertices, namely $(1, e_i)$ for each standard basis vector $e_i$ and $(1, -q(n))$, together with
nine further points $(k, w)$ in which $w$ vanishes outside its last three coordinates. Their last
three coordinates are $(0,0,0)$, $(0,0,-1)$, $(0,-1,-1)$, $(0,-1,-2)$, $(0,-2,-3)$, $(-1,-3,-5)$
and $(-1,-4,-6)$ at height $k = 1$, and $(-2,-7,-10)$ and $(-3,-10,-15)$ at height $k = 2$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_hilbertBasis (n : ℕ) (hn : 2 ≤ n) :
    hilbertBasis (weightedSimplex (almostIDPWeights n)) =
      homogenizedWeightedVertices (almostIDPWeights n) ∪
        Set.range (exceptionalHilbertColumn n)

/-- **Exactly two Hilbert basis elements of height two.** Let $n \ge 2$ and let
$q(n) = (1^{2n-1}, 3n, 10n, 15n)$, that is, $2n - 1$ ones followed by $3n$, $10n$, $15n$. Write the
elements of the Hilbert basis of the cone over the weighted projective simplex $\Delta_{(1,q(n))}$
as pairs $(k, w)$ with height $k \in \mathbb{N}$ and $w \in \mathbb{Z}^{2n+2}$. Exactly two elements
of this Hilbert basis have height $k > 1$, and every element of height $k > 1$ has height $k = 2$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_exactly_two_height_two (n : ℕ) (hn : 2 ≤ n) :
    Set.ncard {a ∈ hilbertBasis (weightedSimplex (almostIDPWeights n)) | 1 < a.1} = 2 ∧
    ∀ a ∈ hilbertBasis (weightedSimplex (almostIDPWeights n)), 1 < a.1 → a.1 = 2

/-- **The $h^*$-polynomial of $\Delta_{(1,q(n))}$ factors.** Let $n \ge 2$, let
$q(n) = (1^{2n-1}, 3n, 10n, 15n)$, that is, $2n - 1$ ones followed by $3n$, $10n$, $15n$, and let
$\Delta_{(1,q(n))} \subseteq \mathbb{R}^{2n+2}$ be the weighted projective simplex. For $t \ge 0$,
let $L(t) = \#\big(t\,\Delta_{(1,q(n))} \cap \mathbb{Z}^{2n+2}\big)$ be the number of lattice
points in the dilate $t\,\Delta_{(1,q(n))}$. Then
$h(z) = (1 + z^2 + \dots + z^{2n-2})(1 + 7z + 14z^2 + 7z^3 + z^4)$ is an $h^*$-polynomial of
$\Delta_{(1,q(n))}$: as formal power series with integer coefficients,

$$\Big(\sum_{t \ge 0} L(t)\, z^t\Big)(1 - z)^{2n+3} = h(z).$$

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_hStar_factorization (n : ℕ) (hn : 2 ≤ n) :
    IsHStarPolynomial (weightedSimplex (almostIDPWeights n))
      (evenGeometricFactor n * almostIDPQuartic)

/-- **Example of support expansion.** Expanding the support values $r = (1, 3)$ with
multiplicities $x = (2, 1)$, that is, taking $2$ copies of $1$ followed by $1$ copy of $3$,
gives the list $(1, 1, 3)$; in the notation $(r_1^{x_1}, r_2^{x_2})$ for this expansion,
$(1^2, 3^1) = (1, 1, 3)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Section 2 (notation `(r_1^{x_1}, …, r_d^{x_d})`). -/
public theorem expandSupport_example : expandSupport ![1, 3] ![2, 1] = [1, 1, 3] := by
  decide

/-- **Least common multiple of the weights $(2, 2, 3)$.** The least common multiple of the list
$(2, 2, 3)$ is $\operatorname{lcm}(2, 2, 3) = 6$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Section 2. -/
public theorem weightLcm_example : weightLcm [2, 2, 3] = 6 := by
  decide

/-- **The $h^*$ formula for the weights $(2,2,3)$.** For $q = (2, 2, 3)$ the $h^*$ formula
$\sum_{b=0}^{7} z^{w(q,b)}$, with weight statistic
$w(q,b) = b - \lfloor 2b/8 \rfloor - \lfloor 2b/8 \rfloor - \lfloor 3b/8 \rfloor$, equals the
integer polynomial $1 + 2z + 4z^2 + z^3$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
example after Theorem 5. -/
public theorem hStarFormula_two_two_three :
    hStarFormula [2, 2, 3] =
      1 + 2 * Polynomial.X + 4 * Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
  have h : ∀ b, weightStatistic [2, 2, 3] b = b - (2 * b / 8 + (2 * b / 8 + 3 * b / 8)) := by
    intro b; simp [weightStatistic]
  rw [hStarFormula, show ([2, 2, 3] : List ℕ).sum + 1 = 8 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h]
  norm_num
  ring

/-- **The integer $\ell$ for the weights $(1^7, 3^4, 5^5)$.** For the support values
$r = (1, 3, 5)$ with multiplicities $x = (7, 4, 5)$, that is, for the weight vector
$q = (1^7, 3^4, 5^5)$, the integer
$\ell(r, x) = \lfloor (1 + \sum_i x_i r_i) / \operatorname{lcm}(r_1, r_2, r_3) \rfloor$ equals $3$.

Indeed $1 + 7 \cdot 1 + 4 \cdot 3 + 5 \cdot 5 = 45$ and $\operatorname{lcm}(1, 3, 5) = 15$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
example after Theorem 6. -/
public theorem setupEll_example : setupEll ![1, 3, 5] ![7, 4, 5] = 3 := by
  decide

/-- **The almost-IDP weight vector for $n = 1$.** The weight vector
$q(n) = (1^{2n-1}, 3n, 10n, 15n)$ of Theorem 13, where $1^{2n-1}$ denotes $2n-1$ entries
equal to $1$, taken at $n = 1$ and listed in coordinate order, is $(1, 3, 10, 15)$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Theorem 13. -/
public theorem almostIDPWeights_one : List.ofFn (almostIDPWeights 1) = [1, 3, 10, 15] := by
  decide

end

end MetaMathlibExt
