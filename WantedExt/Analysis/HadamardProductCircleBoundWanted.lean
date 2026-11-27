/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hadamard product circle bound
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.HadamardProductCircleBoundWanted

/-! Source record `AMR-022-6028__2306028`. -/

/-- **Normalized univalent functions with their Taylor coefficients.** An element of the class
$S$ is a function $f : \mathbb{C} \to \mathbb{C}$ together with a sequence $(a_m)_{m \ge 0}$ of
complex numbers such that $f$ is holomorphic and injective on the open unit disk $\mathbb{D}$ of
all $z \in \mathbb{C}$ with $|z| < 1$, $f(0) = 0$, $f'(0) = 1$, $a_0 = 0$, $a_1 = 1$, and for every
$z \in \mathbb{D}$ the series $\sum_{m \ge 0} a_m z^m$ is unconditionally summable with sum $f(z)$.

Source: [AMR-022-6028] Problem 6.28. -/
structure ClassS where
  f : ℂ → ℂ
  a : ℕ → ℂ
  holo : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)
  map_zero : f 0 = 0
  deriv_one : HasDerivAt f 1 0
  inj : Set.InjOn f (Metric.ball (0 : ℂ) 1)
  coeff_zero : a 0 = 0
  coeff_one : a 1 = 1
  taylor : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun m => a m * z ^ m) (f z)

/-- **Truncated Hadamard product with a polynomial.** For a sequence $(a_k)_{k \ge 0}$ of complex
numbers, a complex polynomial $P(z) = \sum_k p_k z^k$ and $n \in \mathbb{N}$, this is the
polynomial $\sum_{k=0}^{n} a_k p_k z^k$: the coefficient-wise (Hadamard) product of $P$ with the
power series $\sum_k a_k z^k$, truncated at degree $n$.

Source: [AMR-022-6028] Problem 6.28. -/
noncomputable def hadamardProduct (a : ℕ → ℂ) (P : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (a k * P.coeff k) * (Polynomial.X : Polynomial ℂ) ^ k

/-- **Sup norm of a polynomial on the unit circle.** For a complex polynomial $Q$, this is the
real number $\sup_{|z| = 1} |Q(z)|$, the supremum of $|Q(z)|$ over all $z \in \mathbb{C}$ with
$|z| = 1$.

Source: [AMR-022-6028] Problem 6.28. -/
noncomputable def circleMax (Q : Polynomial ℂ) : ℝ :=
  sSup ((fun z => ‖Q.eval z‖) '' Metric.sphere (0 : ℂ) 1)

/-- **Statement of the Hadamard product circle bound.** The proposition that for every
$n \in \mathbb{N}$, every function $f(z) = \sum_{m \ge 0} a_m z^m$ of the class $S$ of normalized
univalent functions on the unit disk, and every complex polynomial $P(z) = \sum_k p_k z^k$ of
degree at most $n$,
$$
\sup_{|z| = 1} \Bigl| \sum_{k=0}^{n} a_k p_k z^k \Bigr| \le n \sup_{|z| = 1} |P(z)|.
$$

Source: [AMR-022-6028] Problem 6.28, where it is posed as an open question. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (S : ClassS) (P : Polynomial ℂ),
    P.natDegree ≤ n →
      circleMax (hadamardProduct S.a P n) ≤ (n : ℝ) * circleMax P

/--
**Hadamard product circle bound for univalent functions.** For every $n \in \mathbb{N}$, every
function $f(z) = \sum_{m \ge 0} a_m z^m$ of the class $S$ of normalized univalent functions on the
unit disk, and every complex polynomial $P(z) = \sum_k p_k z^k$ of degree at most $n$,
$$
\sup_{|z| = 1} \Bigl| \sum_{k=0}^{n} a_k p_k z^k \Bigr| \le n \sup_{|z| = 1} |P(z)|.
$$

Robertson's conjecture implies the bound (Sheil-Small, J. Reine Angew. Math. 258 (1973)), and de
Branges (Acta Math. 154 (1985)) proved Milin's conjecture, hence Robertson's. Both facts are
recorded in Hayman-Lingham (arXiv:1809.07200, Problem 6.28, Update 6.1).

Source:
Walter K. Hayman and Eleanor F. Lingham, Research Problems in Function Theory (New Edition),
arXiv:1809.07200v2 (2018), https://arxiv.org/abs/1809.07200. Moved from
`OpenConjectures/Analysis/HadamardProductCircleBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HadamardProductCircleBoundWanted
