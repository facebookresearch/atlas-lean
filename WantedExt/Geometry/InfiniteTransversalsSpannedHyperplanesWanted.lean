/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OWR-1183-011: infinite transversals from points to spanned hyperplanes
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

namespace MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanesWanted

/-! Source record `OWR-1183-011`. -/

namespace ITSP

/-!
# Clause inventory for [OWR-1183-011]

- Quantifier domain: dimension `d : ℕ` with `1 ≤ d`, ambient `Fin d → ℝ`.
- Quantifier domain: `P : Set (Fin d → ℝ)`.
- Hypothesis: `affineSpan ℝ P = ⊤` (spanning).
- Object: hyperplanes as level sets of nonzero linear functionals.
- Object: `H`, hyperplanes whose affine span is attained by some `Q ⊆ P`.
- Question: `∃ f : P → H` injective with `p ∈ f p` for all `p`.
-/

/-- **Affine hyperplanes in $\mathbb{R}^d$.** An affine subspace $A$ of $\mathbb{R}^d$ is an affine
hyperplane when there are a nonzero linear functional $\ell \colon \mathbb{R}^d \to \mathbb{R}$ and
a real number $c$ such that $A = \{x \in \mathbb{R}^d : \ell(x) = c\}$.

Source: `OWR-1183-011`. -/
def IsAffineHyperplane (d : ℕ) (Hp : AffineSubspace ℝ (Fin d → ℝ)) : Prop :=
  ∃ (l : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), l ≠ 0 ∧ ∀ x, x ∈ Hp ↔ l x = c

/-- **Hyperplanes spanned by a point set.** For a set $P \subseteq \mathbb{R}^d$, the hyperplanes
spanned by $P$ are the affine hyperplanes of $\mathbb{R}^d$ that equal the affine span of some
subset of $P$.

Source: `OWR-1183-011`. -/
def SpannedHyperplaneSet (d : ℕ) (P : Set (Fin d → ℝ)) :
    Set (AffineSubspace ℝ (Fin d → ℝ)) :=
  {Hp | IsAffineHyperplane d Hp ∧ ∃ Q : Set (Fin d → ℝ), Q ⊆ P ∧ affineSpan ℝ Q = Hp}

/-- **Injective point-to-hyperplane matching question.** The statement that for every $d \ge 1$
and every set $P \subseteq \mathbb{R}^d$ whose affine span is all of $\mathbb{R}^d$, writing
$\mathcal{H}$ for the set of affine hyperplanes of $\mathbb{R}^d$ that equal the affine span of
some subset of $P$, there is an injective map $f \colon P \to \mathcal{H}$ with $p \in f(p)$ for
every $p \in P$.

Source: the question of `OWR-1183-011`. -/
def OWR1183Question : Prop :=
  ∀ (d : ℕ) (_hd : 1 ≤ d) (P : Set (Fin d → ℝ)), affineSpan ℝ P = ⊤ →
    ∃ f : P → ↥(SpannedHyperplaneSet d P),
      Function.Injective f ∧ ∀ p : P, p.val ∈ (f p).val

end ITSP

/--
**Spanning point sets have injective point-to-hyperplane matchings.** For every $d \ge 1$ and
every set $P \subseteq \mathbb{R}^d$ whose affine span is all of $\mathbb{R}^d$, let $\mathcal{H}$
be the set of affine hyperplanes of $\mathbb{R}^d$ that equal the affine span of some subset of
$P$. Then there is an injective map $f \colon P \to \mathcal{H}$ with $p \in f(p)$ for every
$p \in P$.

This answers the question of `OWR-1183-011` affirmatively. It follows from Farley's Theorem 11:
every geometric lattice of finite rank greater than $1$, of any cardinality, has an injective
map sending each atom to a coatom containing it; apply it to the lattice of affine flats
spanned by subsets of $P$.

Source: J. D. Farley, A question of Björner from 1981:
infinite geometric lattices of finite rank have matchings, Australasian Journal of Combinatorics
82 (2022) 228-235, arXiv:2004.11972, https://arxiv.org/abs/2004.11972. Moved from
`OpenConjectures/Geometry/InfiniteTransversalsSpannedHyperplanes`.
-/
public theorem_wanted OWR1183Question_holds : ITSP.OWR1183Question

end MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanesWanted
