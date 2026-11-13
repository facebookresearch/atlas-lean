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
public import Mathlib.Basic.Real.Basic
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

/-- Affine hyperplane in `Fin d → ℝ` [OWR-1183-011]: an affine subspace
that is the level set of a nonzero linear functional. -/
def IsAffineHyperplane (d : ℕ) (Hp : AffineSubspace ℝ (Fin d → ℝ)) : Prop :=
  ∃ (l : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), l ≠ 0 ∧ ∀ x, x ∈ Hp ↔ l x = c

/-- The set `H` of hyperplanes spanned by `P` [OWR-1183-011]: hyperplanes
whose affine span is attained by some subset of `P`. -/
def SpannedHyperplaneSet (d : ℕ) (P : Set (Fin d → ℝ)) :
    Set (AffineSubspace ℝ (Fin d → ℝ)) :=
  {Hp | IsAffineHyperplane d Hp ∧ ∃ Q : Set (Fin d → ℝ), Q ⊆ P ∧ affineSpan ℝ Q = Hp}

/-- The question of [OWR-1183-011]: for every `d ≥ 1` and every `P`
spanning the ambient space, with `H` the hyperplanes spanned by `P`,
is there an injective `f : P → H` with `p ∈ f p` for every `p`? -/
def OWR1183Question : Prop :=
  ∀ (d : ℕ) (_hd : 1 ≤ d) (P : Set (Fin d → ℝ)), affineSpan ℝ P = ⊤ →
    ∃ f : P → ↥(SpannedHyperplaneSet d P),
      Function.Injective f ∧ ∀ p : P, p.val ∈ (f p).val

end ITSP

/--
Resolved true: Farley (Australas. J. Combin. 82 (2022), arXiv:2004.11972), Theorem 11: every
geometric lattice of finite rank > 1, of any cardinality, has an injective
atom-to-containing-coatom matching. Applied to the affine-matroid lattice of a spanning P in
R^d, this gives the required injection. Source: J. D. Farley, A question of Björner from 1981:
infinite geometric lattices of finite rank have matchings, Australasian Journal of Combinatorics
82 (2022) 228-235, arXiv:2004.11972, https://arxiv.org/abs/2004.11972. Moved from
`OpenConjectures/Geometry/InfiniteTransversalsSpannedHyperplanes`.
-/
public theorem_wanted OWR1183Question_holds : ITSP.OWR1183Question

end MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanesWanted
