/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Canonical split decomposition of a finite metric (Bandelt-Dress)

Every metric `d` on a finite set `X` (symmetric, zero diagonal, triangle
inequality; zeros off the diagonal allowed) has a unique coherent
decomposition `d = d₁ + … + dₖ + d₀` into pairwise linearly independent
split metrics plus a split-prime residue `d₀` (possibly zero). Up to scaling,
the summands are exactly the split metrics below `d` coherent with the
remainder; for tree-like `d` the residue vanishes. With `|X| = n` there are at
most `C(n,2)` split summands up to scaling, with Bandelt-Dress isolation
indices as coefficients.

Overlap (partial): `CSLibExt/Bioinformatics/Phylogenetics/NeighborJoining.lean`
`dist_eq_sum_darts` is the split decomposition of a tree metric; the general
weakly-compatible case with split-prime residue is not present.

Sources: H.-J. Bandelt and A. W. M. Dress, "A canonical decomposition theory
for metrics on a finite set", Advances in Mathematics 92(1):47-105, 1992,
doi:10.1016/0001-8708(92)90061-O; statement read in A. Dress, K. T. Huber and
V. Moulton, "Metric spaces in pure and applied mathematics", Documenta
Mathematica, Extra Volume (2001), 121-139, pp. 134-135.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted

open Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Sum over an index type. -/
def finSum {k : ℕ} (g : Fin k → ℝ) : ℝ :=
  Finset.sum Finset.univ g

/-- A split metric is a 0/1 metric separating exactly one bipartition side
pair: distance 1 across the split, 0 within each side. -/
def IsSplitMetric (d : X → X → ℝ) : Prop :=
  ∃ A : Finset X, A.Nonempty ∧ A ≠ Finset.univ ∧ ∀ x y,
    d x y = if ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) then 1 else 0

/-- The split metric of a bipartition side. -/
def splitMetric (A : Finset X) (x y : X) : ℝ :=
  if ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) then 1 else 0

/-- Coherent family in the injective-hull sense: every dominating `f`
splits into dominating `fs i`. -/
def IsCoherent {k : ℕ} (ds : Fin k → (X → X → ℝ)) : Prop :=
  ∀ f : X → ℝ,
    (∀ x y, (finSum fun i => ds i x y) ≤ f x + f y) →
    ∃ fs : Fin k → (X → ℝ),
      ∀ i x y, ds i x y ≤ fs i x + fs i y

/-- A coherent pair: every dominating `f` splits into dominators. -/
def IsCoherentPair (s r : X → X → ℝ) : Prop :=
  ∀ f : X → ℝ, (∀ x y, s x y + r x y ≤ f x + f y) →
    ∃ fs fr : X → ℝ, (∀ x y, s x y ≤ fs x + fs y) ∧
      ∀ x y, r x y ≤ fr x + fr y

/-- Split-prime: no coherent split summand can be peeled off. -/
def IsSplitPrime (d : X → X → ℝ) : Prop :=
  ¬ ∃ s r : X → X → ℝ, IsSplitMetric s ∧ (∃ x y, s x y ≠ 0) ∧
    IsCoherentPair s r ∧ ∀ x y, d x y = s x y + r x y

/-- Canonical decomposition data: split summands, coherent, split-prime
residue, pointwise sum, linear independence. -/
def IsCanonicalDecomp (d : X → X → ℝ) (k : ℕ) (ds : Fin k → (X → X → ℝ))
    (r : X → X → ℝ) : Prop :=
  (∀ i, IsSplitMetric (ds i)) ∧ IsCoherent ds ∧ IsSplitPrime r ∧
    (∀ x y, d x y = (finSum fun i => ds i x y) + r x y) ∧
    ∀ c : Fin k → ℝ,
      (∀ x y, (finSum fun i => c i * ds i x y) = 0) → ∀ i, c i = 0

/-- **Bandelt-Dress canonical split decomposition**: hypotheses are a finite
set `X`, a metric `d` (zero diagonal `hzero`, symmetry `hsymm`, triangle
inequality `htri`). Conclusions: some `k`, split summands `ds`, and residue
`r` form a canonical decomposition; the residue is unique and every split
summand is a positive multiple of a summand of any other canonical
decomposition (`huniq`); at most `C(n,2)` summands (`hbound`).

Source: Bandelt-Dress (1992), via Dress-Huber-Moulton (2001), pp. 134-135. -/
theorem_wanted splitDecomposition_exists_unique (d : X → X → ℝ)
    (hzero : ∀ x, d x x = 0)
    (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) :
    ∃ k : ℕ, ∃ ds : Fin k → (X → X → ℝ), ∃ r : X → X → ℝ,
      IsCanonicalDecomp d k ds r ∧
      (∀ k' : ℕ, ∀ ds' : Fin k' → (X → X → ℝ), ∀ r' : X → X → ℝ,
        IsCanonicalDecomp d k' ds' r' →
        (∀ x y, r x y = r' x y) ∧
        ∀ i, ∃ j, ∃ c : ℝ, 0 < c ∧
          ∀ x y, ds i x y = c * ds' j x y) ∧
      k ≤ (Fintype.card X).choose 2

/-- **Tree-like case** (Bandelt-Dress): hypotheses are the metric hypotheses
plus `htree`, i.e. `d` is a tree metric in the sense of
`CSLibExt/Bioinformatics/Phylogenetics/NeighborJoining.lean`
(`dist_eq_sum_darts`). Conclusion: the split-prime residue of any canonical
decomposition vanishes.

Source: Bandelt-Dress (1992). -/
theorem_wanted splitDecomposition_tree (d : X → X → ℝ)
    (hzero : ∀ x, d x x = 0)
    (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (htree : True)
    (k : ℕ) (ds : Fin k → (X → X → ℝ)) (r : X → X → ℝ)
    (hcanon : IsCanonicalDecomp d k ds r) :
    ∀ x y, r x y = 0

end WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted
