/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Canonical split decomposition of a finite metric (Bandelt–Dress)

A metric here is a pseudometric `d` on a finite set `X` (symmetric, zero diagonal, triangle
inequality; zeros off the diagonal allowed). A split metric is a metric whose zero-distance classes
are exactly two; by the triangle inequality it is `c · δ_A` for a proper nonempty `A ⊂ X` and
`c > 0`, where `δ_A(x, y)` is `1` across the split `A | X \ A` and `0` within its sides. A sum
`d = d₁ + ⋯ + d_k` of metrics is coherent when every function `f : X → ℝ` dominating `d`
(`f(x) + f(y) ≥ d(x, y)` for all `x, y`) is a sum `f = f₁ + ⋯ + f_k` of functions dominating the
summands; that is, `P(d) = P(d₁) + ⋯ + P(d_k)` for the polyhedra `P(d)` of functions dominating
`d`, equivalently `T(d) ⊆ T(d₁) + ⋯ + T(d_k)`: every point of the injective hull `T(d)` is a sum of
points of the injective hulls of the summands. A metric is split-prime when it is not a coherent
sum of a split metric and another metric.

Bandelt and Dress (1992): every metric `d` on a finite set `X` has a unique coherent decomposition
`d = d₁ + ⋯ + d_k + d₀` into linearly independent split metrics `d₁, …, d_k` and a split-prime
metric `d₀` (possibly zero); unique means that the residue is determined and the split summands
are determined up to order; with `|X| = n` there are at most `C(n, 2)` split summands; and if `d`
is tree-like the residue `d₀` vanishes. Tree-like is expressed by Buneman's four-point condition
`MathlibExt.Biology.Phylogenetics.Buneman.FourPointCondition`, equivalent to being a tree metric
(`isTreeMetric_iff_fourPointCondition`).

Here the coherence condition includes the requirement `f = f₁ + ⋯ + f_k`, which the survey's
paraphrase omits but which the original definition (`P(d) = ∑ P(dᵢ)`) requires.
Not recorded here: the characterization of the split summands as the split metrics `d'` with
`d - d'` a metric coherent with `d'`, and the isolation-index formula for their weights.

Overlap (partial): `CSLibExt/Bioinformatics/Phylogenetics/NeighborJoining.lean`
(`dist_eq_sum_darts`) decomposes a tree metric along its edges, and
`MathlibExt/Combinatorics/SimpleGraph/TreeMetric.lean` defines the four-point condition used here
and proves it equivalent to being a tree metric; the general case with a split-prime residue is not
present.

Sources: H.-J. Bandelt and A. W. M. Dress, "A canonical decomposition theory for metrics on a finite
set", Advances in Mathematics 92 (1992) 47–105, doi:10.1016/0001-8708(92)90061-O; statement read in
A. Dress, K. T. Huber and V. Moulton, "Metric spaces in pure and applied mathematics", Documenta
Mathematica, Extra Volume Quadratic Forms LSU (2001) 121–139, pp. 133–135; P. Buneman, "A note on
the metric properties of trees", Journal of Combinatorial Theory, Series B 17 (1974) 48–50.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.SimpleGraph.TreeMetric

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted

open MathlibExt.Biology.Phylogenetics.Buneman

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `d` is a **metric** (pseudometric): zero diagonal, symmetric, triangle inequality. -/
def IsMetric (d : X → X → ℝ) : Prop :=
  (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧ ∀ x y z, d x z ≤ d x y + d y z

/-- The split metric `δ_A`: `1` across the split `A | X \ A`, `0` within each side. -/
def splitMetric (A : Finset X) (x y : X) : ℝ :=
  if (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) then 1 else 0

/-- `d` is a **split metric**: `d = c · δ_A` for a proper nonempty `A` and `c > 0` (a metric with
exactly two zero-distance classes). -/
def IsSplitMetric (d : X → X → ℝ) : Prop :=
  ∃ A : Finset X, ∃ c : ℝ, A.Nonempty ∧ A ≠ Finset.univ ∧ 0 < c ∧
    ∀ x y, d x y = c * splitMetric A x y

/-- `f` **dominates** `d`: `d(x, y) ≤ f(x) + f(y)` for all `x, y`. -/
def Dominates (f : X → ℝ) (d : X → X → ℝ) : Prop :=
  ∀ x y, d x y ≤ f x + f y

/-- The family `ds` of `k` summands together with `r` is **coherent**: every function dominating
`∑ ds i + r` is a sum `∑ fs i + f₀` of functions dominating the respective summands. -/
def IsCoherent {k : ℕ} (ds : Fin k → X → X → ℝ) (r : X → X → ℝ) : Prop :=
  ∀ f : X → ℝ, Dominates f (fun x y => ∑ i, ds i x y + r x y) →
    ∃ (fs : Fin k → X → ℝ) (f₀ : X → ℝ), (∀ x, f x = ∑ i, fs i x + f₀ x) ∧
      (∀ i, Dominates (fs i) (ds i)) ∧ Dominates f₀ r

/-- `s + r` is a **coherent pair**: every function dominating `s + r` is `f₁ + f₂` with `f₁`
dominating `s` and `f₂` dominating `r`. -/
def IsCoherentPair (s r : X → X → ℝ) : Prop :=
  ∀ f : X → ℝ, Dominates f (fun x y => s x y + r x y) →
    ∃ f₁ f₂ : X → ℝ, (∀ x, f x = f₁ x + f₂ x) ∧ Dominates f₁ s ∧ Dominates f₂ r

/-- `d` is **split-prime**: it is not a coherent sum `s + r` of a split metric `s` and a metric
`r`. -/
def IsSplitPrime (d : X → X → ℝ) : Prop :=
  ¬ ∃ s r : X → X → ℝ, IsSplitMetric s ∧ IsMetric r ∧ IsCoherentPair s r ∧
    ∀ x y, d x y = s x y + r x y

/-- `(ds, r)` is a **canonical split decomposition** of `d`: the `ds i` are split metrics, `r` is a
split-prime metric, `d = ∑ ds i + r`, the decomposition is coherent, and the `ds i` are linearly
independent. -/
def IsCanonicalDecomp (d : X → X → ℝ) (k : ℕ) (ds : Fin k → X → X → ℝ) (r : X → X → ℝ) :
    Prop :=
  (∀ i, IsSplitMetric (ds i)) ∧ IsMetric r ∧ IsSplitPrime r ∧
    (∀ x y, d x y = ∑ i, ds i x y + r x y) ∧ IsCoherent ds r ∧
    ∀ c : Fin k → ℝ, (∀ x y, ∑ i, c i * ds i x y = 0) → ∀ i, c i = 0

/-- **Bandelt–Dress canonical split decomposition** (Bandelt and Dress 1992, via Dress, Huber and
Moulton 2001): for every metric `d` (zero diagonal, symmetric, triangle inequality) on a finite set
`X`, there is a canonical split decomposition `(ds, r)` of `d` with `k ≤ C(|X|, 2)` split summands,
and it is unique: for every canonical split decomposition `(ds', r')` of `d`, `r' = r`, `k' = k`,
and the summands agree up to a reordering `σ` (`ds' j = ds (σ j)`).

Source: Bandelt and Dress (1992), via Dress, Huber and Moulton (2001), pp. 133–135. -/
public theorem_wanted exists_unique_canonicalDecomp (d : X → X → ℝ) (hd : IsMetric d) :
    ∃ (k : ℕ) (ds : Fin k → X → X → ℝ) (r : X → X → ℝ), IsCanonicalDecomp d k ds r ∧
      k ≤ (Fintype.card X).choose 2 ∧
      ∀ (k' : ℕ) (ds' : Fin k' → X → X → ℝ) (r' : X → X → ℝ), IsCanonicalDecomp d k' ds' r' →
        r' = r ∧ ∃ σ : Fin k' ≃ Fin k, ∀ j, ds' j = ds (σ j)

/-- **Tree-like metrics are totally split-decomposable** (Bandelt and Dress 1992, via Dress, Huber
and Moulton 2001): for every metric `d` (zero diagonal, symmetric, triangle inequality) on a finite
set `X` satisfying the four-point condition, and every canonical split decomposition `(ds, r)` of
`d`, the split-prime residue `r` vanishes.

Source: Bandelt and Dress (1992), via Dress, Huber and Moulton (2001), p. 134. -/
public theorem_wanted canonicalDecomp_residue_eq_zero_of_treeLike (d : X → X → ℝ)
    (hd : IsMetric d) (htree : FourPointCondition d) (k : ℕ) (ds : Fin k → X → X → ℝ)
    (r : X → X → ℝ) (hcanon : IsCanonicalDecomp d k ds r) :
    ∀ x y, r x y = 0

end WantedExt.Biology.ComputationalBiology.SplitDecompositionWanted
