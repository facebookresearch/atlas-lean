/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The space of phylogenetic trees is CAT(0)

Billera, Holmes and Vogtmann (2001, Section 2): a metric `n`-tree is a rooted tree with leaves
labelled `1, …, n`, a leaf `0` hung above the root, and positive lengths on its interior edges.
An interior edge splits the leaves `{0, 1, …, n}` into two sets of at least two elements (a thick
partition), the edges of one tree give pairwise compatible partitions, and a tree is determined by
its set of thick partitions and their lengths (Section 3.2). The tree space `T_n` glues one
closed orthant `[0, ∞)^{n - 2}` for each binary tree along common faces. A point of `T_n` is
recorded here as a length function on thick partitions, each represented by its side not
containing `0`, with pairwise compatible support (`TreeSpace`); the origin is the tree with no
interior edge.

The distance (Section 4) is the least length of a segmented path, each segment lying in a single
orthant and measured by Euclidean distance there (`bhvDist`); two points lie in a common orthant
when their supports together are pairwise compatible. Lemma 4.1: `T_n` is a CAT(0) space (via
Gromov's link condition for cubical complexes, which needs simple connectivity; `T_n` is a cone,
hence contractible). Consequently any two trees are joined by a unique geodesic. Theorem 4.1: in
a CAT(0) space, iterated-midpoint centroids exist for finite families and the centroid function
is convex. Its proof passes to the limit of a Cauchy sequence, so the space is assumed complete
here (Hadamard space); `T_n` is complete. The center of mass (Fréchet mean) is cited by the paper
from Sturm and is not recorded.

The CAT(0) inequality is stated in the form of the paper (Section 4.1): for a geodesic from `a`
to `b` and the point `x` on it at distance `t` from `a`, the distance from `x` to any `c` is at
most the distance between the corresponding points of the Euclidean comparison triangle, which
by Stewart's theorem has square `((d(a, b) - t) d(a, c)² + t d(b, c)²) / d(a, b) - t (d(a, b) - t)`.
Theorem 4.1 uses the shared CAT(0) predicate `IsCATZero` of `WantedExt.Geometry.CATZeroSpaceShared`.
Split compatibility is `CSLibExt.Bioinformatics.Phylogenetics.Splits.Compatible`.

Sources: L. J. Billera, S. P. Holmes and K. Vogtmann, "Geometry of the space of phylogenetic
trees", Advances in Applied Mathematics 27 (2001) 733–767, doi:10.1006/aama.2001.0759,
Sections 2, 3.2 and 4, Lemma 4.1 and Theorem 4.1; M. Gromov, "Hyperbolic groups", in *Essays in
Group Theory*, MSRI Publications 8, Springer, 1987, 75–263; M. R. Bridson and A. Haefliger,
*Metric Spaces of Non-Positive Curvature*, Springer, 1999, Proposition II.2.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import WantedExt.Geometry.CATZeroSpaceShared
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.PhylogeneticTreeSpaceWanted

open Cslib.Bioinformatics.Phylogenetics.Splits
open MathlibExt.Geometry.CATZeroSpaceShared
open Filter Topology

section TreeSpace

variable (n : ℕ)

/-- The leaf set `C ⊆ {0, 1, …, n}` represents a **thick partition** `C | Cᶜ`: `0 ∉ C`, and both
sides have at least two elements. -/
def IsThick (C : Finset (Fin (n + 1))) : Prop :=
  (0 : Fin (n + 1)) ∉ C ∧ 2 ≤ C.card ∧ C.card + 2 ≤ n + 1

/-- The **tree space** `T_n`: nonnegative length functions on leaf sets that are positive only on
thick partitions, with pairwise compatible support (the interior edges of one metric `n`-tree). -/
def TreeSpace : Type :=
  {ℓ : Finset (Fin (n + 1)) → ℝ // (∀ C, 0 ≤ ℓ C) ∧ (∀ C, 0 < ℓ C → IsThick n C) ∧
    ∀ C D, 0 < ℓ C → 0 < ℓ D → Compatible C D}

variable {n}

/-- The trees `x` and `y` lie in a common closed orthant: the thick partitions in their supports
are pairwise compatible. -/
def SameOrthant (x y : TreeSpace n) : Prop :=
  ∀ C D, (0 < x.1 C ∨ 0 < y.1 C) → (0 < x.1 D ∨ 0 < y.1 D) → Compatible C D

/-- The Euclidean length of the segment from `x` to `y` in their common orthant. -/
noncomputable def segmentLength (x y : TreeSpace n) : ℝ :=
  Real.sqrt (∑ C : Finset (Fin (n + 1)), (x.1 C - y.1 C) ^ 2)

/-- The **distance** on `T_n`: the infimum of the lengths of segmented paths from `x` to `y`,
each segment lying in a single orthant. -/
noncomputable def bhvDist (x y : TreeSpace n) : ℝ :=
  sInf {L | ∃ (k : ℕ) (p : Fin (k + 1) → TreeSpace n), p 0 = x ∧ p (Fin.last k) = y ∧
    (∀ i : Fin k, SameOrthant (p i.castSucc) (p i.succ)) ∧
      L = ∑ i : Fin k, segmentLength (p i.castSucc) (p i.succ)}

end TreeSpace

/-- `γ` is a **geodesic** from `a` to `b` for the distance `d`: `γ 0 = a`, `γ (d a b) = b`, and
`γ` is an isometry on `[0, d a b]`. -/
def IsGeodesic {T : Type*} (d : T → T → ℝ) (γ : ℝ → T) (a b : T) : Prop :=
  γ 0 = a ∧ γ (d a b) = b ∧
    ∀ s ∈ Set.Icc 0 (d a b), ∀ t ∈ Set.Icc 0 (d a b), d (γ s) (γ t) = |s - t|

/-- **The space of phylogenetic trees is CAT(0)** (Billera, Holmes and Vogtmann 2001, Lemma 4.1):
`bhvDist` is a metric on `T_n`, any two trees are joined by a geodesic, and triangles are at least
as thin as Euclidean comparison triangles: for a geodesic from `a` to `b` with `d(a, b) > 0` and
`0 ≤ t ≤ d(a, b)`, `d(γ t, c)² ≤ ((d(a, b) - t) d(a, c)² + t d(b, c)²) / d(a, b) - t (d(a, b) - t)`.

Source: Billera, Holmes and Vogtmann (2001), Lemma 4.1. -/
public theorem_wanted treeSpace_isCAT0 (n : ℕ) :
    (∀ x y : TreeSpace n, bhvDist x y = 0 ↔ x = y) ∧
      (∀ x y : TreeSpace n, bhvDist x y = bhvDist y x) ∧
      (∀ x y z : TreeSpace n, bhvDist x z ≤ bhvDist x y + bhvDist y z) ∧
      (∀ x y : TreeSpace n, ∃ γ, IsGeodesic bhvDist γ x y) ∧
      ∀ (a b c : TreeSpace n) (γ : ℝ → TreeSpace n), IsGeodesic bhvDist γ a b →
        0 < bhvDist a b → ∀ t ∈ Set.Icc 0 (bhvDist a b),
          bhvDist (γ t) c ^ 2 ≤ ((bhvDist a b - t) * bhvDist a c ^ 2 + t * bhvDist b c ^ 2) /
            bhvDist a b - t * (bhvDist a b - t)

/-- **Geodesics in tree space are unique** (Billera, Holmes and Vogtmann 2001, consequence of
Lemma 4.1): two geodesics from `a` to `b` agree on `[0, d(a, b)]`.

Source: Billera, Holmes and Vogtmann (2001), Section 4.1. -/
public theorem_wanted treeSpace_geodesic_unique (n : ℕ) (a b : TreeSpace n)
    (γ γ' : ℝ → TreeSpace n) (hγ : IsGeodesic bhvDist γ a b) (hγ' : IsGeodesic bhvDist γ' a b) :
    ∀ t ∈ Set.Icc 0 (bhvDist a b), γ t = γ' t

section Centroid

variable {X : Type*} [MetricSpace X]

/-- `z` is the **midpoint** of `x` and `y`: it lies at half the distance from each. -/
def IsMidpoint (x y z : X) : Prop :=
  dist x z = dist x y / 2 ∧ dist z y = dist x y / 2

/-- One step of the iterated centroid: replace the family `Y` of `n + 3` points by the centroids
`c'` of the `n + 2` subfamilies omitting one point each. -/
def centroidStep {n : ℕ} (c' : (Fin (n + 2) → X) → X) (Y : Fin (n + 3) → X) : Fin (n + 3) → X :=
  fun i => c' fun j => Y (i.succAbove j)

/-- `c` is an **iterated-midpoint centroid function** on families of `n + 2` points: for two
points, the midpoint; for more, every point of the iterated families `cᵏ(Y)` converges to
`c Y`, where the centroid function on one point fewer is used at each step. -/
def IsCentroidFn : (n : ℕ) → ((Fin (n + 2) → X) → X) → Prop
  | 0, c => ∀ Y, IsMidpoint (Y 0) (Y 1) (c Y)
  | n + 1, c => ∃ c' : (Fin (n + 2) → X) → X, IsCentroidFn n c' ∧
      ∀ (Y : Fin (n + 3) → X) (i : Fin (n + 3)),
        Tendsto (fun k => (centroidStep c')^[k] Y i) atTop (𝓝 (c Y))

/-- **Centroids in CAT(0) spaces** (Billera, Holmes and Vogtmann 2001, Theorem 4.1): in a complete
CAT(0) space, iterated-midpoint centroids exist for every finite family of at least two points,
and the centroid function is convex:
`d(c(Y), c(Y')) ≤ (1 / |Y|) ∑ᵢ d(yᵢ, y'ᵢ)`.

Source: Billera, Holmes and Vogtmann (2001), Theorem 4.1. -/
public theorem_wanted exists_convex_centroidFn [CompleteSpace X] (hX : IsCATZero X) (n : ℕ) :
    ∃ c : (Fin (n + 2) → X) → X, IsCentroidFn n c ∧
      ∀ Y Y' : Fin (n + 2) → X, dist (c Y) (c Y') ≤ (∑ i, dist (Y i) (Y' i)) / (n + 2)

end Centroid

end WantedExt.Biology.ComputationalBiology.PhylogeneticTreeSpaceWanted
