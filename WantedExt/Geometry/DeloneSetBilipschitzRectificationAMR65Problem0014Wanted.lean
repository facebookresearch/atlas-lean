/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Delone sets bi-Lipschitz to ℤ² are images of ℤ² under bi-Lipschitz maps of ℝ² (Navas' problem)

F. Adiceam et al., Open Problems and Conjectures Related to the Theory of Mathematical
Quasicrystals, Problem 2.6.1 (A. Navas, after Alestalo, Trotsenko and Väisälä): let `𝒟 ⊆ ℝ²` be a
Delone set BL to `ℤ²`. Does there exist a bi-Lipschitz map `L : ℝ² → ℝ²` with `L(𝒟) = ℤ²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.AperiodicOrder.Delone.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.DeloneSetBilipschitzRectificationAMR65Problem0014Wanted

/-!
Source: F. Adiceam, D. Damanik, F. Gähler, U. Grimm, A. Haynes, A. Julien, A. Navas, L. Sadun and B.
Weiss, Open Problems and Conjectures Related to the Theory of Mathematical Quasicrystals (2016),
arXiv:1604.06280, Problem 2.6.1 (A. Navas). UnsolvedMath record UM-06600014 (`AMR-065-0014`),
dataset ulamai/UnsolvedMath v1.8.0.

A Delone set (uniformly discrete and relatively dense) is Mathlib's `Delone.DeloneSet`. "BL to `ℤ²`"
means there is a bijection `D → ℤ²` that is bi-Lipschitz for the Euclidean metric: `LipschitzWith`
and `AntilipschitzWith` of its restriction to `D` (the convention of
`Delone.DeloneSet.mapBilipschitz`), with a positive antilipschitz constant `K₁`, and likewise for
`L` (`AntilipschitzWith K₁ f` is `edist x y ≤ K₁ * edist (f x) (f y)`; `K₁ = 0` would force a
one-point domain, so the positivity only makes the bi-Lipschitz reading explicit). `L` is not
required to be onto in the statement, as in the source; a bi-Lipschitz self-map of `ℝ²` is onto
anyway.
-/

open scoped NNReal

/-- The integer lattice `ℤ²` inside the Euclidean plane. -/
def integerLattice : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, ∃ k : ℤ, x i = k}

/-- Navas' problem (Adiceam et al., Open Problems ... Mathematical Quasicrystals, Problem 2.6.1):
for every Delone set `D ⊆ ℝ²` (Mathlib's `Delone.DeloneSet`) that is bi-Lipschitz equivalent to
`ℤ²` (a bijection `f : D → ℤ²` that is Lipschitz and antilipschitz, with a positive antilipschitz
constant, for the subspace metric) there is a bi-Lipschitz map `L : ℝ² → ℝ²` with `L(D) = ℤ²`. -/
def deloneBilipschitzRectification : Prop :=
  ∀ D : Delone.DeloneSet (EuclideanSpace ℝ (Fin 2)),
    (∃ (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (K₁ K₂ : ℝ≥0),
      Set.BijOn f D integerLattice ∧ 0 < K₁ ∧
        AntilipschitzWith K₁ ((D : Set (EuclideanSpace ℝ (Fin 2))).domRestrict f) ∧
        LipschitzWith K₂ ((D : Set (EuclideanSpace ℝ (Fin 2))).domRestrict f)) →
    ∃ (L : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (K₁ K₂ : ℝ≥0),
      0 < K₁ ∧ AntilipschitzWith K₁ L ∧ LipschitzWith K₂ L ∧ L '' D = integerLattice

/--
Resolved true: Dymond and Kaluža proved that every bi-Lipschitz map `ℤ² → ℝ²` extends to a
bi-Lipschitz map of `ℝ²` (Theorem 1.1) and state that this completely solves Navas' problem:
extending the inverse of a bi-Lipschitz bijection `D → ℤ²` and inverting gives `L`. Source: F.
Adiceam, D. Damanik, F. Gähler, U. Grimm, A. Haynes, A. Julien, A. Navas, L. Sadun and B. Weiss,
Open Problems and Conjectures Related to the Theory of Mathematical Quasicrystals (2016),
arXiv:1604.06280, Problem 2.6.1 (A. Navas); resolution: M. Dymond and V. Kaluža, Planar bilipschitz
extension from separated nets, J. London Math. Soc. 113 (2026), e70540, arXiv:2410.22294, Theorem
1.1: every L-bilipschitz f : ℤ² → ℝ² extends to a p(L)-bilipschitz F : ℝ² → ℝ²; Introduction: "this
is a complete positive solution of Navas' problem [Problem 2.6.1]",
https://arxiv.org/abs/2410.22294.
-/
public theorem_wanted deloneBilipschitzRectification_holds : deloneBilipschitzRectification

end MathlibExt.Geometry.DeloneSetBilipschitzRectificationAMR65Problem0014Wanted
