/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NormalizedSectionAlgebras
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace
public import Batteries.Util.ProofWanted

/-!
# Basis/filtered-volume comparison for actual complete section series

Reference: Blum--Jonsson, arXiv1706.04548v2, §5 and Theorem C.
The series is the actual complete section series, with finite section
modules and an injectively normalized multiplication comparison. The
computed volume is positive and finite; neither expected vanishing nor
basis averages are arbitrary invariants. The actual nonzero section orders
satisfy the displayed positive linear-growth bound.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NormalizedSectionAlgebras

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CenteredValuationSections

theorem_wanted basis_expected_limit
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (V : NormalVariety k n) [IsProper V.X.hom]
    (hprojective : ∃ N : ℕ, ∃ i : V.X ⟶ ProjectiveSpace.projectiveSpace k N,
      IsClosedImmersion i.left)
    (v : CenteredValuation V) (S : SectionSeries V v)
    (A : SectionMultiplication S) (hpositive : 0 < volume S) (hfinite : volume S < ⊤)
    (hlinear : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      ∀ s : BirationalSectionCoordinates.SectionSpace V (LineBundleTaskContracts.power S.line m),
        s ≠ 0 → -Real.log (v.valuation ((S.evaluation m).map s) : ℝ) ≤ C * m) :
    Filter.Tendsto (fun m : ℕ => maximalBasisOrder S m) Filter.atTop
      (nhds (expectedVanishing S).toEReal)

end MathlibExt.AlgebraicGeometry.NormalizedSectionAlgebras
