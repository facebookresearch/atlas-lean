/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies

/-!
# Tests for log-Fano fibres of DVR models

A log-Fano fibre needs a boundary ideal whose restriction to the special fibre is nonzero: the
zero ideal, like the ideal of the special fibre itself, has none. Its log pair is proper, and its
valuative semistability is the divisorial inequality `S ≤ A` at every divisorial valuation. The
two-model comparisons depend on the chosen generic line comparison only through its powers: the
identity change of comparison changes nothing.
-/

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DVRGradedSectionFamilies

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The zero ideal has no restriction to the special fibre, so it is not a log-Fano boundary. -/
example {X : CategoryTheory.Over (Spec (.of R))} {L : X.left.Modules} {n e : ℕ}
    (F : LogFanoFibre X L ⊥ n e) : False :=
  F.boundaryRestricts (Scheme.IdealSheafData.comap_bot _)

/-- The log pair of a log-Fano fibre is proper. -/
example {X : CategoryTheory.Over (Spec (.of R))} {L : X.left.Modules} {I : X.left.IdealSheafData}
    {n e : ℕ} (F : LogFanoFibre X L I n e) : IsProper F.pair.variety.X.hom :=
  inferInstance

/-- Valuative semistability gives `S(v)/e ≤ c · A(E)` at a divisorial valuation `v = c · ord_E`. -/
example {X : CategoryTheory.Over (Spec (.of R))} {L : X.left.Modules} {I : X.left.IdealSheafData}
    {n e : ℕ} (F : LogFanoFibre X L I n e) (h : F.IsValuativelySemistable)
    (v : MathlibExt.AlgebraicGeometry.CenteredValuationSections.CenteredValuation F.pair.variety)
    (D : MathlibExt.AlgebraicGeometry.MonomialModelRetractions.DivisorialRealization
      (P := F.pair) v) :
    ((MathlibExt.AlgebraicGeometry.CenteredValuationSections.expectedVanishing
        (F.sectionSeries v)) : EReal) / (e : EReal) ≤
      ((D.scale * MathlibExt.AlgebraicGeometry.LogPairs.logDiscrepancy D.model D.prime : ℝ) :
        EReal) :=
  h v D

section TwoModels

variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

set_option backward.isDefEq.respectTransparency false in
/-- Changing the generic line comparison by the identity leaves every power comparison fixed. -/
example (D : TwoModels (R := R) (K := K)) (m : ℕ) :
    (D.withLineAut (CategoryTheory.Iso.refl _)).powerIso m = D.powerIso m := by
  rw [TwoModels.powerIso_withLineAut]
  ext1
  simp

end TwoModels
