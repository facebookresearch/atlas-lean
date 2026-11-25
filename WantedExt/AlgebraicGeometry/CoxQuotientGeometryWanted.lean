/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

/-!
# Cox quotient maps with the actual diagonal gauge action

Cox, alg-geom/9210008v3, Theorem 2.1. The categorical quotient has the
general finite-fan scope with spanning rays. The orbit-fibre statement
is restricted to simplicial fans and complex-valued points.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoxQuotientGeometryWanted

open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

open CategoryTheory FiniteToricCoordinates CoxGradedSheaves CoxNormalizedSheafification

def_wanted cox_projection {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (L : LocalCover R) (C : ChartComparison R) (T : Realization ℂ F) :
    Projection R L C T

theorem_wanted cox_projection_invariant {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (L : LocalCover R) (C : ChartComparison R) (T : Realization ℂ F)
    (P : Projection R L C T) (G : GaugeAction R) : IsInvariant R G P.map

theorem_wanted cox_categorical_quotient {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (L : LocalCover R) (C : ChartComparison R) (T : Realization ℂ F)
    (P : Projection R L C T) (G : GaugeAction R) (W : SchemeOver ℂ)
    (q : openScheme R ⟶ W) (h : IsInvariant R G q) :
    ∃! u : T.scheme ⟶ W, P.map ≫ u = q

theorem_wanted cox_simplicial_orbit_fibres {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (h : IsSimplicial R) (L : LocalCover R) (C : ChartComparison R)
    (T : Realization ℂ F) (P : Projection R L C T) (G : GaugeAction R)
    (p q : testScheme (CommAlgCat.of ℂ ℂ) ⟶ openScheme R) :
    p ≫ P.map = q ≫ P.map ↔ ∃ g : Gauge R (CommAlgCat.of ℂ ℂ),
      G.act (CommAlgCat.of ℂ ℂ) g p = q

end WantedExt.AlgebraicGeometry.CoxQuotientGeometryWanted

