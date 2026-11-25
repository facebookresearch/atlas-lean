/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.UniversalBundleObstruction

/-!
# Global universal stable families

The parameter scheme of a global universal stable family is of finite type, quasi-compact and
separated, it classifies its own universal family, and classifying maps are unique.
-/

noncomputable section

namespace MathlibExtTest.UniversalBundleObstruction

open CategoryTheory MonoidalCategory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.UniversalBundleObstruction
open MathlibExt.AlgebraicGeometry.StableBundleModuli
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

variable {k : Type} [Field k] [IsAlgClosed k] {C : Over (Spec (.of k))} [IsProperCurve C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] {r : ℕ} {hr : 0 < r} {d : ℤ}

example (G : GlobalUniversalStableFamily C r hr d) : LocallyOfFiniteType G.M.hom :=
  inferInstance

example (G : GlobalUniversalStableFamily C r hr d) : QuasiCompact G.M.hom := inferInstance

example (G : GlobalUniversalStableFamily C r hr d) : IsSeparated G.M.hom := inferInstance

example (G : GlobalUniversalStableFamily C r hr d) :
    IsStableFamily C G.M r hr d G.universalBundle := G.stableFamily

/-- The representing scheme classifies its own universal family. -/
example (G : GlobalUniversalStableFamily C r hr d) :
    ∃! f : G.M ⟶ G.M,
      IsBaseTwist C G.M (familyPullback C G.M G.M G.universalBundle f) G.universalBundle :=
  G.universal G.M G.universalBundle G.stableFamily

/-- Classifying maps are unique. -/
example (G : GlobalUniversalStableFamily C r hr d) (T : Over (Spec (.of k)))
    (E : (Limits.prod C T).left.Modules) (hE : IsStableFamily C T r hr d E) (f g : T ⟶ G.M)
    (hf : IsBaseTwist C T (familyPullback C G.M T G.universalBundle f) E)
    (hg : IsBaseTwist C T (familyPullback C G.M T G.universalBundle g) E) : f = g :=
  (G.universal T E hE).unique hf hg

/-- A stable family lives on a parameter scheme of finite type. -/
example (T : Over (Spec (.of k))) (E : (Limits.prod C T).left.Modules)
    (hE : IsStableFamily C T r hr d E) : LocallyOfFiniteType T.hom := hE.1

end MathlibExtTest.UniversalBundleObstruction
