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

The representing scheme classifies its own universal family, classifying maps
are unique, and rank-zero families are never stable over a base with a
rational point, so the stable-family hypothesis of the universal property is
not automatic.
-/

noncomputable section

namespace MathlibExtTest.UniversalBundleObstruction

open CategoryTheory MonoidalCategory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.UniversalBundleObstruction
open MathlibExt.AlgebraicGeometry.StableBundleModuli
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

variable {k : Type} [Field k] {C : Over (Spec (.of k))} {r : ℕ} {d : ℤ}

example (G : GlobalUniversalStableFamily C r d) : LocallyOfFiniteType G.M.hom := G.finiteType

example (G : GlobalUniversalStableFamily C r d) : IsSeparated G.M.hom := G.separated

example (G : GlobalUniversalStableFamily C r d) :
    IsStableFamily C G.M r d G.universalBundle := G.stableFamily

/-- The representing scheme classifies its own universal family. -/
example (G : GlobalUniversalStableFamily C r d) :
    ∃! f : G.M ⟶ G.M,
      IsBaseTwist C G.M (familyPullback C G.M G.M G.universalBundle f) G.universalBundle :=
  G.universal G.M G.finiteType G.quasiCompact G.universalBundle G.stableFamily

/-- Classifying maps are unique. -/
example (G : GlobalUniversalStableFamily C r d) (T : Over (Spec (.of k)))
    (hT : LocallyOfFiniteType T.hom) (hq : QuasiCompact T.hom)
    (E : (Limits.prod C T).left.Modules) (hE : IsStableFamily C T r d E) (f g : T ⟶ G.M)
    (hf : IsBaseTwist C T (familyPullback C G.M T G.universalBundle f) E)
    (hg : IsBaseTwist C T (familyPullback C G.M T G.universalBundle g) E) : f = g :=
  (G.universal T hT hq E hE).unique hf hg

/-- Stability needs positive rank at every rational point. -/
example (T : Over (Spec (.of k))) (x : 𝟙_ (Over (Spec (.of k))) ⟶ T)
    (E : (Limits.prod C T).left.Modules) : ¬ IsStableFamily C T 0 d E := by
  rintro ⟨-, h⟩
  exact lt_irrefl 0 (h x).1.1

end MathlibExtTest.UniversalBundleObstruction
