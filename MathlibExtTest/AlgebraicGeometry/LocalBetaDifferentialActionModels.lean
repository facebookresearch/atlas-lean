/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.LocalBetaDifferentialActionModels

/-!
# The local ring comparisons are canonical

The ring comparisons used by the local action tests are not free fields of
`LocalRestrictedModuleSource`: they are assembled from the monoidal comparison of `β` with inverse
image and the ordinary ring restrictions, which are fixed on actual sections. A ring automorphism
cannot be inserted into them to compensate a twisted global action.
-/

namespace MathlibExtTest.AlgebraicGeometry.LocalBetaDifferentialActionModels

open CategoryTheory TopologicalSpace MathlibExt.AlgebraicGeometry
open CompactSupportIndSheaves NativeIndDifferentialContexts
open MathlibExt.AlgebraicGeometry.LocalBetaDifferentialActionModels

variable (X : TopCat.{0}) (U : Opens X)
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [IndSpaceSource X]
  [HasSheafify (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of U)] [IndSpaceSource (TopCat.of U)]
  (R S : TopCat.Sheaf RingCat.{0} X)
  [BetaRingSource X R] [BetaRingSource X S]
  [BetaRingSource (TopCat.of U) (pulledRing X U R)]
  [BetaRingSource (TopCat.of U) (pulledRing X U S)]
  (F : Bimod (betaRing X R) (betaRing X S)) (L : LocalRestrictedModuleSource X U R S F)

example : L.leftRing =
    LocalRestrictedModuleSource.ringComparison X U R S F L R L.leftRestriction := rfl

example : L.rightRing =
    LocalRestrictedModuleSource.ringComparison X U R S F L S L.rightRestriction := rfl

end MathlibExtTest.AlgebraicGeometry.LocalBetaDifferentialActionModels
