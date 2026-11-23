/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.OriginalQK0UniverseLiftCompatibility

noncomputable section

open CategoryTheory
open AlgebraicKTheory
open AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility

universe uR uM uObj uHom uNative

#check @originalComponentsEquivK0
#print axioms originalComponentsEquivK0
#check @canonicalLoopComponentsK0_bijective
#print axioms canonicalLoopComponentsK0_bijective
#check @categoryK0Equiv
#print axioms categoryK0Equiv
#check @categoryK0Equiv_up
#print axioms categoryK0Equiv_up
#check @nativeLoopFixedK0
#print axioms nativeLoopFixedK0
#check @nativeLoopFixedK0_formula
#print axioms nativeLoopFixedK0_formula
#check @nativeLoopFixedK0_surjective
#print axioms nativeLoopFixedK0_surjective
#check @Qdown_fixedK0
#print axioms Qdown_fixedK0
#check @Qup_fixedK0
#print axioms Qup_fixedK0
#check @Qdown_canonicalEvaluator
#print axioms Qdown_canonicalEvaluator

namespace AlgebraicKTheory.OriginalQK0UniverseLiftCompatibilityTests

attribute [local instance]
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmFunctorAdditive
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmInverseAdditive
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmFunctorIsExact
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmInverseIsExact


-- The class formula has no comparison or homotopy-equivalence argument.
example (R : Type uR) [Ring R]
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.equivOfEquivalence
          (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
          (OriginalQK0Comparison.canonicalLoopComponentsK0
            (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
            (ZerothHomotopy.mk
              (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)))) :=
  nativeLoopFixedK0_formula.{uR, uM, uObj, uHom, uNative} R p

-- Every original fixed RingK0 class is represented in the whole native loop space.
example (R : Type uR) [Ring R] (k : RingK0 R) :
    ∃ p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R,
      nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p = k :=
  nativeLoopFixedK0_surjective.{uR, uM, uObj, uHom, uNative} R k

-- The actual Q descent is compared to the independent original CL evaluator.
example (R : Type uR) [Ring R]
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    originalLoopFixedK0.{uR, uM} R
        (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R p) =
      nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p :=
  Qdown_fixedK0.{uR, uM, uObj, uHom, uNative} R p

-- The actual inverse preserves the same original fixed class.
example (R : Type uR) [Ring R]
    (p : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R
        (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R p) =
      originalLoopFixedK0.{uR, uM} R p :=
  Qup_fixedK0.{uR, uM, uObj, uHom, uNative} R p

-- The actual Hom universe can exceed the object, module and chosen native levels.
example (R : Type) [Ring R] (k : RingK0 R) :
    ∃ p : QuillenUniverseLift.nativeRawLoopSpace.{0, 0, 1, 4, 2} R,
      nativeLoopFixedK0.{0, 0, 1, 4, 2} R p = k :=
  nativeLoopFixedK0_surjective.{0, 0, 1, 4, 2} R k

example (R : Type) [Ring R]
    (p : QuillenUniverseLift.nativeRawLoopSpace.{0, 0, 1, 4, 2} R) :
    originalLoopFixedK0.{0, 0} R (QuillenUniverseLift.Qdown.{0, 0, 1, 4, 2} R p) =
      nativeLoopFixedK0.{0, 0, 1, 4, 2} R p :=
  Qdown_fixedK0.{0, 0, 1, 4, 2} R p

-- The actual object and native levels can independently exceed the Hom level.
example (R : Type) [Ring R] (k : RingK0 R) :
    ∃ p : QuillenUniverseLift.nativeRawLoopSpace.{0, 1, 3, 0, 4} R,
      nativeLoopFixedK0.{0, 1, 3, 0, 4} R p = k :=
  nativeLoopFixedK0_surjective.{0, 1, 3, 0, 4} R k

end AlgebraicKTheory.OriginalQK0UniverseLiftCompatibilityTests

end
