/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicReducedPowerOperations

/-!
# The original classifying-space product diagonal for motivic Cartan

The map sends ((x,y),b) to ((x,b),(y,b)) on every original scheme
test and simplex, with all basepoint axes collapsed by the native smash
quotients. Cartan is a theorem about the canonical total power through
this exact map and the native external cup. Completed coefficient
reconstruction uses c^2=tau*d+rho*c at ell=2 and c^2=0 otherwise.

This source diagram avoids encoding the apparent bidegree typo in the
printed odd-square line of v1 Proposition 9.6.

Source: Voevodsky, arXiv:math/0107109v1, Lemma 5.7,
Theorem 6.16 and Lemma 9.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerCartanModels

open CategoryTheory Opposite
open PointedMotivicModels PointedMotivicQuotients GeneralMotivicBundleThom

variable {k : Type} [Field k]

/-- The full native diagonal sharing the original classifying-space factor. -/
structure ClassifyingPowerDiagonal (B X Y : PointedSpaces (k := k)) where
  map : smash (smash X Y) B ⟶ smash (smash X B) (smash Y B)
  normalization : ∀ (U : (FiniteTransferCycleModels.SmoothScheme k)ᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (x : (X.right.obj U).obj n) (y : (Y.right.obj U).obj n)
    (b : (B.right.obj U).obj n),
    ((map.right.app U).app n) (smashSection (smash X Y) B n U
      (smashSection X Y n U x y) b) =
    smashSection (smash X B) (smash Y B) n U
      (smashSection X B n U x b) (smashSection Y B n U y b)

end MathlibExt.AlgebraicGeometry.MotivicPowerCartanModels
