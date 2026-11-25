/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Degree-zero homology of module complexes

Degree-zero homology of a nonnegative complex of modules is canonically
isomorphic to the quotient by the image of its degree-one differential.
The comparison uses the homology class map and the range-quotient projection.
The ring and module carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uR w

namespace ModuleCat

variable {R : Type uR} [Ring R]
  (K : ChainComplex (ModuleCat.{w} R) ℕ) [K.HasHomology 0]

/-- Degree-zero homology of an actual module complex is the module range quotient. -/
def homologyZeroIsoRangeQuotient : K.homology 0 ≅
    ModuleCat.of R (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom) :=
  IsColimit.coconePointUniqueUpToIso (ChainComplex.homologyZeroCoforkIsColimit K)
    (ModuleCat.cokernelIsColimit (K.d 1 0))

/-- The comparison carries the native chain class to the literal module quotient class. -/
@[reassoc (attr := simp)]
theorem homologyZeroIsoRangeQuotient_class :
    ChainComplex.homologyZeroClass K ≫ (homologyZeroIsoRangeQuotient K).hom =
      ModuleCat.ofHom (LinearMap.range (K.d 1 0).hom).mkQ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (ChainComplex.homologyZeroCoforkIsColimit K) (ModuleCat.cokernelIsColimit (K.d 1 0))
    WalkingParallelPair.one

end ModuleCat
