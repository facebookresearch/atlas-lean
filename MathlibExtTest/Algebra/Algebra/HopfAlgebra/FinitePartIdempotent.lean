/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.HopfAlgebra.FinitePartIdempotent

@[expose] public section

universe u v

example (R : Type*) [CommRing R] [IsLocalRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e)))
      (IsLocalRing.maximalIdeal R) = ⊤) :
    HopfAlgebra.antipode R e = e :=
  HopfAlgebra.antipode_finitePartIdempotent R H e he hfin hgen

example (R : Type u) [CommRing R] [IsLocalRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e)
    (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e)))
      (IsLocalRing.maximalIdeal R) = ⊤) :
    HopfAlgebra.antipode R e = e :=
  HopfAlgebra.antipode_finitePartIdempotent R H e he hfin hgen
