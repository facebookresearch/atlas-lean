/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdeleRingAut

@[expose] public section

open NumberField IsDedekindDomain

/-- The identity automorphism of the adele ring lies over the identity of `L`. -/
example (L : Type*) [Field L] [NumberField L] (v : InfinitePlace L)
    (a : AdeleRing (𝓞 L) L) :
    ‖(RingEquiv.refl (AdeleRing (𝓞 L) L) a).1 (v.comap ((RingEquiv.refl L).symm : L →+* L))‖ =
      ‖a.1 v‖ :=
  AdeleRing.norm_fst_map_comap (RingEquiv.refl _) continuous_id continuous_id
    (RingEquiv.refl L) (fun _ => rfl) v a

/-- The finite-place statement for the identity. -/
example (L : Type*) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (a : AdeleRing (𝓞 L) L) :
    ‖(RingEquiv.refl (AdeleRing (𝓞 L) L) a).2
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv (RingEquiv.refl L)) w)‖
      = ‖a.2 w‖ :=
  AdeleRing.norm_snd_map_equivOfRingEquiv (RingEquiv.refl _) continuous_id continuous_id
    (RingEquiv.refl L) (fun _ => rfl) w a
