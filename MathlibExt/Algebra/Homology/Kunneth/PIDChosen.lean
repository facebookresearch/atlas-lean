/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.CartanEilenberg.Existence
public import MathlibExt.Algebra.Homology.Kunneth.PID

/-!
# The objectwise Künneth sequence for a chosen resolution

This file specializes the supplied-resolution PID Künneth construction to
the repository's noncomputably chosen Cartan--Eilenberg resolution.  See
Weibel, *An Introduction to Homological Algebra*, Theorem 3.6.3, and May,
*A Concise Course in Algebraic Topology*, Chapter 17 §2, for the classical
chain-complex Künneth sequence.

The complexes are nonnegatively graded and the result is objectwise.  The
choice does not supply functoriality or make the right edge independent of
the resolution, and this module proves neither a natural splitting nor the
classical noncanonical splitting.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- The supplied-resolution PID Künneth short complex specialized to the
repository's chosen Cartan--Eilenberg resolution. This is objectwise and does
not assert resolution independence or naturality. -/
noncomputable abbrev kunnethChosenShortComplex
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  kunnethShortComplexOfResolution K
    (CartanEilenbergResolution.of L) hK n

/-- The chosen short complex retains the canonical Künneth tensor map as its
left arrow. -/
theorem kunnethChosenShortComplex_f_eq_kunnethHomologyTensorMap
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (kunnethChosenShortComplex K L hK n).f =
      kunnethHomologyTensorMap K L n :=
  kunnethShortComplexOfResolution_f_eq_kunnethHomologyTensorMap K
    (CartanEilenbergResolution.of L) hK n

/-- The chosen objectwise PID Künneth short complex is exact. -/
theorem kunnethChosenShortComplex_shortExact
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (kunnethChosenShortComplex K L hK n).ShortExact :=
  kunnethShortComplexOfResolution_shortExact K
    (CartanEilenbergResolution.of L) hK n

end HomologicalComplex
