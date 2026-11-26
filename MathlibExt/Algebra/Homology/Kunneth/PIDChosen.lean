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
# The objectwise Künneth row for a chosen Cartan–Eilenberg resolution

Let R be a commutative principal ideal domain and K,L nonnegative chain complexes of R-modules
in universe u, with every K_a flat. Choose a Cartan–Eilenberg resolution P_L of L and specialize
the supplied-resolution Künneth row to this choice.

In degree n the terms are ⊕_{i+j=n}H_i(K)⊗_R H_j(L), H_n(K⊗_R L), and
⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)). The first map remains the canonical homology tensor map; the
right edge is the one constructed from P_L. The resulting objectwise row is short exact.

For the classical sequence, see Weibel, An Introduction to Homological Algebra, Theorem 3.6.3,
and May, A Concise Course in Algebraic Topology, Chapter 17 §2.
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

/-- Let R be a commutative principal ideal domain, with R-modules in the same universe u. Let K,L be
nonnegative chain complexes and assume every term K_a is flat over R. Put T_n=⊕_{i+j=n}H_i(K)⊗_R
H_j(L) and U_n=⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)); U₀=0. Select the Cartan–Eilenberg resolution
P_L of L. In every n≥0, the chosen short complex is T_n→H_n(K⊗_R L)→U_n obtained by specializing
the supplied-resolution construction to P_L. -/
noncomputable abbrev kunnethChosenShortComplex
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  kunnethShortComplexOfResolution K
    (CartanEilenbergResolution.of L) hK n

/-- Let R be a commutative principal ideal domain, with R-modules in the same universe u. Let K,L be
nonnegative chain complexes and assume every term K_a is flat over R. Put T_n=⊕_{i+j=n}H_i(K)⊗_R
H_j(L) and U_n=⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)); U₀=0. For n≥0, the first arrow of the chosen
Künneth short complex equals the canonical map T_n→H_n(K⊗_R L). On a tensor of homology classes
it is the class of the corresponding tensor of cycles in total degree n. -/
theorem kunnethChosenShortComplex_f_eq_kunnethHomologyTensorMap
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (kunnethChosenShortComplex K L hK n).f =
      kunnethHomologyTensorMap K L n :=
  kunnethShortComplexOfResolution_f_eq_kunnethHomologyTensorMap K
    (CartanEilenbergResolution.of L) hK n

/-- Let R be a commutative principal ideal domain, with R-modules in the same universe u. Let K,L be
nonnegative chain complexes and assume every term K_a is flat over R. Put T_n=⊕_{i+j=n}H_i(K)⊗_R
H_j(L) and U_n=⊕_{i+j+1=n}Tor₁^R(H_i(K),H_j(L)); U₀=0. For every n≥0, the row built from the
chosen Cartan–Eilenberg resolution of L is short exact: 0→T_n→H_n(K⊗_R L)→U_n→0. At degree zero
its Tor-one term is zero. -/
theorem kunnethChosenShortComplex_shortExact
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (kunnethChosenShortComplex K L hK n).ShortExact :=
  kunnethShortComplexOfResolution_shortExact K
    (CartanEilenbergResolution.of L) hK n

end HomologicalComplex
