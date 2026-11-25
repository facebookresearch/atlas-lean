/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Depth.CohenMacaulaySystemOfParameters

open IsLocalRing RingTheory

universe u

theorem exactSource
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (IsLocalRing.depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs :=
  IsLocalRing.isRegular_of_systemOfParameters hCM hdim xs hlen hmem hsop

/-- The statement applies to rings in higher universes. -/
example {R : Type (u + 1)} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (IsLocalRing.depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs :=
  IsLocalRing.isRegular_of_systemOfParameters hCM hdim xs hlen hmem hsop

/-- A one-element system of parameters is a nonzerodivisor. -/
example {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (IsLocalRing.depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim R = 1) {x : R} (hx : x ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList [x]) = 0) :
    IsSMulRegular R x := by
  have h := IsLocalRing.isRegular_of_systemOfParameters hCM (d := 1) (by exact_mod_cast hdim)
    [x] rfl (by simpa using hx) hsop
  exact ((RingTheory.Sequence.isWeaklyRegular_cons_iff R x []).mp h.toIsWeaklyRegular).1
