/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.AdelicIndex
public import MathlibExt.AlgebraicGeometry.Curve.DivisorPushPull

/-!
# Pole divisors of transcendental elements

This file defines pole divisors of transcendental elements together with the data used to bound `deg
D - ℓ(D)`.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve

structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where
  x : F
  B : Divisor K F
  hB_eff : 0 ≤ B
  hx_mem : x ∈ LSpace B
  n : ℕ
  hn_pos : 0 < n
  degB_eq : Divisor.degree B = n
  c : ℕ
  u : Fin n → F
  hu_mem : ∀ i, u i ∈ LSpace (c • B)
  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

def HasPoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  Nonempty (PoleDivisorPackage K F)

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where
  x : E
  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)
  v : Place K E
  hvdeg : v.deg = 1
  hxv : v.ord x = -1
  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower

variable (T : TranscendenceTower K E F)

abbrev xF : F := algebraMap E F T.x

def poleDivisor [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] : Divisor K F :=
  Divisor.pullback F (Finsupp.single T.v 1)

def RegularOutside (A : Type*) [CommRing A] [Algebra A E] (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

end TranscendenceTower

structure IntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) where
  c : ℕ
  u : Fin (Module.finrank E F) → F
  hu_indep : LinearIndependent E u
  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in
def HasIntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

variable (K E F) in
def HasIntegralBasisRegularOutside [Algebra.IsSeparable E F] (T : TranscendenceTower K E F) :
    Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

variable (K E F) in
def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

end AlgebraicCurve

end
