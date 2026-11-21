/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_EichlerMass.lean`,
`Definitions/Def_ModularCurve_SupersingularLocus.lean`, and
`Definitions/Def_ModularCurve_SupersingularModuli.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open Polynomial

namespace ModularCurve

/-- The Dedekind psi function: `ψ(N) = ∑ d ∈ N.divisors with Squarefree d, N / d`. -/
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]
public theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  classical
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, if_pos squarefree_one]
  simp

/-- The number of square roots of `-1` modulo `N`. -/
noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

/-- The number of roots of `x ^ 2 + x + 1` modulo `N`. -/
noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

/-- The Eichler mass of level `N` at prime power parameter `q`. -/
noncomputable def eichlerMass (N q : ℕ) : ℚ :=
  ((q : ℚ) - 1) * (dedekindPsi N : ℚ) / 12

/-- The supersingular point-count formula of level `N` at `q`. -/
noncomputable def ssCountFormula (N q : ℕ) : ℚ :=
  eichlerMass N q
    + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3

public theorem eichlerMass_one (q : ℕ) : eichlerMass 1 q = ((q : ℚ) - 1) / 12 := by
  rw [eichlerMass, dedekindPsi_one]
  norm_num

public theorem ssCountFormula_eq (N q : ℕ) :
    ssCountFormula N q = eichlerMass N q
      + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
      + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3 :=
  rfl

/-- The automorphism weight of the `j`-invariant modulo `q`. -/
def autWeight (q : ℕ) (j : ZMod q) : ℕ :=
  if q = 2 then (if j = 0 then 12 else 1)
  else if q = 3 then (if j = 0 then 6 else 1)
  else if j = 0 then 3
  else if j = 1728 then 2
  else 1

public theorem autWeight_two_zero : autWeight 2 0 = 12 := rfl

public theorem autWeight_three_zero : autWeight 3 0 = 6 := rfl

public theorem autWeight_of_ne (q : ℕ) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (j : ZMod q)
    (hj0 : j ≠ 0) (hj : j ≠ 1728) : autWeight q j = 1 := by
  rw [autWeight, if_neg hq2, if_neg hq3, if_neg hj0, if_neg hj]

/-- Supersingular `j`-invariants modulo `2`. -/
def ssSetTwo : Finset (ZMod 2) := {0}

/-- Supersingular `j`-invariants modulo `3`. -/
def ssSetThree : Finset (ZMod 3) := {0}

/-- Supersingular `j`-invariants modulo `5`. -/
def ssSetFive : Finset (ZMod 5) := {0}

/-- Supersingular `j`-invariants modulo `7`. -/
def ssSetSeven : Finset (ZMod 7) := {1728}

/-- Supersingular `j`-invariants modulo `11`. -/
def ssSetEleven : Finset (ZMod 11) := {0, 1728}

/-- Supersingular `j`-invariants modulo `13`. -/
def ssSetThirteen : Finset (ZMod 13) := {5}

noncomputable section

/-- The supersingular polynomial modulo `2`. -/
def ssPolyTwo : Polynomial (ZMod 2) := ∏ a ∈ ssSetTwo, (X - C a)

/-- The supersingular polynomial modulo `3`. -/
def ssPolyThree : Polynomial (ZMod 3) := ∏ a ∈ ssSetThree, (X - C a)

/-- The supersingular polynomial modulo `5`. -/
def ssPolyFive : Polynomial (ZMod 5) := ∏ a ∈ ssSetFive, (X - C a)

/-- The supersingular polynomial modulo `7`. -/
def ssPolySeven : Polynomial (ZMod 7) := ∏ a ∈ ssSetSeven, (X - C a)

/-- The supersingular polynomial modulo `11`. -/
def ssPolyEleven : Polynomial (ZMod 11) := ∏ a ∈ ssSetEleven, (X - C a)

/-- The supersingular polynomial modulo `13`. -/
def ssPolyThirteen : Polynomial (ZMod 13) := ∏ a ∈ ssSetThirteen, (X - C a)

public theorem ssPolyTwo_eq : ssPolyTwo = X := by
  simp [ssPolyTwo, ssSetTwo]

public theorem ssSetEleven_card : ssSetEleven.card = 2 := by
  decide

public theorem ssPolyEleven_monic : ssPolyEleven.Monic := by
  rw [ssPolyEleven]
  exact monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a

/-- First Weierstrass coefficient of the model curve at `j`. -/
def ssModelA (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

/-- Second Weierstrass coefficient of the model curve at `j`. -/
def ssModelB (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

/-- The number of affine `ZMod q`-points on `y ^ 2 = x ^ 3 + A x + B`. -/
def affinePointCount (q : ℕ) [NeZero q] (A B : ZMod q) : ℕ :=
  (Finset.univ.filter fun p : ZMod q × ZMod q => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B).card

/-- The set of supersingular `j`-invariants in `K`: every elliptic curve with
that `j`-invariant has no nonzero `p`-torsion point. -/
def ssJSet (p : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
    ∀ P : W.toAffine.Point, p • P = 0 → P = 0}

public theorem mem_ssJSet_iff {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K} :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl

end

end ModularCurve
