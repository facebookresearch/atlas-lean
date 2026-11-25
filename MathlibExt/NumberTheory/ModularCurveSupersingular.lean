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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import MathlibExt.AlgebraicGeometry.EllipticCurve.Supersingular
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi

@[expose] public section

open Polynomial

namespace ModularCurve

/-- The number of square roots of `-1` modulo `N`. -/
noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

/-- The number of roots of `x ^ 2 + x + 1` modulo `N`. -/
noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

/-- The Eichler mass `(p - 1) ψ(N) / 12` of level `N` in prime characteristic `p`, where `ψ` is
the Dedekind psi function `ArithmeticFunction.dedekindPsi`. For a level `N ≥ 1` not divisible by
`p`, Eichler's mass formula identifies it with the weighted number of supersingular points of
`X₀(N)` over an algebraic closure of `ZMod p`; that formula is not proved here. -/
noncomputable def eichlerMass (N p : ℕ) [Fact p.Prime] : ℚ :=
  ((p : ℚ) - 1) * (ArithmeticFunction.dedekindPsi N : ℚ) / 12

/-- The supersingular point-count formula of level `N` in prime characteristic `p`, with `ν₂` and
`ν₃` (`nuTwo`, `nuThree`) evaluated at the level `N` and in the prime field `ZMod p`. For a level
`N ≥ 1` not divisible by `p` it gives the number of supersingular points of `X₀(N)` over an
algebraic closure of `ZMod p`; that count is not proved here. -/
noncomputable def ssCountFormula (N p : ℕ) [Fact p.Prime] : ℚ :=
  eichlerMass N p
    + (2 - (nuTwo p : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree p : ℚ)) * (nuThree N : ℚ) / 3

public theorem eichlerMass_one (p : ℕ) [Fact p.Prime] :
    eichlerMass 1 p = ((p : ℚ) - 1) / 12 := by
  simp [eichlerMass]

public theorem ssCountFormula_eq (N p : ℕ) [Fact p.Prime] :
    ssCountFormula N p = eichlerMass N p
      + (2 - (nuTwo p : ℚ)) * (nuTwo N : ℚ) / 4
      + (2 - (nuThree p : ℚ)) * (nuThree N : ℚ) / 3 :=
  rfl

/-- The automorphism weight `#Aut(E) / 2` of an elliptic curve `E` with `j`-invariant `j` over an
algebraic closure of the field `F`: `12` for `j = 0` in characteristic `2`, `6` for `j = 0` in
characteristic `3`, and otherwise `3` for `j = 0`, `2` for `j = 1728` and `1` for every other
`j`. -/
noncomputable def autWeight {F : Type*} [Field F] [DecidableEq F] (j : F) : ℕ :=
  if ringChar F = 2 then (if j = 0 then 12 else 1)
  else if ringChar F = 3 then (if j = 0 then 6 else 1)
  else if j = 0 then 3
  else if j = 1728 then 2
  else 1

public theorem autWeight_two_zero {F : Type*} [Field F] [DecidableEq F] (hF : ringChar F = 2) :
    autWeight (0 : F) = 12 := by
  simp [autWeight, hF]

public theorem autWeight_three_zero {F : Type*} [Field F] [DecidableEq F] (hF : ringChar F = 3) :
    autWeight (0 : F) = 6 := by
  simp [autWeight, hF]

public theorem autWeight_of_ne {F : Type*} [Field F] [DecidableEq F] (h2 : ringChar F ≠ 2)
    (h3 : ringChar F ≠ 3) (j : F) (hj0 : j ≠ 0) (hj : j ≠ 1728) : autWeight j = 1 := by
  simp [autWeight, h2, h3, hj0, hj]

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

end

section Model

variable {F : Type*} [Field F] [DecidableEq F]

/-- The coefficient `A` of the short Weierstrass model `y ^ 2 = x ^ 3 + A x + B` of
`j`-invariant `j` (see `ssModel`). -/
def ssModelA (j : F) : F :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

/-- The coefficient `B` of the short Weierstrass model `y ^ 2 = x ^ 3 + A x + B` of
`j`-invariant `j` (see `ssModel`). -/
def ssModelB (j : F) : F :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

/-- The short Weierstrass curve `y ^ 2 = x ^ 3 + A x + B` with `A = ssModelA j` and
`B = ssModelB j`. When the characteristic of `F` is neither `2` nor `3`, it is an elliptic curve
(`isElliptic_ssModel`) with `j`-invariant `j` (`ssModel_j`). In characteristic `2` or `3` it is
singular for every `j` (`ssModel_Δ_eq_zero`); there `WeierstrassCurve.ofJ j` is an elliptic curve
with `j`-invariant `j` in generalized Weierstrass form. -/
def ssModel (j : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := ssModelA j, a₆ := ssModelB j }

public theorem ssModel_Δ (j : F) :
    (ssModel j).Δ = -16 * (4 * ssModelA j ^ 3 + 27 * ssModelB j ^ 2) := by
  simp only [ssModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

public theorem ssModel_c₄ (j : F) : (ssModel j).c₄ = -48 * ssModelA j := by
  simp only [ssModel, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- The short model `ssModel j` is nonsingular when `2` and `3` are nonzero in `F`. -/
public theorem ssModel_Δ_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (j : F) :
    (ssModel j).Δ ≠ 0 := by
  rw [ssModel_Δ]
  by_cases h0 : j = 0
  · simp only [ssModelA, ssModelB, h0, ↓reduceIte]
    rw [show (-16 * (4 * 0 ^ 3 + 27 * 1 ^ 2) : F) = -(2 ^ 4 * 3 ^ 3) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))
  by_cases h1728 : j = 1728
  · have h0' : (1728 : F) ≠ 0 := h1728 ▸ h0
    simp only [ssModelA, ssModelB, h1728, h0', ↓reduceIte]
    rw [show (-16 * (4 * 1 ^ 3 + 27 * 0 ^ 2) : F) = -(2 ^ 6) by ring]
    exact neg_ne_zero.mpr (pow_ne_zero _ h2)
  simp only [ssModelA, ssModelB, h0, h1728, ↓reduceIte]
  rw [show -16 * (4 * (3 * j * (1728 - j)) ^ 3 + 27 * (2 * j * (1728 - j) ^ 2) ^ 2) =
      -(2 ^ 12 * 3 ^ 6 * j ^ 2 * (1728 - j) ^ 3) by ring]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2)
    (pow_ne_zero _ h3)) (pow_ne_zero _ h0)) (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h1728))))

/-- In characteristic `2` or `3` the short model `ssModel j` is singular for every `j`. -/
public theorem ssModel_Δ_eq_zero (h : (2 : F) = 0 ∨ (3 : F) = 0) (j : F) :
    (ssModel j).Δ = 0 := by
  rw [ssModel_Δ]
  rcases h with h | h
  · linear_combination (-8 * (4 * ssModelA j ^ 3 + 27 * ssModelB j ^ 2)) * h
  by_cases h0 : j = 0
  · simp only [ssModelA, ssModelB, h0, ↓reduceIte]
    linear_combination -144 * h
  have h1728 : j ≠ 1728 := fun h' => h0 (h'.trans (by linear_combination 576 * h))
  simp only [ssModelA, ssModelB, h0, h1728, ↓reduceIte]
  linear_combination (-576 * j ^ 3 * (1728 - j) ^ 3 - 576 * j ^ 2 * (1728 - j) ^ 4) * h

instance isElliptic_ssModel [NeZero (2 : F)] [NeZero (3 : F)] (j : F) :
    (ssModel j).IsElliptic :=
  ⟨(ssModel_Δ_ne_zero (NeZero.ne 2) (NeZero.ne 3) j).isUnit⟩

/-- The short model `ssModel j` has `j`-invariant `j` when `2` and `3` are nonzero in `F`. -/
public theorem ssModel_j [NeZero (2 : F)] [NeZero (3 : F)] (j : F) : (ssModel j).j = j := by
  rw [WeierstrassCurve.j_eq, inv_mul_eq_iff_eq_mul₀
    (ssModel_Δ_ne_zero (NeZero.ne 2) (NeZero.ne 3) j), ssModel_Δ, ssModel_c₄]
  by_cases h0 : j = 0
  · simp [ssModelA, h0]
  by_cases h1728 : j = 1728
  · have h0' : (1728 : F) ≠ 0 := h1728 ▸ h0
    simp only [ssModelA, ssModelB, h1728, h0', ↓reduceIte]
    ring
  simp only [ssModelA, ssModelB, h0, h1728, ↓reduceIte]
  ring

/-- The number of affine points `(x, y) ∈ F × F` on `y ^ 2 = x ^ 3 + A x + B` over a finite field
`F`. For `A = ssModelA j` and `B = ssModelB j` these are the affine points of `ssModel j`. -/
def affinePointCount [Fintype F] (A B : F) : ℕ :=
  (Finset.univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B).card

end Model

/-- The supersingular `j`-invariants in characteristic `p`: the values `j` in an algebraic closure
of `ZMod p` such that every elliptic curve over that algebraic closure with `j`-invariant `j` is
supersingular in the sense of `WeierstrassCurve.Affine.IsSupersingular`, that is, has no nonzero
geometric point killed by `p`. -/
def ssJSet (p : ℕ) [Fact p.Prime] : Set (AlgebraicClosure (ZMod p)) :=
  {j | ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic], W.j = j →
    W.toAffine.IsSupersingular}

public theorem mem_ssJSet_iff {p : ℕ} [Fact p.Prime] {j : AlgebraicClosure (ZMod p)} :
    j ∈ ssJSet p ↔ ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic],
      W.j = j → W.toAffine.IsSupersingular :=
  Iff.rfl

end ModularCurve
