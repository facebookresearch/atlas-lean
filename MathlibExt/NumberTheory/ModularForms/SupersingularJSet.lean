/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_EichlerMass.lean`,
`Definitions/Def_ModularCurve_SupersingularLocus.lean` and
`Definitions/Def_ModularCurve_SupersingularModuli.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.Divisors

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace ModularCurve

/-- The Dedekind psi function in divisor-sum form, `∑_{d ∣ N, d squarefree} N / d`. -/
public noncomputable def dedekindPsi (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors.filter Squarefree, N / d

@[simp] public theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, if_pos squarefree_one]
  simp

/-- The number of roots of `x ^ 2 + 1` in `ZMod N`. -/
public noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

/-- The number of roots of `x ^ 2 + x + 1` in `ZMod N`. -/
public noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

/-- The Eichler mass `(q - 1) * ψ(N) / 12` as a rational number. -/
public noncomputable def eichlerMass (N q : ℕ) : ℚ := ((q : ℚ) - 1) * (dedekindPsi N : ℚ) / 12

/-- The supersingular count formula built from the Eichler mass and the
`ν₂`, `ν₃` corrections. -/
public noncomputable def ssCountFormula (N q : ℕ) : ℚ :=
  eichlerMass N q + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3

public theorem eichlerMass_one (q : ℕ) : eichlerMass 1 q = ((q : ℚ) - 1) / 12 := by
  simp [eichlerMass]

/-- The weight `1 / |Aut|` denominator for a supersingular `j`-invariant:
`12` in characteristic `2` at `j = 0`, `6` in characteristic `3` at `j = 0`,
`3` at `j = 0`, `2` at `j = 1728`, and `1` otherwise. -/
public def autWeight (q : ℕ) (j : ZMod q) : ℕ :=
  if q = 2 then (if j = 0 then 12 else 1)
  else if q = 3 then (if j = 0 then 6 else 1)
  else if j = 0 then 3 else if j = 1728 then 2 else 1

public theorem autWeight_two_zero : autWeight 2 0 = 12 := by simp [autWeight]
public theorem autWeight_three_zero : autWeight 3 0 = 6 := by simp [autWeight]

public theorem autWeight_of_ne {q : ℕ} (h2 : q ≠ 2) (h3 : q ≠ 3) {j : ZMod q}
    (h0 : j ≠ 0) (h1728 : j ≠ 1728) : autWeight q j = 1 := by
  simp [autWeight, h2, h3, h0, h1728]

/-- The supersingular `j`-invariants in characteristic `2`. -/
public def ssSetTwo : Finset (ZMod 2) := {0}
/-- The supersingular `j`-invariants in characteristic `3`. -/
public def ssSetThree : Finset (ZMod 3) := {0}
/-- The supersingular `j`-invariants in characteristic `5`. -/
public def ssSetFive : Finset (ZMod 5) := {0}
/-- The supersingular `j`-invariants in characteristic `7`. -/
public def ssSetSeven : Finset (ZMod 7) := {1728}
/-- The supersingular `j`-invariants in characteristic `11`. -/
public def ssSetEleven : Finset (ZMod 11) := {0, 1728}
/-- The supersingular `j`-invariants in characteristic `13`. -/
public def ssSetThirteen : Finset (ZMod 13) := {5}

/-- The supersingular polynomial in characteristic `2`, the product of
`X - j` over the supersingular `j`-invariants. -/
public noncomputable def ssPolyTwo : Polynomial (ZMod 2) :=
  ∏ a ∈ ssSetTwo, (Polynomial.X - Polynomial.C a)
/-- The supersingular polynomial in characteristic `3`. -/
public noncomputable def ssPolyThree : Polynomial (ZMod 3) :=
  ∏ a ∈ ssSetThree, (Polynomial.X - Polynomial.C a)
/-- The supersingular polynomial in characteristic `5`. -/
public noncomputable def ssPolyFive : Polynomial (ZMod 5) :=
  ∏ a ∈ ssSetFive, (Polynomial.X - Polynomial.C a)
/-- The supersingular polynomial in characteristic `7`. -/
public noncomputable def ssPolySeven : Polynomial (ZMod 7) :=
  ∏ a ∈ ssSetSeven, (Polynomial.X - Polynomial.C a)
/-- The supersingular polynomial in characteristic `11`. -/
public noncomputable def ssPolyEleven : Polynomial (ZMod 11) :=
  ∏ a ∈ ssSetEleven, (Polynomial.X - Polynomial.C a)
/-- The supersingular polynomial in characteristic `13`. -/
public noncomputable def ssPolyThirteen : Polynomial (ZMod 13) :=
  ∏ a ∈ ssSetThirteen, (Polynomial.X - Polynomial.C a)

public theorem ssPolyTwo_eq : ssPolyTwo = Polynomial.X - Polynomial.C 0 := by
  simp [ssPolyTwo, ssSetTwo]
public theorem card_ssSetEleven : ssSetEleven.card = 2 := by decide

/-- The first coefficient of the model curve attached to a supersingular
`j`-invariant. -/
public def ssModelA (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

/-- The second coefficient of the model curve attached to a supersingular
`j`-invariant. -/
public def ssModelB (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

public theorem ssModelA_zero (q : ℕ) [NeZero q] : ssModelA q 0 = 0 := by simp [ssModelA]
public theorem ssModelB_zero (q : ℕ) [NeZero q] : ssModelB q 0 = 1 := by simp [ssModelB]

/-- The number of affine points on `y ^ 2 = x ^ 3 + A * x + B` over `ZMod q`. -/
public def affinePointCount (q : ℕ) [NeZero q] (A B : ZMod q) : ℕ :=
  (Finset.univ.filter fun p : ZMod q × ZMod q => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B).card

public theorem affinePointCount_le (q : ℕ) [NeZero q] (A B : ZMod q) :
    affinePointCount q A B ≤ q ^ 2 := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  simp [pow_two]

/-- The set of supersingular `j`-invariants in `K` at `p`: those `j` for which
every elliptic curve over `K` with that `j`-invariant has trivial `p`-torsion. -/
public def ssJSet (p : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
    ∀ P : W.toAffine.Point, p • P = 0 → P = 0}

public theorem mem_ssJSet_iff {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K} :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl

end ModularCurve
