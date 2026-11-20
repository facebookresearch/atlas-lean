/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurveSupersingular

@[expose] public section

open ModularCurve Polynomial

-- Consumer with the original binders.
example (N q : ℕ) : eichlerMass N q = ((q : ℚ) - 1) * (dedekindPsi N : ℚ) / 12 :=
  rfl

example (N q : ℕ) :
    ssCountFormula N q = eichlerMass N q
      + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
      + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3 :=
  ssCountFormula_eq N q

-- The Eichler mass at level one.
example (q : ℕ) : eichlerMass 1 q = ((q : ℚ) - 1) / 12 :=
  eichlerMass_one q

-- Boundary: the automorphism weight drops to `1` away from `0` and `1728`.
example (j : ZMod 5) (hj0 : j ≠ 0) (hj : j ≠ 1728) : autWeight 5 j = 1 :=
  autWeight_of_ne 5 (by norm_num) (by norm_num) j hj0 hj

example : ssPolyTwo = X := ssPolyTwo_eq

example : ssSetEleven.card = 2 := ssSetEleven_card

-- Consumer for the supersingular `j` set with the original binders.
example (p : ℕ) (K : Type*) [Field K] [DecidableEq K] (j : K) :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  mem_ssJSet_iff
