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
public import MathlibExt.AlgebraicGeometry.EllipticCurve.Supersingular
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace ModularCurve

/-- The number of roots of `x ^ 2 + 1` in `ZMod N`. -/
public noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

/-- The number of roots of `x ^ 2 + x + 1` in `ZMod N`. -/
public noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

/-- The Eichler mass `(q - 1) * ψ(N) / 12` as a rational number, where `ψ` is the Dedekind psi
function `ArithmeticFunction.dedekindPsi`. -/
public noncomputable def eichlerMass (N q : ℕ) : ℚ :=
  ((q : ℚ) - 1) * (ArithmeticFunction.dedekindPsi N : ℚ) / 12

/-- The supersingular count formula built from the Eichler mass and the
`ν₂`, `ν₃` corrections. -/
public noncomputable def ssCountFormula (N q : ℕ) : ℚ :=
  eichlerMass N q + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3

public theorem eichlerMass_one (q : ℕ) : eichlerMass 1 q = ((q : ℚ) - 1) / 12 := by
  simp [eichlerMass]

/-- The automorphism weight of a supersingular `j`-invariant in prime characteristic `q`: half the
order of the automorphism group of an elliptic curve `E` over an algebraic closure of `ZMod q`
with `j`-invariant `j`, that is, the order of `Aut E / {±1}`. It is `12` in characteristic `2` at
`j = 0` (`|Aut E| = 24`), `6` in characteristic `3` at `j = 0` (`|Aut E| = 12`), `3` at `j = 0`
(`|Aut E| = 6`) and `2` at `j = 1728` (`|Aut E| = 4`) in characteristic greater than `3`, and `1`
otherwise (`|Aut E| = 2`). So `1 / autWeight q j` is the normalized weight `2 / |Aut E|`, and in
this normalization the Eichler mass formula reads `∑ 1 / autWeight q j = eichlerMass 1 q`, the sum
running over the supersingular `j`. This file computes neither the automorphism groups nor the
mass formula. -/
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

/-- The coefficient `A` of the short Weierstrass equation `y ^ 2 = x ^ 3 + A * x + B` of the
model curve `ssModel q j` attached to `j : ZMod q`, with `B = ssModelB q j`. -/
public def ssModelA (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

/-- The coefficient `B` of the short Weierstrass equation `y ^ 2 = x ^ 3 + A * x + B` of the
model curve `ssModel q j` attached to `j : ZMod q`, with `A = ssModelA q j`. -/
public def ssModelB (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

public theorem ssModelA_zero (q : ℕ) [NeZero q] : ssModelA q 0 = 0 := by simp [ssModelA]
public theorem ssModelB_zero (q : ℕ) [NeZero q] : ssModelB q 0 = 1 := by simp [ssModelB]

/-- The short Weierstrass curve `y ^ 2 = x ^ 3 + ssModelA q j * x + ssModelB q j` attached to
`j : ZMod q`. For a prime `q > 3` it is an elliptic curve with `j`-invariant `j` (`ssModel_j`).
It is not a model in characteristic `2` or `3`, where its discriminant vanishes for every `j`: in
characteristic `2` the discriminant of every short Weierstrass equation does, and in
characteristic `3` the coefficient `ssModelA 3 j` is `0`. In every characteristic,
`WeierstrassCurve.ofJ j` is an elliptic curve with `j`-invariant `j`. -/
public def ssModel (q : ℕ) [NeZero q] (j : ZMod q) : WeierstrassCurve (ZMod q) :=
  ⟨0, 0, 0, ssModelA q j, ssModelB q j⟩

private theorem two_ne_zero_and_three_ne_zero (q : ℕ) [Fact (3 < q)] :
    (2 : ZMod q) ≠ 0 ∧ (3 : ZMod q) ≠ 0 := by
  have hq : 3 < q := Fact.out
  have key (n : ℕ) (hn : n ≠ 0) (hnq : n ≤ 3) : (n : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
    omega
  exact ⟨by exact_mod_cast key 2 (by norm_num) (by norm_num),
    by exact_mod_cast key 3 (by norm_num) (by norm_num)⟩

public instance (q : ℕ) [Fact q.Prime] [Fact (3 < q)] (j : ZMod q) :
    (ssModel q j).IsElliptic := by
  have : (ssModel q j).IsShortNF := ⟨rfl, rfl, rfl⟩
  obtain ⟨h2, h3⟩ := two_ne_zero_and_three_ne_zero q
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [WeierstrassCurve.Δ_of_isShortNF]
  simp only [ssModel, ssModelA, ssModelB]
  split_ifs with h0 h1728
  · have e : (-16 * (4 * 0 ^ 3 + 27 * 1 ^ 2) : ZMod q) = -(2 ^ 4 * 3 ^ 3) := by ring
    rw [e]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))
  · have e : (-16 * (4 * 1 ^ 3 + 27 * 0 ^ 2) : ZMod q) = -(2 ^ 6) := by ring
    rw [e]
    exact neg_ne_zero.mpr (pow_ne_zero _ h2)
  · have e : (-16 * (4 * (3 * j * (1728 - j)) ^ 3 + 27 * (2 * j * (1728 - j) ^ 2) ^ 2) : ZMod q) =
        -(2 ^ 12 * 3 ^ 6) * j ^ 2 * (1728 - j) ^ 3 := by ring
    rw [e]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ h0)) (pow_ne_zero _ ?_)
    · exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))
    · exact sub_ne_zero.mpr (Ne.symm h1728)

public theorem ssModel_j (q : ℕ) [Fact q.Prime] [Fact (3 < q)] (j : ZMod q) :
    (ssModel q j).j = j := by
  have : (ssModel q j).IsShortNF := ⟨rfl, rfl, rfl⟩
  obtain ⟨h2, h3⟩ := two_ne_zero_and_three_ne_zero q
  rw [WeierstrassCurve.j_of_isShortNF]
  simp only [ssModel, ssModelA, ssModelB]
  split_ifs with h0 h1728
  · subst h0
    simp
  · subst h1728
    have e : (4 * 1 ^ 3 + 27 * 0 ^ 2 : ZMod q) = 2 ^ 2 := by ring
    rw [e, div_eq_iff (pow_ne_zero _ h2)]
    ring
  · have e : (4 * (3 * j * (1728 - j)) ^ 3 + 27 * (2 * j * (1728 - j) ^ 2) ^ 2 : ZMod q) =
        2 ^ 8 * 3 ^ 6 * j ^ 2 * (1728 - j) ^ 3 := by ring
    rw [e, div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2)
      (pow_ne_zero _ h3)) (pow_ne_zero _ h0)) (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h1728))))]
    ring

/-- The number of affine points on `y ^ 2 = x ^ 3 + A * x + B` over `ZMod q`. -/
public def affinePointCount (q : ℕ) [NeZero q] (A B : ZMod q) : ℕ :=
  (Finset.univ.filter fun p : ZMod q × ZMod q => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B).card

public theorem affinePointCount_le (q : ℕ) [NeZero q] (A B : ZMod q) :
    affinePointCount q A B ≤ q ^ 2 := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  simp [pow_two]

/-- The supersingular `j`-invariants in characteristic `p`: the `j` in an algebraic closure of
`ZMod p` such that every elliptic curve over that algebraic closure with `j`-invariant `j` is
supersingular in the sense of `WeierstrassCurve.Affine.IsSupersingular`, that is, has no nonzero
geometric point killed by `p`. Every `j` is the `j`-invariant of an elliptic curve, for example
`WeierstrassCurve.ofJ j`, so the condition is not vacuous. -/
public def ssJSet (p : ℕ) [Fact p.Prime] : Set (AlgebraicClosure (ZMod p)) :=
  {j | ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic], W.j = j →
    W.toAffine.IsSupersingular}

public theorem mem_ssJSet_iff {p : ℕ} [Fact p.Prime] {j : AlgebraicClosure (ZMod p)} :
    j ∈ ssJSet p ↔ ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic],
      W.j = j → W.toAffine.IsSupersingular :=
  Iff.rfl

end ModularCurve
