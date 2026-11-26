/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_EllipticCurve_RubinSilverbergFamily.lean`,
`Theorems/Thm_RubinSilverberg_rsBeta_sub_mul_rsGamma.lean`,
`Theorems/Thm_RubinSilverberg_IsKleinDatum_kleinH_ne_zero.lean`,
`Theorems/Thm_RubinSilverberg_IsKleinDatum_kleinT_ne_zero.lean`,
`P2M/Sol/S_RubinSilverberg_rsBeta_sub_mul_rsGamma.lean`,
`P2M/Sol/S_RubinSilverberg_IsKleinDatum_kleinH_ne_zero.lean`
and
`P2M/Sol/S_RubinSilverberg_IsKleinDatum_kleinT_ne_zero.lean`
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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Klein forms and the Rubin–Silverberg family

This file defines the data used by Rubin and Silverberg to parametrize elliptic curves
with a given mod-`5` representation: Felix Klein's icosahedral forms `V`, `H`, `T` and
their homogenizations, the curve `kleinCurve u : y² = x³ - H(u)/48 · x + T(u)/864`, and the
one-parameter family `rsMember a b u₀ l t : y² = x³ + A(t) x + B(t)` built from a base point
`u₀` satisfying the Klein relation `IsKleinDatum a b u₀`.

## Main statements

* `RubinSilverberg.kleinT_sq_sub_kleinH_cube`: Klein's syzygy `T² - H³ = 1728 V⁵`.
* `RubinSilverberg.rsBeta_sub_mul_rsGamma`: the determinant of the Möbius substitution
  used by the family.
* `RubinSilverberg.IsKleinDatum.kleinH_ne_zero`, `RubinSilverberg.IsKleinDatum.kleinT_ne_zero`.

## References

* K. Rubin and A. Silverberg, *Families of elliptic curves with constant mod p
  representations*, 1995.
-/

@[expose] public section

namespace RubinSilverberg

section KleinForms

variable {R : Type*} [CommRing R]

/-- Klein's icosahedral form `V(u) = u (u¹⁰ + 11 u⁵ - 1)`, the dehomogenization of the
degree-`12` binary form `kleinVHom`. -/
def kleinV (u : R) : R := u * (u ^ 10 + 11 * u ^ 5 - 1)

/-- Klein's icosahedral form `H(u) = u²⁰ - 228 u¹⁵ + 494 u¹⁰ + 228 u⁵ + 1` of degree `20`. -/
def kleinH (u : R) : R := u ^ 20 - 228 * u ^ 15 + 494 * u ^ 10 + 228 * u ^ 5 + 1

/-- Klein's icosahedral form `T(u) = u³⁰ + 522 u²⁵ - 10005 u²⁰ - 10005 u¹⁰ - 522 u⁵ + 1` of
degree `30`. -/
def kleinT (u : R) : R :=
  u ^ 30 + 522 * u ^ 25 - 10005 * u ^ 20 - 10005 * u ^ 10 - 522 * u ^ 5 + 1

/-- The homogenization `n d (n¹⁰ + 11 n⁵ d⁵ - d¹⁰)` of `kleinV` to degree `12`, in the
variables `n`, `d`. -/
def kleinVHom (n d : R) : R := n * d * (n ^ 10 + 11 * n ^ 5 * d ^ 5 - d ^ 10)

/-- The homogenization of `kleinH` in the variables `n`, `d`. -/
def kleinHHom (n d : R) : R :=
  n ^ 20 - 228 * n ^ 15 * d ^ 5 + 494 * n ^ 10 * d ^ 10 + 228 * n ^ 5 * d ^ 15 + d ^ 20

/-- The homogenization of `kleinT` in the variables `n`, `d`. -/
def kleinTHom (n d : R) : R :=
  n ^ 30 + 522 * n ^ 25 * d ^ 5 - 10005 * n ^ 20 * d ^ 10 - 10005 * n ^ 10 * d ^ 20
    - 522 * n ^ 5 * d ^ 25 + d ^ 30

/-- Klein's syzygy `T² - H³ = 1728 V⁵`. -/
theorem kleinT_sq_sub_kleinH_cube (u : R) :
    kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV; ring

/-- Klein's syzygy for the homogeneous forms. -/
theorem kleinTHom_sq_sub_kleinHHom_cube (n d : R) :
    kleinTHom n d ^ 2 - kleinHHom n d ^ 3 = 1728 * kleinVHom n d ^ 5 := by
  unfold kleinTHom kleinHHom kleinVHom; ring

theorem kleinHHom_mul_mul (c n d : R) :
    kleinHHom (c * n) (c * d) = c ^ 20 * kleinHHom n d := by
  unfold kleinHHom; ring

theorem kleinTHom_mul_mul (c n d : R) :
    kleinTHom (c * n) (c * d) = c ^ 30 * kleinTHom n d := by
  unfold kleinTHom; ring

@[simp]
theorem kleinHHom_one (n : R) : kleinHHom n 1 = kleinH n := by
  unfold kleinHHom kleinH; ring

@[simp]
theorem kleinTHom_one (n : R) : kleinTHom n 1 = kleinT n := by
  unfold kleinTHom kleinT; ring

section map

variable {S : Type*} [CommRing S] {F : Type*} [FunLike F R S] [RingHomClass F R S]

theorem map_kleinH (f : F) (u : R) : f (kleinH u) = kleinH (f u) := by
  simp [kleinH, map_ofNat]

theorem map_kleinT (f : F) (u : R) : f (kleinT u) = kleinT (f u) := by
  simp [kleinT, map_ofNat]

theorem map_kleinHHom (f : F) (n d : R) : f (kleinHHom n d) = kleinHHom (f n) (f d) := by
  simp [kleinHHom, map_ofNat]

theorem map_kleinTHom (f : F) (n d : R) : f (kleinTHom n d) = kleinTHom (f n) (f d) := by
  simp [kleinTHom, map_ofNat]

end map

end KleinForms

section Family

variable {K : Type*} [Field K]

/-- The Weierstrass curve `y² = x³ - H(u)/48 · x + T(u)/864`. When `6` is invertible in `K`,
Klein's syzygy gives it discriminant `-V(u)⁵`, so for `V(u) ≠ 0` it is an elliptic curve with
`j`-invariant `-H(u)³ / V(u)⁵`. -/
def kleinCurve (u : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, -kleinH u / 48, kleinT u / 864⟩

/-- The coefficient `β(u) = T(u) (57 u¹⁵ - 247 u¹⁰ - 171 u⁵ - 1) / (144 u⁴ (u¹⁰ + 11 u⁵ - 1)⁴)`
of the Möbius substitution defining the Rubin–Silverberg family. -/
def rsBeta (u : K) : K :=
  kleinT u * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1)
    / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)

/-- The coefficient `γ(u) = T(u) (u¹⁵ - 171 u¹⁰ + 247 u⁵ + 57) / (144 (u¹⁰ + 11 u⁵ - 1)⁴)` of
the Möbius substitution defining the Rubin–Silverberg family. -/
def rsGamma (u : K) : K :=
  kleinT u * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57) / (144 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4)

/-- The numerator `(β(u₀) + l u₀) t + u₀` of the substitution. -/
def rsNum (u₀ l t : K) : K := (rsBeta u₀ + l * u₀) * t + u₀

/-- The denominator `(γ(u₀) + l) t + 1` of the substitution. -/
def rsDen (u₀ l t : K) : K := (rsGamma u₀ + l) * t + 1

/-- The coefficient `A(t) = a · H(num, den) / H(u₀)` of the Rubin–Silverberg family. -/
def rsFamilyA (a u₀ l t : K) : K :=
  a * kleinHHom (rsNum u₀ l t) (rsDen u₀ l t) / kleinH u₀

/-- The coefficient `B(t) = b · T(num, den) / T(u₀)` of the Rubin–Silverberg family. -/
def rsFamilyB (b u₀ l t : K) : K :=
  b * kleinTHom (rsNum u₀ l t) (rsDen u₀ l t) / kleinT u₀

/-- The member `y² = x³ + A(t) x + B(t)` of the Rubin–Silverberg family. -/
def rsMember (a b u₀ l t : K) : WeierstrassCurve K :=
  ⟨0, 0, 0, rsFamilyA a u₀ l t, rsFamilyB b u₀ l t⟩

/-- `u₀` is a Klein datum for `y² = x³ + a x + b`: it satisfies
`H(u₀)³ (4a³ + 27b²) + 6912 a³ V(u₀)⁵ = 0` and `V(u₀) ≠ 0`. When `6` is invertible in `K` and
`4a³ + 27b² ≠ 0`, this says that the `j`-invariant of the curve is `-H(u₀)³ / V(u₀)⁵`, the
`j`-invariant of `kleinCurve u₀`. -/
def IsKleinDatum (a b u₀ : K) : Prop :=
  kleinH u₀ ^ 3 * (4 * a ^ 3 + 27 * b ^ 2) + 6912 * a ^ 3 * kleinV u₀ ^ 5 = 0 ∧ kleinV u₀ ≠ 0

theorem map_rsBeta {L : Type*} [Field L] (f : K →+* L) (u : K) :
    f (rsBeta u) = rsBeta (f u) := by
  simp [rsBeta, map_ofNat, map_kleinT]

theorem map_rsGamma {L : Type*} [Field L] (f : K →+* L) (u : K) :
    f (rsGamma u) = rsGamma (f u) := by
  simp [rsGamma, map_ofNat, map_kleinT]

theorem rsBeta_sub_mul_rsGamma (u : K) :
    rsBeta u - u * rsGamma u =
      -(kleinT u * kleinH u) / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) := by
  unfold rsBeta rsGamma kleinH
  field_simp
  ring

namespace IsKleinDatum

variable [CharZero K] {a b u₀ : K}

theorem kleinH_ne_zero (h : IsKleinDatum a b u₀) (ha : a ≠ 0) : kleinH u₀ ≠ 0 := by
  intro hH
  obtain ⟨heq, hV⟩ := h
  rw [hH, zero_pow three_ne_zero, zero_mul, zero_add] at heq
  exact hV (pow_eq_zero_iff (n := 5) (by norm_num) |>.mp
    ((mul_eq_zero.mp heq).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha))))

theorem kleinT_ne_zero (h : IsKleinDatum a b u₀) (hb : b ≠ 0) : kleinT u₀ ≠ 0 := by
  intro hT
  have heq : kleinT u₀ ^ 2 * (4 * a ^ 3 + 27 * b ^ 2) = 46656 * b ^ 2 * kleinV u₀ ^ 5 := by
    linear_combination (4 * a ^ 3 + 27 * b ^ 2) * kleinT_sq_sub_kleinH_cube u₀ + h.1
  rw [hT, zero_pow two_ne_zero, zero_mul] at heq
  exact h.2 (pow_eq_zero_iff (n := 5) (by norm_num) |>.mp
    ((mul_eq_zero.mp heq.symm).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb))))

end IsKleinDatum

end Family

end RubinSilverberg
