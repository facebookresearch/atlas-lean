/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary

/-! # Stable Steinberg Weyl and torus words

Standard type-A words in `St(R)`:

* `w_{ij}(u) = x_{ij}(u) x_{ji}(-u⁻¹) x_{ij}(u)` for `u : Rˣ`,
* `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)` for `u : Rˣ`.

These Weyl and torus conventions are frozen here.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {R : Type u} [Ring R]

/-- Weyl element `w_{ij}(u) = x_{ij}(u) x_{ji}(-u⁻¹) x_{ij}(u)` in `St(R)` for `u : Rˣ`. -/
public def weyl (i j : ℕ) (hij : i ≠ j) (u : Rˣ) : StableSteinberg R :=
  x i j hij (u : R) * x j i hij.symm (-(↑u⁻¹ : R)) * x i j hij (u : R)

/-- Torus element `h_{ij}(u) = w_{ij}(u) w_{ij}(-1)` in `St(R)` for `u : Rˣ`. -/
public def torus (i j : ℕ) (hij : i ≠ j) (u : Rˣ) : StableSteinberg R :=
  weyl i j hij u * weyl i j hij (-1 : Rˣ)

private theorem coe_units_map {S : Type u} [Ring S] (f : R →+* S) (u : Rˣ) :
    (↑(Units.map f.toMonoidHom u) : S) = f (↑u : R) :=
  Units.coe_map (f := f.toMonoidHom) (x := u)

private theorem coe_units_map_inv {S : Type u} [Ring S] (f : R →+* S) (u : Rˣ) :
    (↑(Units.map f.toMonoidHom u)⁻¹ : S) = f (↑u⁻¹ : R) :=
  Units.coe_map_inv (f := f.toMonoidHom) (u := u)

@[simp]
public theorem mapRingHom_weyl {S : Type u} [Ring S] (f : R →+* S) (i j : ℕ) (hij : i ≠ j)
    (u : Rˣ) :
    mapRingHom (R := R) (S := S) f (weyl i j hij u) =
      weyl (R := S) i j hij (Units.map f.toMonoidHom u) := by
  simp only [weyl, map_mul, mapRingHom_x]
  have h1 : f (↑u : R) = (↑(Units.map f.toMonoidHom u) : S) :=
    (coe_units_map f u).symm
  have h2 : f (-(↑u⁻¹ : R)) = (-(↑(Units.map f.toMonoidHom u)⁻¹ : S)) := by
    calc f (-(↑u⁻¹ : R)) = -f (↑u⁻¹ : R) := RingHom.map_neg f _
      _ = -(↑(Units.map f.toMonoidHom u)⁻¹ : S) := by
        rw [← coe_units_map_inv f u]
  rw [h1, h2]

@[simp]
public theorem mapRingHom_torus {S : Type u} [Ring S] (f : R →+* S) (i j : ℕ) (hij : i ≠ j)
    (u : Rˣ) :
    mapRingHom (R := R) (S := S) f (torus i j hij u) =
      torus (R := S) i j hij (Units.map f.toMonoidHom u) := by
  simp only [torus, map_mul, mapRingHom_weyl]
  have h : Units.map f.toMonoidHom (-1 : Rˣ) = (-1 : Sˣ) := by
    ext
    simp
  rw [h]

@[simp]
public theorem toStableE_weyl (i j : ℕ) (hij : i ≠ j) (u : Rˣ) :
    toStableE (R := R) (weyl i j hij u) =
      StableE.natElementary (R := R) i j hij (↑u : R) *
        StableE.natElementary (R := R) j i hij.symm (-(↑u⁻¹ : R)) *
          StableE.natElementary (R := R) i j hij (↑u : R) := by
  simp only [weyl, map_mul, toStableE_x]

@[simp]
public theorem toStableE_torus (i j : ℕ) (hij : i ≠ j) (u : Rˣ) :
    toStableE (R := R) (torus i j hij u) =
      (StableE.natElementary (R := R) i j hij (↑u : R) *
        StableE.natElementary (R := R) j i hij.symm (-(↑u⁻¹ : R)) *
          StableE.natElementary (R := R) i j hij (↑u : R)) *
      (StableE.natElementary (R := R) i j hij (↑(-1 : Rˣ) : R) *
        StableE.natElementary (R := R) j i hij.symm (-(↑(-1 : Rˣ)⁻¹ : R)) *
          StableE.natElementary (R := R) i j hij (↑(-1 : Rˣ) : R)) := by
  simp only [torus, map_mul, toStableE_weyl]

end StableSteinberg

end AlgebraicKTheory

end
