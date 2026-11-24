/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank divisibility from a division-ring action

An `L`-linear map that also preserves an actual `D`-module action has the same
range over the common base field, whether bundled as an `L`-linear or a
`D`-linear map. If `L` has base-field dimension `d` and the division ring `D`
has base-field dimension `d²`, its range over `L` has dimension divisible by `d`.

The two scalar actions need only extend the same base-field action. In
particular, no commutation between `L` and `D`, or `L`-algebra structure on `D`,
is required. The matrix theorem applies to the actual `Matrix.mulVec` action.

## References

Ivanyos, Qiao and Subrahmanyam, *Constructive noncommutative rank computation
in deterministic polynomial time over fields of arbitrary characteristics*,
20 January 2016 addendum, Claim 11. Construction of the source opposite action,
cyclic division algebra, splitting matrices and algorithmic bounds is separate.
-/

@[expose] public section

universe uF uL uD uV uW um un

namespace LinearMap

variable {F : Type uF} {L : Type uL} {D : Type uD}
  [Field F] [Field L] [DivisionRing D] [Algebra F L] [Algebra F D]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module L V] [Module D V]
  [Module F W] [Module L W] [Module D W]
  [IsScalarTower F L V] [IsScalarTower F D V]
  [IsScalarTower F L W] [IsScalarTower F D W]
  [FiniteDimensional F L] [FiniteDimensional L V]

private theorem exists_divisionLinearMap_range (f : V →ₗ[L] W)
    (hD : ∀ (a : D) (v : V), f (a • v) = a • f v) :
    ∃ g : V →ₗ[D] W, (∀ v, g v = f v) ∧
      g.range.restrictScalars F = f.range.restrictScalars F ∧
      Module.Finite D g.range ∧
      Module.finrank F D * Module.finrank D g.range =
        Module.finrank F L * Module.finrank L f.range := by
  let g : V →ₗ[D] W :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := hD }
  let : Module.Finite F V := Module.Finite.trans L V
  let : Module.Finite D V := Module.Finite.of_restrictScalars_finite F D V
  have hfg : g.restrictScalars F = f.restrictScalars F := by
    ext v
    rfl
  have hr : g.range.restrictScalars F = f.range.restrictScalars F := by
    rw [← range_restrictScalars, ← range_restrictScalars, hfg]
  refine ⟨g, fun _ => rfl, hr, inferInstance, ?_⟩
  calc
    Module.finrank F D * Module.finrank D g.range =
        Module.finrank F (g.range.restrictScalars F) :=
      Module.finrank_mul_finrank F D (g.range.restrictScalars F)
    _ = Module.finrank F (f.range.restrictScalars F) :=
      congrArg (fun S : Submodule F W => Module.finrank F S) hr
    _ = Module.finrank F L * Module.finrank L f.range :=
      (Module.finrank_mul_finrank F L (f.range.restrictScalars F)).symm

/-- An actual map preserving both scalar actions has `L`-range dimension divisible by `d`,
when the scalar dimensions over the common base field are `d` and `d²`. -/
theorem dvd_finrank_range_of_divisionRing_action (F : Type uF) (D : Type uD)
    [Field F] [DivisionRing D] [Algebra F L] [Algebra F D]
    [Module F V] [Module D V] [Module F W] [Module D W]
    [IsScalarTower F L V] [IsScalarTower F D V]
    [IsScalarTower F L W] [IsScalarTower F D W]
    [FiniteDimensional F L] (f : V →ₗ[L] W)
    (hD : ∀ (a : D) (v : V), f (a • v) = a • f v)
    {d : ℕ} (hd : 0 < d) (hL : Module.finrank F L = d)
    (hDD : Module.finrank F D = d ^ 2) : d ∣ Module.finrank L f.range := by
  obtain ⟨g, _, _, _, hdim⟩ := exists_divisionLinearMap_range (F := F) f hD
  rw [hDD, hL, pow_two, mul_assoc] at hdim
  exact ⟨Module.finrank D g.range, (Nat.eq_of_mul_eq_mul_left hd hdim).symm⟩

end LinearMap

namespace Matrix

variable {F : Type uF} {L : Type uL} {D : Type uD}
  [Field F] [Field L] [DivisionRing D] [Algebra F L] [Algebra F D]
  [FiniteDimensional F L]
variable {m : Type um} {n : Type un} [Fintype n]
  [Module D (m → L)] [Module D (n → L)]
  [IsScalarTower F D (m → L)] [IsScalarTower F D (n → L)]

/-- A matrix with finitely many columns intertwining actual division-ring actions has rank divisible
by `d`, for scalar dimensions `d` and `d²` over the common base field. -/
theorem dvd_rank_of_divisionRing_action (F : Type uF) (D : Type uD)
    [Field F] [DivisionRing D] [Algebra F L] [Algebra F D]
    [FiniteDimensional F L] [Module D (m → L)] [Module D (n → L)]
    [IsScalarTower F D (m → L)] [IsScalarTower F D (n → L)]
    (A : Matrix m n L)
    (hD : ∀ (a : D) (v : n → L), A.mulVec (a • v) = a • A.mulVec v)
    {d : ℕ} (hd : 0 < d) (hL : Module.finrank F L = d)
    (hDD : Module.finrank F D = d ^ 2) : d ∣ A.rank :=
  LinearMap.dvd_finrank_range_of_divisionRing_action F D A.mulVecLin hD hd hL hDD

end Matrix
