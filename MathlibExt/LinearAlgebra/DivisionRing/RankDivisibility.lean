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
# Rank divisibility from compatible division-algebra actions

Let F,L be fields,D a division F-algebra,dim_F L=d>0 and dim_F D=d². If an L-linear map from a
finite-dimensional L-space also preserves compatible D-actions on source and target, its
L-rank is divisible by d. The D and L actions agree over F, not necessarily over each other.
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

/-- **Division-ring equivariance forces divisibility of a range dimension.**

Let F,L be fields,D a division F-algebra,V a finite-dimensional L-space and W an L-space, both
also D-modules with compatible common F-actions. Suppose f:V→W is L-linear and D-equivariant.
If dim_F L=d>0 and dim_F D=d², then d divides dim_L range(f).
-/
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

/-- **Matrix rank divisibility under division-ring equivariance.**

Let F,L be fields,D a division F-algebra,dim_F L=d>0 and dim_F D=d². Let n be finite,m
arbitrary, with D-actions on L^n,L^m compatible with their F-actions. If A:L^n→L^m is a matrix
map commuting with D, then d divides rank_L(A).
-/
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
