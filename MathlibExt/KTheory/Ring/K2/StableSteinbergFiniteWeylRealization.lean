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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylTorus
public import MathlibExt.KTheory.Ring.K2.StableElementaryNatural
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization

/-! # Finite-rank matrix realization of stable Weyl generators

For `n i j : ℕ` with `i < n`, `j < n`, `i ≠ j` and `u : Rˣ` over `[CommRing R]`:
`finiteWeyl_toStableE_eq_finiteElementary` identifies the stable elementary image
of `weyl i j hij u` with the three-factor finite `StableE.elementary` product at
`⟨i, hi⟩`, `⟨j, hj⟩` with coefficients `u`, `-u⁻¹`, `u`, reusing `toStableE_weyl`
and `natElementary_fin`; `finiteWeylGLUnit_eq_monomial` identifies the finite
`weylGLUnit` at those `Fin n` indices with `monomialMatrixHom R (Fin n)` of the
accepted `weylMonomialBaseUnit`, reusing `weylGLUnit_eq_monomialMatrixHom`. Both
preserve the head-left `x_ij(u) x_ji(-u⁻¹) x_ij(u)` orientation. Purpose:
single-generator finite word realization input for the central-monomial
containment route. Nonclaims: no list-level Weyl evaluation, monomial-cell
permutation uniqueness, torus landing, central-kernel containment, or Matsumoto
claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {R : Type u} [CommRing R]

/-- Finite-rank `StableE` image of a stable Weyl generator: `toStableE` of
`weyl i j hij u` is the three-factor finite `StableE.elementary` product at
`⟨i, hi⟩`, `⟨j, hj⟩` with coefficients `u`, `-u⁻¹`, `u`, in the same head-left
order as `toStableE_weyl`. The finite index inequalities are the exact
transports of `hij` along `Fin.val`. Purpose: finite word realization input.
Nonclaims: no list-level evaluation, permutation uniqueness, torus landing,
kernel containment, or Matsumoto claim. -/
public theorem finiteWeyl_toStableE_eq_finiteElementary
    (n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) (u : Rˣ) :
    StableSteinberg.toStableE (R := R) (StableSteinberg.weyl i j hij u) =
      StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩
        (fun h => hij (congrArg Fin.val h)) (↑u : R) *
        StableE.elementary n ⟨j, hj⟩ ⟨i, hi⟩
          (fun h => hij.symm (congrArg Fin.val h)) (-(↑u⁻¹ : R)) *
          StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩
            (fun h => hij (congrArg Fin.val h)) (↑u : R) := by
  rw [StableSteinberg.toStableE_weyl]
  have e1 : StableE.natElementary (R := R) i j hij (↑u : R) =
      StableE.elementary n ⟨i, hi⟩ ⟨j, hj⟩
        (fun h => hij (congrArg Fin.val h)) (↑u : R) :=
    StableE.natElementary_fin (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
      (fun h => hij (congrArg Fin.val h)) _
  have e2 : StableE.natElementary (R := R) j i hij.symm (-(↑u⁻¹ : R)) =
      StableE.elementary n ⟨j, hj⟩ ⟨i, hi⟩
        (fun h => hij.symm (congrArg Fin.val h)) (-(↑u⁻¹ : R)) :=
    StableE.natElementary_fin (n := n) (i := ⟨j, hj⟩) (j := ⟨i, hi⟩)
      (fun h => hij.symm (congrArg Fin.val h)) _
  -- `e1` rewrites both outer factors, which share the same pattern.
  rw [e1, e2]

/-- Finite-rank monomial realization of a finite Weyl unit: `weylGLUnit` at
`⟨i, hi⟩`, `⟨j, hj⟩` is `monomialMatrixHom R (Fin n)` of the accepted
`weylMonomialBaseUnit`, reusing `weylGLUnit_eq_monomialMatrixHom` with no new
matrix entry calculation. Purpose and nonclaims as in
`finiteWeyl_toStableE_eq_finiteElementary`. -/
public theorem finiteWeylGLUnit_eq_monomial
    (n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i ≠ j) (u : Rˣ) :
    Matrix.GeneralLinearGroup.weylGLUnit (R := R) (⟨i, hi⟩ : Fin n)
        (⟨j, hj⟩ : Fin n) (fun h => hij (congrArg Fin.val h)) u =
      Matrix.GeneralLinearGroup.monomialMatrixHom R (Fin n)
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit (⟨i, hi⟩ : Fin n)
          (⟨j, hj⟩ : Fin n) (fun h => hij (congrArg Fin.val h)) u) :=
  Matrix.GeneralLinearGroup.weylGLUnit_eq_monomialMatrixHom _ _ _ _

end AlgebraicKTheory

end
