/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.PointDerivations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NormNum

@[expose] public section

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →ₐ[k] k)
    (M : Type) [AddCommGroup M] [Module k M] :
    Submodule k (A →ₗ[k] M) :=
  Algebra.PointDerivations k A ev M

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →ₐ[k] k)
    (M : Type) [AddCommGroup M] [Module k M] {D : A →ₗ[k] M}
    (hD : D ∈ Algebra.PointDerivations k A ev M) : D 1 = 0 :=
  Algebra.PointDerivations.apply_one hD

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →ₐ[k] k)
    (M : Type) [AddCommGroup M] [Module k M] {D : A →ₗ[k] M}
    (hD : D ∈ Algebra.PointDerivations k A ev M) (c : k) : D (algebraMap k A c) = 0 :=
  Algebra.PointDerivations.apply_algebraMap hD c

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →ₐ[k] k)
    (c : k) (a : A) : ev (c • a) = c * ev a :=
  Algebra.PointDerivations.ev_smul c a

open Polynomial

private noncomputable def evalDerivativeAt (x : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (aeval x).toLinearMap.comp derivative

private noncomputable def evalDerivativeAtPoint (x : ℚ) :
    ↥(Algebra.PointDerivations ℚ ℚ[X] (aeval x) ℚ) :=
  ⟨evalDerivativeAt x, by
    intro p q
    simp only [evalDerivativeAt, LinearMap.comp_apply, derivative_mul, map_add,
      AlgHom.toLinearMap_apply, map_mul, smul_eq_mul]
    ac_rfl⟩

private def scale (c : ℚ) : ℚ →ₗ[ℚ] ℚ :=
  c • LinearMap.id

example : (evalDerivativeAtPoint 2).1 X = 1 := by
  simp [evalDerivativeAtPoint, evalDerivativeAt]

example : (evalDerivativeAtPoint 2).1 (X ^ 3) = 12 := by
  norm_num [evalDerivativeAtPoint, evalDerivativeAt, derivative_X_pow]

example : (evalDerivativeAtPoint 2).1 (X * (X + C 3)) = 7 := by
  norm_num [evalDerivativeAtPoint, evalDerivativeAt, derivative_mul]

example :
    (Algebra.PointDerivations.map (aeval 2) (scale 3) (evalDerivativeAtPoint 2)).1 X = 3 := by
  norm_num [Algebra.PointDerivations.map_apply_coe, scale, evalDerivativeAtPoint,
    evalDerivativeAt]

example :
    Algebra.PointDerivations.map (aeval 2) (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
        (evalDerivativeAtPoint 2) = evalDerivativeAtPoint 2 :=
  Algebra.PointDerivations.map_id (aeval 2) (evalDerivativeAtPoint 2)

example :
    Algebra.PointDerivations.map (aeval 2) ((scale 3).comp (scale 2))
        (evalDerivativeAtPoint 2) =
      Algebra.PointDerivations.map (aeval 2) (scale 3)
        (Algebra.PointDerivations.map (aeval 2) (scale 2) (evalDerivativeAtPoint 2)) :=
  Algebra.PointDerivations.map_comp (aeval 2) (scale 2) (scale 3) (evalDerivativeAtPoint 2)

example :
    (Algebra.PointDerivations.map (aeval 2) ((scale 3).comp (scale 2))
        (evalDerivativeAtPoint 2)).1 X = 6 := by
  norm_num [Algebra.PointDerivations.map_apply_coe, scale, evalDerivativeAtPoint,
    evalDerivativeAt]
