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

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Determinant

/-!
# Special linear successor stabilization via `GL` stabilization

Ring-generic stabilization `SL (Fin n) R →* SL (Fin (n+1)) R` by restricting
`Matrix.GeneralLinearGroup.stabilization` and using
`Matrix.GeneralLinearGroup.det_stabilization`.  Works over an arbitrary
`CommRing R`; no field or K-theoretic specialization is used.
-/

@[expose] public section

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

/-- `SL` successor stabilization `SL (Fin n) R →* SL (Fin (n + 1)) R` obtained by
restricting `GL` stabilization.  Determinant invariance is reused via
`Matrix.GeneralLinearGroup.det_stabilization`. -/
def stabilization {n : ℕ} (R : Type*) [CommRing R] :
    Matrix.SpecialLinearGroup (Fin n) R →* Matrix.SpecialLinearGroup (Fin (n + 1)) R where
  toFun g :=
    ⟨(Matrix.GeneralLinearGroup.stabilization R (Matrix.SpecialLinearGroup.toGL g)).val,
      by
        have h_det : Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.stabilization R (Matrix.SpecialLinearGroup.toGL g)) = 1 := by
          rw [Matrix.GeneralLinearGroup.det_stabilization,
            Matrix.SpecialLinearGroup.coeToGL_det]
        have h_val : (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.stabilization R (Matrix.SpecialLinearGroup.toGL g))).val
            = (1 : Rˣ).val := congrArg Units.val h_det
        exact h_val⟩
  map_one' := by
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.stabilization R
        (Matrix.SpecialLinearGroup.toGL
          (1 : Matrix.SpecialLinearGroup (Fin n) R))).val
        = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    calc (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL
              (1 : Matrix.SpecialLinearGroup (Fin n) R))).val
        = (Matrix.GeneralLinearGroup.stabilization R
            (1 : Matrix.GeneralLinearGroup (Fin n) R)).val := by
          rw [MonoidHom.map_one]
      _ = (1 : Matrix.GeneralLinearGroup (Fin (n + 1)) R).val := by
          rw [MonoidHom.map_one]
      _ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := rfl
  map_mul' := by
    intro a b
    apply Subtype.ext
    change (Matrix.GeneralLinearGroup.stabilization R
        (Matrix.SpecialLinearGroup.toGL (a * b))).val
        = (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL a)).val *
          (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL b)).val
    calc (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL (a * b))).val
        = (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL b)).val := by
          rw [MonoidHom.map_mul]
      _ = (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL a) *
          Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL b)).val := by
          rw [MonoidHom.map_mul]
      _ = (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL a)).val *
          (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL b)).val := rfl

@[simp]
theorem toGL_stabilization {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    Matrix.SpecialLinearGroup.toGL (stabilization R g) =
      Matrix.GeneralLinearGroup.stabilization R (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rfl

@[simp]
theorem coe_stabilization {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    (stabilization R g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      (Matrix.GeneralLinearGroup.stabilization R
          (Matrix.SpecialLinearGroup.toGL g) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) :=
  rfl

@[simp]
theorem coe_stabilization_def {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    (stabilization R g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      Matrix.reindex (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1))
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) R) 0 0 1) := by
  simp [coe_stabilization, Matrix.GeneralLinearGroup.coe_stabilization]

theorem stabilization_injective {n : ℕ} :
    Function.Injective (stabilization (R := R) (n := n)) := by
  intro a b h
  have hGL :
      Matrix.SpecialLinearGroup.toGL (stabilization R a) =
        Matrix.SpecialLinearGroup.toGL (stabilization R b) :=
      congrArg Matrix.SpecialLinearGroup.toGL h
  rw [toGL_stabilization, toGL_stabilization] at hGL
  have hGL' :
      Matrix.GeneralLinearGroup.stabilization R
          (Matrix.SpecialLinearGroup.toGL a) =
        Matrix.GeneralLinearGroup.stabilization R
          (Matrix.SpecialLinearGroup.toGL b) := hGL
  have hToGL : Matrix.SpecialLinearGroup.toGL a =
      Matrix.SpecialLinearGroup.toGL b :=
    Matrix.GeneralLinearGroup.stabilization_injective hGL'
  exact Matrix.SpecialLinearGroup.toGL_injective hToGL

private theorem toGL_map_aux {n : ℕ} (f : R →+* S)
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.mapRingHom (n := Fin n) f (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rfl

theorem stabilization_map (f : R →+* S) {n : ℕ} :
    (stabilization (R := S) (n := n)).comp
        (Matrix.SpecialLinearGroup.map (n := Fin n) f) =
      (Matrix.SpecialLinearGroup.map (n := Fin (n + 1)) f).comp
        (stabilization (R := R) (n := n)) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.stabilization S
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g))).val
      = ((Matrix.SpecialLinearGroup.map (n := Fin (n + 1)) f
            (stabilization R g) :
          Matrix.SpecialLinearGroup (Fin (n + 1)) S) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) S)
  calc (Matrix.GeneralLinearGroup.stabilization S
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g))).val
      = (Matrix.GeneralLinearGroup.stabilization S
          (Matrix.GeneralLinearGroup.mapRingHom (n := Fin n) f
            (Matrix.SpecialLinearGroup.toGL g))).val := by
        rw [toGL_map_aux]
    _ = (Matrix.GeneralLinearGroup.mapRingHom (n := Fin (n + 1)) f
          (Matrix.GeneralLinearGroup.stabilization R
            (Matrix.SpecialLinearGroup.toGL g))).val := by
        rw [← Matrix.GeneralLinearGroup.stabilization_mapRingHom_apply]
    _ = ((Matrix.SpecialLinearGroup.map (n := Fin (n + 1)) f
            (stabilization R g) :
          Matrix.SpecialLinearGroup (Fin (n + 1)) S) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) S) := rfl

@[simp]
theorem stabilization_map_apply (f : R →+* S) {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R) :
    stabilization S (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (stabilization R g) :=
  DFunLike.congr_fun (stabilization_map (R := R) (S := S) f (n := n)) g

end Matrix.SpecialLinearGroup
