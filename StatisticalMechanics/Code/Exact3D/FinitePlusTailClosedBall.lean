/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FinitePlusTailContraction
















namespace StatMech
namespace Exact3D

open scoped NNReal



structure FinitePlusTailClosedBallContractionCertificate (n : ℕ) (α : Type*) where
  contraction : FinitePlusTailLipschitzCertificate n α
  center : FinitePlusTailState n α
  radius : ℝ
  residual : ℝ
  radius_nonneg : 0 ≤ radius
  residual_bound : (contraction.map center).dist center ≤ residual
  radius_bound : residual + contraction.c * radius ≤ radius

namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}



def ofResidualBound
    (contraction : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (contraction.map center).dist center ≤ residual)
    (hbudget : residual + contraction.c * radius ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate n α where
  contraction := contraction
  center := center
  radius := radius
  residual := residual
  radius_nonneg := hradius
  residual_bound := hresidual
  radius_bound := hbudget



def ofResidualMargin
    (contraction : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual :
      (contraction.map center).dist center ≤
        (1 - contraction.c) * radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  ofResidualBound contraction center
    (radius := radius) (residual := (1 - contraction.c) * radius)
    hradius hresidual (by
      ring_nf
      exact le_rfl)


def ofFixedCenter
    (contraction : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hfixed : contraction.map center = center) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  ofResidualBound contraction center (radius := radius) (residual := 0)
    hradius
    (by rw [hfixed, FinitePlusTailState.dist_self])
    (by
      calc
        0 + contraction.c * radius ≤ 1 * radius := by
          simpa using
            mul_le_mul_of_nonneg_right contraction.c_lt_one.le hradius
      _ = radius := by ring)



noncomputable def ofFiniteClosedBall
    {finiteMap : (Fin n → ℝ) → Fin n → ℝ}
    (C : FiniteContraction.ClosedBallContractionCertificate finiteMap) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  ofResidualMargin
    (FinitePlusTailLipschitzCertificate.ofFiniteMap
      (α := α) finiteMap C.c_nonneg C.c_lt_one C.lipschitz)
    (FinitePlusTailState.ofFinite (α := α) C.center)
    C.radius_nonneg
    (by
      simpa using C.residual_bound)



theorem residual_plus_mul_le_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    C.residual + C.contraction.c * C.radius ≤ C.radius :=
  C.radius_bound


theorem mapsClosedBall
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.MapsClosedBall
      C.contraction.map C.center C.radius :=
  C.contraction.mapsClosedBall_of_residual_and_lipschitz
    C.center C.residual_bound C.residual_plus_mul_le_radius


theorem center_mem
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.ClosedBall C.center C.radius C.center :=
  FinitePlusTailState.center_mem_closedBall C.center C.radius_nonneg


noncomputable def fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState n α :=
  C.contraction.fixedPoint


theorem fixedPoint_isFixed
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    C.contraction.map C.fixedPoint = C.fixedPoint :=
  C.contraction.fixedPoint_isFixed


theorem fixedPoint_mem
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.ClosedBall C.center C.radius C.fixedPoint :=
  C.contraction.fixedPoint_mem_closedBall_of_residual
    C.center C.residual_bound C.residual_plus_mul_le_radius


theorem fixedPoint_mem_selected
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    FinitePlusTailState.ClosedBall C.center C.radius C.fixedPoint :=
  C.fixedPoint_mem


theorem fixedPoint_mem_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    FinitePlusTailState.ClosedBall C.center radius' C.fixedPoint :=
  FinitePlusTailState.closedBall_mono_radius C.fixedPoint_mem hradius


theorem fixedPoint_unique
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {x y : FinitePlusTailState n α}
    (hx : C.contraction.map x = x) (hy : C.contraction.map y = y) :
    x = y :=
  C.contraction.fixedPoint_unique hx hy


theorem eq_fixedPoint_of_isFixed
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {x : FinitePlusTailState n α} (hx : C.contraction.map x = x) :
    x = C.fixedPoint :=
  C.contraction.eq_fixedPoint_of_isFixed hx



@[simp] theorem ofFiniteClosedBall_fixedPoint_eq_ofFinite
    {finiteMap : (Fin n → ℝ) → Fin n → ℝ}
    (C : FiniteContraction.ClosedBallContractionCertificate finiteMap) :
    (ofFiniteClosedBall (α := α) C).fixedPoint =
      FinitePlusTailState.ofFinite (α := α) C.fixedPoint := by
  symm
  apply (ofFiniteClosedBall (α := α) C).eq_fixedPoint_of_isFixed
  change
    (FinitePlusTailLipschitzCertificate.ofFiniteMap
      (α := α) finiteMap C.c_nonneg C.c_lt_one C.lipschitz).map
      (FinitePlusTailState.ofFinite C.fixedPoint) =
        FinitePlusTailState.ofFinite C.fixedPoint
  rw [FinitePlusTailLipschitzCertificate.ofFiniteMap_map_ofFinite]
  rw [C.fixedPoint_isFixed]


theorem exists_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    ∃ p : FinitePlusTailState n α,
      C.contraction.map p = p ∧
        FinitePlusTailState.ClosedBall C.center C.radius p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed, C.fixedPoint_mem⟩


theorem exists_unique_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    ∃! p : FinitePlusTailState n α, C.contraction.map p = p :=
  C.contraction.exists_unique_fixedPoint


theorem iterate_mem
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall C.center C.radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center C.radius
      (C.contraction.iterate k x) :=
  C.contraction.mapsClosedBall_iterate_mem C.mapsClosedBall hx k


theorem iterate_dist_le_pow_mul_of_fixed
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {p : FinitePlusTailState n α}
    (hp : C.contraction.map p = p)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.contraction.iterate k x).dist p ≤
      C.contraction.c ^ k * x.dist p :=
  C.contraction.iterate_dist_le_pow_mul_of_fixed hp x k


theorem iterate_dist_le_pow_mul_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.contraction.iterate k x).dist C.fixedPoint ≤
      C.contraction.c ^ k * x.dist C.fixedPoint :=
  C.contraction.iterate_dist_le_pow_mul_fixedPoint x k


theorem residual_le_margin
    (C : FinitePlusTailClosedBallContractionCertificate n α) :
    C.residual ≤ (1 - C.contraction.c) * C.radius := by
  nlinarith [C.radius_bound]




def with_larger_residual
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    FinitePlusTailClosedBallContractionCertificate n α where
  contraction := C.contraction
  center := C.center
  radius := C.radius
  residual := residual'
  radius_nonneg := C.radius_nonneg
  residual_bound := le_trans C.residual_bound hresidual
  radius_bound := hbudget

@[simp] theorem with_larger_residual_contraction
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).contraction =
      C.contraction :=
  rfl

@[simp] theorem with_larger_residual_center
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).center = C.center :=
  rfl

@[simp] theorem with_larger_residual_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).radius = C.radius :=
  rfl

@[simp] theorem with_larger_residual_residual
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).residual = residual' :=
  rfl

@[simp] theorem with_larger_residual_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {residual' : ℝ} (hresidual : C.residual ≤ residual')
    (hbudget : residual' + C.contraction.c * C.radius ≤ C.radius) :
    (C.with_larger_residual hresidual hbudget).fixedPoint =
      C.fixedPoint :=
  rfl



def with_larger_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    FinitePlusTailClosedBallContractionCertificate n α where
  contraction := C.contraction
  center := C.center
  radius := radius'
  residual := C.residual
  radius_nonneg := le_trans C.radius_nonneg hradius
  residual_bound := C.residual_bound
  radius_bound := by
    have hmargin_nonneg : 0 ≤ 1 - C.contraction.c :=
      sub_nonneg.mpr C.contraction.c_lt_one.le
    have hres_le : C.residual ≤ (1 - C.contraction.c) * radius' :=
      le_trans C.residual_le_margin
        (mul_le_mul_of_nonneg_left hradius hmargin_nonneg)
    calc
      C.residual + C.contraction.c * radius' ≤
          (1 - C.contraction.c) * radius' +
            C.contraction.c * radius' := by
        exact add_le_add_left hres_le (C.contraction.c * radius')
      _ = radius' := by ring

@[simp] theorem with_larger_radius_contraction
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).contraction = C.contraction :=
  rfl

@[simp] theorem with_larger_radius_center
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).center = C.center :=
  rfl

@[simp] theorem with_larger_radius_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).radius = radius' :=
  rfl

@[simp] theorem with_larger_radius_residual
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).residual = C.residual :=
  rfl



@[simp] theorem with_larger_radius_fixedPoint
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).fixedPoint = C.fixedPoint :=
  rfl



theorem mapsClosedBall_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    FinitePlusTailState.MapsClosedBall
      C.contraction.map C.center radius' := by
  simpa using (C.with_larger_radius hradius).mapsClosedBall



theorem exists_fixedPoint_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    ∃ p : FinitePlusTailState n α,
      C.contraction.map p = p ∧
        FinitePlusTailState.ClosedBall C.center radius' p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed,
    C.fixedPoint_mem_of_radius_le hradius⟩



theorem iterate_mem_of_radius_le
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius')
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall C.center radius' x) (k : ℕ) :
    FinitePlusTailState.ClosedBall C.center radius'
      (C.contraction.iterate k x) := by
  simpa using (C.with_larger_radius hradius).iterate_mem hx k

end FinitePlusTailClosedBallContractionCertificate

end Exact3D
end StatMech
