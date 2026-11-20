/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FinitePlusTailClosedBall















namespace StatMech
namespace Exact3D



structure FinitePlusTailBlockBounds (n : ℕ) (α : Type*) where
  finiteMap : FinitePlusTailState n α → Fin n → ℝ
  tailMap : FinitePlusTailState n α → SummableTail α
  finiteToFinite : ℝ
  tailToFinite : ℝ
  finiteToTail : ℝ
  tailToTail : ℝ
  finiteToFinite_nonneg : 0 ≤ finiteToFinite
  tailToFinite_nonneg : 0 ≤ tailToFinite
  finiteToTail_nonneg : 0 ≤ finiteToTail
  tailToTail_nonneg : 0 ≤ tailToTail
  finite_bound :
    ∀ x y,
      FiniteContraction.l1Dist (finiteMap x) (finiteMap y) ≤
        finiteToFinite * x.finiteDist y + tailToFinite * x.tailDist y
  tail_bound :
    ∀ x y,
      (tailMap x).dist (tailMap y) ≤
        finiteToTail * x.finiteDist y + tailToTail * x.tailDist y

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def map (B : FinitePlusTailBlockBounds n α) :
    FinitePlusTailState n α → FinitePlusTailState n α :=
  fun x => { finite := B.finiteMap x, tail := B.tailMap x }

@[simp] theorem map_finite
    (B : FinitePlusTailBlockBounds n α) (x : FinitePlusTailState n α) :
    (B.map x).finite = B.finiteMap x :=
  rfl

@[simp] theorem map_tail
    (B : FinitePlusTailBlockBounds n α) (x : FinitePlusTailState n α) :
    (B.map x).tail = B.tailMap x :=
  rfl


theorem map_finite_bound
    (B : FinitePlusTailBlockBounds n α) (x y : FinitePlusTailState n α) :
    (B.map x).finiteDist (B.map y) ≤
      B.finiteToFinite * x.finiteDist y +
        B.tailToFinite * x.tailDist y := by
  simpa [map, FinitePlusTailState.finiteDist] using B.finite_bound x y


theorem map_tail_bound
    (B : FinitePlusTailBlockBounds n α) (x y : FinitePlusTailState n α) :
    (B.map x).tailDist (B.map y) ≤
      B.finiteToTail * x.finiteDist y +
        B.tailToTail * x.tailDist y := by
  simpa [map, FinitePlusTailState.tailDist] using B.tail_bound x y



noncomputable def with_larger_constants
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    FinitePlusTailBlockBounds n α where
  finiteMap := B.finiteMap
  tailMap := B.tailMap
  finiteToFinite := finiteToFinite'
  tailToFinite := tailToFinite'
  finiteToTail := finiteToTail'
  tailToTail := tailToTail'
  finiteToFinite_nonneg := le_trans B.finiteToFinite_nonneg hff
  tailToFinite_nonneg := le_trans B.tailToFinite_nonneg htf
  finiteToTail_nonneg := le_trans B.finiteToTail_nonneg hft
  tailToTail_nonneg := le_trans B.tailToTail_nonneg htt
  finite_bound := by
    intro x y
    have hfinite_nonneg : 0 ≤ x.finiteDist y :=
      FinitePlusTailState.finiteDist_nonneg x y
    have htail_nonneg : 0 ≤ x.tailDist y :=
      FinitePlusTailState.tailDist_nonneg x y
    calc
      FiniteContraction.l1Dist (B.finiteMap x) (B.finiteMap y) ≤
          B.finiteToFinite * x.finiteDist y +
            B.tailToFinite * x.tailDist y :=
        B.finite_bound x y
      _ ≤
          finiteToFinite' * x.finiteDist y +
            tailToFinite' * x.tailDist y := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hff hfinite_nonneg)
          (mul_le_mul_of_nonneg_right htf htail_nonneg)
  tail_bound := by
    intro x y
    have hfinite_nonneg : 0 ≤ x.finiteDist y :=
      FinitePlusTailState.finiteDist_nonneg x y
    have htail_nonneg : 0 ≤ x.tailDist y :=
      FinitePlusTailState.tailDist_nonneg x y
    calc
      (B.tailMap x).dist (B.tailMap y) ≤
          B.finiteToTail * x.finiteDist y +
            B.tailToTail * x.tailDist y :=
        B.tail_bound x y
      _ ≤
          finiteToTail' * x.finiteDist y +
            tailToTail' * x.tailDist y := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hft hfinite_nonneg)
          (mul_le_mul_of_nonneg_right htt htail_nonneg)

@[simp] theorem with_larger_constants_finiteMap
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).finiteMap = B.finiteMap :=
  rfl

@[simp] theorem with_larger_constants_tailMap
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).tailMap = B.tailMap :=
  rfl

@[simp] theorem with_larger_constants_map
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).map = B.map :=
  rfl

@[simp] theorem with_larger_constants_finiteToFinite
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).finiteToFinite =
      finiteToFinite' :=
  rfl

@[simp] theorem with_larger_constants_tailToFinite
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).tailToFinite =
      tailToFinite' :=
  rfl

@[simp] theorem with_larger_constants_finiteToTail
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).finiteToTail =
      finiteToTail' :=
  rfl

@[simp] theorem with_larger_constants_tailToTail
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    (B.with_larger_constants hff htf hft htt).tailToTail =
      tailToTail' :=
  rfl


noncomputable def ofDecoupled
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ)
    (tailMap : SummableTail α → SummableTail α)
    {finiteConstant tailConstant : ℝ}
    (hfiniteConstant_nonneg : 0 ≤ finiteConstant)
    (htailConstant_nonneg : 0 ≤ tailConstant)
    (hfinite :
      ∀ x y,
        FiniteContraction.l1Dist (finiteMap x) (finiteMap y) ≤
          finiteConstant * FiniteContraction.l1Dist x y)
    (htail :
      ∀ u v, (tailMap u).dist (tailMap v) ≤ tailConstant * u.dist v) :
    FinitePlusTailBlockBounds n α where
  finiteMap := fun x => finiteMap x.finite
  tailMap := fun x => tailMap x.tail
  finiteToFinite := finiteConstant
  tailToFinite := 0
  finiteToTail := 0
  tailToTail := tailConstant
  finiteToFinite_nonneg := hfiniteConstant_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := by norm_num
  tailToTail_nonneg := htailConstant_nonneg
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      hfinite x.finite y.finite
  tail_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      htail x.tail y.tail


noncomputable def decoupledScaling
    (finiteScale tailScale : ℝ) :
    FinitePlusTailBlockBounds n α :=
  ofDecoupled
    (fun x i => finiteScale * x i)
    (SummableTail.scale tailScale)
    (finiteConstant := |finiteScale|)
    (tailConstant := |tailScale|)
    (abs_nonneg finiteScale)
    (abs_nonneg tailScale)
    (by
      intro x y
      rw [FinitePlusTailLipschitzCertificate.l1Dist_scaleFinite])
    (by
      intro u v
      rw [SummableTail.dist_scale])




noncomputable def ofColumnSumFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailBlockBounds n α where
  finiteMap := fun x i => RatInterval.matVec A x.finite i
  tailMap := tailMap
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_matVec_of_columnSumContraction hI hA
        x.finite y.finite
  tail_bound := htail_bound



noncomputable def ofColumnSumAffineFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (offset : Fin n → ℝ)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailBlockBounds n α where
  finiteMap := fun x i => RatInterval.affineMap A offset x.finite i
  tailMap := tailMap
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_affineMap_of_columnSumContraction hI hA offset
        x.finite y.finite
  tail_bound := htail_bound



noncomputable def toLipschitzCertificate
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    FinitePlusTailLipschitzCertificate n α where
  map := B.map
  finiteToFinite := B.finiteToFinite
  tailToFinite := B.tailToFinite
  finiteToTail := B.finiteToTail
  tailToTail := B.tailToTail
  c := c
  finiteToFinite_nonneg := B.finiteToFinite_nonneg
  tailToFinite_nonneg := B.tailToFinite_nonneg
  finiteToTail_nonneg := B.finiteToTail_nonneg
  tailToTail_nonneg := B.tailToTail_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := B.map_finite_bound
  tail_bound := B.map_tail_bound
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := htail_column_sum_le

@[simp] theorem toLipschitzCertificate_map
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).map = B.map :=
  rfl

@[simp] theorem toLipschitzCertificate_c
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).c = c :=
  rfl


theorem mixed_lipschitz
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (x y : FinitePlusTailState n α) :
    (B.map x).dist (B.map y) ≤ c * x.dist y := by
  simpa using
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).mixed_lipschitz x y



theorem exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    ∃! p : FinitePlusTailState n α, B.map p = p := by
  simpa using
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).exists_unique_fixedPoint



noncomputable def toClosedBallCertificate
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  FinitePlusTailClosedBallContractionCertificate.ofResidualBound
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le)
    center hradius (by simpa using hresidual) (by simpa using hbudget)

@[simp] theorem toClosedBallCertificate_contraction
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).contraction =
        B.toLipschitzCertificate hc_nonneg hc_lt_one
          hfinite_column_sum_le htail_column_sum_le :=
  rfl

@[simp] theorem toClosedBallCertificate_center
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).center = center :=
  rfl

@[simp] theorem toClosedBallCertificate_radius
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).radius = radius :=
  rfl

@[simp] theorem toClosedBallCertificate_residual
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).residual = residual :=
  rfl



theorem toClosedBallCertificate_fixedPoint_mem
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    FinitePlusTailState.ClosedBall center radius
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).fixedPoint_mem



theorem toClosedBallCertificate_fixedPoint_isFixed
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    B.map
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).fixedPoint =
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).fixedPoint_isFixed



theorem toClosedBallCertificate_exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    ∃! p : FinitePlusTailState n α,
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).contraction.map p = p :=
  (B.toClosedBallCertificate hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    hresidual hbudget).exists_unique_fixedPoint



theorem toClosedBallCertificate_mapsClosedBall
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    FinitePlusTailState.MapsClosedBall B.map center radius := by
  simpa [toClosedBallCertificate] using
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).mapsClosedBall



theorem residual_bound_of_componentResiduals
    (B : FinitePlusTailBlockBounds n α)
    (center : FinitePlusTailState n α)
    {finiteResidual tailResidual : ℝ}
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual) :
    (B.map center).dist center ≤ finiteResidual + tailResidual := by
  calc
    (B.map center).dist center =
        FiniteContraction.l1Dist (B.finiteMap center) center.finite +
          (B.tailMap center).dist center.tail := rfl
    _ ≤ finiteResidual + tailResidual :=
      add_le_add hfinite htail



theorem finiteResidual_le_of_vectorMem
    (B : FinitePlusTailBlockBounds n α)
    (center : FinitePlusTailState n α)
    {R : RatInterval.IntervalVector n}
    (hR : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R) :
    FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
      (RatInterval.VectorAbsSum R : ℝ) :=
  FiniteContraction.residual_l1Dist_le_of_vectorMem
    (F := fun _ : Fin n → ℝ => B.finiteMap center)
    (center := center.finite) hR



noncomputable def toClosedBallCertificateOfComponentResiduals
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  B.toClosedBallCertificate hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    (B.residual_bound_of_componentResiduals center hfinite htail)
    (by simpa [add_assoc] using hbudget)

@[simp] theorem toClosedBallCertificateOfComponentResiduals_contraction
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).contraction =
        B.toLipschitzCertificate hc_nonneg hc_lt_one
          hfinite_column_sum_le htail_column_sum_le :=
  rfl

@[simp] theorem toClosedBallCertificateOfComponentResiduals_center
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).center = center :=
  rfl

@[simp] theorem toClosedBallCertificateOfComponentResiduals_radius
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).radius = radius :=
  rfl

@[simp] theorem toClosedBallCertificateOfComponentResiduals_residual
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).residual = finiteResidual + tailResidual :=
  rfl



theorem toClosedBallCertificateOfComponentResiduals_fixedPoint_mem
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    FinitePlusTailState.ClosedBall center radius
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).fixedPoint_mem



theorem toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    B.map
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).fixedPoint =
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).fixedPoint_isFixed



theorem toClosedBallCertificateOfComponentResiduals_exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    ∃! p : FinitePlusTailState n α,
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).contraction.map p = p :=
  (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius hfinite
    htail hbudget).exists_unique_fixedPoint



theorem toClosedBallCertificateOfComponentResiduals_mapsClosedBall
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    FinitePlusTailState.MapsClosedBall B.map center radius := by
  simpa [toClosedBallCertificateOfComponentResiduals] using
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).mapsClosedBall



noncomputable def toClosedBallCertificateOfFiniteResidualVector
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    (B.finiteResidual_le_of_vectorMem center hfiniteResidualMem)
    htail hbudget

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_contraction
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).contraction =
        B.toLipschitzCertificate hc_nonneg hc_lt_one
          hfinite_column_sum_le htail_column_sum_le :=
  rfl

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_center
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).center = center :=
  rfl

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_radius
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).radius = radius :=
  rfl

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_residual
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).residual =
        (RatInterval.VectorAbsSum R : ℝ) + tailResidual :=
  rfl



theorem toClosedBallCertificateOfFiniteResidualVector_fixedPoint_mem
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    FinitePlusTailState.ClosedBall center radius
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).fixedPoint_mem



theorem toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    B.map
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).fixedPoint =
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).fixedPoint_isFixed



theorem toClosedBallCertificateOfFiniteResidualVector_exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    ∃! p : FinitePlusTailState n α,
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).contraction.map p = p :=
  (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    hfiniteResidualMem htail hbudget).exists_unique_fixedPoint



theorem toClosedBallCertificateOfFiniteResidualVector_mapsClosedBall
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    FinitePlusTailState.MapsClosedBall B.map center radius := by
  simpa [toClosedBallCertificateOfFiniteResidualVector,
    toClosedBallCertificateOfComponentResiduals] using
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).mapsClosedBall

end FinitePlusTailBlockBounds

end Exact3D
end StatMech
