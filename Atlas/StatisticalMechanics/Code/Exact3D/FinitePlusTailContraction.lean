/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Code.Exact3D.FixedPointSkeleton
import Code.Exact3D.InfiniteTailSummability

open scoped BigOperators ENNReal NNReal

















namespace StatMech
namespace Exact3D


structure SummableTail (α : Type*) where
  coeff : α → ℝ
  summable_abs : Summable fun a => |coeff a|

namespace SummableTail

variable {α : Type*}


def zero : SummableTail α where
  coeff := fun _ => 0
  summable_abs := by
    simp

instance : Zero (SummableTail α) :=
  ⟨zero⟩

@[simp] theorem zero_coeff (a : α) : (0 : SummableTail α).coeff a = 0 :=
  rfl

@[ext]
theorem ext {u v : SummableTail α} (h : u.coeff = v.coeff) : u = v := by
  cases u
  cases v
  cases h
  rfl


noncomputable def norm (u : SummableTail α) : ℝ :=
  ∑' a, |u.coeff a|


noncomputable def dist (u v : SummableTail α) : ℝ :=
  ∑' a, |u.coeff a - v.coeff a|


theorem summable_abs_sub (u v : SummableTail α) :
    Summable fun a => |u.coeff a - v.coeff a| := by
  have hdom : Summable fun a => |u.coeff a| + |v.coeff a| :=
    u.summable_abs.add v.summable_abs
  refine Summable.of_nonneg_of_le
    (fun a => abs_nonneg (u.coeff a - v.coeff a)) ?_ hdom
  intro a
  have h :
      |u.coeff a - v.coeff a| ≤ |u.coeff a| + |-v.coeff a| := by
    simpa [sub_eq_add_neg] using abs_add_le (u.coeff a) (-v.coeff a)
  simpa using h


theorem norm_nonneg (u : SummableTail α) : 0 ≤ u.norm :=
  tsum_nonneg fun a => abs_nonneg (u.coeff a)


theorem dist_nonneg (u v : SummableTail α) : 0 ≤ u.dist v :=
  tsum_nonneg fun a => abs_nonneg (u.coeff a - v.coeff a)


@[simp] theorem dist_self (u : SummableTail α) : u.dist u = 0 := by
  simp [dist]


@[simp] theorem dist_zero (u : SummableTail α) : u.dist 0 = u.norm := by
  unfold dist norm
  refine tsum_congr fun a => ?_
  simp


@[simp] theorem zero_dist (u : SummableTail α) : (0 : SummableTail α).dist u = u.norm := by
  unfold dist norm
  refine tsum_congr fun a => ?_
  simp


theorem dist_comm (u v : SummableTail α) : u.dist v = v.dist u := by
  unfold dist
  refine tsum_congr fun a => ?_
  rw [abs_sub_comm]


theorem abs_sub_coeff_le_dist (u v : SummableTail α) (a : α) :
    |u.coeff a - v.coeff a| ≤ u.dist v :=
  (u.summable_abs_sub v).le_tsum a (fun b _ => abs_nonneg (u.coeff b - v.coeff b))


theorem eq_of_dist_eq_zero {u v : SummableTail α}
    (h : u.dist v = 0) : u = v := by
  ext a
  have habs_nonpos : |u.coeff a - v.coeff a| ≤ 0 := by
    simpa [h] using abs_sub_coeff_le_dist u v a
  have habs_zero : |u.coeff a - v.coeff a| = 0 :=
    le_antisymm habs_nonpos (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_zero)


theorem dist_triangle (u v w : SummableTail α) :
    u.dist w ≤ u.dist v + v.dist w := by
  have hright :
      Summable fun a =>
        |u.coeff a - v.coeff a| + |v.coeff a - w.coeff a| :=
    (u.summable_abs_sub v).add (v.summable_abs_sub w)
  have hle :
      ∀ a,
        |u.coeff a - w.coeff a| ≤
          |u.coeff a - v.coeff a| + |v.coeff a - w.coeff a| := by
    intro a
    have h :
        u.coeff a - w.coeff a =
          (u.coeff a - v.coeff a) + (v.coeff a - w.coeff a) := by
      ring
    rw [h]
    exact abs_add_le _ _
  calc
    u.dist w =
        ∑' a, |u.coeff a - w.coeff a| := rfl
    _ ≤
        ∑' a,
          (|u.coeff a - v.coeff a| + |v.coeff a - w.coeff a|) :=
      Summable.tsum_le_tsum hle (u.summable_abs_sub w) hright
    _ =
        (∑' a, |u.coeff a - v.coeff a|) +
          ∑' a, |v.coeff a - w.coeff a| :=
      (u.summable_abs_sub v).tsum_add (v.summable_abs_sub w)
    _ = u.dist v + v.dist w := rfl


noncomputable def scale (c : ℝ) (u : SummableTail α) :
    SummableTail α where
  coeff := fun a => c * u.coeff a
  summable_abs := by
    have h := u.summable_abs.mul_left |c|
    refine h.congr ?_
    intro a
    simp [abs_mul]


theorem dist_scale (c : ℝ) (u v : SummableTail α) :
    (scale c u).dist (scale c v) = |c| * u.dist v := by
  calc
    (scale c u).dist (scale c v) =
        ∑' a, |c| * |u.coeff a - v.coeff a| := by
      refine tsum_congr fun a => ?_
      have h :
          c * u.coeff a - c * v.coeff a =
            c * (u.coeff a - v.coeff a) := by
        ring
      simp [scale, h, abs_mul]
    _ = |c| * u.dist v := by
      rw [tsum_mul_left]
      rfl


theorem norm_scale (c : ℝ) (u : SummableTail α) :
    (scale c u).norm = |c| * u.norm := by
  calc
    (scale c u).norm =
        ∑' a, |c| * |u.coeff a| := by
      refine tsum_congr fun a => ?_
      simp [scale, abs_mul]
    _ = |c| * u.norm := by
      rw [tsum_mul_left]
      rfl


noncomputable def toLpOne (u : SummableTail α) :
    lp (fun _ : α => ℝ) (1 : ℝ≥0∞) :=
  ⟨u.coeff, by
    change Memℓp u.coeff (1 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (1 : ℝ≥0∞)) (by norm_num)]
    simpa [Real.norm_eq_abs] using u.summable_abs⟩


noncomputable def ofLpOne
    (f : lp (fun _ : α => ℝ) (1 : ℝ≥0∞)) : SummableTail α where
  coeff := fun a => f a
  summable_abs := by
    have hf := (lp.memℓp f).summable (p := (1 : ℝ≥0∞)) (by norm_num)
    simpa [Real.norm_eq_abs] using hf



noncomputable def equivLpOne :
    SummableTail α ≃ lp (fun _ : α => ℝ) (1 : ℝ≥0∞) where
  toFun := toLpOne
  invFun := ofLpOne
  left_inv := by
    intro u
    ext a
    rfl
  right_inv := by
    intro f
    ext a
    rfl


theorem norm_toLpOne_sub (u v : SummableTail α) :
    ‖toLpOne u - toLpOne v‖ = u.dist v := by
  rw [lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num)]
  change
    (∑' i : α, ‖(toLpOne u - toLpOne v) i‖ ^ (1 : ℝ)) ^
        (1 / (1 : ℝ)) =
      u.dist v
  norm_num
  unfold dist
  refine tsum_congr fun i => ?_
  change |u.coeff i - v.coeff i| = |u.coeff i - v.coeff i|
  rfl


theorem dist_toLpOne (u v : SummableTail α) :
    Dist.dist (toLpOne u) (toLpOne v) = u.dist v := by
  rw [dist_eq_norm]
  exact norm_toLpOne_sub u v


noncomputable instance instMetricSpace : MetricSpace (SummableTail α) where
  dist := dist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero := by
    intro u v h
    exact eq_of_dist_eq_zero h


theorem isometry_toLpOne :
    Isometry (toLpOne : SummableTail α → lp (fun _ : α => ℝ) (1 : ℝ≥0∞)) := by
  apply Isometry.of_dist_eq
  intro u v
  simpa using dist_toLpOne u v


theorem isUniformEmbedding_equivLpOne :
    IsUniformEmbedding
      (equivLpOne : SummableTail α ≃ lp (fun _ : α => ℝ) (1 : ℝ≥0∞)) :=
  isometry_toLpOne.isUniformEmbedding


noncomputable instance instCompleteSpace : CompleteSpace (SummableTail α) := by
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  exact (completeSpace_congr (e := equivLpOne) isUniformEmbedding_equivLpOne).2
    inferInstance

end SummableTail



structure FinitePlusTailState (n : ℕ) (α : Type*) where
  finite : Fin n → ℝ
  tail : SummableTail α

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

@[ext]
theorem ext {x y : FinitePlusTailState n α}
    (hfinite : x.finite = y.finite) (htail : x.tail = y.tail) : x = y := by
  cases x
  cases y
  cases hfinite
  cases htail
  rfl

instance instInhabited : Inhabited (FinitePlusTailState n α) :=
  ⟨{ finite := 0, tail := 0 }⟩


def ofFinite (x : Fin n → ℝ) : FinitePlusTailState n α where
  finite := x
  tail := 0

@[simp] theorem ofFinite_finite (x : Fin n → ℝ) :
    (ofFinite (α := α) x).finite = x :=
  rfl

@[simp] theorem ofFinite_tail (x : Fin n → ℝ) :
    (ofFinite (α := α) x).tail = 0 :=
  rfl


noncomputable def dist (x y : FinitePlusTailState n α) : ℝ :=
  FiniteContraction.l1Dist x.finite y.finite + x.tail.dist y.tail


noncomputable def finiteDist (x y : FinitePlusTailState n α) : ℝ :=
  FiniteContraction.l1Dist x.finite y.finite


noncomputable def tailDist (x y : FinitePlusTailState n α) : ℝ :=
  x.tail.dist y.tail


theorem dist_nonneg (x y : FinitePlusTailState n α) :
    0 ≤ x.dist y :=
  add_nonneg (FiniteContraction.l1Dist_nonneg x.finite y.finite)
    (SummableTail.dist_nonneg x.tail y.tail)


theorem finiteDist_nonneg (x y : FinitePlusTailState n α) :
    0 ≤ x.finiteDist y :=
  FiniteContraction.l1Dist_nonneg x.finite y.finite


theorem tailDist_nonneg (x y : FinitePlusTailState n α) :
    0 ≤ x.tailDist y :=
  SummableTail.dist_nonneg x.tail y.tail

@[simp] theorem ofFinite_finiteDist (x y : Fin n → ℝ) :
    (ofFinite (α := α) x).finiteDist (ofFinite y) =
      FiniteContraction.l1Dist x y :=
  rfl

@[simp] theorem ofFinite_tailDist (x y : Fin n → ℝ) :
    (ofFinite (α := α) x).tailDist (ofFinite y) = 0 := by
  simp [ofFinite, tailDist]

@[simp] theorem ofFinite_dist (x y : Fin n → ℝ) :
    (ofFinite (α := α) x).dist (ofFinite y) =
      FiniteContraction.l1Dist x y := by
  simp [dist, ofFinite]


theorem finiteDist_le_dist (x y : FinitePlusTailState n α) :
    x.finiteDist y ≤ x.dist y := by
  calc
    x.finiteDist y ≤ x.finiteDist y + x.tailDist y := by
      exact le_add_of_nonneg_right (tailDist_nonneg x y)
    _ = x.dist y := rfl


theorem tailDist_le_dist (x y : FinitePlusTailState n α) :
    x.tailDist y ≤ x.dist y := by
  calc
    x.tailDist y ≤ x.finiteDist y + x.tailDist y := by
      exact le_add_of_nonneg_left (finiteDist_nonneg x y)
    _ = x.dist y := rfl


@[simp] theorem dist_self (x : FinitePlusTailState n α) :
    x.dist x = 0 := by
  simp [dist, FiniteContraction.l1Dist_self]


theorem dist_comm (x y : FinitePlusTailState n α) :
    x.dist y = y.dist x := by
  simp [dist, FiniteContraction.l1Dist_comm, SummableTail.dist_comm]


theorem dist_triangle (x y z : FinitePlusTailState n α) :
    x.dist z ≤ x.dist y + y.dist z := by
  calc
    x.dist z =
        x.finiteDist z + x.tailDist z := rfl
    _ ≤
        (x.finiteDist y + y.finiteDist z) +
          (x.tailDist y + y.tailDist z) := by
      exact add_le_add
        (FiniteContraction.l1Dist_triangle x.finite y.finite z.finite)
        (SummableTail.dist_triangle x.tail y.tail z.tail)
    _ = x.dist y + y.dist z := by
      simp [dist, finiteDist, tailDist]
      ring


theorem eq_of_dist_eq_zero {x y : FinitePlusTailState n α}
    (h : x.dist y = 0) : x = y := by
  apply ext
  · apply FiniteContraction.l1Dist_eq_zero_iff.mp
    exact le_antisymm
      (by simpa [h, finiteDist] using finiteDist_le_dist x y)
      (FiniteContraction.l1Dist_nonneg x.finite y.finite)
  · apply SummableTail.eq_of_dist_eq_zero
    exact le_antisymm
      (by simpa [h, tailDist] using tailDist_le_dist x y)
      (SummableTail.dist_nonneg x.tail y.tail)


noncomputable instance instMetricSpace :
    MetricSpace (FinitePlusTailState n α) where
  dist := dist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero := by
    intro x y h
    exact eq_of_dist_eq_zero h


noncomputable def equivProduct :
    FinitePlusTailState n α ≃ FiniteContraction.L1Vector n × SummableTail α where
  toFun x := (FiniteContraction.L1Vector.ofFun x.finite, x.tail)
  invFun p := { finite := p.1.coord, tail := p.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro p
    cases p with
    | mk finite tail =>
        cases finite
        rfl



theorem lipschitz_equivProduct :
    LipschitzWith 1
      (equivProduct :
        FinitePlusTailState n α →
          FiniteContraction.L1Vector n × SummableTail α) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [Prod.dist_eq]
  have hmax :
      max (FiniteContraction.l1Dist x.finite y.finite)
          (x.tail.dist y.tail) ≤ x.dist y :=
    max_le
      (by simpa [finiteDist] using finiteDist_le_dist x y)
      (by simpa [tailDist] using tailDist_le_dist x y)
  simpa [equivProduct] using hmax



theorem lipschitz_equivProduct_symm :
    LipschitzWith 2
      ((equivProduct :
        FinitePlusTailState n α ≃
          FiniteContraction.L1Vector n × SummableTail α).symm) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rcases x with ⟨xf, xt⟩
  rcases y with ⟨yf, yt⟩
  rw [Prod.dist_eq]
  change
    FiniteContraction.l1Dist xf.coord yf.coord + xt.dist yt ≤
      ((2 : ℝ≥0) : ℝ) *
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt)
  have hfinite :
      FiniteContraction.l1Dist xf.coord yf.coord ≤
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) :=
    le_max_left _ _
  have htail :
      xt.dist yt ≤
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) :=
    le_max_right _ _
  calc
    FiniteContraction.l1Dist xf.coord yf.coord + xt.dist yt ≤
        max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) +
          max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) :=
      add_le_add hfinite htail
    _ =
        ((2 : ℝ≥0) : ℝ) *
          max (FiniteContraction.l1Dist xf.coord yf.coord) (xt.dist yt) := by
      have htwo : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
      rw [htwo]
      ring


theorem isUniformEmbedding_equivProduct :
    IsUniformEmbedding
      (equivProduct :
        FinitePlusTailState n α ≃
          FiniteContraction.L1Vector n × SummableTail α) :=
  (equivProduct :
    FinitePlusTailState n α ≃
      FiniteContraction.L1Vector n × SummableTail α).isUniformEmbedding
    lipschitz_equivProduct.uniformContinuous
    lipschitz_equivProduct_symm.uniformContinuous




noncomputable instance instCompleteSpace :
    CompleteSpace (FinitePlusTailState n α) :=
  (completeSpace_congr isUniformEmbedding_equivProduct).2 inferInstance


def ClosedBall (center : FinitePlusTailState n α) (radius : ℝ)
    (x : FinitePlusTailState n α) : Prop :=
  x.dist center ≤ radius


def MapsClosedBall (F : FinitePlusTailState n α → FinitePlusTailState n α)
    (center : FinitePlusTailState n α) (radius : ℝ) : Prop :=
  ∀ x, ClosedBall center radius x → ClosedBall center radius (F x)


theorem center_mem_closedBall (center : FinitePlusTailState n α)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    ClosedBall center radius center := by
  unfold ClosedBall
  simpa using hradius


theorem closedBall_mono_radius {center x : FinitePlusTailState n α}
    {radius radius' : ℝ}
    (hx : ClosedBall center radius x) (hradius : radius ≤ radius') :
    ClosedBall center radius' x :=
  le_trans hx hradius



theorem ofFinite_closedBall_iff
    {center x : Fin n → ℝ} {radius : ℝ} :
    ClosedBall (ofFinite (α := α) center) radius (ofFinite x) ↔
      FiniteContraction.ClosedBall center radius x := by
  simp [ClosedBall, FiniteContraction.ClosedBall]

end FinitePlusTailState






structure FinitePlusTailLipschitzCertificate (n : ℕ) (α : Type*) where
  map : FinitePlusTailState n α → FinitePlusTailState n α
  finiteToFinite : ℝ
  tailToFinite : ℝ
  finiteToTail : ℝ
  tailToTail : ℝ
  c : ℝ
  finiteToFinite_nonneg : 0 ≤ finiteToFinite
  tailToFinite_nonneg : 0 ≤ tailToFinite
  finiteToTail_nonneg : 0 ≤ finiteToTail
  tailToTail_nonneg : 0 ≤ tailToTail
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  finite_bound :
    ∀ x y,
      (map x).finiteDist (map y) ≤
        finiteToFinite * x.finiteDist y + tailToFinite * x.tailDist y
  tail_bound :
    ∀ x y,
      (map x).tailDist (map y) ≤
        finiteToTail * x.finiteDist y + tailToTail * x.tailDist y
  finite_column_sum_le : finiteToFinite + finiteToTail ≤ c
  tail_column_sum_le : tailToFinite + tailToTail ≤ c

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


theorem mixed_lipschitz
    (C : FinitePlusTailLipschitzCertificate n α) :
    ∀ x y, (C.map x).dist (C.map y) ≤ C.c * x.dist y := by
  intro x y
  have hfinite_nonneg : 0 ≤ x.finiteDist y :=
    FinitePlusTailState.finiteDist_nonneg x y
  have htail_nonneg : 0 ≤ x.tailDist y :=
    FinitePlusTailState.tailDist_nonneg x y
  calc
    (C.map x).dist (C.map y) =
        (C.map x).finiteDist (C.map y) +
          (C.map x).tailDist (C.map y) := rfl
    _ ≤
        (C.finiteToFinite * x.finiteDist y +
          C.tailToFinite * x.tailDist y) +
        (C.finiteToTail * x.finiteDist y +
          C.tailToTail * x.tailDist y) := by
      exact add_le_add (C.finite_bound x y) (C.tail_bound x y)
    _ =
        (C.finiteToFinite + C.finiteToTail) * x.finiteDist y +
          (C.tailToFinite + C.tailToTail) * x.tailDist y := by
      ring
    _ ≤ C.c * x.finiteDist y + C.c * x.tailDist y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right C.finite_column_sum_le hfinite_nonneg)
        (mul_le_mul_of_nonneg_right C.tail_column_sum_le htail_nonneg)
    _ = C.c * x.dist y := by
      simp [FinitePlusTailState.dist, FinitePlusTailState.finiteDist,
        FinitePlusTailState.tailDist]
      ring_nf


noncomputable def iterate (C : FinitePlusTailLipschitzCertificate n α) :
    ℕ → FinitePlusTailState n α → FinitePlusTailState n α
  | 0, x => x
  | k + 1, x => C.map (C.iterate k x)


theorem iterate_contracts
    (C : FinitePlusTailLipschitzCertificate n α) (k : ℕ)
    (x y : FinitePlusTailState n α) :
    (C.iterate k x).dist (C.iterate k y) ≤ C.c ^ k * x.dist y := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      calc
        (C.iterate (k + 1) x).dist (C.iterate (k + 1) y) =
            (C.map (C.iterate k x)).dist (C.map (C.iterate k y)) := rfl
        _ ≤ C.c * (C.iterate k x).dist (C.iterate k y) :=
          C.mixed_lipschitz _ _
        _ ≤ C.c * (C.c ^ k * x.dist y) := by
          exact mul_le_mul_of_nonneg_left ih C.c_nonneg
        _ = C.c ^ (k + 1) * x.dist y := by
          ring


theorem mapsClosedBall_iterate_mem
    (C : FinitePlusTailLipschitzCertificate n α)
    {center : FinitePlusTailState n α} {radius : ℝ}
    (hmap : FinitePlusTailState.MapsClosedBall C.map center radius)
    {x : FinitePlusTailState n α}
    (hx : FinitePlusTailState.ClosedBall center radius x) (k : ℕ) :
    FinitePlusTailState.ClosedBall center radius (C.iterate k x) := by
  induction k with
  | zero =>
      simpa [iterate] using hx
  | succ _ ih =>
      exact hmap _ ih




theorem mapsClosedBall_of_residual_and_lipschitz
    (C : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hresidual : (C.map center).dist center ≤ residual)
    (hradius : residual + C.c * radius ≤ radius) :
    FinitePlusTailState.MapsClosedBall C.map center radius := by
  intro x hx
  unfold FinitePlusTailState.ClosedBall at hx ⊢
  calc
    (C.map x).dist center ≤
        (C.map x).dist (C.map center) + (C.map center).dist center :=
      FinitePlusTailState.dist_triangle (C.map x) (C.map center) center
    _ ≤ C.c * x.dist center + residual := by
      exact add_le_add (C.mixed_lipschitz x center) hresidual
    _ ≤ C.c * radius + residual := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hx C.c_nonneg) residual
    _ = residual + C.c * radius := by
      ring
    _ ≤ radius := hradius



theorem contractingWith
    (C : FinitePlusTailLipschitzCertificate n α) :
    ContractingWith (⟨C.c, C.c_nonneg⟩ : ℝ≥0) C.map := by
  constructor
  · exact_mod_cast C.c_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change (C.map x).dist (C.map y) ≤ C.c * x.dist y
    exact C.mixed_lipschitz x y


noncomputable def fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α) :
    FinitePlusTailState n α :=
  ContractingWith.fixedPoint C.map C.contractingWith


theorem fixedPoint_isFixed
    (C : FinitePlusTailLipschitzCertificate n α) :
    C.map C.fixedPoint = C.fixedPoint := by
  have hfixed : Function.IsFixedPt C.map C.fixedPoint :=
    C.contractingWith.fixedPoint_isFixedPt
  simpa [fixedPoint, Function.IsFixedPt] using hfixed


theorem fixedPoint_unique
    (C : FinitePlusTailLipschitzCertificate n α)
    {x y : FinitePlusTailState n α}
    (hx : C.map x = x) (hy : C.map y = y) : x = y :=
  C.contractingWith.fixedPoint_unique' hx hy



theorem eq_fixedPoint_of_isFixed
    (C : FinitePlusTailLipschitzCertificate n α)
    {x : FinitePlusTailState n α} (hx : C.map x = x) :
    x = C.fixedPoint :=
  C.contractingWith.fixedPoint_unique hx


theorem exists_fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α) :
    ∃ p : FinitePlusTailState n α, C.map p = p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed⟩


theorem exists_unique_fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α) :
    ∃! p : FinitePlusTailState n α, C.map p = p := by
  refine ⟨C.fixedPoint, C.fixedPoint_isFixed, ?_⟩
  intro y hy
  exact C.eq_fixedPoint_of_isFixed hy


theorem iterate_eq_of_fixed
    (C : FinitePlusTailLipschitzCertificate n α)
    {x : FinitePlusTailState n α} (hx : C.map x = x) (k : ℕ) :
    C.iterate k x = x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, hx]


theorem iterate_dist_le_pow_mul_of_fixed
    (C : FinitePlusTailLipschitzCertificate n α)
    {p : FinitePlusTailState n α} (hp : C.map p = p)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.iterate k x).dist p ≤ C.c ^ k * x.dist p := by
  simpa [C.iterate_eq_of_fixed hp k] using C.iterate_contracts k x p


theorem iterate_dist_le_pow_mul_fixedPoint
    (C : FinitePlusTailLipschitzCertificate n α)
    (x : FinitePlusTailState n α) (k : ℕ) :
    (C.iterate k x).dist C.fixedPoint ≤
      C.c ^ k * x.dist C.fixedPoint :=
  C.iterate_dist_le_pow_mul_of_fixed C.fixedPoint_isFixed x k



theorem fixedPoint_mem_closedBall_of_residual
    (C : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hresidual : (C.map center).dist center ≤ residual)
    (hradius : residual + C.c * radius ≤ radius) :
    FinitePlusTailState.ClosedBall center radius C.fixedPoint := by
  unfold FinitePlusTailState.ClosedBall
  have hd :
      C.fixedPoint.dist center ≤
        C.c * C.fixedPoint.dist center + residual := by
    calc
      C.fixedPoint.dist center =
          (C.map C.fixedPoint).dist center := by
        rw [C.fixedPoint_isFixed]
      _ ≤
          (C.map C.fixedPoint).dist (C.map center) +
            (C.map center).dist center :=
        FinitePlusTailState.dist_triangle
          (C.map C.fixedPoint) (C.map center) center
      _ ≤ C.c * C.fixedPoint.dist center + residual := by
        exact add_le_add (C.mixed_lipschitz C.fixedPoint center) hresidual
  nlinarith [hd, hradius, C.c_lt_one]


theorem exists_fixedPoint_mem_closedBall_of_residual
    (C : FinitePlusTailLipschitzCertificate n α)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hresidual : (C.map center).dist center ≤ residual)
    (hradius : residual + C.c * radius ≤ radius) :
    ∃ p : FinitePlusTailState n α,
      C.map p = p ∧ FinitePlusTailState.ClosedBall center radius p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed,
    C.fixedPoint_mem_closedBall_of_residual center hresidual hradius⟩




noncomputable def ofDecoupled
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ)
    (tailMap : SummableTail α → SummableTail α)
    {finiteConstant tailConstant c : ℝ}
    (hfiniteConstant_nonneg : 0 ≤ finiteConstant)
    (htailConstant_nonneg : 0 ≤ tailConstant)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    (hfinite_le_c : finiteConstant ≤ c)
    (htail_le_c : tailConstant ≤ c)
    (hfinite :
      ∀ x y,
        FiniteContraction.l1Dist (finiteMap x) (finiteMap y) ≤
          finiteConstant * FiniteContraction.l1Dist x y)
    (htail :
      ∀ u v, (tailMap u).dist (tailMap v) ≤ tailConstant * u.dist v) :
    FinitePlusTailLipschitzCertificate n α where
  map := fun x => { finite := finiteMap x.finite, tail := tailMap x.tail }
  finiteToFinite := finiteConstant
  tailToFinite := 0
  finiteToTail := 0
  tailToTail := tailConstant
  c := c
  finiteToFinite_nonneg := hfiniteConstant_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := by norm_num
  tailToTail_nonneg := htailConstant_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      hfinite x.finite y.finite
  tail_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      htail x.tail y.tail
  finite_column_sum_le := by
    simpa using hfinite_le_c
  tail_column_sum_le := by
    simpa using htail_le_c



noncomputable def ofFiniteMap
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite : FiniteContraction.LipschitzWithConstant finiteMap c) :
    FinitePlusTailLipschitzCertificate n α :=
  ofDecoupled finiteMap (fun _ => (0 : SummableTail α))
    (finiteConstant := c) (tailConstant := 0) (c := c)
    hc_nonneg (by norm_num) hc_nonneg hc_lt_one
    (le_refl c) hc_nonneg
    hfinite
    (by
      intro u v
      simp [SummableTail.dist_self])

@[simp] theorem ofFiniteMap_map_ofFinite
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite : FiniteContraction.LipschitzWithConstant finiteMap c)
    (x : Fin n → ℝ) :
    ((ofFiniteMap (α := α) finiteMap hc_nonneg hc_lt_one hfinite).map
      (FinitePlusTailState.ofFinite x)) =
        FinitePlusTailState.ofFinite (α := α) (finiteMap x) :=
  rfl


theorem l1Dist_scaleFinite (c : ℝ) (x y : Fin n → ℝ) :
    FiniteContraction.l1Dist (fun i => c * x i) (fun i => c * y i) =
      |c| * FiniteContraction.l1Dist x y := by
  unfold FiniteContraction.l1Dist RatInterval.supNormVec
  calc
    (∑ i, |c * x i - c * y i|) =
        ∑ i, |c| * |x i - y i| := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have h : c * x i - c * y i = c * (x i - y i) := by ring
      rw [h, abs_mul]
    _ = |c| * ∑ i, |x i - y i| := by
      rw [Finset.mul_sum]



noncomputable def decoupledScaling
    (finiteScale tailScale c : ℝ)
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_abs_le : |finiteScale| ≤ c)
    (htail_abs_le : |tailScale| ≤ c) :
    FinitePlusTailLipschitzCertificate n α :=
  ofDecoupled
    (fun x i => finiteScale * x i)
    (SummableTail.scale tailScale)
    (finiteConstant := |finiteScale|)
    (tailConstant := |tailScale|)
    (c := c)
    (abs_nonneg finiteScale)
    (abs_nonneg tailScale)
    hc_nonneg
    hc_lt_one
    hfinite_abs_le
    htail_abs_le
    (by
      intro x y
      rw [l1Dist_scaleFinite])
    (by
      intro u v
      rw [SummableTail.dist_scale])








noncomputable def ofColumnSumFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail c : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    (hfinite_column_sum_le : (hI.c : ℝ) + finiteToTail ≤ c)
    (htail_column_sum_le : tailToTail ≤ c)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailLipschitzCertificate n α where
  map := fun x =>
    { finite := fun i => RatInterval.matVec A x.finite i
      tail := tailMap x }
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  c := c
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_matVec_of_columnSumContraction hI hA
        x.finite y.finite
  tail_bound := htail_bound
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := by
    simpa using htail_column_sum_le




noncomputable def ofColumnSumAffineFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (offset : Fin n → ℝ)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail c : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    (hfinite_column_sum_le : (hI.c : ℝ) + finiteToTail ≤ c)
    (htail_column_sum_le : tailToTail ≤ c)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailLipschitzCertificate n α where
  map := fun x =>
    { finite := fun i => RatInterval.affineMap A offset x.finite i
      tail := tailMap x }
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  c := c
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_affineMap_of_columnSumContraction hI hA offset
        x.finite y.finite
  tail_bound := htail_bound
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := by
    simpa using htail_column_sum_le

end FinitePlusTailLipschitzCertificate

end Exact3D
end StatMech
