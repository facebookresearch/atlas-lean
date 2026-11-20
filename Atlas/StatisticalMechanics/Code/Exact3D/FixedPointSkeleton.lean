/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Code.Exact3D.MatrixCertificate










namespace StatMech
namespace Exact3D

open scoped NNReal

namespace FiniteContraction


noncomputable def l1Dist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  RatInterval.supNormVec fun i => x i - y i


theorem l1Dist_nonneg {n : ℕ} (x y : Fin n → ℝ) :
    0 ≤ l1Dist x y :=
  RatInterval.supNormVec_nonneg _


theorem abs_sub_coord_le_l1Dist {n : ℕ} (x y : Fin n → ℝ) (i : Fin n) :
    |x i - y i| ≤ l1Dist x y :=
  RatInterval.abs_coord_le_supNormVec (fun i => x i - y i) i


theorem eq_of_l1Dist_eq_zero {n : ℕ} {x y : Fin n → ℝ}
    (h : l1Dist x y = 0) : x = y := by
  funext i
  have habs_nonpos : |x i - y i| ≤ 0 := by
    simpa [h] using abs_sub_coord_le_l1Dist x y i
  have habs_zero : |x i - y i| = 0 :=
    le_antisymm habs_nonpos (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_zero)


def LipschitzWithConstant {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x y, l1Dist (F x) (F y) ≤ c * l1Dist x y


theorem lipschitzWithConstant_mono {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {c c' : ℝ}
    (hLip : LipschitzWithConstant F c) (hc : c ≤ c') :
    LipschitzWithConstant F c' := by
  intro x y
  exact le_trans (hLip x y)
    (mul_le_mul_of_nonneg_right hc (l1Dist_nonneg x y))


noncomputable def iterate {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → Fin n → ℝ
  | 0, x => x
  | k + 1, x => F (iterate F k x)


theorem matVec_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    RatInterval.matVec A x i - RatInterval.matVec A y i =
      RatInterval.matVec A (fun j => x j - y j) i := by
  unfold RatInterval.matVec
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem affineMap_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    RatInterval.affineMap A b x i - RatInterval.affineMap A b y i =
      RatInterval.matVec A (fun j => x j - y j) i := by
  calc
    RatInterval.affineMap A b x i - RatInterval.affineMap A b y i =
        RatInterval.matVec A x i - RatInterval.matVec A y i := by
      unfold RatInterval.affineMap
      ring
    _ = RatInterval.matVec A (fun j => x j - y j) i := matVec_sub A x y i




theorem lipschitz_matVec_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i)
      ((n : ℝ) * (hI.c : ℝ)) := by
  intro x y
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |RatInterval.matVec A x i - RatInterval.matVec A y i|) =
        ∑ i, |RatInterval.matVec A (fun j => x j - y j) i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [matVec_sub]
    _ ≤ ∑ _i : Fin n, (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      exact Finset.sum_le_sum fun i _ => hI.apply_bound hA _ i
    _ = (n : ℝ) * (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring



theorem lipschitz_matVec_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i) (hI.c : ℝ) := by
  intro x y
  unfold l1Dist
  calc
    RatInterval.supNormVec
        (fun i => RatInterval.matVec A x i - RatInterval.matVec A y i) =
        RatInterval.supNormVec
          (fun i => RatInterval.matVec A (fun j => x j - y j) i) := by
      congr 1
      funext i
      exact matVec_sub A x y i
    _ ≤ (hI.c : ℝ) * RatInterval.supNormVec (fun j => x j - y j) :=
      hI.apply_l1_bound hA (fun j => x j - y j)



theorem lipschitz_affineMap_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.affineMap A b x i)
      ((n : ℝ) * (hI.c : ℝ)) := by
  intro x y
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |RatInterval.affineMap A b x i -
        RatInterval.affineMap A b y i|) =
        ∑ i, |RatInterval.matVec A (fun j => x j - y j) i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [affineMap_sub]
    _ ≤ ∑ _i : Fin n, (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      exact Finset.sum_le_sum fun i _ => hI.apply_bound hA _ i
    _ = (n : ℝ) * (hI.c : ℝ) *
        RatInterval.supNormVec (fun j => x j - y j) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring



theorem lipschitz_affineMap_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.affineMap A b x i)
      (hI.c : ℝ) := by
  intro x y
  unfold l1Dist
  calc
    RatInterval.supNormVec
        (fun i => RatInterval.affineMap A b x i -
          RatInterval.affineMap A b y i) =
        RatInterval.supNormVec
          (fun i => RatInterval.matVec A (fun j => x j - y j) i) := by
      congr 1
      funext i
      exact affineMap_sub A b x y i
    _ ≤ (hI.c : ℝ) * RatInterval.supNormVec (fun j => x j - y j) :=
      hI.apply_l1_bound hA (fun j => x j - y j)


theorem lipschitz_affineMatVec_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i + b i)
      ((n : ℝ) * (hI.c : ℝ)) := by
  simpa [RatInterval.affineMap] using
    lipschitz_affineMap_of_rowSumContraction hI hA b


theorem lipschitz_affineMatVec_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) :
    LipschitzWithConstant (fun x i => RatInterval.matVec A x i + b i)
      (hI.c : ℝ) := by
  simpa [RatInterval.affineMap] using
    lipschitz_affineMap_of_columnSumContraction hI hA b


theorem l1Dist_triangle {n : ℕ} (x y z : Fin n → ℝ) :
    l1Dist x z ≤ l1Dist x y + l1Dist y z := by
  classical
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |x i - z i|) ≤ ∑ i, (|x i - y i| + |y i - z i|) := by
      apply Finset.sum_le_sum
      intro i _
      have h : x i - z i = (x i - y i) + (y i - z i) := by ring
      rw [h]
      exact abs_add_le _ _
    _ = (∑ i, |x i - y i|) + ∑ i, |y i - z i| := by
      rw [Finset.sum_add_distrib]


theorem l1Dist_self {n : ℕ} (x : Fin n → ℝ) : l1Dist x x = 0 := by
  simp [l1Dist, RatInterval.supNormVec]


theorem l1Dist_eq_zero_iff {n : ℕ} {x y : Fin n → ℝ} :
    l1Dist x y = 0 ↔ x = y :=
  ⟨eq_of_l1Dist_eq_zero, fun h => by cases h; exact l1Dist_self x⟩


theorem l1Dist_comm {n : ℕ} (x y : Fin n → ℝ) :
    l1Dist x y = l1Dist y x := by
  unfold l1Dist RatInterval.supNormVec
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_sub_comm]




structure L1Vector (n : ℕ) where
  coord : Fin n → ℝ

namespace L1Vector

variable {n : ℕ}


def ofFun (x : Fin n → ℝ) : L1Vector n :=
  ⟨x⟩

@[ext]
theorem ext {x y : L1Vector n} (h : x.coord = y.coord) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance instInhabited : Inhabited (L1Vector n) :=
  ⟨ofFun 0⟩


noncomputable instance instMetricSpace (n : ℕ) : MetricSpace (L1Vector n) where
  dist x y := l1Dist x.coord y.coord
  dist_self x := l1Dist_self x.coord
  dist_comm x y := l1Dist_comm x.coord y.coord
  dist_triangle x y z := l1Dist_triangle x.coord y.coord z.coord
  eq_of_dist_eq_zero := by
    intro x y h
    exact L1Vector.ext (eq_of_l1Dist_eq_zero h)



def equivFun (n : ℕ) : L1Vector n ≃ (Fin n → ℝ) where
  toFun x := x.coord
  invFun := ofFun
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl


theorem pi_dist_le_l1Dist {n : ℕ} (x y : Fin n → ℝ) :
    dist x y ≤ l1Dist x y := by
  rw [dist_pi_le_iff (l1Dist_nonneg x y)]
  intro i
  simpa [Real.dist_eq] using abs_sub_coord_le_l1Dist x y i



theorem l1Dist_le_nat_mul_pi_dist {n : ℕ} (x y : Fin n → ℝ) :
    l1Dist x y ≤ (n : ℝ) * dist x y := by
  unfold l1Dist RatInterval.supNormVec
  calc
    (∑ i, |x i - y i|) = ∑ i, dist (x i) (y i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.dist_eq]
    _ ≤ ∑ _i : Fin n, dist x y := by
      exact Finset.sum_le_sum fun i _ => dist_le_pi_dist x y i
    _ = (n : ℝ) * dist x y := by
      simp [Finset.sum_const, nsmul_eq_mul]



theorem lipschitz_coord {n : ℕ} :
    LipschitzWith 1 (fun x : L1Vector n => x.coord) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  change dist x.coord y.coord ≤ (1 : ℝ≥0) * l1Dist x.coord y.coord
  simpa using pi_dist_le_l1Dist x.coord y.coord



theorem lipschitz_ofFun {n : ℕ} :
    LipschitzWith (n : ℝ≥0) (ofFun : (Fin n → ℝ) → L1Vector n) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  change l1Dist x y ≤ ((n : ℝ≥0) : ℝ) * dist x y
  simpa using l1Dist_le_nat_mul_pi_dist x y


theorem isUniformEmbedding_equivFun (n : ℕ) :
    IsUniformEmbedding (equivFun n) :=
  (equivFun n).isUniformEmbedding
    (lipschitz_coord (n := n)).uniformContinuous
    (lipschitz_ofFun (n := n)).uniformContinuous


noncomputable instance instCompleteSpace (n : ℕ) :
    CompleteSpace (L1Vector n) :=
  (completeSpace_congr (isUniformEmbedding_equivFun n)).2 inferInstance


noncomputable def liftMap {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) (x : L1Vector n) : L1Vector n :=
  ofFun (F x.coord)

end L1Vector



theorem contractingWith_liftMap_of_l1_contraction {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) :
    ContractingWith (⟨c, hc_nonneg⟩ : ℝ≥0) (L1Vector.liftMap F) := by
  constructor
  · exact_mod_cast hc_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change l1Dist (F x.coord) (F y.coord) ≤
      ((⟨c, hc_nonneg⟩ : ℝ≥0) : ℝ) * l1Dist x.coord y.coord
    simpa using hLip x.coord y.coord



noncomputable def certifiedFixedPointOfL1Contraction {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) : Fin n → ℝ :=
  (ContractingWith.fixedPoint (L1Vector.liftMap F)
    (contractingWith_liftMap_of_l1_contraction hc_nonneg hc_lt_one hLip)).coord



theorem certifiedFixedPointOfL1Contraction_isFixed {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) :
    F (certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip) =
      certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip := by
  let hcontract :=
    contractingWith_liftMap_of_l1_contraction
      (F := F) hc_nonneg hc_lt_one hLip
  have hfixed :
      Function.IsFixedPt (L1Vector.liftMap F)
        (ContractingWith.fixedPoint (L1Vector.liftMap F) hcontract) :=
    hcontract.fixedPoint_isFixedPt
  simpa [certifiedFixedPointOfL1Contraction, L1Vector.liftMap,
    L1Vector.ofFun, Function.IsFixedPt] using congrArg L1Vector.coord hfixed


theorem exists_fixedPoint_of_l1_contraction {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hLip : LipschitzWithConstant F c) :
    ∃ p : Fin n → ℝ, F p = p :=
  ⟨certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip,
    certifiedFixedPointOfL1Contraction_isFixed F hc_nonneg hc_lt_one hLip⟩



theorem lipschitz_iterate {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hLip : LipschitzWithConstant F c) (k : ℕ) :
    LipschitzWithConstant (iterate F k) (c ^ k) := by
  induction k with
  | zero =>
      intro x y
      simp [iterate]
  | succ k ih =>
      intro x y
      calc
        l1Dist (iterate F (k + 1) x) (iterate F (k + 1) y) =
            l1Dist (F (iterate F k x)) (F (iterate F k y)) := rfl
        _ ≤ c * l1Dist (iterate F k x) (iterate F k y) := hLip _ _
        _ ≤ c * (c ^ k * l1Dist x y) := by
          exact mul_le_mul_of_nonneg_left (ih x y) hc_nonneg
        _ = c ^ (k + 1) * l1Dist x y := by
          ring


def ClosedBall {n : ℕ} (center : Fin n → ℝ) (radius : ℝ)
    (x : Fin n → ℝ) : Prop :=
  l1Dist x center ≤ radius


def MapsClosedBall {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ)
    (center : Fin n → ℝ) (radius : ℝ) : Prop :=
  ∀ x, ClosedBall center radius x → ClosedBall center radius (F x)


theorem mapsClosedBall_iterate_mem {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {center : Fin n → ℝ} {radius : ℝ}
    (hmap : MapsClosedBall F center radius) {x : Fin n → ℝ}
    (hx : ClosedBall center radius x) (k : ℕ) :
    ClosedBall center radius (iterate F k x) := by
  induction k with
  | zero =>
      simpa [iterate] using hx
  | succ _ ih =>
      exact hmap _ ih




theorem mapsClosedBall_of_residual_and_lipschitz {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c radius : ℝ}
    (center : Fin n → ℝ)
    (hc_nonneg : 0 ≤ c)
    (hLip : LipschitzWithConstant F c)
    (hresidual : l1Dist (F center) center ≤ (1 - c) * radius) :
    MapsClosedBall F center radius := by
  intro x hx
  unfold ClosedBall at hx ⊢
  calc
    l1Dist (F x) center ≤ l1Dist (F x) (F center) + l1Dist (F center) center :=
      l1Dist_triangle (F x) (F center) center
    _ ≤ c * l1Dist x center + (1 - c) * radius := by
      exact add_le_add (hLip x center) hresidual
    _ ≤ c * radius + (1 - c) * radius := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx hc_nonneg) le_rfl
    _ = radius := by ring


theorem center_mem_closedBall {n : ℕ} (center : Fin n → ℝ) {radius : ℝ}
    (hradius : 0 ≤ radius) : ClosedBall center radius center := by
  unfold ClosedBall
  simpa [l1Dist_self] using hradius


theorem closedBall_mono_radius {n : ℕ} {center x : Fin n → ℝ}
    {radius radius' : ℝ}
    (hx : ClosedBall center radius x) (hradius : radius ≤ radius') :
    ClosedBall center radius' x :=
  le_trans hx hradius




structure ClosedBallContractionCertificate {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) where
  center : Fin n → ℝ
  radius : ℝ
  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  radius_nonneg : 0 ≤ radius
  lipschitz : LipschitzWithConstant F c
  residual_bound : l1Dist (F center) center ≤ (1 - c) * radius



def closedBallContractionCertificate_of_residualBound_and_lipschitz {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c radius residualBound : ℝ}
    (center : Fin n → ℝ)
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) (hradius : 0 ≤ radius)
    (hLip : LipschitzWithConstant F c)
    (hresidual : l1Dist (F center) center ≤ residualBound)
    (hresidualBound : residualBound ≤ (1 - c) * radius) :
    ClosedBallContractionCertificate F where
  center := center
  radius := radius
  c := c
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  radius_nonneg := hradius
  lipschitz := hLip
  residual_bound := le_trans hresidual hresidualBound

namespace ClosedBallContractionCertificate

variable {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}


theorem mapsClosedBall (C : ClosedBallContractionCertificate F) :
    MapsClosedBall F C.center C.radius :=
  mapsClosedBall_of_residual_and_lipschitz F C.center C.c_nonneg C.lipschitz
    C.residual_bound


theorem center_mem (C : ClosedBallContractionCertificate F) :
    ClosedBall C.center C.radius C.center :=
  center_mem_closedBall C.center C.radius_nonneg



theorem residual_l1Dist_le_margin
    (C : ClosedBallContractionCertificate F) :
    l1Dist (F C.center) C.center ≤ (1 - C.c) * C.radius :=
  C.residual_bound



theorem residual_plus_mul_le_radius
    (C : ClosedBallContractionCertificate F) :
    l1Dist (F C.center) C.center + C.c * C.radius ≤ C.radius := by
  calc
    l1Dist (F C.center) C.center + C.c * C.radius ≤
        (1 - C.c) * C.radius + C.c * C.radius := by
      exact add_le_add C.residual_l1Dist_le_margin (le_refl (C.c * C.radius))
    _ = C.radius := by ring



def with_larger_radius (C : ClosedBallContractionCertificate F)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    ClosedBallContractionCertificate F where
  center := C.center
  radius := radius'
  c := C.c
  c_nonneg := C.c_nonneg
  c_lt_one := C.c_lt_one
  radius_nonneg := le_trans C.radius_nonneg hradius
  lipschitz := C.lipschitz
  residual_bound := by
    exact le_trans C.residual_bound
      (mul_le_mul_of_nonneg_left hradius (sub_nonneg.mpr C.c_lt_one.le))

@[simp] theorem with_larger_radius_center
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).center = C.center :=
  rfl

@[simp] theorem with_larger_radius_radius
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).radius = radius' :=
  rfl

@[simp] theorem with_larger_radius_c
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).c = C.c :=
  rfl

end ClosedBallContractionCertificate



theorem fixedPoint_unique_of_l1_contraction {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc : c < 1) (hLip : LipschitzWithConstant F c)
    {x y : Fin n → ℝ} (hx : F x = x) (hy : F y = y) : x = y := by
  have hd : l1Dist x y ≤ c * l1Dist x y := by
    simpa [hx, hy] using hLip x y
  have hnot_pos : ¬ 0 < l1Dist x y := by
    intro hpos
    have hstrict : c * l1Dist x y < l1Dist x y := by
      nlinarith
    linarith
  have hdist_zero : l1Dist x y = 0 := by
    exact le_antisymm (le_of_not_gt hnot_pos) (l1Dist_nonneg x y)
  exact eq_of_l1Dist_eq_zero hdist_zero


theorem iterate_eq_of_fixed {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}
    {x : Fin n → ℝ} (hx : F x = x) (k : ℕ) :
    iterate F k x = x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ _ ih =>
      simp [iterate, ih, hx]



theorem iterate_l1Dist_le_pow_mul_of_fixed {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hLip : LipschitzWithConstant F c)
    {p : Fin n → ℝ} (hp : F p = p) (x : Fin n → ℝ) (k : ℕ) :
    l1Dist (iterate F k x) p ≤ c ^ k * l1Dist x p := by
  have hiter := lipschitz_iterate hc_nonneg hLip k x p
  simpa [iterate_eq_of_fixed hp k] using hiter

namespace ClosedBallContractionCertificate

variable {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}


noncomputable def fixedPoint (C : ClosedBallContractionCertificate F) :
    Fin n → ℝ :=
  certifiedFixedPointOfL1Contraction F C.c_nonneg C.c_lt_one C.lipschitz



@[simp] theorem with_larger_radius_fixedPoint
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    (C.with_larger_radius hradius).fixedPoint = C.fixedPoint :=
  rfl


theorem fixedPoint_isFixed (C : ClosedBallContractionCertificate F) :
    F C.fixedPoint = C.fixedPoint :=
  certifiedFixedPointOfL1Contraction_isFixed F C.c_nonneg C.c_lt_one
    C.lipschitz


theorem fixedPoint_unique (C : ClosedBallContractionCertificate F)
    {x y : Fin n → ℝ} (hx : F x = x) (hy : F y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction F C.c_lt_one C.lipschitz hx hy



theorem fixedPoint_mem (C : ClosedBallContractionCertificate F)
    {x : Fin n → ℝ} (hx : F x = x) :
    ClosedBall C.center C.radius x := by
  unfold ClosedBall
  have hd :
      l1Dist x C.center ≤
        C.c * l1Dist x C.center + (1 - C.c) * C.radius := by
    calc
      l1Dist x C.center = l1Dist (F x) C.center := by rw [hx]
      _ ≤ l1Dist (F x) (F C.center) + l1Dist (F C.center) C.center :=
        l1Dist_triangle (F x) (F C.center) C.center
      _ ≤ C.c * l1Dist x C.center + (1 - C.c) * C.radius := by
        exact add_le_add (C.lipschitz x C.center) C.residual_bound
  nlinarith [hd, C.c_lt_one]


theorem fixedPoint_mem_selected (C : ClosedBallContractionCertificate F) :
    ClosedBall C.center C.radius C.fixedPoint :=
  C.fixedPoint_mem C.fixedPoint_isFixed


theorem fixedPoint_mem_of_radius_le
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') :
    ClosedBall C.center radius' C.fixedPoint :=
  closedBall_mono_radius C.fixedPoint_mem_selected hradius


theorem exists_fixedPoint (C : ClosedBallContractionCertificate F) :
    ∃ p : Fin n → ℝ, F p = p ∧ ClosedBall C.center C.radius p :=
  ⟨C.fixedPoint, C.fixedPoint_isFixed, C.fixedPoint_mem_selected⟩


theorem exists_unique_fixedPoint (C : ClosedBallContractionCertificate F) :
    ∃! p : Fin n → ℝ, F p = p := by
  refine ⟨C.fixedPoint, C.fixedPoint_isFixed, ?_⟩
  intro y hy
  exact C.fixedPoint_unique hy C.fixedPoint_isFixed


theorem eq_fixedPoint_of_isFixed (C : ClosedBallContractionCertificate F)
    {x : Fin n → ℝ} (hx : F x = x) : x = C.fixedPoint :=
  C.fixedPoint_unique hx C.fixedPoint_isFixed



theorem iterate_mem (C : ClosedBallContractionCertificate F)
    {x : Fin n → ℝ} (hx : ClosedBall C.center C.radius x) (k : ℕ) :
    ClosedBall C.center C.radius (FiniteContraction.iterate F k x) :=
  mapsClosedBall_iterate_mem C.mapsClosedBall hx k



theorem iterate_mem_of_radius_le
    (C : ClosedBallContractionCertificate F) {radius' : ℝ}
    (hradius : C.radius ≤ radius') {x : Fin n → ℝ}
    (hx : ClosedBall C.center radius' x) (k : ℕ) :
    ClosedBall C.center radius' (FiniteContraction.iterate F k x) :=
  (C.with_larger_radius hradius).iterate_mem hx k



theorem iterate_l1Dist_le_pow_mul_of_fixed
    (C : ClosedBallContractionCertificate F)
    {p : Fin n → ℝ} (hp : F p = p) (x : Fin n → ℝ) (k : ℕ) :
    l1Dist (FiniteContraction.iterate F k x) p ≤ C.c ^ k * l1Dist x p :=
  FiniteContraction.iterate_l1Dist_le_pow_mul_of_fixed C.c_nonneg C.lipschitz
    hp x k


theorem iterate_l1Dist_le_pow_mul_fixedPoint
    (C : ClosedBallContractionCertificate F) (x : Fin n → ℝ) (k : ℕ) :
    l1Dist (FiniteContraction.iterate F k x) C.fixedPoint ≤
      C.c ^ k * l1Dist x C.fixedPoint :=
  C.iterate_l1Dist_le_pow_mul_of_fixed C.fixedPoint_isFixed x k

end ClosedBallContractionCertificate



theorem matVec_fixedPoint_unique_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.matVec A x i) x = x)
    (hy : (fun x i => RatInterval.matVec A x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.matVec A x i) hcontract
    (lipschitz_matVec_of_rowSumContraction hI hA) hx hy



theorem matVec_fixedPoint_unique_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.matVec A x i) x = x)
    (hy : (fun x i => RatInterval.matVec A x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.matVec A x i) hI.constant_lt_one
    (lipschitz_matVec_of_columnSumContraction hI hA) hx hy




theorem affineMap_fixedPoint_unique_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.affineMap A b x i) x = x)
    (hy : (fun x i => RatInterval.affineMap A b x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.affineMap A b x i) hcontract
    (lipschitz_affineMap_of_rowSumContraction hI hA b) hx hy



theorem affineMap_fixedPoint_unique_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b : Fin n → ℝ) {x y : Fin n → ℝ}
    (hx : (fun x i => RatInterval.affineMap A b x i) x = x)
    (hy : (fun x i => RatInterval.affineMap A b x i) y = y) : x = y :=
  fixedPoint_unique_of_l1_contraction
    (fun x i => RatInterval.affineMap A b x i) hI.constant_lt_one
    (lipschitz_affineMap_of_columnSumContraction hI hA b) hx hy



def closedBallContractionCertificate_of_rowSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.matVec A x i) center) center ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) where
  center := center
  radius := radius
  c := (n : ℝ) * (hI.c : ℝ)
  c_nonneg := by
    exact mul_nonneg (Nat.cast_nonneg n) (by exact_mod_cast hI.c_nonneg)
  c_lt_one := hcontract
  radius_nonneg := hradius
  lipschitz := lipschitz_matVec_of_rowSumContraction hI hA
  residual_bound := hresidual



def closedBallContractionCertificate_of_columnSumContraction {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.matVec A x i) center) center ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) where
  center := center
  radius := radius
  c := hI.c
  c_nonneg := by exact_mod_cast hI.c_nonneg
  c_lt_one := hI.constant_lt_one
  radius_nonneg := hradius
  lipschitz := lipschitz_matVec_of_columnSumContraction hI hA
  residual_bound := hresidual



def closedBallContractionCertificate_of_rowSumContraction_affine {n : ℕ}
    {I : RatInterval.IntervalMatrix n n} (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.affineMap A b x i) center) center ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) where
  center := center
  radius := radius
  c := (n : ℝ) * (hI.c : ℝ)
  c_nonneg := by
    exact mul_nonneg (Nat.cast_nonneg n) (by exact_mod_cast hI.c_nonneg)
  c_lt_one := hcontract
  radius_nonneg := hradius
  lipschitz := lipschitz_affineMap_of_rowSumContraction hI hA b
  residual_bound := hresidual



def closedBallContractionCertificate_of_columnSumContraction_affine {n : ℕ}
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual :
      l1Dist ((fun x i => RatInterval.affineMap A b x i) center) center ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) where
  center := center
  radius := radius
  c := hI.c
  c_nonneg := by exact_mod_cast hI.c_nonneg
  c_lt_one := hI.constant_lt_one
  radius_nonneg := hradius
  lipschitz := lipschitz_affineMap_of_columnSumContraction hI hA b
  residual_bound := hresidual


theorem residual_l1Dist_le_of_vectorMem {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {center : Fin n → ℝ}
    {R : RatInterval.IntervalVector n}
    (hR : RatInterval.VectorMem (fun i => F center i - center i) R) :
    l1Dist (F center) center ≤ (RatInterval.VectorAbsSum R : ℝ) := by
  unfold l1Dist RatInterval.supNormVec
  exact RatInterval.VectorMem.abs_sum_le hR



def closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.matVec A center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_rowSumContraction hI hA center hcontract
    hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)



def closedBallContractionCertificate_of_columnSumContraction_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.matVec A center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_columnSumContraction hI hA center
    hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)



def closedBallContractionCertificate_of_rowSumContraction_affine_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.affineMap A b center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_rowSumContraction_affine hI hA b center
    hcontract hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)



def closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (b center : Fin n → ℝ) {radius : ℝ} {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hresidualMem : RatInterval.VectorMem
      (fun i => RatInterval.affineMap A b center i - center i) R)
    (hresidualSum :
      (RatInterval.VectorAbsSum R : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine hI hA b center
    hradius
    (le_trans (residual_l1Dist_le_of_vectorMem hresidualMem) hresidualSum)



def closedBallContractionCertificate_of_rowSumContraction_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℚ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidual I (RatInterval.pointVector center)) :
          ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorResidual_memR_matVec hA
      (RatInterval.pointVector_memR center))
    hresidualSum



def closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (center : Fin n → ℚ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidual I (RatInterval.pointVector center)) :
          ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_columnSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorResidual_memR_matVec hA
      (RatInterval.pointVector_memR center))
    hresidualSum



def closedBallContractionCertificate_of_rowSumContraction_affine_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidual I B
          (RatInterval.pointVector center)) : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_rowSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorAffineResidual_memR_affineMap hA hb
      (RatInterval.pointVector_memR center))
    hresidualSum



def closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidual I B
          (RatInterval.pointVector center)) : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorAffineResidual_memR_affineMap hA hb
      (RatInterval.pointVector_memR center))
    hresidualSum




def closedBallContractionCertificate_of_rowSumContraction_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidualNonneg I
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorResidualNonneg_memR_matVec_pointVector
      hI_nonneg hA center hcenter_nonneg)
    hresidualSum




def closedBallContractionCertificate_of_columnSumContraction_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorResidualNonneg I
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec A x i) :=
  closedBallContractionCertificate_of_columnSumContraction_and_residualVector
    hI hA (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorResidualNonneg_memR_matVec_pointVector
      hI_nonneg hA center hcenter_nonneg)
    hresidualSum




def closedBallContractionCertificate_of_rowSumContraction_affine_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.RowSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidualNonneg I B
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (n : ℝ) * (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_rowSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hcontract hradius
    (RatInterval.matrixVectorAffineResidualNonneg_memR_affineMap_pointVector
      hI_nonneg hA hb center hcenter_nonneg)
    hresidualSum




def closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter
    {n : ℕ} {I : RatInterval.IntervalMatrix n n}
    {B : RatInterval.IntervalVector n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (hI_nonneg : RatInterval.MatrixNonnegative I)
    {b : Fin n → ℝ} (hb : RatInterval.VectorMem b B)
    (center : Fin n → ℚ) (hcenter_nonneg : ∀ i, 0 ≤ center i)
    {radius : ℝ}
    (hradius : 0 ≤ radius)
    (hresidualSum :
      (RatInterval.VectorAbsSum
        (RatInterval.matrixVectorAffineResidualNonneg I B
          (RatInterval.pointVector center) hI_nonneg
          (RatInterval.pointVector_nonnegative hcenter_nonneg)) : ℝ) ≤
        (1 - (hI.c : ℝ)) * radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap A b x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector
    hI hA b (fun i => (center i : ℝ)) hradius
    (RatInterval.matrixVectorAffineResidualNonneg_memR_affineMap
      hI_nonneg (RatInterval.pointVector_nonnegative hcenter_nonneg) hA hb
      (RatInterval.pointVector_memR center))
    hresidualSum


def zeroMap {n : ℕ} (_x : Fin n → ℝ) (_i : Fin n) : ℝ :=
  0


theorem zeroMap_lipschitz_zero {n : ℕ} :
    LipschitzWithConstant (@zeroMap n) 0 := by
  intro x y
  simp [l1Dist, zeroMap, RatInterval.supNormVec]



def zeroMap_closedBallContractionCertificate {n : ℕ} {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate (@zeroMap n) where
  center := 0
  radius := radius
  c := 0
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  radius_nonneg := hradius
  lipschitz := zeroMap_lipschitz_zero
  residual_bound := by
    simpa [l1Dist, zeroMap, RatInterval.supNormVec] using hradius



theorem zeroMap_mapsClosedBall {n : ℕ} {radius : ℝ} (hradius : 0 ≤ radius) :
    MapsClosedBall (@zeroMap n) 0 radius :=
  (zeroMap_closedBallContractionCertificate (n := n) hradius).mapsClosedBall


theorem zeroMap_fixedPoint_eq_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : zeroMap x = x) : x = 0 := by
  have hunique := fixedPoint_unique_of_l1_contraction (@zeroMap n)
    (by norm_num : (0 : ℝ) < 1) zeroMap_lipschitz_zero hx rfl
  simpa [zeroMap] using hunique

namespace NonzeroAffineExample


def matrixQ : Fin 1 → Fin 1 → ℚ :=
  fun _ _ => 1 / 2


def offsetQ : Fin 1 → ℚ :=
  fun _ => 1 / 4


def centerQ : Fin 1 → ℚ :=
  fun _ => 1 / 2


noncomputable def matrix : Fin 1 → Fin 1 → ℝ :=
  fun i j => (matrixQ i j : ℝ)


noncomputable def offset : Fin 1 → ℝ :=
  fun i => (offsetQ i : ℝ)


def intervals : RatInterval.IntervalMatrix 1 1 :=
  RatInterval.pointMatrix matrixQ


def offsetIntervals : RatInterval.IntervalVector 1 :=
  RatInterval.pointVector offsetQ


theorem matrix_mem_intervals : RatInterval.MatrixMem matrix intervals := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [matrix, matrixQ, intervals, RatInterval.pointMatrix,
    RatInterval.point, RatInterval.MemR]


theorem offset_mem_intervals : RatInterval.VectorMem offset offsetIntervals := by
  intro i
  fin_cases i
  norm_num [offset, offsetQ, offsetIntervals, RatInterval.pointVector,
    RatInterval.point, RatInterval.MemR]


theorem intervals_nonnegative : RatInterval.MatrixNonnegative intervals := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [intervals, RatInterval.pointMatrix, matrixQ, RatInterval.point,
    RatInterval.Nonnegative]


theorem centerQ_nonnegative (i : Fin 1) : 0 ≤ centerQ i := by
  fin_cases i
  norm_num [centerQ]


def columnSumContraction : RatInterval.ColumnSumContraction intervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  col_bound := by
    intro j
    fin_cases j
    norm_num [RatInterval.MatrixAbsColSum, intervals, RatInterval.pointMatrix,
      matrixQ, RatInterval.absUpper, RatInterval.point]


theorem center_fixedPoint :
    (fun x i => RatInterval.affineMap matrix offset x i)
      (fun _ : Fin 1 => (1 / 2 : ℝ)) =
      (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  funext i
  fin_cases i
  norm_num [RatInterval.affineMap, RatInterval.matVec, matrix, matrixQ,
    offset, offsetQ]


noncomputable def exactClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine
    columnSumContraction matrix_mem_intervals offset
    (fun _ : Fin 1 => (1 / 2 : ℝ)) hradius (by
      have hnonneg :
          0 ≤ (1 - (columnSumContraction.c : ℝ)) * radius := by
        exact mul_nonneg (by norm_num [columnSumContraction]) hradius
      rw [center_fixedPoint]
      simpa [l1Dist_self] using hnonneg)



theorem affineResidual_absSum_le_radius_one :
    (RatInterval.VectorAbsSum
      (RatInterval.matrixVectorAffineResidual intervals offsetIntervals
        (RatInterval.pointVector centerQ)) : ℝ) ≤
      (1 - (columnSumContraction.c : ℝ)) * (1 : ℝ) := by
  norm_num [RatInterval.VectorAbsSum, RatInterval.matrixVectorAffineResidual,
    RatInterval.matrixVectorAffine, RatInterval.matrixVectorMul,
    RatInterval.pointVector, RatInterval.pointMatrix, RatInterval.finsetSum,
    RatInterval.vectorSub, RatInterval.vectorAdd, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mul, RatInterval.point,
    RatInterval.absUpper, intervals, offsetIntervals, matrixQ, offsetQ,
    centerQ, columnSumContraction]



noncomputable def affineRationalCenterClosedBallCertificate :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter
    columnSumContraction matrix_mem_intervals offset_mem_intervals centerQ
    (radius := 1) (by norm_num) affineResidual_absSum_le_radius_one



theorem affineResidualNonneg_absSum_le_radius_zero :
    (RatInterval.VectorAbsSum
      (RatInterval.matrixVectorAffineResidualNonneg intervals offsetIntervals
        (RatInterval.pointVector centerQ) intervals_nonnegative
        (RatInterval.pointVector_nonnegative centerQ_nonnegative)) : ℝ) ≤
      (1 - (columnSumContraction.c : ℝ)) * (0 : ℝ) := by
  norm_num [RatInterval.VectorAbsSum,
    RatInterval.matrixVectorAffineResidualNonneg,
    RatInterval.matrixVectorAffineNonneg,
    RatInterval.matrixVectorMulNonneg,
    RatInterval.pointVector, RatInterval.pointMatrix, RatInterval.finsetSum,
    RatInterval.vectorSub, RatInterval.vectorAdd, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mulNonneg,
    RatInterval.point, RatInterval.absUpper, intervals, offsetIntervals,
    matrixQ, offsetQ, centerQ, columnSumContraction]



noncomputable def affineRationalCenterExactClosedBallCertificate :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter
    columnSumContraction matrix_mem_intervals intervals_nonnegative
    offset_mem_intervals centerQ centerQ_nonnegative
    (radius := 0) (by norm_num) affineResidualNonneg_absSum_le_radius_zero



theorem exists_fixedPoint_in_ball :
    ∃ p : Fin 1 → ℝ,
      (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧
      ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 p :=
  by
    simpa [affineRationalCenterClosedBallCertificate,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction_affine, centerQ]
      using affineRationalCenterClosedBallCertificate.exists_fixedPoint



theorem exists_fixedPoint_in_exact_ball :
    ∃ p : Fin 1 → ℝ,
      (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧
      ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 0 p :=
  by
    simpa [affineRationalCenterExactClosedBallCertificate,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction_affine, centerQ]
      using affineRationalCenterExactClosedBallCertificate.exists_fixedPoint



noncomputable def affineRationalCenterExactClosedBallCertificateRelaxed :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  affineRationalCenterExactClosedBallCertificate.with_larger_radius
    (radius' := (1 : ℝ))
    (by
      norm_num [affineRationalCenterExactClosedBallCertificate,
        closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter,
        closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
        closedBallContractionCertificate_of_columnSumContraction_affine])


theorem exists_fixedPoint_in_relaxed_exact_ball :
    ∃ p : Fin 1 → ℝ,
      (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧
      ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 p :=
  by
    simpa [affineRationalCenterExactClosedBallCertificateRelaxed,
      affineRationalCenterExactClosedBallCertificate,
      ClosedBallContractionCertificate.with_larger_radius,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_nonnegRationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction_affine, centerQ]
      using affineRationalCenterExactClosedBallCertificateRelaxed.exists_fixedPoint



theorem selectedFixedPoint_eq_center :
    affineRationalCenterClosedBallCertificate.fixedPoint =
      (fun _ : Fin 1 => (1 / 2 : ℝ)) :=
  affineRationalCenterClosedBallCertificate.fixedPoint_unique
    affineRationalCenterClosedBallCertificate.fixedPoint_isFixed center_fixedPoint



theorem selectedExactFixedPoint_eq_center :
    affineRationalCenterExactClosedBallCertificate.fixedPoint =
      (fun _ : Fin 1 => (1 / 2 : ℝ)) :=
  affineRationalCenterExactClosedBallCertificate.fixedPoint_unique
    affineRationalCenterExactClosedBallCertificate.fixedPoint_isFixed
    center_fixedPoint

end NonzeroAffineExample

namespace ZeroLinearExample



noncomputable def matrix : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 0


def intervals : RatInterval.IntervalMatrix 1 1 :=
  fun _ _ => RatInterval.point 0


noncomputable def offset : Fin 1 → ℝ :=
  fun _ => 0


def offsetIntervals : RatInterval.IntervalVector 1 :=
  fun _ => RatInterval.point 0


def offsetQ : Fin 1 → ℚ :=
  fun _ => 0


theorem matrix_mem_intervals : RatInterval.MatrixMem matrix intervals := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [matrix, intervals, RatInterval.point, RatInterval.MemR]


theorem offset_mem_intervals : RatInterval.VectorMem offset offsetIntervals := by
  intro i
  fin_cases i
  norm_num [offset, offsetIntervals, RatInterval.point, RatInterval.MemR]


def rowSumContraction : RatInterval.RowSumContraction intervals where
  c := 0
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i
    norm_num [RatInterval.MatrixAbsRowSum, intervals, RatInterval.point,
      RatInterval.absUpper]



def columnSumContraction : RatInterval.ColumnSumContraction intervals where
  c := 0
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  col_bound := by
    intro j
    fin_cases j
    norm_num [RatInterval.MatrixAbsColSum, intervals, RatInterval.point,
      RatInterval.absUpper]


def residualIntervals : RatInterval.IntervalVector 1 :=
  fun _ => RatInterval.point 0



theorem residual_mem :
    RatInterval.VectorMem
      (fun i => RatInterval.matVec matrix (0 : Fin 1 → ℝ) i -
        (0 : Fin 1 → ℝ) i)
      residualIntervals := by
  intro i
  fin_cases i
  norm_num [matrix, residualIntervals, RatInterval.matVec, RatInterval.point,
    RatInterval.MemR]



noncomputable def closedBallCertificate {radius : ℝ} (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec matrix x i) :=
  closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    rowSumContraction matrix_mem_intervals (0 : Fin 1 → ℝ)
    (by norm_num [rowSumContraction]) hradius residual_mem (by
      simpa [RatInterval.VectorAbsSum, residualIntervals, RatInterval.point,
        RatInterval.absUpper, rowSumContraction] using hradius)



def centerQ : Fin 1 → ℚ :=
  fun _ => 0




noncomputable def rationalCenterClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec matrix x i) :=
  closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter
    columnSumContraction matrix_mem_intervals centerQ hradius (by
      simpa [RatInterval.VectorAbsSum, RatInterval.matrixVectorResidual,
        RatInterval.matrixVectorMul, RatInterval.pointVector, RatInterval.finsetSum,
        RatInterval.vectorSub, RatInterval.sub, RatInterval.add, RatInterval.neg,
        RatInterval.mul, RatInterval.point, RatInterval.absUpper, centerQ,
        columnSumContraction] using hradius)



noncomputable def affineRationalCenterClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter
    columnSumContraction matrix_mem_intervals offset_mem_intervals centerQ
    hradius (by
      simpa [RatInterval.VectorAbsSum, RatInterval.matrixVectorAffineResidual,
        RatInterval.matrixVectorAffine, RatInterval.matrixVectorMul,
        RatInterval.pointVector, RatInterval.finsetSum, RatInterval.vectorSub,
        RatInterval.vectorAdd, RatInterval.sub, RatInterval.add,
        RatInterval.neg, RatInterval.mul, RatInterval.point,
        RatInterval.absUpper, centerQ, offsetIntervals, columnSumContraction]
        using hradius)



theorem mapsClosedBall {radius : ℝ} (hradius : 0 ≤ radius) :
    MapsClosedBall (fun x i => RatInterval.matVec matrix x i) (0 : Fin 1 → ℝ)
      radius :=
  (closedBallCertificate hradius).mapsClosedBall



theorem mapsClosedBall_from_rationalCenter {radius : ℝ} (hradius : 0 ≤ radius) :
    MapsClosedBall (fun x i => RatInterval.matVec matrix x i)
      (fun _ : Fin 1 => (0 : ℝ)) radius :=
  by
    simpa [rationalCenterClosedBallCertificate,
      closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction, centerQ] using
      (rationalCenterClosedBallCertificate hradius).mapsClosedBall



theorem mapsClosedBall_from_affineRationalCenter {radius : ℝ}
    (hradius : 0 ≤ radius) :
    MapsClosedBall (fun x i => RatInterval.affineMap matrix offset x i)
      (fun _ : Fin 1 => (0 : ℝ)) radius :=
  by
    simpa [affineRationalCenterClosedBallCertificate,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter,
      closedBallContractionCertificate_of_columnSumContraction_affine_and_residualVector,
      closedBallContractionCertificate_of_columnSumContraction_affine, centerQ,
      offset] using
      (affineRationalCenterClosedBallCertificate hradius).mapsClosedBall

end ZeroLinearExample

end FiniteContraction

end Exact3D
end StatMech
