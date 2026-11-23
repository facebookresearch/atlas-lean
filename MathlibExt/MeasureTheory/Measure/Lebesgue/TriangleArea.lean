/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Areas of triangles in the Euclidean plane

This file proves the determinant formula for the area of a planar triangle and computes the
volume of the closed unit square.
-/

@[expose] public section

namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

private lemma mem_standardTriangle_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ convexHull ℝ
        ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} : Set (EuclideanSpace ℝ (Fin 2))) ↔
      0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 ∧
        0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 1 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 0 +
            ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1 := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) :=
    {y | 0 ≤ ((euclideanPlaneBasis).toBasis.repr y) 0 ∧
      0 ≤ ((euclideanPlaneBasis).toBasis.repr y) 1 ∧
      ((euclideanPlaneBasis).toBasis.repr y) 0 +
        ((euclideanPlaneBasis).toBasis.repr y) 1 ≤ 1}
  have hconv : Convex ℝ S := by
    rw [convex_iff_add_mem]
    rintro y ⟨hy0, hy1, hys⟩ z ⟨hz0, hz1, hzs⟩ a b ha hb hab
    simp only [S, Set.mem_ofPred_eq, map_add, map_smul, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · positivity
    constructor
    · positivity
    · nlinarith
  constructor
  · intro hx
    change x ∈ S
    exact (convexHull_min (s :=
      ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} : Set (EuclideanSpace ℝ (Fin 2))))
      (t := S) (by rintro y (rfl | rfl | rfl) <;> simp [S]) hconv) hx
  · rintro ⟨hx0, hx1, hxsum⟩
    let r := ((euclideanPlaneBasis).toBasis.repr x) 0
    let s := ((euclideanPlaneBasis).toBasis.repr x) 1
    change 0 ≤ r at hx0
    change 0 ≤ s at hx1
    change r + s ≤ 1 at hxsum
    let w : Fin 3 → ℝ := ![1 - r - s, r, s]
    let z : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![0, euclideanPlaneBasis 0, euclideanPlaneBasis 1]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> simp [w] <;> linarith
    · simp [w, Fin.sum_univ_three]
      ring
    · intro i
      fin_cases i <;> simp [z]
    · have hrepr := (euclideanPlaneBasis).toBasis.sum_repr x
      rw [Fin.sum_univ_two] at hrepr
      simpa [w, z, r, s, Fin.sum_univ_three] using hrepr

private def standardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} : Set (EuclideanSpace ℝ (Fin 2)))

private noncomputable def reflect (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  euclideanPlaneBasis 0 + euclideanPlaneBasis 1 - x

private lemma repr_reflect (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    ((euclideanPlaneBasis).toBasis.repr (reflect x)) i =
      1 - ((euclideanPlaneBasis).toBasis.repr x) i := by
  fin_cases i <;> simp [reflect]

@[simp] private lemma reflect_reflect (x : EuclideanSpace ℝ (Fin 2)) :
    reflect (reflect x) = x := by
  simp [reflect]

private lemma mem_reflect_image_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ reflect '' standardTriangle ↔
      reflect x ∈ standardTriangle := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨reflect x, hx, reflect_reflect x⟩

private lemma mem_reflectedTriangle_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ reflect '' standardTriangle ↔
      ((euclideanPlaneBasis).toBasis.repr x) 0 ≤ 1 ∧
        ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1 ∧
          1 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 +
            ((euclideanPlaneBasis).toBasis.repr x) 1 := by
  rw [mem_reflect_image_iff, standardTriangle,
    mem_standardTriangle_iff, repr_reflect, repr_reflect]
  constructor <;> rintro ⟨h0, h1, hsum⟩ <;> constructor
  · linarith
  · constructor <;> linarith
  · linarith
  · constructor <;> linarith

private lemma parallelepiped_eq_union :
    parallelepiped euclideanPlaneBasis =
      standardTriangle ∪ reflect '' standardTriangle := by
  rw [show parallelepiped euclideanPlaneBasis =
      parallelepiped (euclideanPlaneBasis).toBasis from rfl,
    parallelepiped_basis_eq]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro hx
    have hx0 := hx 0
    have hx1 := hx 1
    rcases le_total (((euclideanPlaneBasis).toBasis.repr x) 0 +
      ((euclideanPlaneBasis).toBasis.repr x) 1) 1 with hsum | hsum
    · left
      rw [standardTriangle, mem_standardTriangle_iff]
      exact ⟨hx0.1, hx1.1, hsum⟩
    · right
      exact (mem_reflectedTriangle_iff x).2 ⟨hx0.2, hx1.2, hsum⟩
  · rintro (hx | hx) i
    · rw [standardTriangle, mem_standardTriangle_iff] at hx
      fin_cases i
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 0 ≤ 1
        exact ⟨hx.1, by linarith [hx.2.2]⟩
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 1 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1
        exact ⟨hx.2.1, by linarith [hx.2.2]⟩
    · rw [mem_reflectedTriangle_iff] at hx
      fin_cases i
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 0 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 0 ≤ 1
        exact ⟨by linarith [hx.2.2], hx.1⟩
      · change 0 ≤ ((euclideanPlaneBasis).toBasis.repr x) 1 ∧
          ((euclideanPlaneBasis).toBasis.repr x) 1 ≤ 1
        exact ⟨by linarith [hx.2.2], hx.2.1⟩

private noncomputable def diagonal :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  AffineSubspace.mk' (euclideanPlaneBasis 0)
    (LinearMap.ker (euclideanPlaneBasis).toBasis.sumCoords)

private lemma mem_diagonal_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ diagonal ↔
      ((euclideanPlaneBasis).toBasis.repr x) 0 +
        ((euclideanPlaneBasis).toBasis.repr x) 1 = 1 := by
  rw [diagonal, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub,
    map_sub, sub_eq_zero]
  change (euclideanPlaneBasis).toBasis.sumCoords x =
      (euclideanPlaneBasis).toBasis.sumCoords ((euclideanPlaneBasis).toBasis 0) ↔ _
  rw [Module.Basis.sumCoords_self_apply]
  classical
  change (((euclideanPlaneBasis).toBasis.repr x).sum fun _ ↦ id) = 1 ↔ _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

private lemma diagonal_ne_top : diagonal ≠ ⊤ := by
  intro htop
  have hz : (0 : EuclideanSpace ℝ (Fin 2)) ∈ diagonal := by
    rw [htop]
    trivial
  rw [mem_diagonal_iff] at hz
  simp at hz

private lemma triangle_inter_reflect_subset_diagonal :
    standardTriangle ∩ reflect '' standardTriangle ⊆ diagonal := by
  rintro x ⟨hx, hrx⟩
  rw [standardTriangle, mem_standardTriangle_iff] at hx
  rw [mem_reflectedTriangle_iff] at hrx
  exact (mem_diagonal_iff x).2 (le_antisymm hx.2.2 hrx.2.2)

private lemma volume_triangle_inter_reflect :
    volume (standardTriangle ∩ reflect '' standardTriangle) = 0 := by
  exact measure_mono_null triangle_inter_reflect_subset_diagonal
    (volume.addHaar_affineSubspace diagonal diagonal_ne_top)

private lemma standardTriangle_isCompact : IsCompact standardTriangle := by
  rw [standardTriangle]
  exact (by simp : Set.Finite
    ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} :
      Set (EuclideanSpace ℝ (Fin 2)))).isCompact_convexHull ℝ

private lemma standardTriangle_measurableSet : MeasurableSet standardTriangle :=
  standardTriangle_isCompact.isClosed.measurableSet

private lemma measurePreserving_reflect :
    MeasurePreserving reflect volume volume := by
  change MeasurePreserving
    ((fun x : EuclideanSpace ℝ (Fin 2) ↦ euclideanPlaneBasis 0 + euclideanPlaneBasis 1 + x) ∘
      fun x ↦ -x) volume volume
  exact (measurePreserving_add_left volume (euclideanPlaneBasis 0 + euclideanPlaneBasis 1)).comp
    (LinearIsometryEquiv.neg ℝ).measurePreserving

private lemma reflect_image_eq_preimage :
    reflect '' standardTriangle = reflect ⁻¹' standardTriangle := by
  ext x
  exact mem_reflect_image_iff x

private lemma reflectedTriangle_measurableSet :
    MeasurableSet (reflect '' standardTriangle) := by
  rw [reflect_image_eq_preimage]
  exact standardTriangle_measurableSet.preimage measurePreserving_reflect.measurable

private lemma volume_reflectedTriangle :
    volume (reflect '' standardTriangle) = volume standardTriangle := by
  rw [reflect_image_eq_preimage]
  exact measurePreserving_reflect.measure_preimage
    standardTriangle_measurableSet.nullMeasurableSet

private lemma two_volume_standardTriangle :
    volume standardTriangle + volume standardTriangle = 1 := by
  calc
    volume standardTriangle + volume standardTriangle =
        volume standardTriangle +
          volume (reflect '' standardTriangle) := by
      rw [volume_reflectedTriangle]
    _ = volume (standardTriangle ∪ reflect '' standardTriangle) := by
      have hunion := measure_union_add_inter (μ := volume) standardTriangle
        reflectedTriangle_measurableSet
      rw [volume_triangle_inter_reflect, add_zero] at hunion
      exact hunion.symm
    _ = volume (parallelepiped euclideanPlaneBasis) := by
      rw [parallelepiped_eq_union]
    _ = 1 := (euclideanPlaneBasis).volume_parallelepiped

private lemma toReal_volume_standardTriangle :
    (volume standardTriangle).toReal = 1 / 2 := by
  have hfinite : volume standardTriangle ≠ ⊤ :=
    ne_of_lt standardTriangle_isCompact.measure_lt_top
  have hre := congrArg ENNReal.toReal two_volume_standardTriangle
  rw [ENNReal.toReal_add hfinite hfinite] at hre
  norm_num at hre ⊢
  linarith

private lemma det_constr (u v : EuclideanSpace ℝ (Fin 2)) :
    ((euclideanPlaneBasis).toBasis.constr ℝ
      (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2))).det =
      u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 := by
  rw [← LinearMap.det_toMatrix (euclideanPlaneBasis).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]
  ring

private lemma image_standardTriangle (u v : EuclideanSpace ℝ (Fin 2)) :
    ((euclideanPlaneBasis).toBasis.constr ℝ
      (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2))) '' standardTriangle =
      convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [standardTriangle, LinearMap.image_convexHull]
  congr 1
  simp

private lemma translate_triangle (a b c : EuclideanSpace ℝ (Fin 2)) :
    (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 2)) a).toAffineMap ''
        convexHull ℝ ({0, b - a, c - a} : Set (EuclideanSpace ℝ (Fin 2))) =
      convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [AffineMap.image_convexHull]
  congr 1
  simp [AffineEquiv.constVAdd_apply]

private lemma volume_translate (a : EuclideanSpace ℝ (Fin 2))
    (s : Set (EuclideanSpace ℝ (Fin 2))) (hs : NullMeasurableSet s volume) :
    volume ((fun x ↦ a + x) '' s) = volume s := by
  have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) ↦ -a + x)
      volume volume := measurePreserving_add_left volume (-a)
  have hset : (fun x : EuclideanSpace ℝ (Fin 2) ↦ -a + x) ⁻¹' s =
      (fun x ↦ a + x) '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨-a + x, hx, by abel_nf⟩
    · rintro ⟨y, hy, rfl⟩
      change -a + (a + y) ∈ s
      simpa only [neg_add_cancel_left] using hy
  have hpre := hmp.measure_preimage hs
  rwa [hset] at hpre

private lemma volume_triangle (a b c : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal |(b - a).ofLp 0 * (c - a).ofLp 1 -
        (b - a).ofLp 1 * (c - a).ofLp 0| * volume standardTriangle := by
  let u := b - a
  let v := c - a
  let f := (euclideanPlaneBasis).toBasis.constr ℝ
    (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2))
  have hcompact : IsCompact
      (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) :=
    (by simp : Set.Finite
      ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))).isCompact_convexHull ℝ
  have hmeas : NullMeasurableSet
      (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) volume :=
    hcompact.isClosed.measurableSet.nullMeasurableSet
  calc
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
        volume ((fun x ↦ a + x) ''
          convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) := by
      rw [show u = b - a from rfl, show v = c - a from rfl,
        ← translate_triangle a b c]
      rfl
    _ = volume (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) :=
      volume_translate a _ hmeas
    _ = volume (f '' standardTriangle) := by
      simp only [f, image_standardTriangle]
    _ = ENNReal.ofReal |f.det| * volume standardTriangle := by
      rw [Measure.addHaar_image_linearMap]
    _ = _ := by
      simp only [f, det_constr, u, v]

/-- **Determinant formula for the area of a triangle.** Write $x = (x_1, x_2)$ for the
coordinates of a point $x$ of the Euclidean plane $\mathbb{R}^2$. For all points $a, b, c$ in
$\mathbb{R}^2$, the Lebesgue measure (area) of the convex hull of $\{a, b, c\}$, as a real
number, equals $\frac{1}{2}\,\lvert (b_1 - a_1)(c_2 - a_2) - (b_2 - a_2)(c_1 - a_1) \rvert$. -/
theorem _root_.MeasureTheory.toReal_volume_convexHull_triangle
    (a b c : EuclideanSpace ℝ (Fin 2)) :
    (volume (convexHull ℝ
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
      |(b - a).ofLp 0 * (c - a).ofLp 1 - (b - a).ofLp 1 * (c - a).ofLp 0| / 2 := by
  rw [volume_triangle, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), toReal_volume_standardTriangle]
  ring

private lemma unitSquare_eq_parallelepiped :
    {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} =
      parallelepiped euclideanPlaneBasis := by
  rw [show parallelepiped euclideanPlaneBasis =
      parallelepiped (euclideanPlaneBasis).toBasis from rfl,
    parallelepiped_basis_eq]
  ext x
  simp

/-- **Area of the unit square.** The closed unit square
$\{x \in \mathbb{R}^2 : 0 \le x_1 \le 1 \text{ and } 0 \le x_2 \le 1\}$ in the Euclidean plane has
Lebesgue measure (area) $1$. -/
theorem _root_.MeasureTheory.volume_unitSquare :
    volume {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} = 1 := by
  rw [unitSquare_eq_parallelepiped]
  exact (euclideanPlaneBasis).volume_parallelepiped

end MetaMathlibExt
