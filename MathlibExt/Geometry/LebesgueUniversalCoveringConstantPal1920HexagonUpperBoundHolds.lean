/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Isometry
public import MathlibExt.Geometry.LebesgueUniversalCoveringJung
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import MathlibExt.MeasureTheory.Measure.Lebesgue.TriangleArea

/-!
# Pál's hexagon upper bound for Lebesgue's universal covering constant

Pál's regular hexagon, the intersection of three strips of width $1$ whose normals are $120°$
apart, is a universal convex cover of area $\sqrt{3}/2$: every nonempty compact convex planar
set of diameter $1$ fits into it after a suitable rotation and translation. The statement is
`pal1920HexagonUpperBound`, proved in `pal1920HexagonUpperBound_holds`.

## References

* Julius Pál, *Über ein elementares Variationsproblem*, Danske Vid. Selsk. Math.-Fys. Medd. 3
  (1920), no. 2: hexagon bound.
-/

open MeasureTheory

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

@[expose] public noncomputable section

/-- **Statement of Pál's hexagon bound.** The proposition that the Lebesgue universal covering
constant is at most $\sqrt{3}/2$, the bound given by Pál's regular hexagon. -/
def pal1920HexagonUpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.sqrt 3 / 2)

/-- The first standard basis vector of the plane. -/
private def e0 : Plane := WithLp.toLp 2 ![1, 0]

/-- The second standard basis vector of the plane. -/
private def e1 : Plane := WithLp.toLp 2 ![0, 1]

/-- First hexagon normal: the unit vector along the $x$-axis. -/
private def hu0 : Plane := WithLp.toLp 2 ![1, 0]

/-- Second hexagon normal: the unit vector at $120°$. -/
private def hu1 : Plane := WithLp.toLp 2 ![-1/2, Real.sqrt 3 / 2]

/-- Third hexagon normal: the unit vector at $240°$. -/
private def hu2 : Plane := WithLp.toLp 2 ![-1/2, -Real.sqrt 3 / 2]

/-- The inner product with `hu0` is the first coordinate. -/
private lemma hu0_inner (x : Plane) : inner ℝ hu0 x = x.ofLp 0 := by
  simp only [hu0, PiLp.inner_apply]
  simp [Fin.sum_univ_two]

/-- The inner product with `hu1`, in coordinates. -/
private lemma hu1_inner (x : Plane) :
    inner ℝ hu1 x = -1/2 * x.ofLp 0 + Real.sqrt 3 / 2 * x.ofLp 1 := by
  simp only [hu1, PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  ring

/-- The inner product with `hu2`, in coordinates. -/
private lemma hu2_inner (x : Plane) :
    inner ℝ hu2 x = -1/2 * x.ofLp 0 - Real.sqrt 3 / 2 * x.ofLp 1 := by
  simp only [hu2, PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  ring

/-- Pál's hexagon: the intersection of three strips of width $1$. -/
private def palHex : Set Plane :=
  {x | |inner ℝ hu0 x| ≤ 1/2 ∧ |inner ℝ hu1 x| ≤ 1/2 ∧ |inner ℝ hu2 x| ≤ 1/2}

/-- Pál's hexagon is nonempty. -/
private lemma palHex_nonempty : palHex.Nonempty := by
  exact ⟨0, by simp [palHex]⟩

/-- Pál's hexagon is convex. -/
private lemma palHex_convex : Convex ℝ palHex := by
  have hIcc : Convex ℝ (Set.Icc (-1/2 : ℝ) (1/2)) := convex_Icc _ _
  have h0 : Convex ℝ {x : Plane | |inner ℝ hu0 x| ≤ 1/2} := by
    have hpre := hIcc.linear_preimage (innerₛₗ ℝ hu0)
    have heq : (innerₛₗ ℝ hu0) ⁻¹' Set.Icc (-1/2 : ℝ) (1/2) =
        {x : Plane | |inner ℝ hu0 x| ≤ 1/2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc, abs_le]
      norm_num [one_div]
    rw [heq] at hpre
    exact hpre
  have h1 : Convex ℝ {x : Plane | |inner ℝ hu1 x| ≤ 1/2} := by
    have hpre := hIcc.linear_preimage (innerₛₗ ℝ hu1)
    have heq : (innerₛₗ ℝ hu1) ⁻¹' Set.Icc (-1/2 : ℝ) (1/2) =
        {x : Plane | |inner ℝ hu1 x| ≤ 1/2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc, abs_le]
      norm_num [one_div]
    rw [heq] at hpre
    exact hpre
  have h2 : Convex ℝ {x : Plane | |inner ℝ hu2 x| ≤ 1/2} := by
    have hpre := hIcc.linear_preimage (innerₛₗ ℝ hu2)
    have heq : (innerₛₗ ℝ hu2) ⁻¹' Set.Icc (-1/2 : ℝ) (1/2) =
        {x : Plane | |inner ℝ hu2 x| ≤ 1/2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc, abs_le]
      norm_num [one_div]
    rw [heq] at hpre
    exact hpre
  have hinter : palHex = {x : Plane | |inner ℝ hu0 x| ≤ 1/2} ∩
      {x : Plane | |inner ℝ hu1 x| ≤ 1/2} ∩ {x : Plane | |inner ℝ hu2 x| ≤ 1/2} := by
    ext x
    simp [palHex]
    tauto
  rw [hinter]
  exact (h0.inter h1).inter h2

-- Constants for area covering.

/-- The constant $\sqrt{3}/6$, the inner half-height of the triangulation. -/
private def c1 : ℝ := Real.sqrt 3 / 6

/-- The constant $\sqrt{3}/3$, the outer half-height of the triangulation. -/
private def c2 : ℝ := Real.sqrt 3 / 3

/-- `c1` is positive. -/
private lemma c1_pos : 0 < c1 := by
  simp only [c1]
  positivity

/-- `c2` is twice `c1`. -/
private lemma c2_eq_two_c1 : c2 = 2 * c1 := by
  simp [c1, c2]
  ring

/-- The plane point with the given coordinates. -/
private def pt (a b : ℝ) : Plane := WithLp.toLp 2 ![a, b]

/-- First coordinate of `pt`. -/
private lemma pt_ofLp0 (a b : ℝ) : (pt a b).ofLp 0 = a := by simp [pt]

/-- Second coordinate of `pt`. -/
private lemma pt_ofLp1 (a b : ℝ) : (pt a b).ofLp 1 = b := by simp [pt]

-- Coordinate bounds from hexagon membership.

/-- Coordinate bounds for points of the hexagon. -/
private lemma palHex_bounds (x : Plane) (hx : x ∈ palHex) :
    |x.ofLp 0| ≤ 1/2 ∧ |-x.ofLp 0 + Real.sqrt 3 * x.ofLp 1| ≤ 1 ∧
    |-x.ofLp 0 - Real.sqrt 3 * x.ofLp 1| ≤ 1 := by
  simp only [palHex, Set.mem_ofPred_eq] at hx
  obtain ⟨h0, h1, h2⟩ := hx
  rw [hu0_inner] at h0
  rw [hu1_inner] at h1
  rw [hu2_inner] at h2
  refine ⟨h0, ?_, ?_⟩
  · have heq : -x.ofLp 0 + Real.sqrt 3 * x.ofLp 1 =
        2 * (-1/2 * x.ofLp 0 + Real.sqrt 3 / 2 * x.ofLp 1) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [h1]
  · have heq : -x.ofLp 0 - Real.sqrt 3 * x.ofLp 1 =
        2 * (-1/2 * x.ofLp 0 - Real.sqrt 3 / 2 * x.ofLp 1) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [h2]

/-- $\sqrt{3} \cdot \sqrt{3} = 3$. -/
private lemma sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

-- Four covering triangles.

/-- First covering triangle: the lower-left half of the middle strip. -/
private def tri1 : Set Plane :=
  convexHull ℝ ({pt (-1/2) (-c1), pt (1/2) (-c1), pt (1/2) c1} : Set Plane)

/-- Second covering triangle: the upper-right half of the middle strip. -/
private def tri2 : Set Plane :=
  convexHull ℝ ({pt (-1/2) (-c1), pt (1/2) c1, pt (-1/2) c1} : Set Plane)

/-- Top covering triangle. -/
private def triTop : Set Plane :=
  convexHull ℝ ({pt (-1/2) c1, pt (1/2) c1, pt 0 c2} : Set Plane)

/-- Bottom covering triangle. -/
private def triBot : Set Plane :=
  convexHull ℝ ({pt (-1/2) (-c1), pt (1/2) (-c1), pt 0 (-c2)} : Set Plane)

/-- Membership criterion for the first covering triangle. -/
private lemma mem_tri1 (x : Plane) (hX : |x.ofLp 0| ≤ 1 / 2)
    (hS : |Real.sqrt 3 * x.ofLp 1| ≤ 1 / 2)
    (hdiag : Real.sqrt 3 * x.ofLp 1 ≤ x.ofLp 0) : x ∈ tri1 := by
  have hXlo := (abs_le.mp hX).1
  have hXhi := (abs_le.mp hX).2
  have hSlo := (abs_le.mp hS).1
  have hShi := (abs_le.mp hS).2
  set X := x.ofLp 0 with hXdef
  set Y := x.ofLp 1 with hYdef
  set S := Real.sqrt 3 * Y with hSdef
  have hw1nn : 0 ≤ (1 - 2 * X) / 2 := by linarith [hXhi]
  have hw2nn : 0 ≤ X - S := by linarith [hdiag]
  have hw3nn : 0 ≤ 1/2 + S := by linarith [hSlo]
  have hsum : (1 - 2 * X) / 2 + (X - S) + (1/2 + S) = 1 := by ring
  let w : Fin 3 → ℝ := ![((1 - 2 * X) / 2), (X - S), (1/2 + S)]
  let z : Fin 3 → Plane := ![pt (-1/2) (-c1), pt (1/2) (-c1), pt (1/2) c1]
  have hwsum : ∑ i, w i • z i = x := by
    rw [Fin.sum_univ_three]
    simp only [w, z, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp0]
      ring
    · have hfactor : (-c1) * ((1 - 2 * X) / 2) + (-c1) * (X - S) + c1 * (1/2 + S) =
          c1 * (2 * S) := by ring
      have hcs : c1 * (2 * S) = Y := by
        simp only [c1, hSdef, hYdef]
        have hmul := sqrt3_mul_self
        calc (Real.sqrt 3 / 6) * (2 * (Real.sqrt 3 * x.ofLp 1))
            = (Real.sqrt 3 * Real.sqrt 3) * x.ofLp 1 / 3 := by ring
          _ = x.ofLp 1 := by rw [hmul]; ring
      have key : (1 - 2 * X) / 2 * -c1 + (X - S) * -c1 + (1/2 + S) * c1 = x.ofLp 1 := by
        linarith [hfactor, hcs]
      simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp1] using key
  unfold tri1
  refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ hwsum
  · intro i
    fin_cases i <;> simp [w] <;> linarith [hw1nn, hw2nn, hw3nn]
  · simp [w, Fin.sum_univ_three]
    linarith [hsum]
  · intro i
    fin_cases i <;> simp [z]

/-- The identity $2 c_1 \sqrt{3} Y = Y$. -/
private lemma two_c1_mul_S (Y : ℝ) : 2 * c1 * (Real.sqrt 3 * Y) = Y := by
  simp only [c1]
  have hmul := sqrt3_mul_self
  calc 2 * (Real.sqrt 3 / 6) * (Real.sqrt 3 * Y)
      = (Real.sqrt 3 * Real.sqrt 3) * Y / 3 := by ring
    _ = Y := by rw [hmul]; ring

/-- Membership criterion for the second covering triangle. -/
private lemma mem_tri2 (x : Plane) (hX : |x.ofLp 0| ≤ 1 / 2)
    (hS : |Real.sqrt 3 * x.ofLp 1| ≤ 1 / 2)
    (hdiag : x.ofLp 0 ≤ Real.sqrt 3 * x.ofLp 1) : x ∈ tri2 := by
  have hXlo := (abs_le.mp hX).1
  have hXhi := (abs_le.mp hX).2
  have hSlo := (abs_le.mp hS).1
  have hShi := (abs_le.mp hS).2
  set X := x.ofLp 0 with hXdef
  set Y := x.ofLp 1 with hYdef
  set S := Real.sqrt 3 * Y with hSdef
  have hw1nn : 0 ≤ 1/2 - S := by linarith [hShi]
  have hw2nn : 0 ≤ X + 1/2 := by linarith [hXlo]
  have hw3nn : 0 ≤ S - X := by linarith [hdiag]
  have hsum : (1/2 - S) + (X + 1/2) + (S - X) = 1 := by ring
  let w : Fin 3 → ℝ := ![(1/2 - S), (X + 1/2), (S - X)]
  let z : Fin 3 → Plane := ![pt (-1/2) (-c1), pt (1/2) c1, pt (-1/2) c1]
  have hwsum : ∑ i, w i • z i = x := by
    rw [Fin.sum_univ_three]
    simp only [w, z, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp0]
      ring
    · have hfactor : (-c1) * (1/2 - S) + c1 * (X + 1/2) + c1 * (S - X) =
          c1 * (2 * S) := by ring
      have hcs : c1 * (2 * S) = Y := by
        have h2 := two_c1_mul_S Y
        simp only [hSdef] at h2 ⊢
        linarith [h2]
      have key : (1/2 - S) * -c1 + (X + 1/2) * c1 + (S - X) * c1 = x.ofLp 1 := by
        linarith [hfactor, hcs]
      simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp1] using key
  unfold tri2
  refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ hwsum
  · intro i
    fin_cases i <;> simp [w] <;> linarith [hw1nn, hw2nn, hw3nn]
  · simp [w, Fin.sum_univ_three]
    linarith [hsum]
  · intro i
    fin_cases i <;> simp [z]

/-- Membership criterion for the top covering triangle. -/
private lemma mem_triTop (x : Plane) (hSlo : 1 / 2 ≤ Real.sqrt 3 * x.ofLp 1)
    (_hShi : Real.sqrt 3 * x.ofLp 1 ≤ 1)
    (hX : |x.ofLp 0| ≤ 1 - Real.sqrt 3 * x.ofLp 1) : x ∈ triTop := by
  have hXpair := abs_le.mp hX
  set X := x.ofLp 0 with hXdef
  set Y := x.ofLp 1 with hYdef
  set S := Real.sqrt 3 * Y with hSdef
  have hw1nn : 0 ≤ (1 - S) - X := by
    have h1 : X ≤ 1 - S := hXpair.2
    linarith
  have hw2nn : 0 ≤ (1 - S) + X := by
    have h1 : -(1 - S) ≤ X := hXpair.1
    linarith
  have hw3nn : 0 ≤ 2 * S - 1 := by linarith [hSlo]
  have hsum : ((1 - S) - X) + ((1 - S) + X) + (2 * S - 1) = 1 := by ring
  let w : Fin 3 → ℝ := ![((1 - S) - X), ((1 - S) + X), (2 * S - 1)]
  let z : Fin 3 → Plane := ![pt (-1/2) c1, pt (1/2) c1, pt 0 c2]
  have hwsum : ∑ i, w i • z i = x := by
    rw [Fin.sum_univ_three]
    simp only [w, z, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp0]
      ring
    · have hcc : c2 = 2 * c1 := c2_eq_two_c1
      have hfactor : c1 * ((1 - S) - X) + c1 * ((1 - S) + X) + c2 * (2 * S - 1) =
          c1 * (2 * S) := by
        rw [hcc]
        ring
      have hcs : c1 * (2 * S) = Y := by
        have h2 := two_c1_mul_S Y
        simp only [hSdef] at h2 ⊢
        linarith [h2]
      have key : ((1 - S) - X) * c1 + ((1 - S) + X) * c1 + (2 * S - 1) * c2 =
          x.ofLp 1 := by
        linarith [hfactor, hcs]
      simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp1] using key
  unfold triTop
  refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ hwsum
  · intro i
    fin_cases i <;> simp [w] <;> linarith [hw1nn, hw2nn, hw3nn]
  · simp [w, Fin.sum_univ_three]
    linarith [hsum]
  · intro i
    fin_cases i <;> simp [z]

/-- Membership criterion for the bottom covering triangle. -/
private lemma mem_triBot (x : Plane) (hShi : Real.sqrt 3 * x.ofLp 1 ≤ -1 / 2)
    (_hSlo : -1 ≤ Real.sqrt 3 * x.ofLp 1)
    (hX : |x.ofLp 0| ≤ 1 + Real.sqrt 3 * x.ofLp 1) : x ∈ triBot := by
  have hXpair := abs_le.mp hX
  set X := x.ofLp 0 with hXdef
  set Y := x.ofLp 1 with hYdef
  set S := Real.sqrt 3 * Y with hSdef
  have hw1nn : 0 ≤ (1 + S) - X := by
    have h1 : X ≤ 1 + S := hXpair.2
    linarith
  have hw2nn : 0 ≤ (1 + S) + X := by
    have h1 : -(1 + S) ≤ X := hXpair.1
    linarith
  have hw3nn : 0 ≤ -2 * S - 1 := by linarith [hShi]
  have hsum : ((1 + S) - X) + ((1 + S) + X) + (-2 * S - 1) = 1 := by ring
  let w : Fin 3 → ℝ := ![((1 + S) - X), ((1 + S) + X), (-2 * S - 1)]
  let z : Fin 3 → Plane := ![pt (-1/2) (-c1), pt (1/2) (-c1), pt 0 (-c2)]
  have hwsum : ∑ i, w i • z i = x := by
    rw [Fin.sum_univ_three]
    simp only [w, z, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp0]
      ring
    · have hcc : c2 = 2 * c1 := c2_eq_two_c1
      have hfactor : (-c1) * ((1 + S) - X) + (-c1) * ((1 + S) + X) +
          (-c2) * (-2 * S - 1) = c1 * (2 * S) := by
        rw [hcc]
        ring
      have hcs : c1 * (2 * S) = Y := by
        have h2 := two_c1_mul_S Y
        simp only [hSdef] at h2 ⊢
        linarith [h2]
      have key : ((1 + S) - X) * -c1 + ((1 + S) + X) * -c1 + (-2 * S - 1) * -c2 =
          x.ofLp 1 := by
        linarith [hfactor, hcs]
      simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pt_ofLp1] using key
  unfold triBot
  refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ hwsum
  · intro i
    fin_cases i <;> simp [w] <;> linarith [hw1nn, hw2nn, hw3nn]
  · simp [w, Fin.sum_univ_three]
    linarith [hsum]
  · intro i
    fin_cases i <;> simp [z]

/-- The hexagon is covered by the four triangles. -/
private lemma palHex_subset_union : palHex ⊆ tri1 ∪ tri2 ∪ triTop ∪ triBot := by
  intro x hx
  obtain ⟨hX0, hXS1, hXS2⟩ := palHex_bounds x hx
  set X := x.ofLp 0 with hXdef
  set S := Real.sqrt 3 * x.ofLp 1 with hSdef
  have hX : |X| ≤ 1/2 := hX0
  have ha : |-X + S| ≤ 1 := hXS1
  have hb : |-X - S| ≤ 1 := hXS2
  have ha1 := (abs_le.mp ha).1
  have ha2 := (abs_le.mp ha).2
  have hb1 := (abs_le.mp hb).1
  have hb2 := (abs_le.mp hb).2
  have hSle1 : S ≤ 1 := by linarith [ha2, hb1]
  have hSge1 : -1 ≤ S := by linarith [ha1, hb2]
  have hSabs : |S| ≤ 1 := abs_le.mpr ⟨hSge1, hSle1⟩
  by_cases hTop : 1/2 < S
  · have hXtop : |X| ≤ 1 - S := by
      have h1 : X ≤ 1 - S := by linarith [hb1]
      have h2 : -(1 - S) ≤ X := by linarith [ha2]
      exact abs_le.mpr ⟨h2, h1⟩
    have hmem : x ∈ triTop := by
      apply mem_triTop x _ hSle1 hXtop
      linarith [hTop]
    simp only [Set.mem_union]
    tauto
  · by_cases hBot : S < -1/2
    · have hXbot : |X| ≤ 1 + S := by
        have h1 : X ≤ 1 + S := by linarith [ha1]
        have h2 : -(1 + S) ≤ X := by linarith [hb2]
        exact abs_le.mpr ⟨h2, h1⟩
      have hmem : x ∈ triBot := by
        apply mem_triBot x _ hSge1 hXbot
        linarith [hBot]
      simp only [Set.mem_union]
      tauto
    · have hSmid : |S| ≤ 1/2 := by
        rw [abs_le]
        constructor
        · have h2 : -1/2 ≤ S := le_of_not_gt hBot
          linarith [h2]
        · exact le_of_not_gt hTop
      have hSmid' : |Real.sqrt 3 * x.ofLp 1| ≤ 1/2 := hSmid
      have hX' : |x.ofLp 0| ≤ 1/2 := hX
      rcases le_total S X with hdiag | hdiag
      · have hmem := mem_tri1 x hX' hSmid' hdiag
        simp only [Set.mem_union]
        tauto
      · have hmem := mem_tri2 x hX' hSmid' hdiag
        simp only [Set.mem_union]
        tauto

-- Area of each covering triangle.

/-- First coordinate of a difference. -/
private lemma sub_ofLp0 (a b : Plane) : (a - b).ofLp 0 = a.ofLp 0 - b.ofLp 0 := by
  simp [sub_eq_add_neg]

/-- Second coordinate of a difference. -/
private lemma sub_ofLp1 (a b : Plane) : (a - b).ofLp 1 = a.ofLp 1 - b.ofLp 1 := by
  simp [sub_eq_add_neg]

/-- Real-valued area of the first covering triangle. -/
private lemma toReal_tri1 : (volume tri1).toReal = c1 := by
  unfold tri1
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  simp only [sub_ofLp0, sub_ofLp1, pt_ofLp0, pt_ofLp1]
  have hc1 : 0 < c1 := c1_pos
  have hdet : |(1/2 - -1/2) * (c1 - -c1) - (-c1 - -c1) * (1/2 - -1/2)| / 2 = c1 := by
    have h1 : (1/2 : ℝ) - -1/2 = 1 := by ring
    have h2 : c1 - -c1 = 2 * c1 := by ring
    have h3 : (-c1 : ℝ) - -c1 = 0 := by ring
    rw [h1, h2, h3]
    simp only [zero_mul, sub_zero]
    rw [abs_of_pos (by linarith [hc1] : (0:ℝ) < 1 * (2 * c1))]
    ring
  exact hdet

/-- Real-valued area of the second covering triangle. -/
private lemma toReal_tri2 : (volume tri2).toReal = c1 := by
  unfold tri2
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  simp only [sub_ofLp0, sub_ofLp1, pt_ofLp0, pt_ofLp1]
  have hc1 : 0 < c1 := c1_pos
  have hdet : |(1/2 - -1/2) * (c1 - -c1) - (c1 - -c1) * (-1/2 - -1/2)| / 2 = c1 := by
    have h1 : (1/2 : ℝ) - -1/2 = 1 := by ring
    have h2 : c1 - -c1 = 2 * c1 := by ring
    have h3 : (-1/2 : ℝ) - -1/2 = 0 := by ring
    rw [h1, h2, h3]
    simp only [mul_zero, sub_zero]
    rw [abs_of_pos (by linarith [hc1] : (0:ℝ) < 1 * (2 * c1))]
    ring
  exact hdet

/-- Real-valued area of the top covering triangle. -/
private lemma toReal_triTop : (volume triTop).toReal = c1 / 2 := by
  unfold triTop
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  simp only [sub_ofLp0, sub_ofLp1, pt_ofLp0, pt_ofLp1]
  have hc1 : 0 < c1 := c1_pos
  have hcc : c2 - c1 = c1 := by
    have h := c2_eq_two_c1
    linarith [h]
  have hdet : |(1/2 - -1/2) * (c2 - c1) - (c1 - c1) * (0 - -1/2)| / 2 = c1 / 2 := by
    have h1 : (1/2 : ℝ) - -1/2 = 1 := by ring
    have h3 : (c1 : ℝ) - c1 = 0 := by ring
    rw [h1, hcc, h3]
    simp only [zero_mul, sub_zero]
    rw [abs_of_pos (by linarith [hc1] : (0:ℝ) < 1 * c1)]
    ring
  exact hdet

/-- Real-valued area of the bottom covering triangle. -/
private lemma toReal_triBot : (volume triBot).toReal = c1 / 2 := by
  unfold triBot
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  simp only [sub_ofLp0, sub_ofLp1, pt_ofLp0, pt_ofLp1]
  have hc1 : 0 < c1 := c1_pos
  have hcc : -c2 - -c1 = -c1 := by
    have h := c2_eq_two_c1
    linarith [h]
  have hdet : |(1/2 - -1/2) * (-c2 - -c1) - (-c1 - -c1) * (0 - -1/2)| / 2 = c1 / 2 := by
    have h1 : (1/2 : ℝ) - -1/2 = 1 := by ring
    have h3 : (-c1 : ℝ) - -c1 = 0 := by ring
    rw [h1, hcc, h3]
    simp only [zero_mul, sub_zero]
    rw [abs_of_neg (by linarith [hc1] : (1:ℝ) * -c1 < 0)]
    ring
  exact hdet

/-- Area of the first covering triangle. -/
private lemma vol_tri1 : volume tri1 = ENNReal.ofReal c1 := by
  have hcompact : IsCompact tri1 := by
    unfold tri1
    exact (by simp : Set.Finite
      ({pt (-1/2) (-c1), pt (1/2) (-c1), pt (1/2) c1} : Set Plane)).isCompact_convexHull ℝ
  have hne : volume tri1 ≠ ⊤ := ne_of_lt hcompact.measure_lt_top
  have h := ENNReal.ofReal_toReal hne
  rw [toReal_tri1] at h
  exact h.symm

/-- Area of the second covering triangle. -/
private lemma vol_tri2 : volume tri2 = ENNReal.ofReal c1 := by
  have hcompact : IsCompact tri2 := by
    unfold tri2
    exact (by simp : Set.Finite
      ({pt (-1/2) (-c1), pt (1/2) c1, pt (-1/2) c1} : Set Plane)).isCompact_convexHull ℝ
  have hne : volume tri2 ≠ ⊤ := ne_of_lt hcompact.measure_lt_top
  have h := ENNReal.ofReal_toReal hne
  rw [toReal_tri2] at h
  exact h.symm

/-- Area of the top covering triangle. -/
private lemma vol_triTop : volume triTop = ENNReal.ofReal (c1 / 2) := by
  have hcompact : IsCompact triTop := by
    unfold triTop
    exact (by simp : Set.Finite
      ({pt (-1/2) c1, pt (1/2) c1, pt 0 c2} : Set Plane)).isCompact_convexHull ℝ
  have hne : volume triTop ≠ ⊤ := ne_of_lt hcompact.measure_lt_top
  have h := ENNReal.ofReal_toReal hne
  rw [toReal_triTop] at h
  exact h.symm

/-- Area of the bottom covering triangle. -/
private lemma vol_triBot : volume triBot = ENNReal.ofReal (c1 / 2) := by
  have hcompact : IsCompact triBot := by
    unfold triBot
    exact (by simp : Set.Finite
      ({pt (-1/2) (-c1), pt (1/2) (-c1), pt 0 (-c2)} : Set Plane)).isCompact_convexHull ℝ
  have hne : volume triBot ≠ ⊤ := ne_of_lt hcompact.measure_lt_top
  have h := ENNReal.ofReal_toReal hne
  rw [toReal_triBot] at h
  exact h.symm

/-- The hexagon has area at most $\sqrt{3}/2$. -/
private lemma palHex_area_le : planarArea palHex ≤ ENNReal.ofReal (Real.sqrt 3 / 2) := by
  have hmono : volume palHex ≤ volume (tri1 ∪ tri2 ∪ triTop ∪ triBot) :=
    measure_mono palHex_subset_union
  have h12 : volume (tri1 ∪ tri2) ≤ volume tri1 + volume tri2 :=
    measure_union_le tri1 tri2
  have h123 : volume (tri1 ∪ tri2 ∪ triTop) ≤ volume (tri1 ∪ tri2) + volume triTop :=
    measure_union_le _ _
  have h1234 : volume (tri1 ∪ tri2 ∪ triTop ∪ triBot) ≤
      volume (tri1 ∪ tri2 ∪ triTop) + volume triBot :=
    measure_union_le _ _
  have hle : volume (tri1 ∪ tri2 ∪ triTop ∪ triBot) ≤
      volume tri1 + volume tri2 + volume triTop + volume triBot := by
    calc volume (tri1 ∪ tri2 ∪ triTop ∪ triBot)
        ≤ volume (tri1 ∪ tri2 ∪ triTop) + volume triBot := h1234
      _ ≤ (volume (tri1 ∪ tri2) + volume triTop) + volume triBot :=
        add_le_add_left h123 (volume triBot)
      _ ≤ ((volume tri1 + volume tri2) + volume triTop) + volume triBot :=
        add_le_add_left (add_le_add_left h12 (volume triTop)) (volume triBot)
      _ = volume tri1 + volume tri2 + volume triTop + volume triBot := by
        ac_rfl
  have hsum : volume tri1 + volume tri2 + volume triTop + volume triBot =
      ENNReal.ofReal (Real.sqrt 3 / 2) := by
    rw [vol_tri1, vol_tri2, vol_triTop, vol_triBot]
    have hc1nn : 0 ≤ c1 := le_of_lt c1_pos
    have hc1dnn : 0 ≤ c1 / 2 := by linarith [hc1nn]
    rw [← ENNReal.ofReal_add hc1nn hc1nn,
      ← ENNReal.ofReal_add (by linarith [hc1nn] : 0 ≤ c1 + c1) hc1dnn,
      ← ENNReal.ofReal_add (by linarith [hc1nn, hc1dnn] : 0 ≤ c1 + c1 + c1 / 2) hc1dnn]
    congr 1
    simp only [c1]
    ring
  exact le_trans hmono (le_trans hle (le_of_eq hsum))

-- Direction vectors for support function.

/-- The unit vector at angle $θ$. -/
private def dirVec (θ : ℝ) : Plane := Real.cos θ • e0 + Real.sin θ • e1

/-- `e0` is a unit vector. -/
private lemma e0_inner_e0 : inner ℝ e0 e0 = 1 := by
  simp only [e0, PiLp.inner_apply]
  simp [Fin.sum_univ_two]

/-- `e1` is a unit vector. -/
private lemma e1_inner_e1 : inner ℝ e1 e1 = 1 := by
  simp only [e1, PiLp.inner_apply]
  simp [Fin.sum_univ_two]

/-- `e0` and `e1` are orthogonal. -/
private lemma e0_inner_e1 : inner ℝ e0 e1 = 0 := by
  simp only [e0, e1, PiLp.inner_apply]
  simp [Fin.sum_univ_two]

/-- `dirVec θ` is a unit vector. -/
private lemma dirVec_norm (θ : ℝ) : ‖dirVec θ‖ = 1 := by
  have h : inner ℝ (dirVec θ) (dirVec θ) = 1 := by
    simp only [dirVec, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      e0_inner_e0, e1_inner_e1, e0_inner_e1]
    have h10 : inner ℝ e1 e0 = 0 := by rw [real_inner_comm]; exact e0_inner_e1
    rw [h10]
    simp only [conj_trivial, mul_one, mul_zero, add_zero, zero_add]
    have hcos := Real.cos_sq_add_sin_sq θ
    simpa [pow_two] using hcos
  have hnorm : ‖dirVec θ‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h
  have hnn : 0 ≤ ‖dirVec θ‖ := norm_nonneg _
  calc ‖dirVec θ‖ = Real.sqrt (‖dirVec θ‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt 1 := by rw [hnorm]
    _ = 1 := Real.sqrt_one

/-- `dirVec` is continuous. -/
private lemma dirVec_continuous : Continuous dirVec := by
  unfold dirVec
  fun_prop

-- Support function for compact K.

/-- The support value of `K` in direction `u`. -/
private def supInner (K : Set Plane) (u : Plane) : ℝ :=
  sSup ((fun x : Plane => inner ℝ u x) '' K)

/-- The support value is attained on `K`. -/
private lemma supInner_mem (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (u : Plane) : ∃ x ∈ K, inner ℝ u x = supInner K u := by
  have hcont : Continuous (fun x : Plane => inner ℝ u x) :=
    (Continuous.inner continuous_const continuous_id)
  have himg : IsCompact ((fun x : Plane => inner ℝ u x) '' K) := hK.image hcont
  have hneimg : ((fun x : Plane => inner ℝ u x) '' K).Nonempty :=
    hne.image _
  have hmem := himg.sSup_mem hneimg
  simp only [supInner] at hmem ⊢
  obtain ⟨x, hxK, hxx⟩ := hmem
  exact ⟨x, hxK, hxx⟩

/-- Every point of `K` lies below the support value. -/
private lemma supInner_ge (K : Set Plane) (hK : IsCompact K) (_hne : K.Nonempty)
    (u : Plane) (x : Plane) (hx : x ∈ K) : inner ℝ u x ≤ supInner K u := by
  have hcont : Continuous (fun x : Plane => inner ℝ u x) :=
    (Continuous.inner continuous_const continuous_id)
  have himg : IsCompact ((fun x : Plane => inner ℝ u x) '' K) := hK.image hcont
  have hbdd : BddAbove ((fun x : Plane => inner ℝ u x) '' K) := himg.bddAbove
  exact le_csSup hbdd ⟨x, hx, rfl⟩

/-- `dirVec` at opposite angles. -/
private lemma dirVec_add_pi (θ : ℝ) : dirVec (θ + Real.pi) = -dirVec θ := by
  simp only [dirVec, Real.cos_add_pi, Real.sin_add_pi]
  rw [neg_add, neg_smul, neg_smul]

/-- A unit-diameter compact set has width at most $1$ in any direction. -/
private lemma width_le_one (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (hdiam : Metric.diam K = 1) (θ : ℝ) :
    supInner K (dirVec θ) + supInner K (dirVec (θ + Real.pi)) ≤ 1 := by
  obtain ⟨x1, hx1K, hx1eq⟩ := supInner_mem K hK hne (dirVec θ)
  obtain ⟨x2, hx2K, hx2eq⟩ := supInner_mem K hK hne (dirVec (θ + Real.pi))
  rw [dirVec_add_pi] at hx2eq
  have hsum : supInner K (dirVec θ) + supInner K (dirVec (θ + Real.pi)) =
      inner ℝ (dirVec θ) (x1 - x2) := by
    rw [dirVec_add_pi]
    rw [← hx1eq, ← hx2eq]
    simp only [inner_sub_right, inner_neg_left]
    ring
  rw [hsum]
  have hle : inner ℝ (dirVec θ) (x1 - x2) ≤ ‖dirVec θ‖ * ‖x1 - x2‖ :=
    real_inner_le_norm _ _
  rw [dirVec_norm] at hle
  simp only [one_mul] at hle
  have hdist : ‖x1 - x2‖ = dist x1 x2 := (dist_eq_norm x1 x2).symm
  rw [hdist] at hle
  have hbdd : Bornology.IsBounded K := hK.isBounded
  have hdd : dist x1 x2 ≤ Metric.diam K := Metric.dist_le_diam_of_mem hbdd hx1K hx2K
  rw [hdiam] at hdd
  linarith [hle, hdd]

/-- A uniform norm bound on a nonempty compact set. -/
private lemma compact_norm_bound (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖x‖ ≤ C := by
  have himg : IsCompact ((fun x : Plane => ‖x‖) '' K) := hK.image continuous_norm
  have hneimg : ((fun x : Plane => ‖x‖) '' K).Nonempty := hne.image _
  obtain ⟨x, hxK, hxeq⟩ := himg.sSup_mem hneimg
  refine ⟨sSup ((fun x : Plane => ‖x‖) '' K), ?_, ?_⟩
  · rw [← hxeq]
    exact norm_nonneg x
  · intro x hx
    exact le_csSup himg.bddAbove ⟨x, hx, rfl⟩

/-- One-sided Lipschitz bound for the support function. -/
private lemma supInner_sub_le (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ) (hC : ∀ x ∈ K, ‖x‖ ≤ C) (u1 u2 : Plane) :
    supInner K u1 - supInner K u2 ≤ C * ‖u1 - u2‖ := by
  obtain ⟨x1, hx1K, hx1eq⟩ := supInner_mem K hK hne u1
  have hle : inner ℝ (u1 - u2) x1 ≤ ‖u1 - u2‖ * ‖x1‖ := real_inner_le_norm _ _
  have hC1 : ‖u1 - u2‖ * ‖x1‖ ≤ ‖u1 - u2‖ * C :=
    mul_le_mul_of_nonneg_left (hC x1 hx1K) (norm_nonneg _)
  have hge : inner ℝ u2 x1 ≤ supInner K u2 := supInner_ge K hK hne u2 x1 hx1K
  have heq : inner ℝ u1 x1 - supInner K u2 ≤ inner ℝ (u1 - u2) x1 := by
    rw [inner_sub_left]
    linarith [hge]
  rw [← hx1eq]
  calc inner ℝ u1 x1 - supInner K u2 ≤ inner ℝ (u1 - u2) x1 := heq
    _ ≤ ‖u1 - u2‖ * ‖x1‖ := hle
    _ ≤ ‖u1 - u2‖ * C := hC1
    _ = C * ‖u1 - u2‖ := mul_comm _ _

/-- The support function is Lipschitz in the direction. -/
private lemma supInner_lipschitz (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (C : ℝ) (hC : ∀ x ∈ K, ‖x‖ ≤ C) (u1 u2 : Plane) :
    |supInner K u1 - supInner K u2| ≤ C * ‖u1 - u2‖ := by
  have h12 := supInner_sub_le K hK hne C hC u1 u2
  have h21 := supInner_sub_le K hK hne C hC u2 u1
  rw [norm_sub_rev] at h21
  rw [abs_le]
  constructor
  · linarith [h21]
  · linarith [h12]

/-- The support function is continuous in the direction. -/
private lemma continuous_supInner (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (supInner K) := by
  obtain ⟨C, hC0, hC⟩ := compact_norm_bound K hK hne
  apply LipschitzWith.continuous
  refine LipschitzWith.of_dist_le_mul (K := ⟨C, hC0⟩) ?_
  intro u1 u2
  rw [Real.dist_eq, dist_eq_norm]
  exact supInner_lipschitz K hK hne C hC u1 u2

/-- The infimum of inner products with `u` over `K`. -/
private def infInner (K : Set Plane) (u : Plane) : ℝ :=
  sInf ((fun x : Plane => inner ℝ u x) '' K)

/-- The infimum lies below every value on `K`. -/
private lemma infInner_le (K : Set Plane) (hK : IsCompact K) (_hne : K.Nonempty)
    (u : Plane) (x : Plane) (hx : x ∈ K) : infInner K u ≤ inner ℝ u x := by
  have hcont : Continuous (fun x : Plane => inner ℝ u x) :=
    (Continuous.inner continuous_const continuous_id)
  have himg : IsCompact ((fun x : Plane => inner ℝ u x) '' K) := hK.image hcont
  have hbdd : BddBelow ((fun x : Plane => inner ℝ u x) '' K) := himg.bddBelow
  exact csInf_le hbdd ⟨x, hx, rfl⟩

/-- The infimum in direction `u` is the negated supremum in direction $-u$. -/
private lemma infInner_eq_neg (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (u : Plane) : infInner K u = -supInner K (-u) := by
  simp only [infInner, supInner]
  apply le_antisymm
  · have hne2 : ((fun x : Plane => inner ℝ (-u) x) '' K).Nonempty := hne.image _
    have hle : sSup ((fun x : Plane => inner ℝ (-u) x) '' K) ≤
        -sInf ((fun x : Plane => inner ℝ u x) '' K) := by
      apply csSup_le hne2
      rintro t ⟨x, hx, rfl⟩
      have hcont : Continuous (fun x : Plane => inner ℝ u x) :=
        (Continuous.inner continuous_const continuous_id)
      have hbdd : BddBelow ((fun x : Plane => inner ℝ u x) '' K) :=
        (hK.image hcont).bddBelow
      have h1 : sInf ((fun x : Plane => inner ℝ u x) '' K) ≤ inner ℝ u x :=
        csInf_le hbdd ⟨x, hx, rfl⟩
      have h2 : inner ℝ (-u) x = -inner ℝ u x := inner_neg_left u x
      linarith [h1, h2]
    linarith [hle]
  · have hne1 : ((fun x : Plane => inner ℝ u x) '' K).Nonempty := hne.image _
    apply le_csInf hne1
    rintro s ⟨x, hx, rfl⟩
    have hcont : Continuous (fun x : Plane => inner ℝ (-u) x) :=
      (Continuous.inner continuous_const continuous_id)
    have hbdd : BddAbove ((fun x : Plane => inner ℝ (-u) x) '' K) :=
      (hK.image hcont).bddAbove
    have h1 : inner ℝ (-u) x ≤ sSup ((fun x : Plane => inner ℝ (-u) x) '' K) :=
      le_csSup hbdd ⟨x, hx, rfl⟩
    have h2 : inner ℝ (-u) x = -inner ℝ u x := inner_neg_left u x
    linarith [h1, h2]

/-- $\cos(2\pi/3) = -1/2$. -/
private lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have h : (2 : ℝ) * Real.pi / 3 = 2 * (Real.pi / 3) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_three]
  norm_num

/-- $\sin(2\pi/3) = \sqrt{3}/2$. -/
private lemma sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : (2 : ℝ) * Real.pi / 3 = 2 * (Real.pi / 3) := by ring
  rw [h, Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]
  ring

/-- $\cos(4\pi/3) = -1/2$. -/
private lemma cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
  have h : (4 : ℝ) * Real.pi / 3 = 2 * (2 * Real.pi / 3) := by ring
  rw [h, Real.cos_two_mul, cos_two_pi_div_three]
  norm_num

/-- $\sin(4\pi/3) = -\sqrt{3}/2$. -/
private lemma sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
  have h : (4 : ℝ) * Real.pi / 3 = 2 * (2 * Real.pi / 3) := by ring
  rw [h, Real.sin_two_mul, sin_two_pi_div_three, cos_two_pi_div_three]
  ring

/-- Inner products of direction vectors via the cosine of the angle difference. -/
private lemma inner_dirVec_cos (α β : ℝ) :
    inner ℝ (dirVec α) (dirVec β) = Real.cos (α - β) := by
  simp only [dirVec, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    e0_inner_e0, e1_inner_e1, e0_inner_e1]
  have h10 : inner ℝ e1 e0 = 0 := by rw [real_inner_comm]; exact e0_inner_e1
  rw [h10]
  simp only [conj_trivial, mul_one, mul_zero, add_zero, zero_add]
  rw [Real.cos_sub]
  ring

/-- The angle step $2\pi/3$. -/
private def hstep : ℝ := 2 * Real.pi / 3

/-- The direction indices $0, 1, 2$ as reals. -/
private def ucoef : Fin 3 → ℝ := ![0, 1, 2]

/-- The three unit directions $120°$ apart, rotated by $θ$. -/
private def uvec (i : Fin 3) (θ : ℝ) : Plane := dirVec (θ + ucoef i * hstep)

/-- Each `uvec` direction is a unit vector. -/
private lemma uvec_self_inner (i : Fin 3) (θ : ℝ) : inner ℝ (uvec i θ) (uvec i θ) = 1 := by
  simp only [uvec, inner_dirVec_cos, sub_self, Real.cos_zero]

/-- Distinct `uvec` directions have inner product $-1/2$. -/
private lemma uvec_cross_inner (i j : Fin 3) (hij : i ≠ j) (θ : ℝ) :
    inner ℝ (uvec i θ) (uvec j θ) = -1 / 2 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · change inner ℝ (uvec 0 θ) (uvec 1 θ) = -1 / 2
    have e0 : ucoef 0 = 0 := by simp [ucoef]
    have e1 : ucoef 1 = 1 := by simp [ucoef]
    simp only [uvec, inner_dirVec_cos, e0, e1]
    have h : (θ + 0 * hstep) - (θ + 1 * hstep) = -(2 * Real.pi / 3) := by
      simp only [hstep]
      ring
    rw [h, Real.cos_neg, cos_two_pi_div_three]
  · change inner ℝ (uvec 0 θ) (uvec 2 θ) = -1 / 2
    have e0 : ucoef 0 = 0 := by simp [ucoef]
    have e2 : ucoef 2 = 2 := by simp [ucoef]
    simp only [uvec, inner_dirVec_cos, e0, e2]
    have h : (θ + 0 * hstep) - (θ + 2 * hstep) = -(4 * Real.pi / 3) := by
      simp only [hstep]
      ring
    rw [h, Real.cos_neg, cos_four_pi_div_three]
  · change inner ℝ (uvec 1 θ) (uvec 0 θ) = -1 / 2
    have e1 : ucoef 1 = 1 := by simp [ucoef]
    have e0 : ucoef 0 = 0 := by simp [ucoef]
    simp only [uvec, inner_dirVec_cos, e1, e0]
    have h : (θ + 1 * hstep) - (θ + 0 * hstep) = 2 * Real.pi / 3 := by
      simp only [hstep]
      ring
    rw [h, cos_two_pi_div_three]
  · exact absurd rfl hij
  · change inner ℝ (uvec 1 θ) (uvec 2 θ) = -1 / 2
    have e1 : ucoef 1 = 1 := by simp [ucoef]
    have e2 : ucoef 2 = 2 := by simp [ucoef]
    simp only [uvec, inner_dirVec_cos, e1, e2]
    have h : (θ + 1 * hstep) - (θ + 2 * hstep) = -(2 * Real.pi / 3) := by
      simp only [hstep]
      ring
    rw [h, Real.cos_neg, cos_two_pi_div_three]
  · change inner ℝ (uvec 2 θ) (uvec 0 θ) = -1 / 2
    have e2 : ucoef 2 = 2 := by simp [ucoef]
    have e0 : ucoef 0 = 0 := by simp [ucoef]
    simp only [uvec, inner_dirVec_cos, e2, e0]
    have h : (θ + 2 * hstep) - (θ + 0 * hstep) = 4 * Real.pi / 3 := by
      simp only [hstep]
      ring
    rw [h, cos_four_pi_div_three]
  · change inner ℝ (uvec 2 θ) (uvec 1 θ) = -1 / 2
    have e2 : ucoef 2 = 2 := by simp [ucoef]
    have e1 : ucoef 1 = 1 := by simp [ucoef]
    simp only [uvec, inner_dirVec_cos, e2, e1]
    have h : (θ + 2 * hstep) - (θ + 1 * hstep) = 2 * Real.pi / 3 := by
      simp only [hstep]
      ring
    rw [h, cos_two_pi_div_three]
  · exact absurd rfl hij

/-- `dirVec` is $2\pi$-periodic. -/
private lemma dirVec_add_two_pi (φ : ℝ) : dirVec (φ + 2 * Real.pi) = dirVec φ := by
  simp only [dirVec, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- `uvec` is $2\pi$-periodic in $θ$. -/
private lemma uvec_add_two_pi (i : Fin 3) (θ : ℝ) :
    uvec i (θ + 2 * Real.pi) = uvec i θ := by
  simp only [uvec]
  have h : θ + 2 * Real.pi + ucoef i * hstep = (θ + ucoef i * hstep) + 2 * Real.pi := by
    ring
  rw [h, dirVec_add_two_pi]

/-- Shifting $θ$ by $\pi$ negates each `uvec` direction. -/
private lemma uvec_add_pi (i : Fin 3) (θ : ℝ) : uvec i (θ + Real.pi) = -uvec i θ := by
  simp only [uvec]
  have h : θ + Real.pi + ucoef i * hstep = (θ + ucoef i * hstep) + Real.pi := by ring
  rw [h, dirVec_add_pi]

/-- The sum of the three support values at angle $θ$. -/
private def balanceFun (K : Set Plane) (θ : ℝ) : ℝ :=
  supInner K (uvec 0 θ) + supInner K (uvec 1 θ) + supInner K (uvec 2 θ)

/-- `balanceFun` is continuous. -/
private lemma continuous_balanceFun (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (balanceFun K) := by
  have hc := continuous_supInner K hK hne
  have h0 : Continuous (fun θ : ℝ => uvec 0 θ) := by
    unfold uvec
    exact dirVec_continuous.comp (continuous_id.add_const _)
  have h1 : Continuous (fun θ : ℝ => uvec 1 θ) := by
    unfold uvec
    exact dirVec_continuous.comp (continuous_id.add_const _)
  have h2 : Continuous (fun θ : ℝ => uvec 2 θ) := by
    unfold uvec
    exact dirVec_continuous.comp (continuous_id.add_const _)
  unfold balanceFun
  exact ((hc.comp h0).add (hc.comp h1)).add (hc.comp h2)

/-- `balanceFun` is $2\pi$-periodic. -/
private lemma balanceFun_add_two_pi (K : Set Plane) (θ : ℝ) :
    balanceFun K (θ + 2 * Real.pi) = balanceFun K θ := by
  simp only [balanceFun, uvec_add_two_pi]

/-- Per-direction width bound at the rotated directions. -/
private lemma balanceWidth_le (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (hdiam : Metric.diam K = 1) (i : Fin 3) (θ : ℝ) :
    supInner K (uvec i θ) + supInner K (uvec i (θ + Real.pi)) ≤ 1 := by
  have h := width_le_one K hK hne hdiam (θ + ucoef i * hstep)
  have e1 : uvec i θ = dirVec (θ + ucoef i * hstep) := rfl
  have e2 : uvec i (θ + Real.pi) = dirVec (θ + ucoef i * hstep + Real.pi) := by
    simp only [uvec]
    congr 1
    ring
  rw [e1, e2]
  exact h

/-- Some angle balances the support sum with its antipode. -/
private lemma exists_balance_point (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ θ₀ : ℝ, θ₀ ∈ Set.Icc 0 Real.pi ∧
      balanceFun K θ₀ = balanceFun K (θ₀ + Real.pi) := by
  set H : ℝ → ℝ := fun θ => balanceFun K θ - balanceFun K (θ + Real.pi) with hHdef
  have hcont : ContinuousOn H (Set.Icc 0 Real.pi) :=
    ((continuous_balanceFun K hK hne).sub
      ((continuous_balanceFun K hK hne).comp (continuous_id.add_const _))).continuousOn
  have hF : balanceFun K (Real.pi + Real.pi) = balanceFun K 0 := by
    have h : Real.pi + Real.pi = 0 + 2 * Real.pi := by ring
    rw [h]
    exact balanceFun_add_two_pi K 0
  have hanti : H Real.pi = -H 0 := by
    simp only [hHdef, zero_add]
    linarith [hF]
  rcases le_total (H 0) (H Real.pi) with hle | hle
  · have h0mem : (0 : ℝ) ∈ Set.Icc (H 0) (H Real.pi) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [hanti, hle]
    have hsub := intermediate_value_Icc (Real.pi_pos.le) hcont
    obtain ⟨θ₀, hθ₀mem, hθ₀eq⟩ := hsub h0mem
    refine ⟨θ₀, hθ₀mem, ?_⟩
    simp only [hHdef] at hθ₀eq
    linarith [hθ₀eq]
  · have h0mem : (0 : ℝ) ∈ Set.Icc (H Real.pi) (H 0) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [hanti, hle]
    have hsub := intermediate_value_Icc' (Real.pi_pos.le) hcont
    obtain ⟨θ₀, hθ₀mem, hθ₀eq⟩ := hsub h0mem
    refine ⟨θ₀, hθ₀mem, ?_⟩
    simp only [hHdef] at hθ₀eq
    linarith [hθ₀eq]

/-- Rotation of the plane by the angle $ψ$. -/
private def rotFun (ψ : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![Real.cos ψ * x.ofLp 0 - Real.sin ψ * x.ofLp 1,
    Real.sin ψ * x.ofLp 0 + Real.cos ψ * x.ofLp 1]

/-- Inverse rotation of the plane by the angle $ψ$. -/
private def rotInv (ψ : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![Real.cos ψ * x.ofLp 0 + Real.sin ψ * x.ofLp 1,
    -Real.sin ψ * x.ofLp 0 + Real.cos ψ * x.ofLp 1]

/-- First coordinate of `rotFun`. -/
private lemma rotFun_ofLp0 (ψ : ℝ) (x : Plane) :
    (rotFun ψ x).ofLp 0 = Real.cos ψ * x.ofLp 0 - Real.sin ψ * x.ofLp 1 := by
  simp [rotFun]

/-- Second coordinate of `rotFun`. -/
private lemma rotFun_ofLp1 (ψ : ℝ) (x : Plane) :
    (rotFun ψ x).ofLp 1 = Real.sin ψ * x.ofLp 0 + Real.cos ψ * x.ofLp 1 := by
  simp [rotFun]

/-- First coordinate of `rotInv`. -/
private lemma rotInv_ofLp0 (ψ : ℝ) (x : Plane) :
    (rotInv ψ x).ofLp 0 = Real.cos ψ * x.ofLp 0 + Real.sin ψ * x.ofLp 1 := by
  simp [rotInv]

/-- Second coordinate of `rotInv`. -/
private lemma rotInv_ofLp1 (ψ : ℝ) (x : Plane) :
    (rotInv ψ x).ofLp 1 = -Real.sin ψ * x.ofLp 0 + Real.cos ψ * x.ofLp 1 := by
  simp [rotInv]

/-- `rotFun` preserves norms. -/
private lemma rotFun_norm (ψ : ℝ) (x : Plane) : ‖rotFun ψ x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, rotFun_ofLp0, rotFun_ofLp1]
  have hcos := Real.cos_sq_add_sin_sq ψ
  congr 1
  ring_nf
  nlinarith [hcos, sq_nonneg (x.ofLp 0), sq_nonneg (x.ofLp 1),
    sq_nonneg (Real.cos ψ), sq_nonneg (Real.sin ψ)]

/-- `rotFun` after `rotInv` is the identity. -/
private lemma rotFun_rotInv (ψ : ℝ) (x : Plane) : rotFun ψ (rotInv ψ x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rotFun ψ (rotInv ψ x)).ofLp 0 = x.ofLp 0
    simp only [rotFun_ofLp0, rotInv_ofLp0, rotInv_ofLp1]
    have hcos := Real.cos_sq_add_sin_sq ψ
    linear_combination (x.ofLp 0) * hcos
  · change (rotFun ψ (rotInv ψ x)).ofLp 1 = x.ofLp 1
    simp only [rotFun_ofLp1, rotInv_ofLp0, rotInv_ofLp1]
    have hcos := Real.cos_sq_add_sin_sq ψ
    linear_combination (x.ofLp 1) * hcos

/-- `rotFun` is an isometry. -/
private lemma rotFun_isometry (ψ : ℝ) : Isometry (rotFun ψ) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hlin : rotFun ψ x - rotFun ψ y = rotFun ψ (x - y) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change (rotFun ψ x - rotFun ψ y).ofLp 0 = (rotFun ψ (x - y)).ofLp 0
      simp [rotFun_ofLp0]
      ring
    · change (rotFun ψ x - rotFun ψ y).ofLp 1 = (rotFun ψ (x - y)).ofLp 1
      simp [rotFun_ofLp1]
      ring
  rw [hlin, rotFun_norm]

/-- Rotation by $ψ$ as an isometry of the plane. -/
private def rot (ψ : ℝ) : Plane ≃ᵢ Plane :=
  IsometryEquiv.mk' (rotFun ψ) (rotInv ψ) (rotFun_rotInv ψ) (rotFun_isometry ψ)

/-- Inner products in coordinates. -/
private lemma inner_ofLp_eq (a b : Plane) :
    inner ℝ a b = b.ofLp 0 * a.ofLp 0 + b.ofLp 1 * a.ofLp 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- `rotFun` preserves inner products. -/
private lemma rotFun_inner (ψ : ℝ) (x y : Plane) :
    inner ℝ (rotFun ψ x) (rotFun ψ y) = inner ℝ x y := by
  have hcos := Real.cos_sq_add_sin_sq ψ
  simp only [inner_ofLp_eq, rotFun_ofLp0, rotFun_ofLp1]
  linear_combination (x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1) * hcos

/-- First coordinate of `dirVec`. -/
private lemma dirVec_ofLp0 (φ : ℝ) : (dirVec φ).ofLp 0 = Real.cos φ := by
  simp [dirVec, e0, e1]

/-- Second coordinate of `dirVec`. -/
private lemma dirVec_ofLp1 (φ : ℝ) : (dirVec φ).ofLp 1 = Real.sin φ := by
  simp [dirVec, e0, e1]

/-- `rotFun` adds $ψ$ to the angle of `dirVec`. -/
private lemma rotFun_dirVec (ψ φ : ℝ) : rotFun ψ (dirVec φ) = dirVec (φ + ψ) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rotFun ψ (dirVec φ)).ofLp 0 = (dirVec (φ + ψ)).ofLp 0
    simp only [rotFun_ofLp0, dirVec_ofLp0, dirVec_ofLp1]
    rw [Real.cos_add]
    ring
  · change (rotFun ψ (dirVec φ)).ofLp 1 = (dirVec (φ + ψ)).ofLp 1
    simp only [rotFun_ofLp1, dirVec_ofLp0, dirVec_ofLp1]
    rw [Real.sin_add]
    ring

/-- `rotInv` subtracts $ψ$ from the angle of `dirVec`. -/
private lemma rotInv_dirVec (ψ φ : ℝ) : rotInv ψ (dirVec φ) = dirVec (φ - ψ) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rotInv ψ (dirVec φ)).ofLp 0 = (dirVec (φ - ψ)).ofLp 0
    simp only [rotInv_ofLp0, dirVec_ofLp0, dirVec_ofLp1]
    rw [Real.cos_sub]
    ring
  · change (rotInv ψ (dirVec φ)).ofLp 1 = (dirVec (φ - ψ)).ofLp 1
    simp only [rotInv_ofLp1, dirVec_ofLp0, dirVec_ofLp1]
    rw [Real.sin_sub]
    ring

/-- `hu0` is `dirVec 0`. -/
private lemma hu0_eq_dirVec : hu0 = dirVec 0 := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change hu0.ofLp 0 = (dirVec 0).ofLp 0
    simp [hu0, dirVec, e0, e1, Real.cos_zero]
  · change hu0.ofLp 1 = (dirVec 0).ofLp 1
    simp [hu0, dirVec, e0, e1, Real.sin_zero]

/-- `hu1` is `dirVec (2\pi/3)`. -/
private lemma hu1_eq_dirVec : hu1 = dirVec (2 * Real.pi / 3) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change hu1.ofLp 0 = (dirVec (2 * Real.pi / 3)).ofLp 0
    rw [dirVec_ofLp0, cos_two_pi_div_three]
    simp [hu1]
  · change hu1.ofLp 1 = (dirVec (2 * Real.pi / 3)).ofLp 1
    rw [dirVec_ofLp1, sin_two_pi_div_three]
    simp [hu1]

/-- `hu2` is `dirVec (4\pi/3)`. -/
private lemma hu2_eq_dirVec : hu2 = dirVec (4 * Real.pi / 3) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change hu2.ofLp 0 = (dirVec (4 * Real.pi / 3)).ofLp 0
    rw [dirVec_ofLp0, cos_four_pi_div_three]
    simp [hu2]
  · change hu2.ofLp 1 = (dirVec (4 * Real.pi / 3)).ofLp 1
    rw [dirVec_ofLp1, sin_four_pi_div_three]
    simp [hu2]

/-- The three hexagon normals. -/
private def huVec : Fin 3 → Plane := ![hu0, hu1, hu2]

/-- Every nonempty compact convex set of diameter $1$ fits in the hexagon. -/
private lemma covers_compact (K : Set Plane) (hK : IsCompact K) (hne : K.Nonempty)
    (hdiam : Metric.diam K = 1) : CoversCongruentCopy palHex K := by
  obtain ⟨θ₀, _hθ₀mem, hθ₀eq⟩ := exists_balance_point K hK hne
  set sP : Fin 3 → ℝ := fun i => supInner K (uvec i θ₀) with hsPdef
  set sM : Fin 3 → ℝ := fun i => infInner K (uvec i θ₀) with hsMdef
  have hneg : ∀ i : Fin 3, -uvec i θ₀ = uvec i (θ₀ + Real.pi) :=
    fun i => (uvec_add_pi i θ₀).symm
  have hsM : ∀ i : Fin 3, sM i = -supInner K (uvec i (θ₀ + Real.pi)) := by
    intro i
    simp only [hsMdef]
    rw [infInner_eq_neg K hK hne, hneg]
  have hwidth : ∀ i : Fin 3, sP i - sM i ≤ 1 := by
    intro i
    have h := balanceWidth_le K hK hne hdiam i θ₀
    simp only [hsPdef]
    rw [hsM i]
    linarith [h]
  set y : Fin 3 → ℝ := fun i => -(sP i + sM i) / 2 with hydef
  have hyJ : ∀ i : Fin 3, -1 / 2 - sM i ≤ y i ∧ y i ≤ 1 / 2 - sP i := by
    intro i
    have h := hwidth i
    simp only [hydef]
    constructor <;> linarith [h]
  have hysum : y 0 + y 1 + y 2 = 0 := by
    have hF0 : sP 0 + sP 1 + sP 2 = balanceFun K θ₀ := by simp only [hsPdef, balanceFun]
    have hFpi : sM 0 + sM 1 + sM 2 = -balanceFun K (θ₀ + Real.pi) := by
      rw [hsM 0, hsM 1, hsM 2]
      simp only [balanceFun]
      ring
    simp only [hydef]
    linarith [hF0, hFpi, hθ₀eq]
  set t : Plane := (2 / 3 : ℝ) • (y 0 • uvec 0 θ₀ + y 1 • uvec 1 θ₀ + y 2 • uvec 2 θ₀)
    with htdef
  have hself : ∀ i : Fin 3, inner ℝ (uvec i θ₀) (uvec i θ₀) = 1 :=
    fun i => uvec_self_inner i θ₀
  have hcross : ∀ i j : Fin 3, i ≠ j → inner ℝ (uvec i θ₀) (uvec j θ₀) = -1 / 2 :=
    fun i j hij => uvec_cross_inner i j hij θ₀
  have ht : ∀ i : Fin 3, inner ℝ (uvec i θ₀) t = y i := by
    intro i
    fin_cases i
    · change inner ℝ (uvec 0 θ₀) t = y 0
      simp only [htdef, inner_smul_right, inner_add_right]
      rw [hself 0, hcross 0 1 (by decide), hcross 0 2 (by decide)]
      linarith [hysum]
    · change inner ℝ (uvec 1 θ₀) t = y 1
      simp only [htdef, inner_smul_right, inner_add_right]
      rw [hself 1, hcross 1 0 (by decide), hcross 1 2 (by decide)]
      linarith [hysum]
    · change inner ℝ (uvec 2 θ₀) t = y 2
      simp only [htdef, inner_smul_right, inner_add_right]
      rw [hself 2, hcross 2 0 (by decide), hcross 2 1 (by decide)]
      linarith [hysum]
  set ψ : ℝ := -θ₀ with hψdef
  have hrot : ∀ i : Fin 3, rotInv ψ (huVec i) = uvec i θ₀ := by
    intro i
    fin_cases i
    · change rotInv ψ (huVec 0) = uvec 0 θ₀
      simp only [huVec, Matrix.cons_val_zero]
      rw [hu0_eq_dirVec, rotInv_dirVec]
      have h : (0 : ℝ) - ψ = θ₀ + ucoef 0 * hstep := by
        simp only [hψdef, ucoef, hstep, Matrix.cons_val_zero]
        ring
      simp only [h, uvec]
    · change rotInv ψ (huVec 1) = uvec 1 θ₀
      simp only [huVec, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hu1_eq_dirVec, rotInv_dirVec]
      have h : 2 * Real.pi / 3 - ψ = θ₀ + ucoef 1 * hstep := by
        have e1 : ucoef 1 = 1 := by simp [ucoef]
        rw [e1]
        simp only [hψdef, hstep]
        ring
      simp only [h, uvec]
    · change rotInv ψ (huVec 2) = uvec 2 θ₀
      have ehu : huVec 2 = hu2 := by simp [huVec]
      rw [ehu, hu2_eq_dirVec, rotInv_dirVec]
      have h : 4 * Real.pi / 3 - ψ = θ₀ + ucoef 2 * hstep := by
        have e2 : ucoef 2 = 2 := by simp [ucoef]
        rw [e2]
        simp only [hψdef, hstep]
        ring
      simp only [h, uvec]
  have hkey : ∀ i : Fin 3, ∀ x : Plane,
      inner ℝ (huVec i) (rotFun ψ x) = inner ℝ (uvec i θ₀) x := by
    intro i x
    have h1 : huVec i = rotFun ψ (rotInv ψ (huVec i)) := (rotFun_rotInv ψ _).symm
    rw [h1, rotFun_inner, hrot i]
  refine ⟨(rot ψ).trans (IsometryEquiv.subRight (-(rotFun ψ t))), ?_⟩
  intro z hz
  obtain ⟨x, hxK, rfl⟩ := hz
  rw [IsometryEquiv.trans_apply, IsometryEquiv.subRight_apply]
  change rotFun ψ x - -rotFun ψ t ∈ palHex
  have hmem : ∀ i : Fin 3,
      |inner ℝ (huVec i) (rotFun ψ x - -rotFun ψ t)| ≤ 1 / 2 := by
    intro i
    have hx1 : inner ℝ (uvec i θ₀) x ≤ sP i := supInner_ge K hK hne _ x hxK
    have hx0 : sM i ≤ inner ℝ (uvec i θ₀) x := infInner_le K hK hne _ x hxK
    have hy := hyJ i
    have hti : inner ℝ (uvec i θ₀) t = y i := ht i
    have hexpand : inner ℝ (huVec i) (rotFun ψ x - -rotFun ψ t) =
        inner ℝ (uvec i θ₀) x + y i := by
      rw [inner_sub_right, hkey i x]
      have hti2 : inner ℝ (huVec i) (rotFun ψ t) = y i := by
        rw [hkey i t, hti]
      rw [inner_neg_right, hti2]
      ring
    rw [hexpand, abs_le]
    constructor <;> linarith [hx0, hx1, hy.1, hy.2]
  have h0 := hmem 0
  have h1 := hmem 1
  have h2 := hmem 2
  have ehu0 : huVec 0 = hu0 := by simp [huVec]
  have ehu1 : huVec 1 = hu1 := by simp [huVec]
  have ehu2 : huVec 2 = hu2 := by simp [huVec]
  rw [ehu0] at h0
  rw [ehu1] at h1
  rw [ehu2] at h2
  change |inner ℝ hu0 (rotFun ψ x - -rotFun ψ t)| ≤ 1 / 2 ∧
    |inner ℝ hu1 (rotFun ψ x - -rotFun ψ t)| ≤ 1 / 2 ∧
    |inner ℝ hu2 (rotFun ψ x - -rotFun ψ t)| ≤ 1 / 2
  exact ⟨h0, h1, h2⟩

/-- The hexagon is a universal convex cover. -/
private lemma isUniversalConvexCover_palHex : IsUniversalConvexCover palHex := by
  refine ⟨palHex_nonempty, palHex_convex, ?_⟩
  rintro K ⟨hneK, hconvK, hdiamK⟩
  have hbounded : Bornology.IsBounded K := by
    by_contra h
    exact zero_ne_one ((Metric.diam_eq_zero_of_unbounded h).symm.trans hdiamK)
  have hneC : (closure K).Nonempty := hneK.closure
  have hconvC : Convex ℝ (closure K) := hconvK.closure
  have hcompC : IsCompact (closure K) := hbounded.isCompact_closure
  have hdiamC : Metric.diam (closure K) = 1 := by rw [Metric.diam_closure, hdiamK]
  obtain ⟨e, he⟩ := covers_compact (closure K) hcompC hneC hdiamC
  refine ⟨e, ?_⟩
  exact le_trans (Set.image_mono subset_closure) he

/-- **Pál's hexagon bound.** The Lebesgue universal covering constant is at most $\sqrt{3}/2$.

Source: Pál, Über ein elementares Variationsproblem (1920), hexagon bound. -/
theorem pal1920HexagonUpperBound_holds : pal1920HexagonUpperBound := by
  unfold pal1920HexagonUpperBound
  exact le_trans (sInf_le ⟨palHex, isUniversalConvexCover_palHex, rfl⟩) palHex_area_le

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
