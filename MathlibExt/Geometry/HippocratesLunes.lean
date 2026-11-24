/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/HippocratesLunes.lean` (leanprover/lean-eval), commit
38361be884302c7edce1908c4aef8296eb2cb27e, problem `hippocrates_lunes`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
The adapted portions are the coordinate and region definitions and the statement of
`hippocrates_lunes` (manifest `manifests/problems/hippocrates_lunes.toml`, rev 1,
submitter Kim Morrison, status archived).

Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The wanted module replaced the
lean-eval theorem marker with a Batteries wanted declaration, inlined the helpers and
placed the declarations in the ATLAS namespace. This module moves those declarations
from the wanted library and supplies the proof.
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Hippocrates' theorem on lunes

`hippocrates_lunes` proves that the lunes on the legs of a right triangle have combined
area equal to the area of the triangle. The half-disks on the three sides are similar,
and removing the common circular segments gives the area identity.
-/

@[expose] public section

namespace MathlibExt.Geometry.HippocratesLunesWanted
namespace Geometry.HippocratesLunes

open MeasureTheory

set_option linter.dupNamespace false in
/-- **Coordinate plane for Hippocrates' lunes.** The coordinate plane is the set
$\mathbb{R} \times \mathbb{R}$ of ordered pairs $(x, y)$ of real numbers. -/
abbrev Plane := ℝ × ℝ

set_option linter.dupNamespace false in
/-- **Planar determinant for Hippocrates' lunes.** For vectors $u = (u_1, u_2)$ and
$v = (v_1, v_2)$ of the coordinate plane, $\det(u, v) = u_1 v_2 - u_2 v_1$, the signed area of
the parallelogram spanned by $u$ and $v$. -/
def det2 (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

set_option linter.dupNamespace false in
/-- **Midpoint of two points in the plane.** For points $p = (p_1, p_2)$ and
$q = (q_1, q_2)$ of the coordinate plane, their midpoint is
$\left(\frac{p_1 + q_1}{2}, \frac{p_2 + q_2}{2}\right)$. -/
noncomputable def midpoint (p q : Plane) : Plane := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

set_option linter.dupNamespace false in
/-- **Displacement vector between two points of the plane.** For points $p = (p_1, p_2)$ and
$q = (q_1, q_2)$ of $\mathbb{R}^2$, the displacement vector from $p$ to $q$ is
$(q_1 - p_1, q_2 - p_2)$. -/
def vec (p q : Plane) : Plane := (q.1 - p.1, q.2 - p.2)

set_option linter.dupNamespace false in
/-- **Squared Euclidean distance in the plane.** For points $p = (p_1, p_2)$ and
$q = (q_1, q_2)$ of the coordinate plane, the squared Euclidean distance between them is
$(p_1 - q_1)^2 + (p_2 - q_2)^2$.

This uses the Euclidean distance, not the sup metric of the product
$\mathbb{R} \times \mathbb{R}$. -/
def euclideanDistSq (p q : Plane) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

set_option linter.dupNamespace false in
/-- **Closed half-disk on a diameter.** Given points $p$ and $q$ of the coordinate plane and a
property $S$ of real numbers, this is the set of points $x$ such that the squared Euclidean
distance from $x$ to the midpoint of $p$ and $q$ is at most one quarter of the squared Euclidean
distance from $p$ to $q$ (so $x$ lies in the closed disk with diameter $pq$), and $S$ holds of
the planar determinant $\det(q - p, x - p)$. For $p \ne q$, taking $S(t)$ to be $t \ge 0$
(respectively $t \le 0$) selects the closed half of that disk to the left (respectively right)
of the directed line from $p$ to $q$. -/
def closedHalfDisk (p q : Plane) (side : ℝ → Prop) : Set Plane :=
  {x | euclideanDistSq x (midpoint p q) ≤ euclideanDistSq p q / 4 ∧
    side (det2 (vec p q) (vec p x))}

set_option linter.dupNamespace false in
/-- **Right-angle vertex of the lune triangle.** The point $A = (0, 0)$, the origin of the
coordinate plane; it is the right-angle vertex of the triangle in Hippocrates' theorem on
lunes. -/
def A : Plane := (0, 0)
set_option linter.dupNamespace false in
/-- **Horizontal leg endpoint of the lune triangle.** For a real number $a$, the point
$B = (a, 0)$ on the $x$-axis of the coordinate plane; it is the endpoint of the horizontal leg of
the right triangle in Hippocrates' theorem on lunes. -/
def B (a : ℝ) : Plane := (a, 0)
set_option linter.dupNamespace false in
/-- **Vertical leg endpoint of the lune triangle.** For a real number $b$, the point
$C = (0, b)$ on the $y$-axis of the coordinate plane; it is the endpoint of the vertical leg of
the right triangle in Hippocrates' theorem on lunes. -/
def C (b : ℝ) : Plane := (0, b)

set_option linter.dupNamespace false in
/-- **Half-disk on the hypotenuse.** For real numbers $a$ and $b$, let $B = (a, 0)$ and
$C = (0, b)$. The half-disk on the hypotenuse is the set of points $x = (x_1, x_2)$ of the
closed disk with diameter $BC$ satisfying $\det(C - B, x - B) \ge 0$, that is,
$b x_1 + a x_2 \le ab$. For $a, b > 0$ this is the half of the disk on the side of the line
$BC$ containing the right-angle vertex $(0, 0)$. -/
def hypotenuseSemidisk (a b : ℝ) : Set Plane :=
  closedHalfDisk (B a) (C b) (fun t => 0 ≤ t)

set_option linter.dupNamespace false in
/-- **Lune on the horizontal leg.** For real numbers $a$ and $b$, let $A = (0, 0)$,
$B = (a, 0)$ and $C = (0, b)$. The lune on the horizontal leg is the set of points
$x = (x_1, x_2)$ of the closed disk with diameter $AB$ satisfying $a x_2 \le 0$ that do not
lie in the half-disk on the hypotenuse, the set of points of the closed disk with diameter $BC$
satisfying $b x_1 + a x_2 \le ab$. For $a, b > 0$ this is the set of points of the closed lower
half-disk on the leg $AB$ that lie outside the closed disk with diameter $BC$. -/
def horizontalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (B a) (fun t => t ≤ 0) \ hypotenuseSemidisk a b

set_option linter.dupNamespace false in
/-- **Hippocrates lune on the vertical leg.** For real numbers $a$ and $b$, the vertical lune is
the set of points $(x, y) \in \mathbb{R}^2$ with $x^2 + (y - b/2)^2 \le b^2/4$ and $bx \le 0$
that do not satisfy both $(x - a/2)^2 + (y - b/2)^2 \le (a^2 + b^2)/4$ and $bx + ay \le ab$.

For $a, b > 0$ this is the closed half-disk on the segment from $(0, 0)$ to $(0, b)$, on the side
away from $(a, 0)$, minus the closed half-disk on the hypotenuse from $(a, 0)$ to $(0, b)$, on
the side of the origin. -/
def verticalLune (a b : ℝ) : Set Plane :=
  closedHalfDisk A (C b) (fun t => 0 ≤ t) \ hypotenuseSemidisk a b

set_option linter.dupNamespace false in
/-- **Right triangle with legs on the axes.** For real numbers $a$ and $b$, the right triangle
$T(a, b)$ is the convex hull in the plane $\mathbb{R}^2$ of the three points $(0, 0)$, $(a, 0)$
and $(0, b)$. -/
def rightTriangle (a b : ℝ) : Set Plane :=
  convexHull ℝ ({A, B a, C b} : Set Plane)

open Set

/-- The model half-disk has diameter one and is centered at the origin. -/
private def unitHalfDisk : Set Plane :=
  {x | x.1 ^ 2 + x.2 ^ 2 ≤ 1 / 4 ∧ 0 ≤ x.2}

private lemma unitHalfDisk_finite : volume unitHalfDisk ≠ ⊤ := by
  refine ne_top_of_le_ne_top (isCompact_Icc.measure_lt_top (μ := volume)).ne
    (measure_mono (t := Icc ((-1, -1) : Plane) (1, 1)) ?_)
  rintro ⟨x, y⟩ ⟨hd, _⟩
  change x ^ 2 + y ^ 2 ≤ 1 / 4 at hd
  change (-1 ≤ x ∧ -1 ≤ y) ∧ x ≤ 1 ∧ y ≤ 1
  constructor <;> constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1),
    sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg x, sq_nonneg y]

/-- A similarity taking the horizontal unit diameter to the directed diameter from `p` to `q`
scales area by the squared length of that diameter. -/
private lemma volume_leftHalfDisk (p q : Plane) (hpq : 0 < euclideanDistSq p q) :
    volume (closedHalfDisk p q (0 ≤ ·)) =
      ENNReal.ofReal (euclideanDistSq p q) * volume unitHalfDisk := by
  let u := q.1 - p.1
  let v := q.2 - p.2
  let L := Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![u, -v; v, u]
  have hdet : LinearMap.det L = euclideanDistSq p q := by
    simp only [L, LinearMap.det_toLin, Matrix.det_fin_two_of, euclideanDistSq, u, v]
    ring
  have hsurj : Function.Surjective L := (L.equivOfDetNeZero (hdet ▸ hpq.ne')).surjective
  have himage : closedHalfDisk p q (0 ≤ ·) =
      (midpoint p q + ·) '' (L '' unitHalfDisk) := by
    ext x
    obtain ⟨z, rfl⟩ := ((Equiv.addLeft (midpoint p q)).surjective.comp hsurj) x
    change midpoint p q + L z ∈ _ ↔ midpoint p q + L z ∈ _
    have hinj : Function.Injective L := (L.equivOfDetNeZero (hdet ▸ hpq.ne')).injective
    rw [(add_right_injective (midpoint p q)).mem_set_image, hinj.mem_set_image]
    have hnorm : euclideanDistSq (midpoint p q + L z) (midpoint p q) =
        euclideanDistSq p q * (z.1 ^ 2 + z.2 ^ 2) := by
      simp [euclideanDistSq, L, u, v]
      ring
    have hside : det2 (vec p q) (vec p (midpoint p q + L z)) =
        euclideanDistSq p q * z.2 := by
      simp [det2, vec, midpoint, euclideanDistSq, L, u, v]
      ring
    change (_ ≤ _ ∧ 0 ≤ _) ↔ (_ ≤ _ ∧ 0 ≤ _)
    rw [hnorm, hside, div_eq_mul_one_div (euclideanDistSq p q), mul_le_mul_iff_right₀ hpq,
      mul_nonneg_iff_of_pos_left hpq]
  have : (volume : Measure Plane).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  rw [himage, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap,
    hdet, abs_of_pos hpq]

private abbrev horizontalHalf (a : ℝ) := closedHalfDisk A (B a) (· ≤ 0)
private abbrev verticalHalf (b : ℝ) := closedHalfDisk A (C b) (0 ≤ ·)

private lemma mem_horizontalHalf {a : ℝ} (ha : 0 < a) (z : Plane) :
    z ∈ horizontalHalf a ↔ z.1 ^ 2 + z.2 ^ 2 ≤ a * z.1 ∧ z.2 ≤ 0 := by
  simp only [horizontalHalf, closedHalfDisk, Set.mem_ofPred_eq, euclideanDistSq, det2, vec,
    midpoint, A, B, sub_zero, zero_add, zero_mul, sub_self, zero_div, mul_nonpos_iff,
    ha.not_ge, ha.le]
  apply and_congr
  · constructor <;> intro h <;> nlinarith only [h]
  · simp

private lemma mem_verticalHalf {b : ℝ} (hb : 0 < b) (z : Plane) :
    z ∈ verticalHalf b ↔ z.1 ^ 2 + z.2 ^ 2 ≤ b * z.2 ∧ z.1 ≤ 0 := by
  simp only [verticalHalf, closedHalfDisk, Set.mem_ofPred_eq, euclideanDistSq, det2, vec,
    midpoint, A, C, sub_zero, zero_add, zero_mul, zero_sub, zero_div, neg_nonneg,
    mul_nonpos_iff, hb.not_ge, hb.le]
  apply and_congr
  · constructor <;> intro h <;> nlinarith only [h]
  · simp

private lemma mem_hypotenuse (a b : ℝ) (z : Plane) :
    z ∈ hypotenuseSemidisk a b ↔
      z.1 ^ 2 + z.2 ^ 2 ≤ a * z.1 + b * z.2 ∧ b * z.1 + a * z.2 ≤ a * b := by
  simp only [hypotenuseSemidisk, closedHalfDisk, Set.mem_ofPred_eq, euclideanDistSq, det2,
    vec, midpoint, B, C, sub_zero, zero_add, add_zero, zero_sub]
  constructor <;> rintro ⟨h, k⟩ <;> constructor <;> nlinarith only [h, k]

private lemma mem_rightTriangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : Plane) :
    z ∈ rightTriangle a b ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ b * z.1 + a * z.2 ≤ a * b := by
  let region : Set Plane := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ b * x.1 + a * x.2 ≤ a * b}
  change z ∈ convexHull ℝ _ ↔ z ∈ region
  constructor
  · apply convexHull_min
    · rintro _ (rfl | rfl | h) <;> simp_all [region, A, B, C, ha.le, hb.le, mul_comm,
        mul_nonneg ha.le hb.le]
    · intro x hx y hy s t hs ht hst
      obtain ⟨hx₁, hx₂, hx₃⟩ := hx
      obtain ⟨hy₁, hy₂, hy₃⟩ := hy
      change 0 ≤ s * x.1 + t * y.1 ∧ 0 ≤ s * x.2 + t * y.2 ∧
        b * (s * x.1 + t * y.1) + a * (s * x.2 + t * y.2) ≤ a * b
      refine ⟨by positivity, by positivity, ?_⟩
      calc
        _ = s * (b * x.1 + a * x.2) + t * (b * y.1 + a * y.2) := by ring
        _ ≤ s * (a * b) + t * (a * b) := by gcongr
        _ = a * b := by rw [← add_mul, hst, one_mul]
  · rintro ⟨hx, hy, hxy⟩
    let w : Fin 3 → ℝ := ![1 - z.1 / a - z.2 / b, z.1 / a, z.2 / b]
    apply mem_convexHull_of_exists_fintype w ![A, B a, C b]
    · intro i
      fin_cases i
      · change 0 ≤ 1 - z.1 / a - z.2 / b
        rw [sub_nonneg]
        field_simp [ha, hb]
        nlinarith only [hxy]
      · exact div_nonneg hx ha.le
      · exact div_nonneg hy hb.le
    · simp [Fin.sum_univ_succ, w]
    · intro i
      fin_cases i <;> simp
    · ext <;> simp [Fin.sum_univ_succ, w, A, B, C, ha.ne', hb.ne']

private lemma measurable_halfDisk (p q : Plane) {side : ℝ → Prop}
    (hs : MeasurableSet {t | side t}) : MeasurableSet (closedHalfDisk p q side) := by
  change MeasurableSet ({x | euclideanDistSq x (midpoint p q) ≤ euclideanDistSq p q / 4} ∩
    (fun x ↦ det2 (vec p q) (vec p x)) ⁻¹' {t | side t})
  apply MeasurableSet.inter
  · apply measurableSet_le <;> unfold euclideanDistSq <;> fun_prop
  · apply hs.preimage
    unfold det2 vec
    fun_prop

private lemma horizontalHalf_reverse (a : ℝ) :
    horizontalHalf a = closedHalfDisk (B a) A (0 ≤ ·) := by
  ext z
  simp [horizontalHalf, closedHalfDisk, A, B, midpoint, det2, vec, euclideanDistSq]

private lemma halfDisk_areas {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalHalf a) + volume (verticalHalf b) = volume (hypotenuseSemidisk a b) ∧
      volume (hypotenuseSemidisk a b) ≠ ⊤ := by
  have hA : euclideanDistSq (B a) A = a ^ 2 := by simp [euclideanDistSq, A, B]
  have hB : euclideanDistSq A (C b) = b ^ 2 := by simp [euclideanDistSq, A, C]
  have hC : euclideanDistSq (B a) (C b) = a ^ 2 + b ^ 2 := by simp [euclideanDistSq, B, C]
  rw [horizontalHalf_reverse, verticalHalf, hypotenuseSemidisk,
    volume_leftHalfDisk _ _ (hA ▸ by positivity), volume_leftHalfDisk _ _ (hB ▸ by positivity),
    volume_leftHalfDisk _ _ (hC ▸ by positivity), hA, hB, hC,
    ENNReal.ofReal_add (sq_nonneg a) (sq_nonneg b), add_mul]
  exact ⟨rfl, ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitHalfDisk_finite,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top unitHalfDisk_finite⟩⟩

private lemma ae_off_axes : ∀ᵐ z : Plane, z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  exact (Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0 : ℝ))).and
    (Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne (0 : ℝ)))

private lemma legs_aeDisjoint {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    AEDisjoint volume (horizontalHalf a) (verticalHalf b) := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_off_axes] with z hz
  rintro ⟨hh, hv⟩
  have h := ((mem_horizontalHalf ha z).mp hh).1
  have k := ((mem_verticalHalf hb z).mp hv).2
  linarith [mul_neg_of_pos_of_neg ha (lt_of_le_of_ne k hz.1), sq_nonneg z.1, sq_nonneg z.2]

/-- Away from the axes, removing the leg half-disks from the hypotenuse half-disk leaves
exactly the triangle. -/
private lemma triangle_ae_sdiff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    hypotenuseSemidisk a b \ (horizontalHalf a ∪ verticalHalf b) =ᵐ[volume] rightTriangle a b := by
  filter_upwards [ae_off_axes] with z hz
  rw [Set.mem_sdiff, Set.mem_union, mem_rightTriangle ha hb, mem_hypotenuse,
    mem_horizontalHalf ha, mem_verticalHalf hb]
  constructor
  · rintro ⟨⟨hd, hs⟩, h⟩
    refine ⟨?_, ?_, hs⟩
    · by_contra! hx
      exact h (.inr ⟨by linarith [mul_neg_of_pos_of_neg ha hx], hx.le⟩)
    · by_contra! hy
      exact h (.inl ⟨by linarith [mul_neg_of_pos_of_neg hb hy], hy.le⟩)
  · rintro ⟨hx, hy, hs⟩
    have hxa : z.1 ≤ a := (mul_le_mul_iff_right₀ hb).mp (by nlinarith [mul_nonneg ha.le hy])
    have hyb : z.2 ≤ b := (mul_le_mul_iff_right₀ ha).mp (by nlinarith [mul_nonneg hb.le hx])
    refine ⟨⟨?_, hs⟩, ?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hxa) hx, mul_nonneg (sub_nonneg.mpr hyb) hy]
    · rintro (hh | hv)
      · exact hz.2 (le_antisymm hh.2 hy)
      · exact hz.1 (le_antisymm hv.2 hx)

set_option linter.dupNamespace false in
/-- **Hippocrates' theorem on lunes.** Let $a, b > 0$ and consider the right triangle with
vertices $A = (0, 0)$, $B = (a, 0)$ and $C = (0, b)$. The Lebesgue measure of the lune on the
horizontal leg plus the Lebesgue measure of the lune on the vertical leg equals the Lebesgue
measure of the triangle, that is, of the convex hull of $A$, $B$ and $C$.

Source: Hippocrates of Chios (c. 440 BC). Knill, §166. Via leanprover/lean-eval@38361be,
problem `hippocrates_lunes`. -/
public theorem hippocrates_lunes (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b) := by
  have hH : MeasurableSet (horizontalHalf a) := measurable_halfDisk _ _ measurableSet_Iic
  have hV : MeasurableSet (verticalHalf b) := measurable_halfDisk _ _ measurableSet_Ici
  have hD : MeasurableSet (hypotenuseSemidisk a b) := measurable_halfDisk _ _ measurableSet_Ici
  have hd := legs_aeDisjoint ha hb
  obtain ⟨hareas, hfin⟩ := halfDisk_areas ha hb
  have heq : volume (horizontalHalf a ∪ verticalHalf b) = volume (hypotenuseSemidisk a b) :=
    (measure_union₀ hV.nullMeasurableSet hd).trans hareas
  rw [← measure_congr (triangle_ae_sdiff ha hb), horizontalLune, verticalLune,
    ← measure_union₀ (hV.diff hD).nullMeasurableSet (hd.mono sdiff_subset sdiff_subset),
    ← union_sdiff_distrib, measure_sdiff' _ hD.nullMeasurableSet hfin,
    measure_sdiff' _ (hH.union hV).nullMeasurableSet (heq ▸ hfin), heq, union_comm]

end Geometry.HippocratesLunes
end MathlibExt.Geometry.HippocratesLunesWanted
