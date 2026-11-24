/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/Morley.lean` (leanprover/lean-eval), problem `morley_theorem`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest `manifests/problems/morley_theorem.toml`,
rev 1, submitter Kim Morrison, status archived).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
You may not use these portions except in compliance with the License.
Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

The adapted portions are the plane, equilateral-triple, closed-triangle and Morley configuration
definitions and the statement of Morley's theorem. ATLAS first moved them into the
`MathlibExt.Geometry.MorleyWanted` namespace and stated the result with Batteries' proof-wanted
command. ATLAS subsequently proved the theorem and moved these declarations from
`WantedExt/Geometry/MorleyWanted.lean` with their names, statements and docstrings intact.
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Morley's trisector theorem

The intersections of adjacent internal angle trisectors of a nondegenerate Euclidean triangle
form an equilateral triangle. The proof uses the laws of sines and cosines to compute its side
lengths.
-/

@[expose] public section

namespace MathlibExt.Geometry.MorleyWanted
namespace Geometry.Morley

open scoped EuclideanGeometry

set_option linter.dupNamespace false in
/-- **Euclidean plane for Morley's theorem.** The Euclidean plane $\mathbb{R}^2$ with its
standard Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

set_option linter.dupNamespace false in
/-- **Equilateral triple of points.** Three points $P$, $Q$, $R$ of the Euclidean plane form an
equilateral triple when, writing $d$ for the Euclidean distance, $d(P, Q) = d(Q, R)$ and
$d(Q, R) = d(R, P)$. Coincident points are allowed, so $P = Q = R$ qualifies. -/
def IsEquilateralTriple (P Q R : Plane) : Prop :=
  dist P Q = dist Q R ∧ dist Q R = dist R P

set_option linter.dupNamespace false in
/-- **Point in a closed triangle.** A point $X$ of the Euclidean plane lies in the triangle with
vertices $A$, $B$, $C$ when $X$ belongs to the convex hull of $\{A, B, C\}$, the closed triangle
$ABC$ (a segment or a point when $A$, $B$, $C$ are collinear). -/
def LiesInTriangle (A B C X : Plane) : Prop :=
  X ∈ convexHull ℝ ({A, B, C} : Set Plane)

set_option linter.dupNamespace false in
/-- **Morley configuration.** Points $A$, $B$, $C$, $P$, $Q$, $R$ of the Euclidean plane form a
Morley configuration when $A$, $B$, $C$ are not collinear, each of $P$, $Q$, $R$ lies in the
closed triangle $ABC$, and, writing $\angle XYZ \in [0, \pi]$ for the unoriented angle at $Y$,
$0 < \angle CAR = \angle RAP = \angle PAB$ and $3 \angle PAB = \angle CAB$;
$0 < \angle ABP = \angle PBQ = \angle QBC$ and $3 \angle QBC = \angle ABC$;
$0 < \angle BCQ = \angle QCR = \angle RCA$ and $3 \angle RCA = \angle BCA$.
Thus $P$, $Q$, $R$ are the intersections of adjacent angle trisectors of the triangle $ABC$. -/
def IsMorleyConfiguration (A B C P Q R : Plane) : Prop :=
  ¬ Collinear ℝ ({A, B, C} : Set Plane) ∧
  LiesInTriangle A B C P ∧ LiesInTriangle A B C Q ∧ LiesInTriangle A B C R ∧
  0 < (∠ C A R) ∧ (∠ C A R) = (∠ R A P) ∧ (∠ R A P) = (∠ P A B) ∧
  3 * (∠ P A B) = (∠ C A B) ∧
  0 < (∠ A B P) ∧ (∠ A B P) = (∠ P B Q) ∧ (∠ P B Q) = (∠ Q B C) ∧
  3 * (∠ Q B C) = (∠ A B C) ∧
  0 < (∠ B C Q) ∧ (∠ B C Q) = (∠ Q C R) ∧ (∠ Q C R) = (∠ R C A) ∧
  3 * (∠ R C A) = (∠ B C A)

open Real EuclideanGeometry

/-- Factor the triple-angle sine with the sine of the sum of the other two trisector angles. -/
private lemma sin_three_mul_factor (x : ℝ) :
    sin (3 * x) = 4 * sin x * sin (π / 3 + x) * sin (π / 3 - x) := by
  have h := two_mul_sin_mul_sin (π / 3 + x) (π / 3 - x)
  rw [show π / 3 + x - (π / 3 - x) = 2 * x by ring,
    show π / 3 + x + (π / 3 - x) = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three,
    cos_two_mul_eq_one_sub] at h
  rw [sin_three_mul]
  linear_combination -2 * sin x * h

private lemma sin_add_sq (u v : ℝ) :
    sin u ^ 2 + sin v ^ 2 + 2 * sin u * sin v * cos (u + v) = sin (u + v) ^ 2 := by
  rw [cos_add, sin_add]
  linear_combination -sin u ^ 2 * sin_sq_add_cos_sq v - sin v ^ 2 * sin_sq_add_cos_sq u

/-- Apply the sine law in the triangle built on one side of the original triangle. -/
private lemma dist_to_trisector {A B P : Plane} {a b c D : ℝ} (hBA : B ≠ A)
    (ha : ∠ P A B = a) (hb : ∠ A B P = b) (hsum : a + b + c = π / 3)
    (ha₀ : 0 < a) (hb₀ : 0 < b) (hc₀ : 0 < c) (hAB : dist A B = D * sin (3 * c)) :
    dist P A = 4 * D * sin b * sin c * sin (π / 3 + c) := by
  have hAPB : ∠ A P B = π - (a + b) := by
    have h := angle_add_angle_add_angle_eq_pi P hBA
    rw [angle_comm B P A, ha, hb] at h
    linarith
  have hsin : sin (a + b) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])).ne'
  have h := law_sin P B A
  rw [angle_comm P B A, hb, hAPB, sin_pi_sub, dist_comm B A, dist_comm A P,
    hAB, sin_three_mul_factor c, show π / 3 - c = a + b by linarith] at h
  apply mul_left_cancel₀ hsin
  linear_combination -h

/-- Use the cosine law across the middle trisector angle at one outer vertex. -/
private lemma dist_across_vertex {A B C P R : Plane} {a b c D : ℝ}
    (hBA : B ≠ A) (hCA : C ≠ A) (hsum : a + b + c = π / 3)
    (ha₀ : 0 < a) (hb₀ : 0 < b) (hc₀ : 0 < c) (hD : 0 ≤ D)
    (hAB : dist A B = D * sin (3 * c)) (hAC : dist A C = D * sin (3 * b))
    (hPAB : ∠ P A B = a) (hABP : ∠ A B P = b)
    (hRAC : ∠ R A C = a) (hACR : ∠ A C R = c) (hPAR : ∠ P A R = a) :
    dist P R = 4 * D * sin a * sin b * sin c := by
  let s := 4 * D * sin b * sin c
  let u := π / 3 + c
  let v := π / 3 + b
  have hp : dist P A = s * sin u :=
    dist_to_trisector hBA hPAB hABP hsum ha₀ hb₀ hc₀ hAB
  have hr : dist R A = s * sin v := by
    rw [show s = 4 * D * sin c * sin b by dsimp [s]; ring]
    exact dist_to_trisector hCA hRAC hACR (by linarith) ha₀ hc₀ hb₀ hAC
  have huv : u + v = π - a := by dsimp [u, v]; linarith
  have hcos : cos a = -cos (u + v) := by rw [huv, cos_pi_sub, neg_neg]
  have hsin_a := (sin_pos_of_pos_of_lt_pi ha₀ (by linarith [Real.pi_pos])).le
  have hsin_b := (sin_pos_of_pos_of_lt_pi hb₀ (by linarith [Real.pi_pos])).le
  have hsin_c := (sin_pos_of_pos_of_lt_pi hc₀ (by linarith [Real.pi_pos])).le
  have hnonneg : 0 ≤ 4 * D * sin a * sin b * sin c := by positivity
  have h := law_cos P A R
  rw [hp, hr, hPAR, hcos] at h
  apply (sq_eq_sq₀ dist_nonneg hnonneg).mp
  calc
    dist P R ^ 2 = s ^ 2 * (sin u ^ 2 + sin v ^ 2 + 2 * sin u * sin v * cos (u + v)) := by
      linear_combination h
    _ = (4 * D * sin a * sin b * sin c) ^ 2 := by
      rw [sin_add_sq, huv, sin_pi_sub]
      dsimp [s]
      ring

set_option linter.dupNamespace false in
/-- **Morley's trisector theorem.** If points $A$, $B$, $C$, $P$, $Q$, $R$ of the Euclidean plane
form a Morley configuration, so that $ABC$ is a nondegenerate triangle and $P$, $Q$, $R$ are the
intersections of its adjacent angle trisectors, then $P$, $Q$, $R$ form an equilateral triple:
writing $d$ for the Euclidean distance, $d(P, Q) = d(Q, R)$ and $d(Q, R) = d(R, P)$.

Source: F. Morley (c. 1899). Knill, §162. Via leanprover/lean-eval@38361be, problem
`morley_theorem`. -/
theorem morley_theorem (A B C P Q R : Plane)
    (h : IsMorleyConfiguration A B C P Q R) :
    IsEquilateralTriple P Q R := by
  rcases h with ⟨hnc, _, _, _, hposA, hCAR, hRAP, hCAB, hposB, hABP, hPBQ, hABC,
    hposC, hBCQ, hQCR, hBCA⟩
  let a := ∠ P A B
  let b := ∠ Q B C
  let c := ∠ R C A
  change 3 * a = ∠ C A B at hCAB
  change 3 * b = ∠ A B C at hABC
  change 3 * c = ∠ B C A at hBCA
  have ha₀ : 0 < a := by simpa only [a, ← hRAP, ← hCAR] using hposA
  have hb₀ : 0 < b := by simpa only [b, ← hPBQ, ← hABP] using hposB
  have hc₀ : 0 < c := by simpa only [c, ← hQCR, ← hBCQ] using hposC
  have hAB := ne₁₂_of_not_collinear hnc
  have hBC := ne₂₃_of_not_collinear hnc
  have hCA := (ne₁₃_of_not_collinear hnc).symm
  have hsum : a + b + c = π / 3 := by
    have h := angle_add_angle_add_angle_eq_pi C hAB.symm
    rw [← hCAB, ← hABC, ← hBCA] at h
    linarith
  have hsinC := sin_pos_of_pos_of_lt_pi (show 0 < 3 * c by positivity) (by linarith [hsum])
  let D := dist A B / sin (3 * c)
  have hD : 0 ≤ D := div_nonneg dist_nonneg hsinC.le
  -- Normalize all three outer sides by the same ratio of a side to the sine opposite it.
  have hab : dist A B = D * sin (3 * c) := (div_mul_cancel₀ _ hsinC.ne').symm
  have hca : dist C A = D * sin (3 * b) := by
    have h := law_sin B C A
    rw [← hBCA, ← hABC, hab] at h
    exact mul_left_cancel₀ hsinC.ne' (by linear_combination h)
  have hbc : dist B C = D * sin (3 * a) := by
    have h := law_sin A C B
    rw [angle_comm A C B, angle_comm B A C, ← hBCA, ← hCAB, dist_comm C B,
      dist_comm B A, hab] at h
    exact mul_left_cancel₀ hsinC.ne' (by linear_combination h)
  -- Apply the same side calculation at each outer vertex.
  have hPR := dist_across_vertex hAB.symm hCA hsum ha₀ hb₀ hc₀ hD hab
    ((dist_comm A C).trans hca) rfl (hABP.trans hPBQ)
    ((angle_comm R A C).trans (hCAR.trans hRAP)) (angle_comm A C R)
    ((angle_comm P A R).trans hRAP)
  have hQP := dist_across_vertex hBC.symm hAB (by linarith) hb₀ hc₀ ha₀ hD hbc
    ((dist_comm B A).trans hab) rfl (hBCQ.trans hQCR)
    ((angle_comm P B A).trans (hABP.trans hPBQ)) (angle_comm B A P)
    ((angle_comm Q B P).trans hPBQ)
  have hRQ := dist_across_vertex hCA.symm hBC (by linarith) hc₀ ha₀ hb₀ hD hca
    ((dist_comm C B).trans hbc) rfl (hCAR.trans hRAP)
    ((angle_comm Q C B).trans (hBCQ.trans hQCR)) (angle_comm C B Q)
    ((angle_comm R C Q).trans hQCR)
  refine ⟨?_, ?_⟩
  · rw [dist_comm P Q, dist_comm Q R, hQP, hRQ]
    ring
  · rw [dist_comm Q R, dist_comm R P, hRQ, hPR]
    ring

end Geometry.Morley

end MathlibExt.Geometry.MorleyWanted
