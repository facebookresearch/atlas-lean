/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open EuclideanGeometry Real

section
namespace MetaMathlibExt

/-- Algebra core: given the cyclic diagonal constraint, the sum of the two Heron
areas over the diagonal equals the Brahmagupta area. -/
private theorem heron_sum (a b c d e s : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hC : e ^ 2 * (a * b + c * d) = (a * c + b * d) * (a * d + b * c))
    (hs : s = (a + b + c + d) / 2) :
    Real.sqrt (((a+b+e)/2) * (((a+b+e)/2) - a) * (((a+b+e)/2) - b) * (((a+b+e)/2) - e))
      + Real.sqrt (((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e))
      = Real.sqrt ((s-a) * (s-b) * (s-c) * (s-d)) := by
  set cQ := (a^2 + b^2 - e^2) / (2*a*b) with hcQ
  set cS := (c^2 + d^2 - e^2) / (2*c*d) with hcS
  have hab : (0:ℝ) < a*b := mul_pos ha hb
  have hcd : (0:ℝ) < c*d := mul_pos hc hd
  have hsign : cS = -cQ := by
    rw [hcS, hcQ]; field_simp; linear_combination -hC
  have hesq : e^2 = (a*c + b*d) * (a*d + b*c) / (a*b + c*d) := by
    field_simp; linear_combination hC
  have hH1 : ((a+b+e)/2) * (((a+b+e)/2) - a) * (((a+b+e)/2) - b) * (((a+b+e)/2) - e)
      = (a*b/2)^2 * (1 - cQ^2) := by
    rw [hcQ]; field_simp; ring
  have hH2 : ((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e)
      = (c*d/2)^2 * (1 - cQ^2) := by
    have hH2' : ((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e)
        = (c*d/2)^2 * (1 - cS^2) := by rw [hcS]; field_simp; ring
    rw [hH2', hsign]; ring
  have hcQ2 : cQ^2 = (a^2 + b^2 - e^2)^2 / (2*a*b)^2 := by rw [hcQ]; ring
  have hK : (s-a) * (s-b) * (s-c) * (s-d) = ((a*b + c*d)/2)^2 * (1 - cQ^2) := by
    rw [hcQ2, hs, hesq]; field_simp; ring
  rw [hH1, hH2, hK]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- Geometry core: for a convex cyclic quadrilateral (all sides positive) the diagonal
`e` satisfies the cyclic constraint `e² (ab + cd) = (ac + bd)(ad + bc)`. -/
private theorem hC_pos (P Q R S T : EuclideanSpace ℝ (Fin 2)) (a b c d e : ℝ)
    (hcosph : Cospherical ({P, Q, R, S} : Set (EuclideanSpace ℝ (Fin 2))))
    (hPTR : Sbtw ℝ P T R) (hQTS : Sbtw ℝ Q T S)
    (hPQ : dist P Q = a) (hQR : dist Q R = b) (hRS : dist R S = c) (hSP : dist S P = d)
    (hPR : dist P R = e)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    e^2 * (a*b + c*d) = (a*c + b*d) * (a*d + b*c) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  have : Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
    ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation⟩
  have hPneQ : P ≠ Q := by intro h; rw [h, dist_self] at hPQ; linarith
  have hQneR : Q ≠ R := by intro h; rw [h, dist_self] at hQR; linarith
  have hRneS : R ≠ S := by intro h; rw [h, dist_self] at hRS; linarith
  have hSneP : S ≠ P := by intro h; rw [h, dist_self] at hSP; linarith
  have hPneR : P ≠ R := hPTR.left_ne_right
  have s1a : (∡ P Q T).sign = (∡ P Q R).sign := hPTR.oangle_sign_eq_left Q
  have s1b : ∡ P Q T = ∡ P Q S := hQTS.wbtw.oangle_eq_right hQTS.ne_left
  have s1c : (∡ P Q S).sign = (∡ P R S).sign := hPTR.oangle_sign_eq_of_sbtw hQTS.symm
  have hs1 : (∡ P Q R).sign = (∡ P R S).sign := by rw [← s1a, s1b]; exact s1c
  have s2a : (∡ P S T).sign = (∡ P S R).sign := hPTR.oangle_sign_eq_left S
  have s2b : ∡ P S T = ∡ P S Q := hQTS.symm.wbtw.oangle_eq_right hQTS.symm.ne_left
  have s2c : (∡ P S Q).sign = (∡ P R Q).sign := hPTR.oangle_sign_eq_of_sbtw hQTS
  have hs2 : (∡ P S R).sign = (∡ P R Q).sign := by rw [← s2a, s2b]; exact s2c
  have star : (∡ Q R T).sign = (∡ T R S).sign := hQTS.oangle_sign_eq R
  have qrt : ∡ Q R T = ∡ Q R P := hPTR.symm.wbtw.oangle_eq_right hPTR.symm.ne_left
  have trs : ∡ T R S = ∡ P R S := hPTR.symm.wbtw.oangle_eq_left hPTR.symm.ne_left
  have hstar : (∡ Q R P).sign = (∡ P R S).sign := by rw [← qrt, star, trs]
  have hrev : (∡ Q R P).sign = -(∡ P R Q).sign := by
    rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg]
  have hkey : (∡ P R S).sign = -(∡ P R Q).sign := hstar.symm.trans hrev
  have hsgn : (∡ P Q R).sign = -(∡ P S R).sign := by rw [hs1, hkey, hs2]
  have hai : AffineIndependent ℝ ![P, Q, R] :=
    hcosph.affineIndependent_of_mem_of_ne (by simp) (by simp) (by simp) hPneQ hPneR hQneR
  have hncol : ¬Collinear ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineIndependent_iff_not_collinear_set.mp hai
  have hnz : (∡ P Q R).sign ≠ 0 := fun h =>
    hncol (oangle_sign_eq_zero_iff_collinear.mp h)
  have hco : Cospherical ({P, Q, S, R} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [Set.pair_comm S R]; exact hcosph
  have hIA : (2 : ℤ) • ∡ P Q R = (2 : ℤ) • ∡ P S R :=
    hco.two_zsmul_oangle_eq hPneQ.symm hQneR hSneP hRneS.symm
  have hpi : ∡ P Q R = ∡ P S R + ↑π := by
    rcases Real.Angle.two_zsmul_eq_iff.mp hIA with h | h
    · exfalso
      have hs : (∡ P Q R).sign = (∡ P S R).sign := by rw [h]
      rw [hsgn] at hs
      have kkey : ∀ x : SignType, -x = x → x = 0 := by decide
      have h0 := kkey _ hs
      rw [h] at hnz
      exact hnz h0
    · exact h
  have hcos : Real.cos (∠ P Q R) = -Real.cos (∠ P S R) := by
    rw [← cos_oangle_eq_cos_angle hPneQ hQneR.symm,
        ← cos_oangle_eq_cos_angle hSneP.symm hRneS, hpi, Real.Angle.cos_add_pi]
  have hlc1 : e * e = a * a + b * b - 2 * a * b * Real.cos (∠ P Q R) := by
    have h := EuclideanGeometry.law_cos P Q R
    rw [hPR, hPQ, dist_comm R Q, hQR] at h; linarith [h]
  have hlc2 : e * e = d * d + c * c - 2 * d * c * Real.cos (∠ P S R) := by
    have h := EuclideanGeometry.law_cos P S R
    rw [hPR, dist_comm P S, hSP, hRS] at h; linarith [h]
  linear_combination (c * d) * hlc1 + (a * b) * hlc2 - 2 * a * b * c * d * hcos

/-- **Brahmagupta's formula.** Let $P, Q, R, S$ be points of the Euclidean plane with side
lengths $|PQ| = a$, $|QR| = b$, $|RS| = c$, $|SP| = d$ and diagonal $|PR| = e$, and let
$s = (a + b + c + d)/2$. Suppose that some point $O$ is equidistant from $P, Q, R, S$ (so the
quadrilateral $PQRS$ is cyclic) and that some point $T$ satisfies $|PT| + |TR| = |PR|$ and
$|QT| + |TS| = |QS|$ with $|PT|, |TR|, |QT|, |TS| > 0$ (so $T$ lies strictly inside both
diagonals and $PQRS$ is convex). Let $p = (a + b + e)/2$ and $q = (c + d + e)/2$, and let $A$ be
the sum of the Heron areas of the triangles $PQR$ and $RSP$:

$$A = \sqrt{p(p - a)(p - b)(p - e)} + \sqrt{q(q - c)(q - d)(q - e)}.$$

Then $A = \sqrt{(s - a)(s - b)(s - c)(s - d)}$.

Proves `Wanted` entry `brahmagupta_area`.

Source: https://en.wikipedia.org/wiki/Brahmagupta%27s_formula
-/
theorem brahmagupta_area (a b c d s A e : ℝ)
    (P Q R S : EuclideanSpace ℝ (Fin 2))
    (h_sides : dist P Q = a ∧ dist Q R = b ∧ dist R S = c ∧ dist S P = d)
    (h_diag : dist P R = e)
    (h_semi : s = (a + b + c + d) / 2)
    (h_cyclic : ∃ O : EuclideanSpace ℝ (Fin 2),
      dist O P = dist O Q ∧ dist O Q = dist O R ∧ dist O R = dist O S)
    (h_convex : ∃ T : EuclideanSpace ℝ (Fin 2),
      dist P T + dist T R = dist P R ∧ dist Q T + dist T S = dist Q S ∧
      0 < dist P T ∧ 0 < dist T R ∧ 0 < dist Q T ∧ 0 < dist T S)
    (h_area : A = Real.sqrt (((a + b + e) / 2) * (((a + b + e) / 2) - a) *
        (((a + b + e) / 2) - b) * (((a + b + e) / 2) - e)) +
      Real.sqrt (((c + d + e) / 2) * (((c + d + e) / 2) - c) *
        (((c + d + e) / 2) - d) * (((c + d + e) / 2) - e)))
    : A = Real.sqrt ((s - a) * (s - b) * (s - c) * (s - d)) := by
  obtain ⟨hPQ, hQR, hRS, hSP⟩ := h_sides
  obtain ⟨O, hOPQ, hOQR, hORS⟩ := h_cyclic
  obtain ⟨T, hPTRadd, hQTSadd, hPTpos, hTRpos, hQTpos, hTSpos⟩ := h_convex
  have hcosph : Cospherical ({P, Q, R, S} : Set (EuclideanSpace ℝ (Fin 2))) := by
    refine ⟨O, dist P O, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · rw [dist_comm x O, ← hOPQ, dist_comm O P]
    · rw [dist_comm x O, ← hOQR, ← hOPQ, dist_comm O P]
    · rw [dist_comm x O, ← hORS, ← hOQR, ← hOPQ, dist_comm O P]
  have hTneP : T ≠ P := by intro h; rw [h, dist_self] at hPTpos; exact lt_irrefl _ hPTpos
  have hTneR : T ≠ R := by intro h; rw [h, dist_self] at hTRpos; exact lt_irrefl _ hTRpos
  have hTneQ : T ≠ Q := by intro h; rw [h, dist_self] at hQTpos; exact lt_irrefl _ hQTpos
  have hTneS : T ≠ S := by intro h; rw [h, dist_self] at hTSpos; exact lt_irrefl _ hTSpos
  have hPTR : Sbtw ℝ P T R := ⟨dist_add_dist_eq_iff.mp hPTRadd, hTneP, hTneR⟩
  have hQTS : Sbtw ℝ Q T S := ⟨dist_add_dist_eq_iff.mp hQTSadd, hTneQ, hTneS⟩
  rw [h_area]
  by_cases ha0 : a = 0
  · have hPeqQ : P = Q := dist_eq_zero.mp (hPQ.trans ha0)
    have hbe : b = e := by rw [← hQR, ← hPeqQ, h_diag]
    have hE1 : ((a+b+e)/2) * (((a+b+e)/2) - a) * (((a+b+e)/2) - b) * (((a+b+e)/2) - e) = 0 := by
      rw [ha0, hbe]; ring
    have hEK : ((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e)
        = (s-a) * (s-b) * (s-c) * (s-d) := by rw [h_semi, ha0, hbe]; ring
    rw [hE1, Real.sqrt_zero, zero_add, hEK]
  by_cases hb0 : b = 0
  · have hQeqR : Q = R := dist_eq_zero.mp (hQR.trans hb0)
    have hae : a = e := by rw [← hPQ, hQeqR, h_diag]
    have hE1 : ((a+b+e)/2) * (((a+b+e)/2) - a) * (((a+b+e)/2) - b) * (((a+b+e)/2) - e) = 0 := by
      rw [hb0, hae]; ring
    have hEK : ((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e)
        = (s-a) * (s-b) * (s-c) * (s-d) := by rw [h_semi, hb0, hae]; ring
    rw [hE1, Real.sqrt_zero, zero_add, hEK]
  by_cases hc0 : c = 0
  · have hReqS : R = S := dist_eq_zero.mp (hRS.trans hc0)
    have hde : d = e := by rw [← hSP, ← hReqS, dist_comm R P, h_diag]
    have hE2 : ((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e) = 0 := by
      rw [hc0, hde]; ring
    have hEK : ((a+b+e)/2) * (((a+b+e)/2) - a) * (((a+b+e)/2) - b) * (((a+b+e)/2) - e)
        = (s-a) * (s-b) * (s-c) * (s-d) := by rw [h_semi, hc0, hde]; ring
    rw [hE2, Real.sqrt_zero, add_zero, hEK]
  by_cases hd0 : d = 0
  · have hSeqP : S = P := dist_eq_zero.mp (hSP.trans hd0)
    have hce : c = e := by rw [← hRS, hSeqP, dist_comm R P, h_diag]
    have hE2 : ((c+d+e)/2) * (((c+d+e)/2) - c) * (((c+d+e)/2) - d) * (((c+d+e)/2) - e) = 0 := by
      rw [hd0, hce]; ring
    have hEK : ((a+b+e)/2) * (((a+b+e)/2) - a) * (((a+b+e)/2) - b) * (((a+b+e)/2) - e)
        = (s-a) * (s-b) * (s-c) * (s-d) := by rw [h_semi, hd0, hce]; ring
    rw [hE2, Real.sqrt_zero, add_zero, hEK]
  -- All sides positive.
  have ha : 0 < a := lt_of_le_of_ne (hPQ ▸ dist_nonneg) (Ne.symm ha0)
  have hb : 0 < b := lt_of_le_of_ne (hQR ▸ dist_nonneg) (Ne.symm hb0)
  have hc : 0 < c := lt_of_le_of_ne (hRS ▸ dist_nonneg) (Ne.symm hc0)
  have hd : 0 < d := lt_of_le_of_ne (hSP ▸ dist_nonneg) (Ne.symm hd0)
  have hC := hC_pos P Q R S T a b c d e hcosph hPTR hQTS hPQ hQR hRS hSP h_diag ha hb hc hd
  exact heron_sum a b c d e s ha hb hc hd hC h_semi

end MetaMathlibExt
