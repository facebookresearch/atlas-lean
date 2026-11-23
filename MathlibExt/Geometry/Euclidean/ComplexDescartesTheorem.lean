/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The complex Descartes theorem

For four mutually tangent circles in the plane `ℂ` with signed curvatures `kᵢ` and centers `cᵢ`,
the products `kᵢ cᵢ` satisfy the Descartes relation `(∑ kᵢ cᵢ)² = 2 ∑ (kᵢ cᵢ)²` (Lagarias, Mallows
and Wilks, *Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002),
arXiv:math/0101066v1, Theorem 2.1).

Proof. Put `uⱼ = cⱼ - c₀` and let `pⱼₗ = ⟨uⱼ, uₗ⟩` be the real inner products, which the
tangency conditions determine in terms of the signed radii `sᵢ = 1/kᵢ`. The Gram determinant of
the three plane vectors `u₁, u₂, u₃` vanishes; in terms of the radii this is the Descartes relation
for the curvatures. The complex number `F₀ = (∑ⱼ kⱼ uⱼ)² - 2 ∑ⱼ (kⱼ uⱼ)²` has `|F₀|²` equal to a
polynomial in the `pⱼₗ` (by the identity `(a × b)(c × d) = (a·c)(b·d) - (a·d)(b·c)` in the plane),
and substituting the radii shows `|F₀|² = 0`; likewise `G = (∑ kᵢ)(∑ⱼ kⱼ uⱼ) - 2 ∑ⱼ kⱼ² uⱼ` has
`|G|² = 0`. Finally `(∑ kᵢ cᵢ)² - 2 ∑ (kᵢ cᵢ)² = F₀ + 2 c₀ G + c₀² ((∑ kᵢ)² - 2 ∑ kᵢ²) = 0`.
-/

@[expose] public section

namespace MathlibExt.Geometry.Euclidean.ComplexDescartesTheorem

open Complex

/-- The polynomial in the inner products `pⱼₗ` equal to `|F₀|²`. -/
private def phi (p11 p12 p13 p22 p23 p33 k1 k2 k3 : ℝ) : ℝ :=
  k1^4*p11^2 - 4*k1^3*k2*p11*p12 - 4*k1^3*k3*p11*p13 + 2*k1^2*k2^2*p11*p22 + 4*k1^2*k2^2*p12^2 +
  12*k1^2*k2*k3*p11*p23 - 8*k1^2*k2*k3*p12*p13 + 2*k1^2*k3^2*p11*p33 + 4*k1^2*k3^2*p13^2 -
  4*k1*k2^3*p12*p22 - 8*k1*k2^2*k3*p12*p23 + 12*k1*k2^2*k3*p13*p22 + 12*k1*k2*k3^2*p12*p33 -
  8*k1*k2*k3^2*p13*p23 - 4*k1*k3^3*p13*p33 + k2^4*p22^2 - 4*k2^3*k3*p22*p23 + 2*k2^2*k3^2*p22*p33
  + 4*k2^2*k3^2*p23^2 - 4*k2*k3^3*p23*p33 + k3^4*p33^2

/-- The polynomial in the inner products `pⱼₗ` equal to `|G|²`. -/
private def psi (p11 p12 p13 p22 p23 p33 k0 k1 k2 k3 : ℝ) : ℝ :=
  k0^2*k1^2*p11 + 2*k0^2*k1*k2*p12 + 2*k0^2*k1*k3*p13 + k0^2*k2^2*p22 + 2*k0^2*k2*k3*p23 +
  k0^2*k3^2*p33 - 2*k0*k1^3*p11 + 2*k0*k1^2*k2*p11 + 2*k0*k1^2*k3*p11 + 2*k0*k1*k2^2*p22 +
  4*k0*k1*k2*k3*p12 + 4*k0*k1*k2*k3*p13 + 4*k0*k1*k2*k3*p23 + 2*k0*k1*k3^2*p33 - 2*k0*k2^3*p22 +
  2*k0*k2^2*k3*p22 + 2*k0*k2*k3^2*p33 - 2*k0*k3^3*p33 + k1^4*p11 - 2*k1^3*k2*p11 - 2*k1^3*k2*p12 -
  2*k1^3*k3*p11 - 2*k1^3*k3*p13 + k1^2*k2^2*p11 + 4*k1^2*k2^2*p12 + k1^2*k2^2*p22 +
  2*k1^2*k2*k3*p11 + 2*k1^2*k2*k3*p23 + k1^2*k3^2*p11 + 4*k1^2*k3^2*p13 + k1^2*k3^2*p33 -
  2*k1*k2^3*p12 - 2*k1*k2^3*p22 + 2*k1*k2^2*k3*p13 + 2*k1*k2^2*k3*p22 + 2*k1*k2*k3^2*p12 +
  2*k1*k2*k3^2*p33 - 2*k1*k3^3*p13 - 2*k1*k3^3*p33 + k2^4*p22 - 2*k2^3*k3*p22 - 2*k2^3*k3*p23 +
  k2^2*k3^2*p22 + 4*k2^2*k3^2*p23 + k2^2*k3^2*p33 - 2*k2*k3^3*p23 - 2*k2*k3^3*p33 + k3^4*p33

/-- The numerator of `(∑ 1/sᵢ)² - 2 ∑ (1/sᵢ)²` times `-1`, a symmetric polynomial in the radii. -/
private def descartesNumerator (s0 s1 s2 s3 : ℝ) : ℝ :=
  s0^2*s1^2*s2^2 - 2*s0^2*s1^2*s2*s3 + s0^2*s1^2*s3^2 - 2*s0^2*s1*s2^2*s3 - 2*s0^2*s1*s2*s3^2 +
  s0^2*s2^2*s3^2 - 2*s0*s1^2*s2^2*s3 - 2*s0*s1^2*s2*s3^2 - 2*s0*s1*s2^2*s3^2 + s1^2*s2^2*s3^2

private theorem normSq_F0 (u1 u2 u3 : ℂ) (k1 k2 k3 : ℝ) :
    normSq (((k1 : ℂ) * u1 + (k2 : ℂ) * u2 + (k3 : ℂ) * u3) ^ 2 -
        2 * (((k1 : ℂ) * u1) ^ 2 + ((k2 : ℂ) * u2) ^ 2 + ((k3 : ℂ) * u3) ^ 2)) =
      phi (u1.re * u1.re + u1.im * u1.im) (u1.re * u2.re + u1.im * u2.im)
        (u1.re * u3.re + u1.im * u3.im) (u2.re * u2.re + u2.im * u2.im)
        (u2.re * u3.re + u2.im * u3.im) (u3.re * u3.re + u3.im * u3.im) k1 k2 k3 := by
  simp only [phi, normSq_apply, pow_two, mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re,
    ofReal_im, re_ofNat, im_ofNat]
  ring

private theorem normSq_G (u1 u2 u3 : ℂ) (k0 k1 k2 k3 : ℝ) :
    normSq (((k0 : ℂ) + k1 + k2 + k3) * ((k1 : ℂ) * u1 + (k2 : ℂ) * u2 + (k3 : ℂ) * u3) -
        2 * ((k1 : ℂ) ^ 2 * u1 + (k2 : ℂ) ^ 2 * u2 + (k3 : ℂ) ^ 2 * u3)) =
      psi (u1.re * u1.re + u1.im * u1.im) (u1.re * u2.re + u1.im * u2.im)
        (u1.re * u3.re + u1.im * u3.im) (u2.re * u2.re + u2.im * u2.im)
        (u2.re * u3.re + u2.im * u3.im) (u3.re * u3.re + u3.im * u3.im) k0 k1 k2 k3 := by
  simp only [psi, normSq_apply, pow_two, mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re,
    ofReal_im, re_ofNat, im_ofNat]
  ring

private theorem dist_sq_eq (z w : ℂ) :
    dist z w ^ 2 = (z - w).re * (z - w).re + (z - w).im * (z - w).im := by
  rw [Complex.dist_eq, Complex.sq_norm, normSq_apply]

/-- **Complex Descartes theorem for signed radii.** Let `cᵢ ∈ ℂ` and nonzero real numbers `sᵢ`
satisfy `|cᵢ - cⱼ|² = (sᵢ + sⱼ)²` for `i ≠ j`, and let `kᵢ = 1/sᵢ`. Then
`(∑ kᵢ cᵢ)² = 2 ∑ (kᵢ cᵢ)²` and `(∑ kᵢ)² = 2 ∑ kᵢ²` (Lagarias, Mallows and Wilks,
arXiv:math/0101066v1, Theorem 2.1 and Theorem 1.1, with signed radii `sᵢ`: positive for a circle
whose interior is disjoint from the others, negative for an enclosing circle). -/
theorem complex_descartes_of_signed (c : Fin 4 → ℂ) (s k : Fin 4 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hk : ∀ i, k i = 1 / s i)
    (hdist : ∀ i j, i ≠ j → dist (c i) (c j) ^ 2 = (s i + s j) ^ 2) :
    (∑ i, (k i : ℂ) * c i) ^ 2 = 2 * ∑ i, ((k i : ℂ) * c i) ^ 2 ∧
      (∑ i, k i) ^ 2 = 2 * ∑ i, k i ^ 2 := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  set s0 := s 0
  set s1 := s 1
  set s2 := s 2
  set s3 := s 3
  set u1 := c 1 - c 0 with hu1
  set u2 := c 2 - c 0 with hu2
  set u3 := c 3 - c 0 with hu3
  have d01 := hdist 1 0 (by decide)
  have d02 := hdist 2 0 (by decide)
  have d03 := hdist 3 0 (by decide)
  have d12 := hdist 2 1 (by decide)
  have d13 := hdist 3 1 (by decide)
  have d23 := hdist 3 2 (by decide)
  rw [dist_sq_eq] at d01 d02 d03 d12 d13 d23
  have r12 : c 2 - c 1 = u2 - u1 := by rw [hu1, hu2]; ring
  have r13 : c 3 - c 1 = u3 - u1 := by rw [hu1, hu3]; ring
  have r23 : c 3 - c 2 = u3 - u2 := by rw [hu2, hu3]; ring
  rw [r12] at d12
  rw [r13] at d13
  rw [r23] at d23
  simp only [sub_re, sub_im] at d12 d13 d23
  have e11 : u1.re * u1.re + u1.im * u1.im = (s1 + s0) ^ 2 := d01
  have e22 : u2.re * u2.re + u2.im * u2.im = (s2 + s0) ^ 2 := d02
  have e33 : u3.re * u3.re + u3.im * u3.im = (s3 + s0) ^ 2 := d03
  have e12 : u1.re * u2.re + u1.im * u2.im =
      ((s1 + s0) ^ 2 + (s2 + s0) ^ 2 - (s2 + s1) ^ 2) / 2 := by
    linear_combination (d01 + d02 - d12) / 2
  have e13 : u1.re * u3.re + u1.im * u3.im =
      ((s1 + s0) ^ 2 + (s3 + s0) ^ 2 - (s3 + s1) ^ 2) / 2 := by
    linear_combination (d01 + d03 - d13) / 2
  have e23 : u2.re * u3.re + u2.im * u3.im =
      ((s2 + s0) ^ 2 + (s3 + s0) ^ 2 - (s3 + s2) ^ 2) / 2 := by
    linear_combination (d02 + d03 - d23) / 2
  -- The Gram determinant of three plane vectors vanishes.
  have hGram : (u1.re * u1.re + u1.im * u1.im) *
        ((u2.re * u2.re + u2.im * u2.im) * (u3.re * u3.re + u3.im * u3.im) -
          (u2.re * u3.re + u2.im * u3.im) ^ 2) -
      (u1.re * u2.re + u1.im * u2.im) *
        ((u1.re * u2.re + u1.im * u2.im) * (u3.re * u3.re + u3.im * u3.im) -
          (u2.re * u3.re + u2.im * u3.im) * (u1.re * u3.re + u1.im * u3.im)) +
      (u1.re * u3.re + u1.im * u3.im) *
        ((u1.re * u2.re + u1.im * u2.im) * (u2.re * u3.re + u2.im * u3.im) -
          (u2.re * u2.re + u2.im * u2.im) * (u1.re * u3.re + u1.im * u3.im)) = 0 := by
    ring
  rw [e11, e22, e33, e12, e13, e23] at hGram
  have hN : descartesNumerator s0 s1 s2 s3 = 0 := by
    simp only [descartesNumerator]
    linear_combination (-1 / 4 : ℝ) * hGram
  have hk0 : k 0 = 1 / s0 := hk 0
  have hk1 : k 1 = 1 / s1 := hk 1
  have hk2 : k 2 = 1 / s2 := hk 2
  have hk3 : k 3 = 1 / s3 := hk 3
  -- The real Descartes relation.
  have hD : (k 0 + k 1 + k 2 + k 3) ^ 2 - 2 * (k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2) = 0 := by
    rw [hk0, hk1, hk2, hk3]
    rw [show (1 / s0 + 1 / s1 + 1 / s2 + 1 / s3) ^ 2 -
        2 * ((1 / s0) ^ 2 + (1 / s1) ^ 2 + (1 / s2) ^ 2 + (1 / s3) ^ 2) =
        -(descartesNumerator s0 s1 s2 s3) / (s0 ^ 2 * s1 ^ 2 * s2 ^ 2 * s3 ^ 2) by
      simp only [descartesNumerator]
      field_simp
      ring, hN]
    simp
  -- `F₀ = 0`.
  have hF0 : ((k 1 : ℂ) * u1 + (k 2 : ℂ) * u2 + (k 3 : ℂ) * u3) ^ 2 -
      2 * (((k 1 : ℂ) * u1) ^ 2 + ((k 2 : ℂ) * u2) ^ 2 + ((k 3 : ℂ) * u3) ^ 2) = 0 := by
    rw [← normSq_eq_zero, normSq_F0, e11, e22, e33, e12, e13, e23, hk1, hk2, hk3]
    rw [show phi ((s1 + s0) ^ 2) (((s1 + s0) ^ 2 + (s2 + s0) ^ 2 - (s2 + s1) ^ 2) / 2)
        (((s1 + s0) ^ 2 + (s3 + s0) ^ 2 - (s3 + s1) ^ 2) / 2) ((s2 + s0) ^ 2)
        (((s2 + s0) ^ 2 + (s3 + s0) ^ 2 - (s3 + s2) ^ 2) / 2) ((s3 + s0) ^ 2)
        (1 / s1) (1 / s2) (1 / s3) =
        descartesNumerator s0 s1 s2 s3 *
          (descartesNumerator s0 s1 s2 s3 - 16 * s1 ^ 2 * s2 ^ 2 * s3 ^ 2) /
          (s1 ^ 4 * s2 ^ 4 * s3 ^ 4) by
      simp only [phi, descartesNumerator]
      field_simp
      ring, hN]
    simp
  -- `G = 0`.
  have hG : ((k 0 : ℂ) + k 1 + k 2 + k 3) * ((k 1 : ℂ) * u1 + (k 2 : ℂ) * u2 + (k 3 : ℂ) * u3) -
      2 * ((k 1 : ℂ) ^ 2 * u1 + (k 2 : ℂ) ^ 2 * u2 + (k 3 : ℂ) ^ 2 * u3) = 0 := by
    rw [← normSq_eq_zero, normSq_G, e11, e22, e33, e12, e13, e23, hk0, hk1, hk2, hk3]
    rw [show psi ((s1 + s0) ^ 2) (((s1 + s0) ^ 2 + (s2 + s0) ^ 2 - (s2 + s1) ^ 2) / 2)
        (((s1 + s0) ^ 2 + (s3 + s0) ^ 2 - (s3 + s1) ^ 2) / 2) ((s2 + s0) ^ 2)
        (((s2 + s0) ^ 2 + (s3 + s0) ^ 2 - (s3 + s2) ^ 2) / 2) ((s3 + s0) ^ 2)
        (1 / s0) (1 / s1) (1 / s2) (1 / s3) =
        descartesNumerator s0 s1 s2 s3 *
          (descartesNumerator s0 s1 s2 s3 - 4 * s1 ^ 2 * s2 ^ 2 * s3 ^ 2) /
          (s0 ^ 2 * s1 ^ 4 * s2 ^ 4 * s3 ^ 4) by
      simp only [psi, descartesNumerator]
      field_simp
      ring, hN]
    simp
  have hDC : ((k 0 : ℂ) + k 1 + k 2 + k 3) ^ 2 -
      2 * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 + (k 3 : ℂ) ^ 2) = 0 := by
    exact_mod_cast hD
  refine ⟨?_, ?_⟩
  · simp only [Fin.sum_univ_four]
    rw [hu1, hu2, hu3] at hF0 hG
    linear_combination hF0 + 2 * c 0 * hG + c 0 ^ 2 * hDC
  · simp only [Fin.sum_univ_four]
    linear_combination hD

/-- **Complex Descartes theorem.** Let four circles in the plane `ℂ` have centers `cᵢ` and radii
`rᵢ > 0`, and signed curvatures `kᵢ`, in either configuration of Descartes' circle theorem: (a)
pairwise externally tangent, `|cᵢ - cⱼ| = rᵢ + rⱼ`, with `kᵢ = 1/rᵢ`; or (b) one circle `e`
internally tangent to the three others, `|c_e - cⱼ| = r_e - rⱼ`, which are pairwise externally
tangent, with `k_e = -1/r_e` and `kⱼ = 1/rⱼ` for `j ≠ e`. Then the products `kᵢ cᵢ` of curvature
and center satisfy the same relation as the curvatures, `(∑ kᵢ cᵢ)² = 2 ∑ (kᵢ cᵢ)²` in `ℂ`
(Lagarias, Mallows and Wilks, *Beyond the Descartes circle theorem*, arXiv:math/0101066v1,
Theorem 2.1, stated there for all Descartes configurations, lines included). -/
theorem complex_descartes_theorem (c : Fin 4 → ℂ) (r k : Fin 4 → ℝ)
    (hr : ∀ i, 0 < r i)
    (htan : ((∀ i j, i ≠ j → dist (c i) (c j) = r i + r j) ∧ ∀ i, k i = 1 / r i) ∨
      ∃ e : Fin 4, k e = -1 / r e ∧ (∀ j, j ≠ e → k j = 1 / r j) ∧
        (∀ j, j ≠ e → dist (c e) (c j) = r e - r j) ∧
        ∀ i j, i ≠ e → j ≠ e → i ≠ j → dist (c i) (c j) = r i + r j) :
    (∑ i, (k i : ℂ) * c i) ^ 2 = 2 * ∑ i, ((k i : ℂ) * c i) ^ 2 := by
  rcases htan with ⟨hdist, hk⟩ | ⟨e, hke, hk, hdist_e, hdist⟩
  · refine (complex_descartes_of_signed c r k (fun i ↦ ne_of_gt (hr i)) hk ?_).1
    intro i j hij
    rw [hdist i j hij]
  · let s : Fin 4 → ℝ := fun i ↦ if i = e then -r i else r i
    refine (complex_descartes_of_signed c s k ?_ ?_ ?_).1
    · intro i
      dsimp [s]
      split_ifs
      · exact neg_ne_zero.mpr (ne_of_gt (hr i))
      · exact ne_of_gt (hr i)
    · intro i
      by_cases hi : i = e
      · subst i
        have hse : s e = -r e := by simp [s]
        rw [hse, hke]
        field_simp [ne_of_gt (hr e)]
      · have hsi : s i = r i := by simp [s, hi]
        rw [hsi]
        exact hk i hi
    · intro i j hij
      by_cases hi : i = e
      · subst i
        have hj : j ≠ e := Ne.symm hij
        have hse : s e = -r e := by simp [s]
        have hsj : s j = r j := by simp [s, hj]
        rw [hse, hsj, hdist_e j hj]
        ring
      · by_cases hj : j = e
        · subst j
          have hsi : s i = r i := by simp [s, hi]
          have hse : s e = -r e := by simp [s]
          rw [hsi, hse, dist_comm, hdist_e i hi]
          ring
        · have hsi : s i = r i := by simp [s, hi]
          have hsj : s j = r j := by simp [s, hj]
          rw [hsi, hsj, hdist i j hi hj hij]

end MathlibExt.Geometry.Euclidean.ComplexDescartesTheorem
