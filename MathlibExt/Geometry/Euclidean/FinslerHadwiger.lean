/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MetaMathlibExt

@[expose] public section

private theorem finsler_hadwiger_identity (A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2))
    (hD0 : (D - A).ofLp 0 = -((B - A).ofLp 1)) (hD1 : (D - A).ofLp 1 = (B - A).ofLp 0)
    (hC : C = B + D - A)
    (hG0 : (G - A).ofLp 0 = -((E - A).ofLp 1)) (hG1 : (G - A).ofLp 1 = (E - A).ofLp 0)
    (hF : F = E + G - A)
    (hO1 : O1 = (2 : ℝ)⁻¹ • (A + C)) (hO2 : O2 = (2 : ℝ)⁻¹ • (A + F))
    (hP : P = (2 : ℝ)⁻¹ • (B + G)) (hQ : Q = (2 : ℝ)⁻¹ • (D + E)) :
    ‖P - Q‖ = ‖O1 - O2‖ ∧
      ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
        (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
      O1 + O2 = P + Q := by
  subst hC; subst hF; subst hO1; subst hO2; subst hP; subst hQ
  simp only [PiLp.sub_apply] at hD0 hD1 hG0 hG1
  have hD0c : D.ofLp 0 = A.ofLp 0 - (B.ofLp 1 - A.ofLp 1) := by linarith
  have hD1c : D.ofLp 1 = A.ofLp 1 + (B.ofLp 0 - A.ofLp 0) := by linarith
  have hG0c : G.ofLp 0 = A.ofLp 0 - (E.ofLp 1 - A.ofLp 1) := by linarith
  have hG1c : G.ofLp 1 = A.ofLp 1 + (E.ofLp 0 - A.ofLp 0) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hsq : ‖(2 : ℝ)⁻¹ • (B + G) - (2 : ℝ)⁻¹ • (D + E)‖ ^ 2
        = ‖(2 : ℝ)⁻¹ • (A + (B + D - A)) - (2 : ℝ)⁻¹ • (A + (E + G - A))‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Real.norm_eq_abs, sq_abs]
      rw [hD0c, hD1c, hG0c, hG1c]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  · simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hD0c, hD1c, hG0c, hG1c]
    ring
  · module

/-- **Finsler–Hadwiger theorem.** Let $A, B, C, D, E, F, G$ be points of the Euclidean plane
$\mathbb{R}^2$ with $B \ne A$ and $E \ne A$, and let $\rho(x, y) = (-y, x)$ be the
counterclockwise rotation by $90^\circ$. Suppose that $ABCD$ and $AEFG$ are squares sharing the
vertex $A$, in the sense that $D - A = \rho(B - A)$, $C = B + D - A$, $G - A = \rho(E - A)$ and
$F = E + G - A$. Let $O_1 = (A + C)/2$ and $O_2 = (A + F)/2$ be their centers, and let
$P = (B + G)/2$ and $Q = (D + E)/2$. Then $\|P - Q\| = \|O_1 - O_2\|$, the vectors $P - Q$ and
$O_1 - O_2$ are orthogonal, and $O_1 + O_2 = P + Q$; that is, the segments $O_1O_2$ and $PQ$
have equal length, are perpendicular and share their midpoint.

The hypotheses $B \ne A$ and $E \ne A$ are not used. When $B = E$ both segments are zero; with
$B \ne E$ one also gets $O_1 \ne O_2$, so that $O_1 P O_2 Q$ is a square as in the source.

Source: https://en.wikipedia.org/wiki/Finsler%E2%80%93Hadwiger_theorem
(statement finsler-hadwiger-s1).
Proves `Wanted` entry `finsler_hadwiger`.
-/
theorem finsler_hadwiger :
    ∀ (A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2)),
      B ≠ A →
      E ≠ A →
      (D - A).ofLp 0 = -((B - A).ofLp 1) →
      (D - A).ofLp 1 = (B - A).ofLp 0 →
      C = B + D - A →
      (G - A).ofLp 0 = -((E - A).ofLp 1) →
      (G - A).ofLp 1 = (E - A).ofLp 0 →
      F = E + G - A →
      O1 = (2 : ℝ)⁻¹ • (A + C) →
      O2 = (2 : ℝ)⁻¹ • (A + F) →
      P = (2 : ℝ)⁻¹ • (B + G) →
      Q = (2 : ℝ)⁻¹ • (D + E) →
      ‖P - Q‖ = ‖O1 - O2‖ ∧
        ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
          (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
        O1 + O2 = P + Q := by
  intro A B C D E F G O1 O2 P Q _ _ hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ
  exact finsler_hadwiger_identity A B C D E F G O1 O2 P Q hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ

/-- **Finsler–Hadwiger theorem for distinct squares.** Let $A, B, C, D, E, F, G$ be points of
the Euclidean plane $\mathbb{R}^2$ with $B \ne E$, and let $\rho(x, y) = (-y, x)$ be the
counterclockwise rotation by $90^\circ$. Suppose that $ABCD$ and $AEFG$ are squares sharing the
vertex $A$, in the sense that $D - A = \rho(B - A)$, $C = B + D - A$, $G - A = \rho(E - A)$ and
$F = E + G - A$. Let $O_1 = (A + C)/2$ and $O_2 = (A + F)/2$ be their centers, and let
$P = (B + G)/2$ and $Q = (D + E)/2$. Then $\|P - Q\| = \|O_1 - O_2\|$, the vectors $P - Q$ and
$O_1 - O_2$ are orthogonal, $O_1 + O_2 = P + Q$ and $O_1 \ne O_2$; so the segments $O_1O_2$ and
$PQ$ are nonzero, equal, perpendicular and share their midpoint, and $O_1 P O_2 Q$ is a square.

The points $B$ and $E$ may equal $A$: if, say, $E = A$, then $AEFG$ is the single point $A$
and $O_1 P O_2 Q$ is a quarter of $ABCD$. -/
theorem finsler_hadwiger_of_ne (A B C D E F G O1 O2 P Q : EuclideanSpace ℝ (Fin 2))
    (hBE : B ≠ E)
    (hD0 : (D - A).ofLp 0 = -((B - A).ofLp 1)) (hD1 : (D - A).ofLp 1 = (B - A).ofLp 0)
    (hC : C = B + D - A)
    (hG0 : (G - A).ofLp 0 = -((E - A).ofLp 1)) (hG1 : (G - A).ofLp 1 = (E - A).ofLp 0)
    (hF : F = E + G - A)
    (hO1 : O1 = (2 : ℝ)⁻¹ • (A + C)) (hO2 : O2 = (2 : ℝ)⁻¹ • (A + F))
    (hP : P = (2 : ℝ)⁻¹ • (B + G)) (hQ : Q = (2 : ℝ)⁻¹ • (D + E)) :
    ‖P - Q‖ = ‖O1 - O2‖ ∧
      ((P - Q).ofLp 0 * (O1 - O2).ofLp 0 +
        (P - Q).ofLp 1 * (O1 - O2).ofLp 1 = 0) ∧
      O1 + O2 = P + Q ∧ O1 ≠ O2 := by
  obtain ⟨hnorm, horth, hmid⟩ :=
    finsler_hadwiger_identity A B C D E F G O1 O2 P Q hD0 hD1 hC hG0 hG1 hF hO1 hO2 hP hQ
  refine ⟨hnorm, horth, hmid, fun h => hBE ?_⟩
  subst hC hF hO1 hO2
  simp only [PiLp.sub_apply] at hD0 hD1 hG0 hG1
  have h0 := congrArg (·.ofLp 0) h
  have h1 := congrArg (·.ofLp 1) h
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    linarith
  · simp only [Fin.mk_one, Fin.isValue]
    linarith

end

end MetaMathlibExt
