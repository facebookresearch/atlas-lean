/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

@[expose] public section

namespace MetaMathlibExt

/-- **Van Aubel's theorem.** Let $A$, $B$, $C$, $D$ be any four points of the Euclidean plane
$\mathbb{R}^2$, and let $\rho(x, y) = (-y, x)$ be the counterclockwise rotation by $90^\circ$.
On each directed side $A \to B$, $B \to C$, $C \to D$, $D \to A$ erect the square lying to its
left; its centre is the side midpoint plus half the side vector rotated by $\rho$:
$O_{AB} = \tfrac12(A + B) + \tfrac12\rho(B - A)$,
$O_{BC} = \tfrac12(B + C) + \tfrac12\rho(C - B)$,
$O_{CD} = \tfrac12(C + D) + \tfrac12\rho(D - C)$ and
$O_{DA} = \tfrac12(D + A) + \tfrac12\rho(A - D)$.
Then $\lVert O_{AB} - O_{CD} \rVert = \lVert O_{BC} - O_{DA} \rVert$ and
$\langle O_{AB} - O_{CD}, O_{BC} - O_{DA} \rangle = 0$: the segments joining the centres of
opposite squares have equal length and are perpendicular.

No orientation hypothesis is needed. When the vertices are listed clockwise these are the
outward squares; when they are listed counterclockwise they are the inward squares, and the
outward version is Van Aubel's theorem with squares on the right.

Proves `Wanted` entry `vanAubel`.

Source: https://en.wikipedia.org/wiki/Van_Aubel%27s_theorem (statement `vanaubel-s1`).
-/
theorem vanAubel :
    ∀ (A B C D : EuclideanSpace ℝ (Fin 2))
      (Oab Obc Ocd Oda : EuclideanSpace ℝ (Fin 2)),
      Oab = (2 : ℝ)⁻¹ • (A + B) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((B - A).ofLp 1), ((B - A).ofLp 0)]) →
      Obc = (2 : ℝ)⁻¹ • (B + C) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((C - B).ofLp 1), ((C - B).ofLp 0)]) →
      Ocd = (2 : ℝ)⁻¹ • (C + D) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((D - C).ofLp 1), ((D - C).ofLp 0)]) →
      Oda = (2 : ℝ)⁻¹ • (D + A) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((A - D).ofLp 1), ((A - D).ofLp 0)]) →
      ‖Oab - Ocd‖ = ‖Obc - Oda‖ ∧ ⟪Oab - Ocd, Obc - Oda⟫_ℝ = 0 := by
  intro A B C D Oab Obc Ocd Oda h1 h2 h3 h4
  subst h1
  subst h2
  subst h3
  subst h4
  constructor
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    ring
  · rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vec2_dotProduct]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_add, Fin.isValue, PiLp.sub_apply, neg_sub,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Pi.star_apply,
      star_trivial, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

/-- **Van Aubel's theorem with squares on the right.** Let $A$, $B$, $C$, $D$ be any four
points of the Euclidean plane $\mathbb{R}^2$, and let $\rho(x, y) = (y, -x)$ be the clockwise
rotation by $90^\circ$. On each directed side $A \to B$, $B \to C$, $C \to D$, $D \to A$
erect the square lying to its right; its centre is the side midpoint plus half the side vector
rotated by $\rho$:
$O_{AB} = \tfrac12(A + B) + \tfrac12\rho(B - A)$,
$O_{BC} = \tfrac12(B + C) + \tfrac12\rho(C - B)$,
$O_{CD} = \tfrac12(C + D) + \tfrac12\rho(D - C)$ and
$O_{DA} = \tfrac12(D + A) + \tfrac12\rho(A - D)$.
Then $\lVert O_{AB} - O_{CD} \rVert = \lVert O_{BC} - O_{DA} \rVert$ and
$\langle O_{AB} - O_{CD}, O_{BC} - O_{DA} \rangle = 0$: the segments joining the centres of
opposite squares have equal length and are perpendicular.

When $A$, $B$, $C$, $D$ are listed counterclockwise these are the outward squares; together
with Van Aubel's theorem for squares on the left this covers the outward construction for both
orientations.
-/
theorem vanAubel_right :
    ∀ (A B C D : EuclideanSpace ℝ (Fin 2))
      (Oab Obc Ocd Oda : EuclideanSpace ℝ (Fin 2)),
      Oab = (2 : ℝ)⁻¹ • (A + B) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((B - A).ofLp 1), -((B - A).ofLp 0)]) →
      Obc = (2 : ℝ)⁻¹ • (B + C) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((C - B).ofLp 1), -((C - B).ofLp 0)]) →
      Ocd = (2 : ℝ)⁻¹ • (C + D) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((D - C).ofLp 1), -((D - C).ofLp 0)]) →
      Oda = (2 : ℝ)⁻¹ • (D + A) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((A - D).ofLp 1), -((A - D).ofLp 0)]) →
      ‖Oab - Ocd‖ = ‖Obc - Oda‖ ∧ ⟪Oab - Ocd, Obc - Oda⟫_ℝ = 0 := by
  intro A B C D Oab Obc Ocd Oda h1 h2 h3 h4
  subst h1
  subst h2
  subst h3
  subst h4
  constructor
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    ring
  · rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vec2_dotProduct]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_add, Fin.isValue, PiLp.sub_apply, neg_sub,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Pi.star_apply,
      star_trivial, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

end MetaMathlibExt

end
