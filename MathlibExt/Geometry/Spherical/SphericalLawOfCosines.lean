/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Spherical law of cosines, general form.** Write $x \cdot y = \sum_{i=1}^{3} x_i y_i$ for the
dot product and $\lVert x \rVert = \sqrt{x \cdot x}$ for the Euclidean norm on $\mathbb{R}^3$. Let
$u, v, w \in \mathbb{R}^3$ be unit vectors and let $a, b, c, C$ be real numbers with $0 < a < \pi$
and $0 < b < \pi$. Suppose that $v \cdot w = \cos a$, $u \cdot w = \cos b$, $u \cdot v = \cos c$
and
$$
\cos C = \frac{u \cdot v - (u \cdot w)(v \cdot w)}
{\lVert u - (u \cdot w)\, w \rVert \, \lVert v - (v \cdot w)\, w \rVert}.
$$
Then $\cos c = \cos a \cos b + \sin a \sin b \cos C$.

Only $a$ and $b$ need to lie in $(0, \pi)$: $c$ and $C$ enter only through their cosines. The
quotient above is the cosine of the angle at $w$ between the great-circle arcs from $w$ to $u$
and from $w$ to $v$. -/
theorem spherical_law_of_cosines_general (a b c C : ℝ)
    (u v w : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < Real.pi)
    (hb : 0 < b ∧ b < Real.pi)
    (hu : ∑ i, u i * u i = 1)
    (hv : ∑ i, v i * v i = 1)
    (hw : ∑ i, w i * w i = 1)
    (ha_side : ∑ i, v i * w i = Real.cos a)
    (hb_side : ∑ i, u i * w i = Real.cos b)
    (hc_side : ∑ i, u i * v i = Real.cos c)
    (hC_angle : Real.cos C = ((∑ i, u i * v i) - (∑ i, u i * w i) * (∑ i, v i * w i)) /
      (Real.sqrt (∑ i, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i)) * Real.sqrt
      (∑ i, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i)))) :
    Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
  have hsin_a_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hsin_b_pos : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  have hsin_a_ne : Real.sin a ≠ 0 := ne_of_gt hsin_a_pos
  have hsin_b_ne : Real.sin b ≠ 0 := ne_of_gt hsin_b_pos
  have hsin_sq_a : Real.sin a ^ 2 = 1 - Real.cos a ^ 2 := by
    have h := Real.sin_sq_add_cos_sq a
    linarith
  have hsin_sq_b : Real.sin b ^ 2 = 1 - Real.cos b ^ 2 := by
    have h := Real.sin_sq_add_cos_sq b
    linarith
  have hSq_u : (∑ i, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i))
      = Real.sin b ^ 2 := by
    have hterm : ∀ i : Fin 3, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i)
        = (u i * u i) - (2 * (∑ j, u j * w j)) * (u i * w i)
          + (∑ j, u j * w j) ^ 2 * (w i * w i) := by
      intro i
      ring
    have hsum : (∑ i : Fin 3, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i))
        = (∑ i : Fin 3, u i * u i) - (2 * (∑ j, u j * w j)) * (∑ i : Fin 3, u i * w i)
          + (∑ j, u j * w j) ^ 2 * (∑ i : Fin 3, w i * w i) := by
      calc ∑ i : Fin 3, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i)
          = ∑ i : Fin 3, ((u i * u i) - (2 * (∑ j, u j * w j)) * (u i * w i)
            + (∑ j, u j * w j) ^ 2 * (w i * w i)) := by
              congr 1
              ext i
              exact hterm i
        _ = (∑ i : Fin 3, u i * u i) - (2 * (∑ j, u j * w j)) * (∑ i : Fin 3, u i * w i)
            + (∑ j, u j * w j) ^ 2 * (∑ i : Fin 3, w i * w i) := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum, hu, hw, hb_side]
    rw [hsin_sq_b]
    ring
  have hSq_v : (∑ i, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i))
      = Real.sin a ^ 2 := by
    have hterm : ∀ i : Fin 3, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i)
        = (v i * v i) - (2 * (∑ j, v j * w j)) * (v i * w i)
          + (∑ j, v j * w j) ^ 2 * (w i * w i) := by
      intro i
      ring
    have hsum : (∑ i : Fin 3, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i))
        = (∑ i : Fin 3, v i * v i) - (2 * (∑ j, v j * w j)) * (∑ i : Fin 3, v i * w i)
          + (∑ j, v j * w j) ^ 2 * (∑ i : Fin 3, w i * w i) := by
      calc ∑ i : Fin 3, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i)
          = ∑ i : Fin 3, ((v i * v i) - (2 * (∑ j, v j * w j)) * (v i * w i)
            + (∑ j, v j * w j) ^ 2 * (w i * w i)) := by
              congr 1
              ext i
              exact hterm i
        _ = (∑ i : Fin 3, v i * v i) - (2 * (∑ j, v j * w j)) * (∑ i : Fin 3, v i * w i)
            + (∑ j, v j * w j) ^ 2 * (∑ i : Fin 3, w i * w i) := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum, hv, hw, ha_side]
    rw [hsin_sq_a]
    ring
  have hSqrt_u : Real.sqrt (∑ i, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i))
      = Real.sin b := by
    rw [hSq_u, Real.sqrt_sq_eq_abs, abs_of_pos hsin_b_pos]
  have hSqrt_v : Real.sqrt (∑ i, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i))
      = Real.sin a := by
    rw [hSq_v, Real.sqrt_sq_eq_abs, abs_of_pos hsin_a_pos]
  rw [hSqrt_u, hSqrt_v, hc_side, hb_side, ha_side] at hC_angle
  have hdenom_ne : Real.sin b * Real.sin a ≠ 0 := mul_ne_zero hsin_b_ne hsin_a_ne
  have hmul : Real.cos C * (Real.sin b * Real.sin a) = Real.cos c - Real.cos b * Real.cos a := by
    rw [hC_angle]
    field_simp
  linear_combination -hmul

set_option linter.unusedVariables false in
/-- **Spherical law of cosines.** Write $x \cdot y = \sum_{i=1}^{3} x_i y_i$ for the dot product
and $\lVert x \rVert = \sqrt{x \cdot x}$ for the Euclidean norm on $\mathbb{R}^3$. Let
$u, v, w \in \mathbb{R}^3$ be unit vectors and let $a, b, c, C$ be real numbers, each strictly
between $0$ and $\pi$. Suppose that $v \cdot w = \cos a$, $u \cdot w = \cos b$,
$u \cdot v = \cos c$ and
$$
\cos C = \frac{u \cdot v - (u \cdot w)(v \cdot w)}
{\lVert u - (u \cdot w)\, w \rVert \, \lVert v - (v \cdot w)\, w \rVert}.
$$
Then $\cos c = \cos a \cos b + \sin a \sin b \cos C$.

Geometrically, $u$, $v$, $w$ are the vertices of a spherical triangle on the unit sphere, $a$,
$b$, $c$ are the lengths of the sides opposite $u$, $v$, $w$, and $C$ is the angle at $w$,
opposite the side $c$.

Source: https://en.wikipedia.org/wiki/Spherical_law_of_cosines
(statement `spherical-cosines-s1`).
It follows from `spherical_law_of_cosines_general`; the hypotheses `hc` and `hC` are unused
and keep the source's shape.
Proves `Wanted` entry `spherical_law_of_cosines`.
-/
theorem spherical_law_of_cosines (a b c C : ℝ)
    (u v w : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < Real.pi)
    (hb : 0 < b ∧ b < Real.pi)
    (hc : 0 < c ∧ c < Real.pi)
    (hC : 0 < C ∧ C < Real.pi)
    (hu : ∑ i, u i * u i = 1)
    (hv : ∑ i, v i * v i = 1)
    (hw : ∑ i, w i * w i = 1)
    (ha_side : ∑ i, v i * w i = Real.cos a)
    (hb_side : ∑ i, u i * w i = Real.cos b)
    (hc_side : ∑ i, u i * v i = Real.cos c)
    (hC_angle : Real.cos C = ((∑ i, u i * v i) - (∑ i, u i * w i) * (∑ i, v i * w i)) /
      (Real.sqrt (∑ i, (u i - (∑ j, u j * w j) * w i) * (u i - (∑ j, u j * w j) * w i)) * Real.sqrt
      (∑ i, (v i - (∑ j, v j * w j) * w i) * (v i - (∑ j, v j * w j) * w i)))) :
    Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
  exact spherical_law_of_cosines_general a b c C u v w ha hb hu hv hw ha_side hb_side hc_side
    hC_angle

end

end MetaMathlibExt
