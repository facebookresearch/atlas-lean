/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace MetaMathlibExt

@[expose] public section

/-- **De Gua's theorem.** Let $u, v, w \in \mathbb{R}^3$ be pairwise orthogonal vectors, so that
the tetrahedron with vertices $0, u, v, w$ has a right angle between any two of the edges at $0$.
Write $|x|$ for the Euclidean norm and $\langle x, y \rangle$ for the inner product. Let
$A_{uv}, A_{uw}, A_{vw}, A$ be real numbers with $A_{uv} = |u||v|/2$, $A_{uw} = |u||w|/2$,
$A_{vw} = |v||w|/2$ (the areas of the three right-angled faces) and
$(2A)^2 = |u - v|^2 |u - w|^2 - \langle u - v, u - w \rangle^2$, so that $A$ is, up to sign, the
area of the face with vertices $u, v, w$. Then $A^2 = A_{uv}^2 + A_{uw}^2 + A_{vw}^2$.

Proves `Wanted` entry `deGua` (statement `degua-s1`).

Source: https://en.wikipedia.org/wiki/De_Gua%27s_theorem
-/
theorem deGua : ∀ (u v w : EuclideanSpace ℝ (Fin 3)),
  ⟪u, v⟫_ℝ = 0 →
  ⟪u, w⟫_ℝ = 0 →
  ⟪v, w⟫_ℝ = 0 →
  ∀ (Auv Auw Avw Ahyp : ℝ),
  Auv = ‖u‖ * ‖v‖ / 2 →
  Auw = ‖u‖ * ‖w‖ / 2 →
  Avw = ‖v‖ * ‖w‖ / 2 →
  (2 * Ahyp) ^ 2 = ‖u - v‖ ^ 2 * ‖u - w‖ ^ 2 - (⟪u - v, u - w⟫_ℝ) ^ 2 →
  Ahyp ^ 2 = Auv ^ 2 + Auw ^ 2 + Avw ^ 2 := by
  intro u v w huv huw hvw Auv Auw Avw Ahyp hAuv hAuw hAvw hHyp
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  have h1 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, huv]; ring
  have h2 : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [norm_sub_sq_real, huw]; ring
  have h3 : ⟪u - v, u - w⟫_ℝ = ‖u‖ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, huw, hvu, hvw]
    ring
  rw [h1, h2, h3] at hHyp
  rw [hAuv, hAuw, hAvw]
  linear_combination hHyp / 4

end

end MetaMathlibExt
