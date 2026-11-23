/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hinge theorem

This file proves Euclid's hinge theorem for the Euclidean plane by expanding squared norms with
the vector law of cosines.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem hinge_opposite_side_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (A B C : V) :
    ‖C - B‖ ^ 2 =
      ‖C - A‖ ^ 2 - 2 * inner ℝ (C - A) (B - A) + ‖B - A‖ ^ 2 := by
  rw [show C - B = (C - A) - (B - A) by abel]
  exact norm_sub_sq_real (C - A) (B - A)

private theorem hinge_sq_lt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A B C D E F : V)
    (hAB : ‖B - A‖ = ‖E - D‖) (hAC : ‖C - A‖ = ‖F - D‖)
    (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
    ‖F - E‖ ^ 2 < ‖C - B‖ ^ 2 := by
  rw [hinge_opposite_side_sq D E F, hinge_opposite_side_sq A B C]
  rw [real_inner_comm (E - D) (F - D), real_inner_comm (B - A) (C - A)]
  rw [← hAC, ← hAB]
  linarith

private theorem hinge_norm_lt_of_sq_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {x y : V}
    (h : ‖x‖ ^ 2 < ‖y‖ ^ 2) : ‖x‖ < ‖y‖ :=
  (sq_lt_sq₀ (norm_nonneg x) (norm_nonneg y)).mp h

/-- **Hinge theorem in inner product spaces.** Let $V$ be a real inner product space and let
$A, B, C, D, E, F \in V$. If $\|B - A\| = \|E - D\|$, $\|C - A\| = \|F - D\|$ and
$\langle B - A, C - A \rangle < \langle E - D, F - D \rangle$, then $\|F - E\| < \|C - B\|$.

Proof: Expand both squared opposite sides by the law of cosines and compare them.

Source: Euclid's *Elements*, Book I, Proposition 24.
-/
theorem hinge_theorem_of_inner_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (A B C D E F : V)
    (hAB : ‖B - A‖ = ‖E - D‖) (hAC : ‖C - A‖ = ‖F - D‖)
    (hinner : inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D)) :
    ‖F - E‖ < ‖C - B‖ :=
  hinge_norm_lt_of_sq_lt (hinge_sq_lt A B C D E F hAB hAC hinner)

/-- **Hinge theorem.** Let $A, B, C$ and $D, E, F$ be two triples of pairwise distinct points of
the Euclidean plane $\mathbb{R}^2$ forming nondegenerate triangles: $C - A$ is not a real
multiple of $B - A$, and $F - D$ is not a real multiple of $E - D$. Write $XY$ for the distance
between points $X$ and $Y$. If $AB = DE$, $AC = DF$ and
$\langle B - A, C - A \rangle < \langle E - D, F - D \rangle$, that is, the angle at $A$ is
larger than the angle at $D$, then $EF < BC$.

Proof: The vector law of cosines compares the squared opposite sides, following Euclid's
*Elements*, Book I, Proposition 24.

Proves `Wanted` entry `hinge_theorem`.

Source: Euclid's Elements, Book I, Proposition 24
(https://mathcs.clarku.edu/~djoyce/elements/bookI/propI24.html); see also
https://en.wikipedia.org/wiki/Hinge_theorem.
-/
theorem hinge_theorem : ∀ (A B C D E F : EuclideanSpace ℝ (Fin 2)),
  B ≠ A → C ≠ A → C ≠ B → E ≠ D → F ≠ D → F ≠ E →
  (∀ t : ℝ, C - A ≠ t • (B - A)) →
  (∀ s : ℝ, F - D ≠ s • (E - D)) →
  ‖B - A‖ = ‖E - D‖ → ‖C - A‖ = ‖F - D‖ →
  inner ℝ (B - A) (C - A) < inner ℝ (E - D) (F - D) →
  ‖F - E‖ < ‖C - B‖ :=
  fun A B C D E F _ _ _ _ _ _ _ _ => hinge_theorem_of_inner_lt A B C D E F

end MetaMathlibExt
