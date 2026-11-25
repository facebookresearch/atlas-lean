/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import MathlibExt.Geometry.Manifold.MorseTheory

@[expose] public section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.ReebSphereWanted

open MathlibExt.Geometry.Manifold.MorseTheoryWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Morse function.** Let $M$ be a $C^\infty$ manifold without boundary modelled on a real
normed space of finite dimension $d$. A function $f \colon M \to \mathbb{R}$ is a Morse function
if it is $C^\infty$ and, for every critical point $p$ of $f$ (a point where the differential
$df_p$ is zero), there exist an integer $0 \le k \le d$, a map $\varphi \colon M \to \mathbb{R}^d$
that is a local $C^\infty$ diffeomorphism at $p$ with $\varphi(p) = 0$, and an open set $U$
containing $p$ such that $f(q) = f(p) + Q_k(\varphi(q))$ for all $q \in U$. Here $Q_k$ is the
Morse quadratic form $Q_k(y) = -y_1^2 - \dots - y_k^2 + y_{k+1}^2 + \dots + y_d^2$ on
$\mathbb{R}^d$. -/
def IsMorseFunction (f : M → ℝ) : Prop :=
  ContMDiff I (𝓘(ℝ, ℝ)) (⊤ : ℕ∞) f ∧
    ∀ p : M, mfderiv I (𝓘(ℝ, ℝ)) f p = 0 →
      ∃ (k : ℕ) (_ : k ≤ Module.finrank ℝ E)
        (φ : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
        IsLocalDiffeomorphAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
            (⊤ : ℕ∞) φ p ∧
          φ p = 0 ∧
            ∃ (U : Set M) (_ : IsOpen U) (_ : p ∈ U),
              ∀ q ∈ U, f q = f p + morseQuadratic k (Module.finrank ℝ E) (φ q)

end MathlibExt.Geometry.Manifold.ReebSphereWanted
