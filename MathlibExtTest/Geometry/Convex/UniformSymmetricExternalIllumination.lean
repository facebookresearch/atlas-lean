/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Convex.CubeCovering
import MathlibExt.Geometry.Convex.UniformSymmetricExternalIllumination

open ConvexCovering Set

-- Illuminating every centrally symmetric body by external points needs at least 2ⁿ points,
-- because the cube needs 2ⁿ translates of its interior.
example {n q : ℕ} (hn : 0 < n)
    (h : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IsCentrallySymmetric K →
      IlluminatedByExternalPoints K q) : 2 ^ n ≤ q :=
  symmetricInteriorTranslateBound_ge_two_pow
    ((uniformSymmetricExternalIlluminationInterpretation n hn q).mpr h)

-- Conversely, a uniform covering bound gives that many external points illuminating the cube.
example {n q : ℕ} (hn : 0 < n) (h : UniformSymmetricInteriorTranslateBound n q) :
    IlluminatedByExternalPoints (coordinateCube n) q :=
  (uniformSymmetricExternalIlluminationInterpretation n hn q).mp h (coordinateCube n)
    (coordinateCube_isConvexBody n) (coordinateCube_isCentrallySymmetric n)

-- In particular, seven external points do not illuminate every centrally symmetric body in ℝ³.
example : ¬ ∀ K : Set (EuclideanSpace ℝ (Fin 3)), IsConvexBody K → IsCentrallySymmetric K →
    IlluminatedByExternalPoints K 7 := by
  rw [← uniformSymmetricExternalIlluminationInterpretation 3 (by decide) 7]
  intro h
  exact absurd (symmetricInteriorTranslateBound_ge_two_pow h) (by decide)

-- The hypothesis `0 < n` is needed: in dimension zero a convex body is the whole one-point space,
-- whose boundary is empty, so zero external points illuminate it; but zero translates cover no
-- nonempty set.
example : ¬ (UniformSymmetricInteriorTranslateBound 0 0 ↔
    ∀ K : Set (EuclideanSpace ℝ (Fin 0)), IsConvexBody K → IsCentrallySymmetric K →
      IlluminatedByExternalPoints K 0) := by
  intro h
  have hlight : ∀ K : Set (EuclideanSpace ℝ (Fin 0)), IsConvexBody K →
      IsCentrallySymmetric K → IlluminatedByExternalPoints K 0 := by
    intro K hK _
    obtain ⟨y, hy⟩ := hK.2.2
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun x hx ↦ (hx.2 (Subsingleton.elim y x ▸ hy)).elim⟩
  obtain ⟨w, hw⟩ := h.mpr hlight univ ⟨isCompact_univ, convex_univ, by simp⟩ ⟨0, by simp⟩
  obtain ⟨i, -⟩ := mem_iUnion.mp (hw (mem_univ 0))
  exact i.elim0
