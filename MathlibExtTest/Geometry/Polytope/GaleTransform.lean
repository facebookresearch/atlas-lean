/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.GaleTransform

@[expose] public section

open MathlibExt.Geometry.Polytope

namespace MathlibExtTest.Geometry.Polytope.GaleTransform

/-- The vectors of any Gale transform sum to zero. -/
example {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} {ι : Type*} {v : Fin n → E}
    (b : Module.Basis ι ℝ (affineDependences v)) : ∑ i, galeTransform b i = 0 :=
  sum_galeTransform b

/-- Four points spanning the plane have a one-dimensional space of affine dependences. -/
example {v : Fin 4 → ℝ × ℝ} (h : affineSpan ℝ (Set.range v) = ⊤) :
    Module.finrank ℝ (affineDependences v) = 1 := by
  rw [finrank_affineDependences h]
  simp

end MathlibExtTest.Geometry.Polytope.GaleTransform
