/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.TreeLike
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.TreeLike

/-- A constant path in the plane is tree-like. -/
example : IsTreeLike (fun _ : ℝ => (0 : EuclideanSpace ℝ (Fin 2))) 1 := isTreeLike_const _ _

/-- A nonconstant tree-like path: the segment to `(1/2) e₀` and back, on `[0, 1]`. -/
example : IsTreeLike (fun t : ℝ => min t (1 - t) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 1 :=
  isTreeLike_out_and_back _ zero_le_one

/-- A path that is not tree-like: the segment `t ↦ t e₀` on `[0, 1]` ends away from its start. -/
example : ¬ IsTreeLike (fun t : ℝ => t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 1 := by
  intro h
  have := h.apply_eq zero_le_one
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) this
  simp at h1

end MathlibExtTest.Analysis.PathSignature.TreeLike
