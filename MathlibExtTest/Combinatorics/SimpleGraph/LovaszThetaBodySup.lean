/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodySup
import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaPentagon

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
open MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted

/-- On the empty vertex type the only attainable coordinate sum is zero. -/
example (G : SimpleGraph (Fin 0)) : lovaszTheta G = 0 := by
  rw [lovaszTheta_eq_sSup_th]
  have h : (th G).Nonempty := ⟨0, le_rfl, by simp⟩
  simp [h.image_const]

/-- The pentagon's umbrella labeling bounds the coordinate sums on its theta body. -/
example : sSup ((fun x : Fin 5 → ℝ => ∑ v, x v) '' th (SimpleGraph.cycleGraph 5)) ≤ √5 := by
  rw [← lovaszTheta_eq_sSup_th]
  exact lovaszTheta_cycleGraph_five_le
