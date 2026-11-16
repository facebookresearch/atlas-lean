/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

@[expose] public section

/-- A point mass compared with itself has distance zero. -/
example : traceDist (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 1) = 0 := by
  simp [traceDist]

end
