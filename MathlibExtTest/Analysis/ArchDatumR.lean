/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ArchDatumR

@[expose] public section

namespace LanglandsTunnell.Converse

/-- Consumer using the original binders of the archimedean datum carrier. -/
theorem exactSource (P : RealArchParam) (d : ArchDatumR P)
    (g : Matrix (Fin 2) (Fin 2) ℝ) : d.W g = d.W g := rfl

example (P : RealArchParam) (d : ArchDatumR P) : ArchDatumR P := d

example : RealArchParam := RealArchParam.principal 0 0 0 0

example (P : RealArchParam) : ℂ := (P.twist 0 0).epsilonFactor

end LanglandsTunnell.Converse
