/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.ControlTheory.StateSpace.SISO
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# CSTR deviation dynamics as a SISO linear system

## i. Overview

The linear CSTR right-hand side for concentration `c` and inlet
concentration `cin` is `(Q / V) * (cin - c) - k * c`, the field of the
explicit-solution module. Around an equilibrium pair `(css, cinss)`, the
deviation state `x = c - css` (concentration units) and deviation input
`u = cin - cinss` (inlet concentration units) obey exactly
`x' = -(Q / V + k) * x + (Q / V) * u`. This is an affine change of
variables with zero model error, not a linearization with a remainder.
The output is `y = C * x` for a declared gain `C` in output units per
concentration unit, with no direct feedthrough. The linear-system
semantics are the imported SISO ones; this module only builds the CSTR
instance and proves the correspondence.

## ii. Key results

- `ControlBridge.cstrLinearSystem_field_eq` and
  `ControlBridge.cstrLinearSystem_output_eq`: the instance field and
  output in closed form.
- `ControlBridge.cstr_deviation_field_eq`: around an equilibrium pair,
  the CSTR right-hand side at deviated state and inlet is the mapped
  field, with no remainder term.

## iii. Table of contents

- A. The deviation-variable CSTR instance and correspondence

## iv. References

- D. E. Seborg, T. F. Edgar, D. A. Mellichamp and F. J. Doyle,
  *Process Dynamics and Control*, 4th ed., Wiley (2017), Chapters 2-4
  (deviation variables and transfer-function models).
- `MathlibExt/ControlTheory/StateSpace/SISO.lean`: the imported
  `LinearSystem`, `field` and `output` semantics.
- `PhyslibExt/Engineering/Process/CSTR.lean`: the explicit-solution CSTR
  whose right-hand side is mapped here.
-/

@[expose] public section

open Matrix
open MathlibExt.Biology.Dynamics.IntegralFeedback

namespace Engineering.Process.ControlBridge

/-! ## A. The deviation-variable CSTR instance and correspondence -/

/-- The deviation-variable CSTR as a one-state SISO linear system:
state matrix `-(Q / V + k)`, input vector `Q / V`, output gain `C`, and
zero feedthrough. -/
noncomputable def cstrLinearSystem (V Q k C : ℝ) :
    LinearSystem (Fin 1) where
  A := Matrix.of ![![-(Q / V + k)]]
  b := ![Q / V]
  c := ![C]
  d := 0

set_option linter.flexible false in
/-- The mapped field is exactly `-(Q / V + k) * x + (Q / V) * u` in the
single state component. -/
lemma cstrLinearSystem_field_eq (V Q k C : ℝ) (x : Fin 1 → ℝ) (u : ℝ) :
    (cstrLinearSystem V Q k C).field x u =
      ![-(Q / V + k) * x 0 + (Q / V) * u] := by
  funext i
  fin_cases i
  simp [cstrLinearSystem, LinearSystem.field]
  have h : Matrix.vecHead x = x 0 := rfl
  rw [h]
  ring

set_option linter.flexible false in
/-- The mapped output is exactly `C * x`, with no feedthrough term. -/
lemma cstrLinearSystem_output_eq (V Q k C : ℝ) (x : Fin 1 → ℝ) (u : ℝ) :
    (cstrLinearSystem V Q k C).output x u = C * x 0 := by
  simp [cstrLinearSystem, LinearSystem.output]
  have h : Matrix.vecHead x = x 0 := rfl
  rw [h]
  left
  rfl

set_option linter.unusedVariables false in
/-- **Exact deviation correspondence.** Around an equilibrium pair, the
CSTR right-hand side at the deviated state and inlet is the mapped
linear-system field, with no remainder term. -/
lemma cstr_deviation_field_eq {V Q k css cinss x u : ℝ} (hV : 0 < V)
    (hQ : 0 < Q) (hk : 0 ≤ k)
    (hss : (Q / V) * (cinss - css) - k * css = 0) :
    ![(Q / V) * ((cinss + u) - (css + x)) - k * (css + x)] =
      (cstrLinearSystem V Q k 1).field ![x] u := by
  rw [cstrLinearSystem_field_eq]
  simp only [Matrix.cons_val_zero]
  congr 1
  linear_combination hss

end Engineering.Process.ControlBridge
