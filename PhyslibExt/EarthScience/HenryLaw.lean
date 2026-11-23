/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Henry's law: doubling pressure doubles dissolved concentration

## i. Overview

Under the declared Henry convention `c = H * p` with `H > 0`,
doubling the gas partial pressure doubles the dissolved equilibrium
concentration, zero pressure gives zero concentration, and the `H_cp`
(concentration/pressure) and `H_pc` (pressure/concentration) conventions
are reciprocals for nonzero constants. Nonreactive dilute gas, fixed
temperature/solvent, `p ≥ 0`; the equilibrium law is a hypothesis.

## ii. Key results

- `EarthScience.henry_doubling`: doubling `p` doubles `c`.
- `EarthScience.henry_zero_pressure`: zero pressure gives zero concentration.
- `EarthScience.henry_conversion_reciprocal`: the two conventions are
  reciprocals.

## iii. Table of contents

- A. Doubling and zero pressure
- B. Convention conversion

## iv. References

- R. Sander et al., *Henry's law constants (IUPAC Recommendations 2021)*,
  Pure Appl. Chem. 94 (2022), 71–85, https://doi.org/10.1515/PAC-2020-0302.
- R. Sander, *Compilation of Henry's law constants (version 5.0.0) for
  water as solvent*, Atmos. Chem. Phys. 23 (2023), 10901–12440,
  https://doi.org/10.5194/acp-23-10901-2023, §2.1 and Table 1.
  The constants here use the concentration/partial-pressure convention:
  `H` and `H_cp` denote the solubility constant `H_s^{cp} = c_a / p`,
  while `H_pc` denotes the volatility constant `H_v^{pc} = p / c_a`.
  Table 1 gives `H_v^{pc} = 1 / H_s^{cp}`. These equilibrium constants
  refer to the infinite-dilution limit at fixed temperature and solvent;
  this module assumes the resulting proportionality law.
- Field arithmetic in Mathlib (`field_simp`, `mul_inv_cancel`).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Doubling and zero pressure -/

/-- Henry's law doubling: for a Henry constant `H > 0` and a nonnegative
partial pressure `p ≥ 0`, under `c = H * p`, doubling the gas partial
pressure doubles the dissolved equilibrium concentration. -/
theorem henry_doubling {H p c : ℝ} (_hH : 0 < H) (_hp : 0 ≤ p) (h : c = H * p) :
    H * (2 * p) = 2 * c := by
  rw [h]
  ring

/-- Zero partial pressure gives zero dissolved concentration: for a Henry
constant `H > 0`, if `c = H * 0` then `c = 0`. -/
theorem henry_zero_pressure {H c : ℝ} (_hH : 0 < H) (h : c = H * (0 : ℝ)) :
    c = 0 := by
  rw [h, mul_zero]

/-! ## B. Convention conversion -/

/-- Henry-constant conversion: the `H_cp` (concentration/pressure) and
`H_pc` (pressure/concentration) conventions are reciprocals for nonzero
constants: if `H_cp = 1 / H_pc` then `H_pc = 1 / H_cp`. -/
theorem henry_conversion_reciprocal {H_cp H_pc : ℝ} (hpc : H_pc ≠ 0)
    (h : H_cp = 1 / H_pc) :
    H_pc = 1 / H_cp := by
  have hcp : H_cp ≠ 0 := by rw [h]; exact one_div_ne_zero hpc
  field_simp
  rw [h]
  field_simp

end EarthScience
