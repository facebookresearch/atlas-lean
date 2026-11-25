/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Closed-star-ideal quotient API examples

Functions vanishing at infinity supply an actual nonunital coefficient algebra.
The top ideal produces the zero quotient, while the bottom quotient retains
coefficients and their original norm bound. All quotient dictionaries below
come from the bundled closed ideals' actual constructors.
-/

noncomputable section
open scoped ZeroAtInfty
namespace ClosedStarIdealSmoke

private abbrev Coefficients := C₀(ℝ, ℂ)
private abbrev zeroIdeal := ClosedStarIdeal.bot Coefficients
private abbrev wholeIdeal := ClosedStarIdeal.top Coefficients

local instance : NonUnitalCStarAlgebra zeroIdeal.Quotient :=
  zeroIdeal.quotientCStarAlgebra
local instance : NonUnitalCStarAlgebra wholeIdeal.Quotient :=
  wholeIdeal.quotientCStarAlgebra

-- No coefficient survives the quotient by the whole algebra.
example (f : Coefficients) : wholeIdeal.quotientMap f = 0 :=
  (wholeIdeal.quotientMap_eq_zero_iff f).2 (ClosedStarIdeal.mem_top f)

-- The bottom quotient kills exactly zero, including for nonunital coefficients.
example (f : Coefficients) : zeroIdeal.quotientMap f = 0 ↔ f = 0 := by
  rw [zeroIdeal.quotientMap_eq_zero_iff, ClosedStarIdeal.mem_bot]

-- The actual quotient projection is contractive in its inherited C-star norm.
example (f : Coefficients) : ‖zeroIdeal.quotientMap f‖ ≤ ‖f‖ :=
  NonUnitalStarAlgHom.norm_apply_le zeroIdeal.quotientMap f

-- Multiplication and involution remain those of the original nonunital quotient.
example (f g : Coefficients) :
    zeroIdeal.quotientMap (f * g) = zeroIdeal.quotientMap f * zeroIdeal.quotientMap g :=
  map_mul zeroIdeal.quotientMap f g

example (f : Coefficients) :
    zeroIdeal.quotientMap (star f) = star (zeroIdeal.quotientMap f) :=
  map_star zeroIdeal.quotientMap f

end ClosedStarIdealSmoke
