/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 380

/-!
# Bessel Function of the First Kind

## References

* See the NIST Digital Library of Mathematical Functions, equation 10.2.2:
  https://dlmf.nist.gov/10.2.E2, See also: A. Baricz, C. G. Kokologiannaki and T. K. Pogany, Zeros
  of Bessel Function Derivatives, Proceedings of the American Mathematical Society 146 (2018),
  209-222. https://doi.org/10.1090/proc/13725 https://arxiv.org/abs/1602.04295 (for `besselJ`)
-/

namespace MetaMathlibExt

-- Analysis 380: Bessel Function of the First Kind

/-- For real order ν and complex argument z, the Bessel function of the
first kind is defined by

J_ν(z)=∑ₖ₌₀^∞((-1)ᵏ)/(k!Γ(ν+k+1))(z/2)^{2k+ν}.

For noninteger ν, the complex power is interpreted using the principal
branch.
-/
noncomputable def besselJ
    (ν : ℝ)
    (z : ℂ) : ℂ :=
  ∑' k : ℕ,
    ((-1 : ℂ) ^ k /
      ((Nat.factorial k : ℂ) *
        Complex.Gamma ((ν : ℂ) + (k : ℂ) + 1))) *
      Complex.cpow (z / 2)
        (((2 * k : ℕ) : ℂ) + (ν : ℂ))

end MetaMathlibExt

end
