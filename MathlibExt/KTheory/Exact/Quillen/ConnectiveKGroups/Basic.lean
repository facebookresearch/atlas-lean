/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpace

/-!
# Raw connective Quillen carriers

The constant loop and cube-based homotopy carrier retain the original
Quillen nerve realization and chosen zero point. This basic interface
provides no Q/S comparison, K-zero dictionary or functorial group map.
-/

public section
noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe uC vC

namespace AlgebraicKTheory.ConnectiveKGroups

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The original chosen zero is the basepoint of every raw connective carrier. -/
abbrev zeroLoop : NQKSpace C := Path.refl (NQReal.basepoint C)

/-- The generic raw degree-n K-group carrier is the original cube homotopy carrier. -/
abbrev rawCarrier (n : ℕ) := HomotopyGroup.Pi n (NQKSpace C) (zeroLoop C)

end AlgebraicKTheory.ConnectiveKGroups

end
