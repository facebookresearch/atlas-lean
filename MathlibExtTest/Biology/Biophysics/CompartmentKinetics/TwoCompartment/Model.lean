/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model

/-! Tests: component equations at concrete rates. -/

open Matrix

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model

open MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model

/-- Central component at rates `1, 2, 3`. -/
example : (pk2Generator 1 2 3 *ᵥ ![4, 5]) 0 = -(1 + 2) * 4 + 3 * 5 :=
  pk2_central_component 1 2 3 4 5

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model
