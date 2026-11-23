/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.FibrationCoproducts

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

example {ι : Type u} {A B : ι → TopCat.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) : Fibration (Limits.Sigma.map q) :=
  fibration_sigmaMap q hq

example {ι : Type u} (X B : ι → TopCat.{u}) : Fibration (sigmaProductProjection X B) :=
  fibration_sigmaProductProjection X B

example {ι : Type u} (X B : ι → TopCat.{u}) (c : ι) (x : X c) (b : B c) :
    sigmaProductProjection X B ⟨c, x, b⟩ = ⟨c, b⟩ :=
  sigmaProductProjection_apply X B c x b

end TopCat
