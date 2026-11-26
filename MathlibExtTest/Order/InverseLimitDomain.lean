/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.InverseLimitDomain

/-!
# Scott's model over the two-element lattice

The level-zero projection distinguishes the images of the two Boolean values in the model.
-/

open MathlibExt.Order.ScottContinuity.ContinuousLattice
open MathlibExt.Order.InverseLimitDomainWanted

example : ∃ (D : Type) (_ : CompleteLattice D), IsContinuousLattice D ∧ Nontrivial D ∧
    Nonempty (D ≃o {f : D → D // ScottContinuous f}) := by
  obtain ⟨D, lattice, iso, e, p, hD, _, _, hpe, _⟩ :=
    exists_orderIso_scottContinuous_self Bool isContinuousLattice_bool
  have hleft : Function.LeftInverse p e := congrFun hpe
  exact ⟨D, lattice, hD, ⟨e false, e true, hleft.injective.ne (by decide)⟩, ⟨iso⟩⟩
