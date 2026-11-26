/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelector

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelector`

* `shb_DynamicEdgeExploration.selects_append_iff` with an empty prefix;
* `shb_ExplorationKernel.weight_append` and `weight_antitone` for any kernel;
* the chain rule `P2` and monotonicity `P3` of a `ρ`-realization.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelector

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.shb_DynamicEdgeExploration
open _root_.StatMech.Sharpness.shb_ExplorationKernel
open _root_.StatMech.Sharpness.shb_ExplorationRhoRealization

-- Selecting `[] ++ q` is selecting `[]` and then `q` from the residual.
example {D E : Type*} (X : shb_DynamicEdgeExploration D E) (adm : D → E → Bool) (d : D)
    (q : List E) :
    X.Selects adm d ([] ++ q) ↔ X.Selects adm d [] ∧ X.Selects adm (X.residual d []) q :=
  X.selects_append_iff adm d [] q

-- Kernel weights multiply along concatenation and decrease with the domain.
example {D E : Type*} [Preorder D] [DecidableEq E] (K : shb_ExplorationKernel D E) (d : D)
    (p q : List E) {small large : D} (hle : small ≤ large) :
    K.weight d (p ++ q) = K.weight d p * K.weight (K.exploration.residual d p) q ∧
      K.weight large p ≤ K.weight small p :=
  ⟨K.weight_append d p q, K.weight_antitone hle p⟩

-- The chain rule and monotonicity of a realization.
example {D E : Type*} [Preorder D] [DecidableEq E] (R : shb_ExplorationRhoRealization D E)
    (d : D) (p q : List E) {small large : D} (hle : small ≤ large) :
    R.rho d (p ++ q) = R.rho d p * R.rho (R.kernel.exploration.residual d p) q ∧
      R.rho large p ≤ R.rho small p :=
  ⟨R.P2 d p q, R.P3 hle p⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelector
