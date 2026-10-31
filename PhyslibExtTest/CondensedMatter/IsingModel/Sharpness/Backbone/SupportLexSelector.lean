/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexSelector

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexSelector`

* `shb_P1_support` (the sum rule P1, unconditional) on `K₂` at `β = J = 1`;
* `shb_backboneSelectSupport_mapLe` applied to a current supported on the subgraph;
* `shb_P2_support_of_complementResummation` applied under its resummation hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexSelector

open _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The sum rule on `K₂`.
example : expectationJ (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) {0, 1} =
    ∑ p, shb_rhoSupport (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) 0 1 p :=
  shb_P1_support ⊤ 1 _ zero_le_one (fun _ => zero_le_one) (by decide)

-- Selection commutes with inclusion of a supporting subgraph.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {H G : SimpleGraph V}
    (hHG : H ≤ G) (n : Current V) (hn : shb_CurrentSupportedOn H n) (x y : V) :
    Option.map (shb_pathMapLe hHG) (shb_backboneSelectSupport H n x y) =
      shb_backboneSelectSupport G n x y :=
  shb_backboneSelectSupport_mapLe hHG n hn x y

-- The chain rule under the complement resummation.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G H : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) {x z u : V} (p₁₂ : G.Path x z) (p₁ : G.Path x u) (p₂ : H.Path u z)
    (h : shb_P2ComplementResummation G H β J p₁₂ p₁ p₂) :
    shb_rhoSupport G β J x z p₁₂ = shb_rhoSupport G β J x u p₁ * shb_rhoSupport H β J u z p₂ :=
  shb_P2_support_of_complementResummation G H β J p₁₂ p₁ p₂ h

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexSelector
