/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Realization

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Realization`

* `shbK4_sources_eq_boundary` for the zero current on `K₄`;
* `shbK4_source_selector_fiber_iff` and `shbK4_isBackboneOf_iff_pathSupported` on any `K₄`
  subgraph;
* `shb_backboneSelectSupport_eq_some_iff` (the selector picks the least backbone).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Realization

open _root_.StatMech.Sharpness

-- Sources are the boundary of the odd support (zero current).
example : sources (shbK4Graph shbK4G) (fun _ => 0) =
    shbK4Boundary (shbK4OddSupport shbK4G fun _ => 0) :=
  shbK4_sources_eq_boundary shbK4G _

-- The literal direct-path fiber is the parity-model fiber.
example (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) (n : Current (Fin 4)) :
    sources (shbK4Graph E) n = {0, 3} ∧
        shb_backboneSelectSupport (shbK4Graph E) n 0 3 = some (shbK4DirectPath E h03) ↔
      shbK4SelectsDirect03 (shbK4OddSupport E n) :=
  shbK4_source_selector_fiber_iff E h03 n

-- Backbones are the paths supported by the odd support.
example (E : Finset shbK4Edge) (n : Current (Fin 4)) (x y : Fin 4) (p : (shbK4Graph E).Path x y) :
    shb_IsBackboneOf (shbK4Graph E) n x y p ↔ shbK4PathSupported (shbK4OddSupport E n) p :=
  shbK4_isBackboneOf_iff_pathSupported E n p

-- The support-lex selector picks the least backbone.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : Current V) (x y : V) (p : G.Path x y) :=
  shb_backboneSelectSupport_eq_some_iff G n x y p

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Realization
