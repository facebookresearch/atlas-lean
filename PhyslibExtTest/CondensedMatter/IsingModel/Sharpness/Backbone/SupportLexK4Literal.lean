/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Literal

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Literal`

* `shb_supportLex_literal_P3_counterexample`: on `K₄`, `ρ_{K₄ \ 12}(0 → 3) < ρ_{K₄}(0 → 3)`;
* `shbK4_rhoSupport_eq_directRhoSeries` at `x = 0` on the full `K₄`;
* `shb_current_tsum_eq_paritySeriesMassOn` for the trivial predicate.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Literal

open _root_.StatMech.Sharpness

-- The literal P3 counterexample on `K₄`.
example := shb_supportLex_literal_P3_counterexample

-- The literal weight is the series weight (here at `x = 1`).
example (h03 : shbK4Edge.e03 ∈ shbK4G) :
    shb_rhoSupport (shbK4Graph shbK4G) 1 (fun _ => 1) 0 3 (shbK4DirectPath shbK4G h03) =
      shbK4DirectRhoSeries shbK4G 1 :=
  shbK4_rhoSupport_eq_directRhoSeries shbK4G h03 1 zero_le_one

-- Current series grouped by parity support, for the trivial predicate.
example (S : Finset (Fin 2)) :
    (∑' m : S → ℕ, if True then ∏ e, shbCurrentTerm 1 (m e) else 0) =
      shbParitySeriesMassOn S (fun _ => True) 1 :=
  shb_current_tsum_eq_paritySeriesMassOn S (fun _ => True) 1 zero_le_one

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Literal
