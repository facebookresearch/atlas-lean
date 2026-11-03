/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexDomainResummationCounterexample

/-!
# Tests for `SupportLexDomainResummationCounterexample`

Module under test:
`PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexDomainResummationCounterexample`

* `shb_no_universal_supportLex_P3` (refutation): support-lex P3 fails on `Fin 4`;
* `shb_supportLex_literal_domainResummation_counterexample` (refutation): the domain
  resummation hypothesis fails on the `K₄` pair, so `shb_P3DomainResummation` is not universal.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone
namespace SupportLexDomainResummationCounterexample

open _root_.StatMech.Sharpness

-- No universal P3 for the support-lex weight.
example : ¬ ∀ (H G : SimpleGraph (Fin 4)) [DecidableRel H.Adj] [DecidableRel G.Adj] (hHG : H ≤ G)
    (β : ℝ) (J : Sym2 (Fin 4) → ℝ) {x y : Fin 4} (p : H.Path x y),
    shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p :=
  shb_no_universal_supportLex_P3

-- The domain resummation fails on the `K₄` pair.
example := shb_supportLex_literal_domainResummation_counterexample

-- Hence the domain resummation is not universal on `Fin 4`.
example : ¬ ∀ (H G : SimpleGraph (Fin 4)) [DecidableRel H.Adj] [DecidableRel G.Adj] (hHG : H ≤ G)
    (β : ℝ) (J : Sym2 (Fin 4) → ℝ) {x y : Fin 4} (p : H.Path x y),
    shb_P3DomainResummation H G hHG β J p :=
  fun h => shb_supportLex_literal_domainResummation_counterexample (h _ _ _ _ _ _)

end SupportLexDomainResummationCounterexample
end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone
