/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.PartialEdgeCopySwitching
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Literal

/-!
# No support-lex domain resummation on `K₄`

The cross-multiplied domain-monotonicity inequality `shb_P3DomainResummation` fails for the literal
backbone weight on `K₄ \ 12 ⊆ K₄`, so domain monotonicity (P3) of the support-ordered backbone
weight does not hold for all graphs.

## i. Overview

`SupportLexK4Literal` shows that the literal support-ordered backbone weight `shb_rhoSupport` of
the direct path `0 → 3` is strictly larger in `K₄` than in `K₄ \ 12` at `β = artanh (2/3)`,
`J ≡ 1`. Since P3 follows from `shb_P3DomainResummation` (`shb_P3_support_of_domainResummation`),
the resummation inequality fails there, and the universal P3 statement over `Fin 4` is false.

Headline fidelity: both results are unconditional refutations. In particular
`shb_P3DomainResummation` does not hold for every subgraph pair, so a result assuming it for all
graphs would be vacuous for the support-lex selector.

## ii. Key results

- `shb_supportLex_literal_domainResummation_counterexample` : `shb_P3DomainResummation` fails on
  `K₄ \ 12 ⊆ K₄` (unconditional)
- `shb_no_universal_supportLex_P3` : P3 for `shb_rhoSupport` fails for some graphs on `Fin 4`
  (unconditional)

## iii. Table of contents

- A. Failure of domain monotonicity on `K₄`

## iv. References

None beyond those in the imported modules.
-/
@[expose] public section

namespace StatMech.Sharpness

/-! ## A. Failure of domain monotonicity on `K₄` -/

/-- The domain-resummation inequality fails for the direct path of `K₄ \ 12 ⊆ K₄` at
`β = artanh (2/3)`, `J ≡ 1`. -/
theorem shb_supportLex_literal_domainResummation_counterexample :
    ¬shb_P3DomainResummation
      (shbK4Graph shbK4H) (shbK4Graph shbK4G)
      (shbK4Graph_mono shbK4H_subset_shbK4G)
      (Real.artanh (2 / 3)) (fun _ => 1)
      (shbK4DirectPath shbK4H (by decide)) := by
  intro hresum
  have hle := shb_P3_support_of_domainResummation
    (shbK4Graph shbK4H) (shbK4Graph shbK4G)
    (shbK4Graph_mono shbK4H_subset_shbK4G)
    (Real.artanh (2 / 3)) (fun _ => 1)
    (shbK4DirectPath shbK4H (by decide)) hresum
  exact (not_le_of_gt shb_supportLex_literal_P3_counterexample) hle

/-- Domain monotonicity of the support-ordered backbone weight fails for some graphs on `Fin 4`. -/
theorem shb_no_universal_supportLex_P3 :
    ¬(∀ (H G : SimpleGraph (Fin 4))
        [DecidableRel H.Adj] [DecidableRel G.Adj]
        (hHG : H ≤ G) (beta : Real) (J : Sym2 (Fin 4) -> Real)
        {x y : Fin 4} (p : H.Path x y),
      shb_rhoSupport G beta J x y (shb_pathMapLe hHG p) ≤
        shb_rhoSupport H beta J x y p) := by
  intro hP3
  have hle := hP3
    (shbK4Graph shbK4H) (shbK4Graph shbK4G)
    (shbK4Graph_mono shbK4H_subset_shbK4G)
    (Real.artanh (2 / 3)) (fun _ => 1)
    (shbK4DirectPath shbK4H (by decide))
  exact (not_le_of_gt shb_supportLex_literal_P3_counterexample) hle

end StatMech.Sharpness

