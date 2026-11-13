/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.BackbonePartialEdgeCopySwitching
import Code.Sharpness.BackboneSupportLexK4Literal

namespace StatMech.Sharpness



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

