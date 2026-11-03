/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CutResummation

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CutResummation`

* `shb_tsum_weight_cut_factor` and `shb_cutJoinMass_factor` on `K₂` at `β = J = 1`, cutting
  along the predicate "every edge" (one side is empty);
* `shb_weight_cutJoin_split` for any cut;
* `shb_cutEquiv` is an equivalence (round trip).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2CutResummation

open _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The full mass factorizes across the trivial cut on `K₂`.
example : shb_fullWeightMass (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) =
    shb_cutLeftMass (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) (fun _ => True) *
      shb_cutRightMass (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) (fun _ => True) :=
  shb_tsum_weight_cut_factor ⊤ 1 _ _

-- The same for the joined mass.
example : shb_cutJoinMass (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) (fun _ => True) =
    shb_cutLeftMass (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) (fun _ => True) *
      shb_cutRightMass (⊤ : SimpleGraph (Fin 2)) 1 (fun _ => 1) (fun _ => True) :=
  shb_cutJoinMass_factor ⊤ 1 _ _

-- Weights split across a cut.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] (a : { e // P e } → ℕ) (b : { e // ¬ P e } → ℕ) :
    weight G β J (ofEdgeFun G (shb_cutJoin G P (a, b))) =
      weight G β J (ofEdgeFun G (shb_cutLeft G P a)) *
        weight G β J (ofEdgeFun G (shb_cutRight G P b)) :=
  shb_weight_cutJoin_split G β J P a b

-- The cut equivalence round-trips.
example {V : Type*} [Fintype V] (G : SimpleGraph V) (P : G.edgeFinset → Prop) [DecidablePred P]
    (m : G.edgeFinset → ℕ) : (shb_cutEquiv G P).symm (shb_cutEquiv G P m) = m :=
  (shb_cutEquiv G P).symm_apply_apply m

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2CutResummation
