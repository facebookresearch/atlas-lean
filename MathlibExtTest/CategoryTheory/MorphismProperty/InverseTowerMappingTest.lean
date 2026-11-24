/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.MorphismProperty.InverseTowerMapping

set_option autoImplicit false
noncomputable section
universe w uC vC uV vV

open CategoryTheory CategoryTheory.Limits Opposite

namespace InverseTowerMappingClients

variable {C : Type uC} [Category.{vC} C] {V : Type uV} [Category.{vV} V]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (G : Cᵒᵖ ⥤ V) [PreservesLimitsOfSize.{w, w} G]

/-- A neutral source functor carries the caller's actual predecessor colimit to its limit. -/
example (Q : J ⥤ C) [Q.IsWellOrderContinuous] (m : J) (hm : Order.IsSuccLimit m) :
    IsLimit (OriginalInverseTowerLifting.precedingCone (Q.op ⋙ G) m) :=
  OriginalInverseTowerLifting.sourcePrecedingIsLimit G Q m hm

/-- Full source limits and successor lifting give the caller's actual initial restriction. -/
example (P : MorphismProperty V) (Q : J ⥤ C) [Q.IsWellOrderContinuous]
    (q : Cocone Q) (hq : IsColimit q)
    (hSucc : ∀ j : J, ¬IsMax j → P.rlp ((Q.op ⋙ G).map (homOfLE (Order.le_succ j)).op)) :
    P.rlp (G.map (q.ι.app ⊥).op) := by
  let D := Q.op ⋙ G
  let c := G.mapCone q.op
  let hc := isLimitOfPreserves G hq.op
  let : D.rightOp.IsWellOrderContinuous :=
    OriginalInverseTowerLifting.sourceMappingWellOrderContinuous G Q
  exact MorphismProperty.continuous_inverse_tower_rlp P D c hc hSucc

end InverseTowerMappingClients
