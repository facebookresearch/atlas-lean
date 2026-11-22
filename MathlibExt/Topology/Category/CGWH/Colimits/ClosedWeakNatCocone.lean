/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHWeakHomotopyTransfiniteClosed

/-!
# The original closed weak Nat cocone and its whole transfinite witness

Every chosen diagram, stage-zero map and actual cocone leg remains. The
native closed transfinite weak-equivalence closure proves weakness of the
same chosen endpoint, with independent native universes.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Topology

namespace CGWH.ClosedWeakNatCocone

/-- The full actual same-cocone transfinite witness uses the original F, legs and stage zero. -/
def transfinite {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hStep : ∀ n : ℕ, CGWH.weakHomotopyEquivalences (F.map (homOfLE (Nat.le_succ n))) ∧
      IsClosedEmbedding (ConcreteCategory.hom (F.map (homOfLE (Nat.le_succ n))))) :
    (CGWH.weakHomotopyEquivalences ⊓
      TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop).TransfiniteCompositionOfShape
      ℕ (c.ι.app 0) where
  F := F
  isoBot := Iso.refl (F.obj 0)
  incl := c.ι
  isColimit := hc
  fac := Category.id_comp _
  map_mem n _hn := hStep n

/-- The entire original diagram is retained by the actual witness. -/
theorem transfinite_F {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hStep : ∀ n : ℕ, CGWH.weakHomotopyEquivalences (F.map (homOfLE (Nat.le_succ n))) ∧
      IsClosedEmbedding (ConcreteCategory.hom (F.map (homOfLE (Nat.le_succ n))))) :
    (transfinite c hc hStep).F = F := rfl

/-- The entire original cocone-leg function is retained by the actual witness. -/
theorem transfinite_incl {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hStep : ∀ n : ℕ, CGWH.weakHomotopyEquivalences (F.map (homOfLE (Nat.le_succ n))) ∧
      IsClosedEmbedding (ConcreteCategory.hom (F.map (homOfLE (Nat.le_succ n))))) :
    (transfinite c hc hStep).incl = c.ι := rfl

/-- The actual original identity stage-zero comparison is retained whole. -/
theorem transfinite_isoBot {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hStep : ∀ n : ℕ, CGWH.weakHomotopyEquivalences (F.map (homOfLE (Nat.le_succ n))) ∧
      IsClosedEmbedding (ConcreteCategory.hom (F.map (homOfLE (Nat.le_succ n))))) :
    (transfinite c hc hStep).isoBot = Iso.refl (F.obj 0) := rfl

/-- Genuine native closed transfinite closure gives weakness of the SAME actual original leg. -/
theorem endpoint_weak {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hStep : ∀ n : ℕ, CGWH.weakHomotopyEquivalences (F.map (homOfLE (Nat.le_succ n))) ∧
      IsClosedEmbedding (ConcreteCategory.hom (F.map (homOfLE (Nat.le_succ n))))) :
    CGWH.weakHomotopyEquivalences (c.ι.app 0) := by
  let e : ULift.{v} ℕ ≃o ℕ := ULift.orderIso
  let _ : SuccOrder (ULift.{v} ℕ) := SuccOrder.ofOrderIso e.symm
  exact CGWH.weakHomotopyEquivalences.of_transfiniteComposition_closed
    (J := ULift.{v} ℕ) (X := F.obj 0) (Y := c.pt) (f := c.ι.app 0)
    ((transfinite c hc hStep).ofOrderIso e)

end CGWH.ClosedWeakNatCocone
