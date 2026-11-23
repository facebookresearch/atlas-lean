/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.BasedWhiteheadUniverseLift

open CategoryTheory Topology Set

universe u v w

#check Topology.CWComplex.uliftCWComplex
#print axioms Topology.CWComplex.uliftCWComplex
#check Topology.CWComplex.basedCWTypeWhiteheadIndependentModels
#print axioms Topology.CWComplex.basedCWTypeWhiteheadIndependentModels

-- The literal old zero-cell identifier lifts and remains that point at every coordinate.
example (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (x : X) (j : (inferInstance : CWComplex (Set.univ : Set X)).cell 0)
    (hj : (inferInstance : CWComplex (Set.univ : Set X)).map 0 j ![] = x) :
    let cw : CWComplex (Set.univ : Set (ULift.{v} X)) := CWComplex.uliftCWComplex X
    ∃ j' : cw.cell 0, ∀ z : Fin 0 → ℝ, cw.map 0 j' z = ULift.up x := by
  refine ⟨ULift.up j, ?_⟩
  intro z
  have hz : z = ![] := Subsingleton.elim _ _
  change ULift.up ((inferInstance : CWComplex (Set.univ : Set X)).map 0 j z) = ULift.up x
  rw [hz, hj]

-- The actual lifted weak topology is usable without a separation assumption on X.
example (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Set (ULift.{v} X)) :
    let cw : CWComplex (Set.univ : Set (ULift.{v} X)) := CWComplex.uliftCWComplex X
    (∀ n j, IsClosed (A ∩ cw.map n j '' Metric.closedBall 0 1)) → IsClosed A := by
  dsimp only
  intro hA
  exact (CWComplex.uliftCWComplex X).closed' A (Set.subset_univ _) hA

section IndependentModels

variable (X Y : TopCat.{u}) (CX : TopCat.{v}) (CY : TopCat.{w})
  [T2Space CX] [T2Space CY]
  [CWComplex (Set.univ : Set CX)] [CWComplex (Set.univ : Set CY)]
  (x : X) (y : Y) (cx : CX) (cy : CY)
  (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0) (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
  (hjx : Topology.CWComplex.map 0 jx ![] = cx) (hjy : Topology.CWComplex.map 0 jy ![] = cy)
  (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
  (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
  (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
  (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
  (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
  (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
  (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f)

-- Both whole families have the exact initial and final maps on the original carriers.
example : ∃ g : Y ⟶ X, g y = x ∧
    ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (TopCat.Hom.hom (𝟙 X)) {x},
    ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (TopCat.Hom.hom (𝟙 Y)) {y},
      HL.toHomotopy.curry 0 = (f ≫ g).hom ∧
      HL.toHomotopy.curry 1 = TopCat.Hom.hom (𝟙 X) ∧
      HR.toHomotopy.curry 0 = (g ≫ f).hom ∧
      HR.toHomotopy.curry 1 = TopCat.Hom.hom (𝟙 Y) := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ := CWComplex.basedCWTypeWhiteheadIndependentModels
    X Y CX CY x y cx cy jx jy hjx hjy rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf
  exact ⟨g, hg, HL, HR, HL.toHomotopy.curry_zero, HL.toHomotopy.curry_one,
    HR.toHomotopy.curry_zero, HR.toHomotopy.curry_one⟩

-- Independent times fix the two independently selected original points.
example : ∃ g : Y ⟶ X, g y = x ∧
    ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (TopCat.Hom.hom (𝟙 X)) {x},
    ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (TopCat.Hom.hom (𝟙 Y)) {y},
      ∀ s t : unitInterval, HL (s, x) = x ∧ HR (t, y) = y := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ := CWComplex.basedCWTypeWhiteheadIndependentModels
    X Y CX CY x y cx cy jx jy hjx hjy rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf
  exact ⟨g, hg, HL, HR, fun s t => ⟨HL.eq_snd s (Set.mem_singleton x),
    HR.eq_snd t (Set.mem_singleton y)⟩⟩

-- The ordinary equivalence has the ORIGINAL forward map and same based inverse.
example : ∃ E : ContinuousMap.HomotopyEquiv X Y,
    E.toFun = f.hom ∧ E.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (E.invFun.comp E.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (E.toFun.comp E.invFun) (ContinuousMap.id Y) {y}) := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ := CWComplex.basedCWTypeWhiteheadIndependentModels
    X Y CX CY x y cx cy jx jy hjx hjy rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf
  let E : ContinuousMap.HomotopyEquiv X Y :=
    { toFun := f.hom
      invFun := g.hom
      left_inv := ⟨HL.toHomotopy.cast (TopCat.hom_comp f g) (TopCat.hom_id (X := X))⟩
      right_inv := ⟨HR.toHomotopy.cast (TopCat.hom_comp g f) (TopCat.hom_id (X := Y))⟩ }
  exact ⟨E, rfl, hg, ⟨HL.cast (TopCat.hom_comp f g) (TopCat.hom_id (X := X))⟩,
    ⟨HR.cast (TopCat.hom_comp g f) (TopCat.hom_id (X := Y))⟩⟩

end IndependentModels
