/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.BasedWhitehead

/-! # Ordinary public clients for the original-map based CW Whitehead theorem -/

open CategoryTheory Topology Topology.CWComplex

universe u

#check Topology.CWComplex.subcomplexInclusion_mem_realizedBoundaryLLP
#print axioms Topology.CWComplex.subcomplexInclusion_mem_realizedBoundaryLLP
#check Topology.CWComplex.basedCWTypeWhitehead
#print axioms Topology.CWComplex.basedCWTypeWhitehead

section BasedModels

variable (X Y CX CY : TopCat.{u}) [T2Space CX] [T2Space CY]
  [CWComplex (Set.univ : Set CX)] [CWComplex (Set.univ : Set CY)]
  (x : X) (y : Y) (cx : CX) (cy : CY)
  (jx : cell (Set.univ : Set CX) 0) (jy : cell (Set.univ : Set CY) 0)
  (hjx : map 0 jx ![] = cx) (hjy : map 0 jy ![] = cy)
  (rx : X ⟶ CX) (sx : CX ⟶ X) (ry : Y ⟶ CY) (sy : CY ⟶ Y)
  (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
  (LX : ContinuousMap.HomotopyRel (rx ≫ sx).hom (𝟙 X : X ⟶ X).hom {x})
  (RX : ContinuousMap.HomotopyRel (sx ≫ rx).hom (𝟙 CX : CX ⟶ CX).hom {cx})
  (LY : ContinuousMap.HomotopyRel (ry ≫ sy).hom (𝟙 Y : Y ⟶ Y).hom {y})
  (RY : ContinuousMap.HomotopyRel (sy ≫ ry).hom (𝟙 CY : CY ⟶ CY).hom {cy})
  (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f)

-- Both full curried endpoint maps use the same actual inverse and original f.
example : ∃ g : Y ⟶ X, g y = x ∧
    ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x},
    ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y},
      HL.toContinuousMap.curry 0 = (f ≫ g).hom ∧
      HL.toContinuousMap.curry 1 = (𝟙 X : X ⟶ X).hom ∧
      HR.toContinuousMap.curry 0 = (g ≫ f).hom ∧
      HR.toContinuousMap.curry 1 = (𝟙 Y : Y ⟶ Y).hom := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ := basedCWTypeWhitehead X Y CX CY x y cx cy jx jy hjx hjy
    rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf
  refine ⟨g, hg, HL, HR, ?_, ?_, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro z
    exact HL.map_zero_left z
  · apply ContinuousMap.ext
    intro z
    exact HL.map_one_left z
  · apply ContinuousMap.ext
    intro z
    exact HR.map_zero_left z
  · apply ContinuousMap.ext
    intro z
    exact HR.map_one_left z

-- Independent time parameters fix both literal original points.
example : ∃ g : Y ⟶ X, g y = x ∧
    ∃ HL : ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x},
    ∃ HR : ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {y},
      ∀ s t : unitInterval, HL (s, x) = x ∧ HR (t, y) = y := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ := basedCWTypeWhitehead X Y CX CY x y cx cy jx jy hjx hjy
    rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf
  refine ⟨g, hg, HL, HR, ?_⟩
  intro s t
  exact ⟨HL.eq_snd s (Set.mem_singleton x), HR.eq_snd t (Set.mem_singleton y)⟩

-- The ordinary equivalence retains the original forward map and based inverse data.
example : ∃ e : ContinuousMap.HomotopyEquiv X Y,
    e.toFun = f.hom ∧ e.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel
        (e.invFun.comp e.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel
        (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) := by
  obtain ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩ := basedCWTypeWhitehead X Y CX CY x y cx cy jx jy hjx hjy
    rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf
  let e : ContinuousMap.HomotopyEquiv X Y :=
    { toFun := f.hom
      invFun := g.hom
      left_inv := ⟨HL.toHomotopy⟩
      right_inv := ⟨HR.toHomotopy⟩ }
  exact ⟨e, rfl, hg, ⟨HL⟩, ⟨HR⟩⟩

end BasedModels
