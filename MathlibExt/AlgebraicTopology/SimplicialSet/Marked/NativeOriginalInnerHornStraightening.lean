/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalInnerHornWeakAttachment
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverFibrationCells

/-!
# Every original inner cell and actual native unstraightening

The original inner-cell summand keeps every original whole target map
to the base. Marked identity carriers identify each exact original
slice cell with its same physical native horn inclusion. The proved
weak image and the actual native adjunction therefore give the original
inner-cell right lifts for unstraightening every actual coherent-model
fibration. These are genuine underlying inner fibrations over arbitrary
original bases; the remaining Cartesian conditions are separate proofs.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original entire inner-cell summand retains its exact original horn dimensions and omitted indices. -/
abbrev NativeOriginalInnerCellIndex :=
  Σ n : ℕ, {i : Fin (n + 3) // 0 < i ∧ i < Fin.last (n + 2)}

/-- Each original inner cell is precisely the same original Cartesian cell at its unchanged inner summand index. -/
def nativeOriginalInnerCell (s : NativeOriginalInnerCellIndex) : Arrow Marked.{u} :=
  cartesianCell (.inl s)

/-- The original inner cells retain every actual whole target map into the same original maximally marked base. -/
def nativeOriginalInnerCellsOver (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  overCells nativeOriginalInnerCell.{u} (max B)

/-- Each original whole-base inner cell is genuinely isomorphic to its same physical native minimally marked horn
inclusion, through marked identity carriers and the original full Yoneda base equation. -/
def nativeOriginalInnerHornOverCellArrowIso (B : SSet.{u})
    (s : OverCellIndex nativeOriginalInnerCell.{u} (max B)) :
    Arrow.mk (overCell nativeOriginalInnerCell.{u} (max B) s) ≅
      Arrow.mk (nativeSubcomplexInclusion B (s.1.1 + 2) (SSet.yonedaEquiv s.2.hom)
        (horn (s.1.1 + 2) s.1.2.val)) := by
  rcases s with ⟨⟨n, ⟨i, hi, hi'⟩⟩, p⟩
  let q : (Δ[n + 2] : SSet.{u}) ⟶ B := p.hom
  have hq : SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q := SSet.yonedaEquiv.symm_apply_apply q
  let X : Over.mk (innerCell n i ≫ p) ≅
      nativeSubcomplexBasis B (n + 2) (SSet.yonedaEquiv p.hom) (horn (n + 2) i) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change (𝟙 (horn (n + 2) i : SSet.{u})) ≫
        ((horn (n + 2) i).ι ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv q)) = (horn (n + 2) i).ι ≫ q
      exact (Category.id_comp _).trans (congrArg (fun f => (horn (n + 2) i).ι ≫ f) hq))
  let Y : Over.mk p ≅ nativeSimplexBasis B (n + 2) (SSet.yonedaEquiv p.hom) :=
    Over.isoMk (Iso.refl _) (by
      apply Hom.ext
      change (𝟙 (Δ[n + 2] : SSet.{u})) ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv q) = q
      exact (Category.id_comp _).trans hq)
  exact Arrow.isoMk X Y (by
    apply Over.OverMorphism.ext
    apply Hom.ext
    ext r a
    rfl)

/-- Every same actual original inner cell over every whole original target-to-base map straightens into the genuine
full weak projective left class. -/
theorem nativeOriginalInnerCell_straightening_projectiveWeakLeft (B : SSet.{u})
    (s : OverCellIndex nativeOriginalInnerCell.{u} (max B)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (overCell nativeOriginalInnerCell.{u} (max B) s)) := by
  let P := ((enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp).inverseImage
    (nativeStraightening B)
  exact (P.arrow_iso_iff (nativeOriginalInnerHornOverCellArrowIso B s)).mpr
    (nativeOriginalInnerHornInclusion_straightening_projectiveWeakLeft B (SSet.yonedaEquiv s.2.hom)
      s.1.2.val s.1.2.property.1 s.1.2.property.2)

/-- The entire actual original inner-cell family, retaining every whole original base map, has its genuine weak
image under the same native straightening functor. -/
theorem nativeOriginalInnerCellsOver_straightening_projectiveWeakLeft (B : SSet.{u}) :
    nativeOriginalInnerCellsOver B ≤
      ((enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp).inverseImage
        (nativeStraightening B) :=
  (ofHoms_le_iff (overCell nativeOriginalInnerCell.{u} (max B)) _).mpr
    (nativeOriginalInnerCell_straightening_projectiveWeakLeft B)

/-- Actual native unstraightening of every original coherent-model fibration lifts every same complete original
inner cell over every actual original whole base map. -/
theorem nativeUnstraightening_map_originalInnerRlp (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → (nativeOriginalInnerCellsOver B).rlp ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let J := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos
  have hq' : J.rlp q := (fibration_iff q).mp hq
  rintro X Y i ⟨s⟩
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (overCell nativeOriginalInnerCell.{u} (max B) s) q).mp
    ((nativeOriginalInnerCell_straightening_projectiveWeakLeft B s) q hq')

/-- Actual native unstraightening sends every genuine original coherent-model fibration to an underlying inner
fibration on its complete original marked total map, over arbitrary original simplicial bases. -/
theorem nativeUnstraightening_map_innerFibration (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → InnerFibration (((nativeUnstraightening B).map q).left.hom) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let p := ((nativeUnstraightening B).map q).left
  have hOver := nativeUnstraightening_map_originalInnerRlp B q hq
  have h : (ofHoms (fun s : NativeOriginalInnerCellIndex => (nativeOriginalInnerCell.{u} s).hom)).rlp p :=
    (overCells_rlp_iff nativeOriginalInnerCell.{u} (max B) ((nativeUnstraightening B).map q)).mp hOver
  apply (innerCell_rlp_iff p).mp
  intro n i hi hi'
  exact h _ (ofHoms.mk (f := fun s : NativeOriginalInnerCellIndex => (nativeOriginalInnerCell.{u} s).hom)
    ⟨n, ⟨i, hi, hi'⟩⟩)

end SSet.Marked
