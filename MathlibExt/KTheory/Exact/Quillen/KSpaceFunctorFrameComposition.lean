/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorRootComposition
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMapCrossFrame

/-!
# Whole canonical K-map composition in the original working frames

Original same-frame and original down-object-frame whole realization-map
equations are combined with the genuine original zero-root composition
family. This gives jointly continuous composition homotopies of the entire
canonical exact-functor K-maps, with their actual moving unit Paths.
The arbitrary six-role whole-map composition theorem remains a separate scope.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped ContinuousMap

universe uC vC uD vD uE vE

namespace AlgebraicKTheory

section OriginalRootLooping

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

private theorem weaklyPointedEqOfCompositionValues
    {X : Type uC} {Y : Type uE} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y)
    (hMap : f.hom = g.hom)
    (hRoot : ∀ t : unitInterval, f.rootPath t = g.rootPath t) : f = g := by
  rcases f with ⟨f, p⟩
  rcases g with ⟨g, q⟩
  cases hMap
  have h : p = q := by
    apply Path.ext
    funext t
    exact hRoot t
  cases h
  rfl

private theorem canonicalFunctorLoopMapComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQRealFunctorWeaklyPointed F).loopMap = NQKSpaceFunctorMap F := by
  apply ContinuousMap.ext
  intro γ
  exact (NQKSpaceFunctorMap_apply F γ).symm

private def canonicalCompositionLoopingComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (h : (NQRealFunctorWeaklyPointed (F ⋙ G)).hom =
      (NQRealFunctorWeaklyPointed G).hom.comp (NQRealFunctorWeaklyPointed F).hom) :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G))
      ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F)) := by
  let x := NQReal.basepoint C
  let a := NQRealFunctorWeaklyPointed (F ⋙ G)
  let b := ContinuousMap.WeaklyPointed.comp
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
  have hMap : a.hom = b.hom := h
  let hx := congrArg (fun k : C(NQReal C, NQReal E) => k x) hMap
  let r := b.rootPath.cast hx rfl
  let w : ContinuousMap.WeaklyPointed x (NQReal.basepoint E) := ⟨a.hom, r⟩
  have hw : w = b := weaklyPointedEqOfCompositionValues w b hMap (fun _ => rfl)
  let q := (((NQRealFunctorWeaklyPointed F).rootPath.map
    (NQRealFunctorWeaklyPointed G).hom.continuous).cast
      (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
        (NQRealFunctorWeaklyPointed G).rootPath
  have hRoot : q = w.rootPath := by
    apply Path.ext
    rfl
  let Hp : a.rootPath.Homotopy w.rootPath :=
    (NQRealFunctorCompMappedRootHomotopy F G).cast rfl hRoot
  let H₀ := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom Hp
  let H₁ : ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G)) b.loopMap :=
    H₀.cast (canonicalFunctorLoopMapComputed (F ⋙ G))
      (congrArg ContinuousMap.WeaklyPointed.loopMap hw)
  let H₂ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
  have hEnd : (NQRealFunctorWeaklyPointed G).loopMap.comp
      (NQRealFunctorWeaklyPointed F).loopMap =
      (NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F) :=
    (congrArg (fun k : C(NQKSpace D, NQKSpace E) =>
      k.comp (NQRealFunctorWeaklyPointed F).loopMap)
        (canonicalFunctorLoopMapComputed G)).trans
      (congrArg (fun k : C(NQKSpace C, NQKSpace D) =>
        (NQKSpaceFunctorMap G).comp k) (canonicalFunctorLoopMapComputed F))
  exact H₁.trans (H₂.cast rfl hEnd)

end OriginalRootLooping

section SameFrameTarget

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D E : Type uD} [Category.{vD} D] [Category.{vD} E]
  [Preadditive D] [Preadditive E] [HasZeroObject D] [HasZeroObject E]
  [HasBinaryBiproducts D] [HasBinaryBiproducts E] [ExactCategory D] [ExactCategory E]

private theorem canonicalPostcompSameFrameHomComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).hom =
      (NQRealFunctorWeaklyPointed G).hom.comp (NQRealFunctorWeaklyPointed F).hom := by
  exact (NQRealFunctorWeaklyPointed_comp_hom F G).trans
    (ContinuousMap.WeaklyPointed.comp_hom
      (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G))

/-- One joint homotopy of the ENTIRE original canonical composed K-map
and the two actual K-maps in succession, with the original two zero roots. -/
def NQKSpaceFunctorCompHomotopySameFrame
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G))
      ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F)) :=
  canonicalCompositionLoopingComputed F G (canonicalPostcompSameFrameHomComputed F G)

/-- The actual moving unit Path of the full original same-frame composition family. -/
def NQKSpaceFunctorCompUnitPathSameFrame
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    Path (NQKSpaceFunctorMap (F ⋙ G) (Path.refl (NQReal.basepoint C)))
      (NQKSpaceFunctorMap G (NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)))) :=
  (NQKSpaceFunctorCompHomotopySameFrame F G).evalAt (Path.refl (NQReal.basepoint C))

private theorem canonicalSameFrameUnitValueComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t s : unitInterval) :
    ((NQKSpaceFunctorCompUnitPathSameFrame F G).toContinuousMap.toFun t :
      unitInterval → NQReal E) s =
    (NQKSpaceFunctorCompHomotopySameFrame F G
      (t, Path.refl (NQReal.basepoint C)) : unitInterval → NQReal E) s := rfl

/-- Every pair of times of the original same-frame moving unit is retained. -/
theorem NQKSpaceFunctorCompUnitPath_sameFrame_apply
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t s : unitInterval) :
    ((NQKSpaceFunctorCompUnitPathSameFrame F G).toContinuousMap.toFun t :
      unitInterval → NQReal E) s =
    (NQKSpaceFunctorCompHomotopySameFrame F G
      (t, Path.refl (NQReal.basepoint C)) : unitInterval → NQReal E) s :=
  canonicalSameFrameUnitValueComputed F G t s

private theorem canonicalSameFrameWholeLoopValueComputed (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorCompHomotopySameFrame F G).toContinuousMap.toFun (t, γ) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (NQRealFunctorWeaklyPointed (F ⋙ G)).hom
          (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else
        (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
          (NQRealFunctorWeaklyPointed F)
          (NQRealFunctorWeaklyPointed G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ) := by
  let h := canonicalPostcompSameFrameHomComputed F G
  let x := NQReal.basepoint C
  let a := NQRealFunctorWeaklyPointed (F ⋙ G)
  let b := ContinuousMap.WeaklyPointed.comp
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
  have hMap : a.hom = b.hom := h
  let hx := congrArg (fun k : C(NQReal C, NQReal E) => k x) hMap
  let r := b.rootPath.cast hx rfl
  let w : ContinuousMap.WeaklyPointed x (NQReal.basepoint E) := ⟨a.hom, r⟩
  have hw : w = b := weaklyPointedEqOfCompositionValues w b hMap (fun _ => rfl)
  let q := (((NQRealFunctorWeaklyPointed F).rootPath.map
    (NQRealFunctorWeaklyPointed G).hom.continuous).cast
      (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
        (NQRealFunctorWeaklyPointed G).rootPath
  have hRoot : q = w.rootPath := by
    apply Path.ext
    rfl
  let Hp : a.rootPath.Homotopy w.rootPath :=
    (NQRealFunctorCompMappedRootHomotopy F G).cast rfl hRoot
  let H₀ := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom Hp
  let H₁ : ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G)) b.loopMap :=
    H₀.cast (canonicalFunctorLoopMapComputed (F ⋙ G))
      (congrArg ContinuousMap.WeaklyPointed.loopMap hw)
  let H₂ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
  have hEnd : (NQRealFunctorWeaklyPointed G).loopMap.comp
      (NQRealFunctorWeaklyPointed F).loopMap =
      (NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F) :=
    (congrArg (fun k : C(NQKSpace D, NQKSpace E) =>
      k.comp (NQRealFunctorWeaklyPointed F).loopMap)
        (canonicalFunctorLoopMapComputed G)).trans
      (congrArg (fun k : C(NQKSpace C, NQKSpace D) =>
        (NQKSpaceFunctorMap G).comp k) (canonicalFunctorLoopMapComputed F))
  let middleMap : C(NQKSpace C, NQKSpace E) := b.loopMap
  let targetMap : C(NQKSpace C, NQKSpace E) :=
    (NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F)
  let Hfirst : ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G)) middleMap := H₁
  let Hsecond : ContinuousMap.Homotopy middleMap targetMap := H₂.cast rfl hEnd
  let originalFirst : C(unitInterval × NQKSpace C, NQKSpace E) :=
    (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom
      (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap
  let originalSecond : C(unitInterval × NQKSpace C, NQKSpace E) := H₂.toContinuousMap
  have hValue :
      (NQKSpaceFunctorCompHomotopySameFrame F G).toContinuousMap.toFun (t, γ) =
        (Hfirst.trans Hsecond).toContinuousMap.toFun (t, γ) := rfl
  have hTrans := ContinuousMap.Homotopy.trans_apply Hfirst Hsecond (t, γ)
  have hFirstValue (u : unitInterval) :
      Hfirst.toContinuousMap.toFun (u, γ) = originalFirst.toFun (u, γ) := by
    have hCastValue : Hfirst.toContinuousMap.toFun (u, γ) =
        H₀.toContinuousMap.toFun (u, γ) := rfl
    have hEval : Hp.eval u = (NQRealFunctorCompMappedRootHomotopy F G).eval u := by
      apply Path.ext
      funext s
      rfl
    have hFirst := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy_apply a.hom Hp u γ
    have hOriginal := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy_apply a.hom
      (NQRealFunctorCompMappedRootHomotopy F G) u γ
    have hWord := congrArg (fun r : Path (a.hom x) (NQReal.basepoint E) =>
      r.symm.trans ((ContinuousMap.strictLoopMap a.hom x γ).trans r)) hEval
    exact hCastValue.trans (hFirst.trans (hWord.trans hOriginal.symm))
  have hSecondValue (u : unitInterval) :
      Hsecond.toContinuousMap.toFun (u, γ) = originalSecond.toFun (u, γ) := rfl
  have hPieces :
      (if ht : (t : ℝ) ≤ 1 / 2 then Hfirst.toContinuousMap.toFun
        (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else Hsecond.toContinuousMap.toFun
        (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ)) =
      (if ht : (t : ℝ) ≤ 1 / 2 then originalFirst.toFun
        (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else originalSecond.toFun
        (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ)) := by
    split_ifs with ht
    · exact hFirstValue _
    · exact hSecondValue _
  exact hValue.trans (hTrans.trans hPieces)

/-- Every original time and whole source loop of the same-frame
composition homotopy retains the SAME original root-composition homotopy
and actual weak composition family with its original half clocks. -/
theorem NQKSpaceFunctorCompHomotopySameFrame_loopMap_value (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorCompHomotopySameFrame F G).toContinuousMap.toFun (t, γ) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (NQRealFunctorWeaklyPointed (F ⋙ G)).hom
          (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else
        (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
          (NQRealFunctorWeaklyPointed F)
          (NQRealFunctorWeaklyPointed G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ) :=
  canonicalSameFrameWholeLoopValueComputed F G t γ

end SameFrameTarget

section OriginalCrossTarget

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type (max uE vE)} [Category.{max uE vE} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

private theorem canonicalPostcompCrossFrameHomComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).hom =
      (NQRealFunctorWeaklyPointed G).hom.comp (NQRealFunctorWeaklyPointed F).hom := by
  exact (NQRealFunctorWeaklyPointed_comp_hom F G).trans
    (ContinuousMap.WeaklyPointed.comp_hom
      (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G))

/-- One joint composition homotopy for the ACTUAL original down-object
canonical K-maps, including the original source values and both original zero roots. -/
def NQKSpaceFunctorCompHomotopyCrossFrame
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G))
      ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F)) :=
  canonicalCompositionLoopingComputed F G (canonicalPostcompCrossFrameHomComputed F G)

/-- The actual moving unit Path of the full original down-frame composition family. -/
def NQKSpaceFunctorCompUnitPathCrossFrame
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    Path (NQKSpaceFunctorMap (F ⋙ G) (Path.refl (NQReal.basepoint C)))
      (NQKSpaceFunctorMap G (NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)))) :=
  (NQKSpaceFunctorCompHomotopyCrossFrame F G).evalAt (Path.refl (NQReal.basepoint C))

private theorem canonicalCrossFrameUnitValueComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t s : unitInterval) :
    ((NQKSpaceFunctorCompUnitPathCrossFrame F G).toContinuousMap.toFun t :
      unitInterval → NQReal E) s =
    (NQKSpaceFunctorCompHomotopyCrossFrame F G
      (t, Path.refl (NQReal.basepoint C)) : unitInterval → NQReal E) s := rfl

/-- Every pair of times of the original down-frame moving unit is retained. -/
theorem NQKSpaceFunctorCompUnitPath_crossFrame_apply
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t s : unitInterval) :
    ((NQKSpaceFunctorCompUnitPathCrossFrame F G).toContinuousMap.toFun t :
      unitInterval → NQReal E) s =
    (NQKSpaceFunctorCompHomotopyCrossFrame F G
      (t, Path.refl (NQReal.basepoint C)) : unitInterval → NQReal E) s :=
  canonicalCrossFrameUnitValueComputed F G t s

private theorem canonicalCrossFrameWholeLoopValueComputed (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorCompHomotopyCrossFrame F G).toContinuousMap.toFun (t, γ) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (NQRealFunctorWeaklyPointed (F ⋙ G)).hom
          (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else
        (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
          (NQRealFunctorWeaklyPointed F)
          (NQRealFunctorWeaklyPointed G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ) := by
  let h := canonicalPostcompCrossFrameHomComputed F G
  let x := NQReal.basepoint C
  let a := NQRealFunctorWeaklyPointed (F ⋙ G)
  let b := ContinuousMap.WeaklyPointed.comp
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
  have hMap : a.hom = b.hom := h
  let hx := congrArg (fun k : C(NQReal C, NQReal E) => k x) hMap
  let r := b.rootPath.cast hx rfl
  let w : ContinuousMap.WeaklyPointed x (NQReal.basepoint E) := ⟨a.hom, r⟩
  have hw : w = b := weaklyPointedEqOfCompositionValues w b hMap (fun _ => rfl)
  let q := (((NQRealFunctorWeaklyPointed F).rootPath.map
    (NQRealFunctorWeaklyPointed G).hom.continuous).cast
      (NQRealFunctor_comp_basepoint_eq F G) rfl).trans
        (NQRealFunctorWeaklyPointed G).rootPath
  have hRoot : q = w.rootPath := by
    apply Path.ext
    rfl
  let Hp : a.rootPath.Homotopy w.rootPath :=
    (NQRealFunctorCompMappedRootHomotopy F G).cast rfl hRoot
  let H₀ := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom Hp
  let H₁ : ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G)) b.loopMap :=
    H₀.cast (canonicalFunctorLoopMapComputed (F ⋙ G))
      (congrArg ContinuousMap.WeaklyPointed.loopMap hw)
  let H₂ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
  have hEnd : (NQRealFunctorWeaklyPointed G).loopMap.comp
      (NQRealFunctorWeaklyPointed F).loopMap =
      (NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F) :=
    (congrArg (fun k : C(NQKSpace D, NQKSpace E) =>
      k.comp (NQRealFunctorWeaklyPointed F).loopMap)
        (canonicalFunctorLoopMapComputed G)).trans
      (congrArg (fun k : C(NQKSpace C, NQKSpace D) =>
        (NQKSpaceFunctorMap G).comp k) (canonicalFunctorLoopMapComputed F))
  let middleMap : C(NQKSpace C, NQKSpace E) := b.loopMap
  let targetMap : C(NQKSpace C, NQKSpace E) :=
    (NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F)
  let Hfirst : ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G)) middleMap := H₁
  let Hsecond : ContinuousMap.Homotopy middleMap targetMap := H₂.cast rfl hEnd
  let originalFirst : C(unitInterval × NQKSpace C, NQKSpace E) :=
    (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom
      (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap
  let originalSecond : C(unitInterval × NQKSpace C, NQKSpace E) := H₂.toContinuousMap
  have hValue :
      (NQKSpaceFunctorCompHomotopyCrossFrame F G).toContinuousMap.toFun (t, γ) =
        (Hfirst.trans Hsecond).toContinuousMap.toFun (t, γ) := rfl
  have hTrans := ContinuousMap.Homotopy.trans_apply Hfirst Hsecond (t, γ)
  have hFirstValue (u : unitInterval) :
      Hfirst.toContinuousMap.toFun (u, γ) = originalFirst.toFun (u, γ) := by
    have hCastValue : Hfirst.toContinuousMap.toFun (u, γ) =
        H₀.toContinuousMap.toFun (u, γ) := rfl
    have hEval : Hp.eval u = (NQRealFunctorCompMappedRootHomotopy F G).eval u := by
      apply Path.ext
      funext s
      rfl
    have hFirst := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy_apply a.hom Hp u γ
    have hOriginal := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy_apply a.hom
      (NQRealFunctorCompMappedRootHomotopy F G) u γ
    have hWord := congrArg (fun r : Path (a.hom x) (NQReal.basepoint E) =>
      r.symm.trans ((ContinuousMap.strictLoopMap a.hom x γ).trans r)) hEval
    exact hCastValue.trans (hFirst.trans (hWord.trans hOriginal.symm))
  have hSecondValue (u : unitInterval) :
      Hsecond.toContinuousMap.toFun (u, γ) = originalSecond.toFun (u, γ) := rfl
  have hPieces :
      (if ht : (t : ℝ) ≤ 1 / 2 then Hfirst.toContinuousMap.toFun
        (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else Hsecond.toContinuousMap.toFun
        (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ)) =
      (if ht : (t : ℝ) ≤ 1 / 2 then originalFirst.toFun
        (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else originalSecond.toFun
        (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ)) := by
    split_ifs with ht
    · exact hFirstValue _
    · exact hSecondValue _
  exact hValue.trans (hTrans.trans hPieces)

/-- Every original time and whole source loop of the cross-frame
composition homotopy retains the SAME original root-composition homotopy
and actual weak composition family with its original half clocks. -/
theorem NQKSpaceFunctorCompHomotopyCrossFrame_loopMap_value (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorCompHomotopyCrossFrame F G).toContinuousMap.toFun (t, γ) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (NQRealFunctorWeaklyPointed (F ⋙ G)).hom
          (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else
        (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
          (NQRealFunctorWeaklyPointed F)
          (NQRealFunctorWeaklyPointed G)).toContinuousMap.toFun
            (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ) :=
  canonicalCrossFrameWholeLoopValueComputed F G t γ

end OriginalCrossTarget

end AlgebraicKTheory

end
