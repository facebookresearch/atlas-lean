/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Contractible
public import MathlibExt.CategoryTheory.NatIso

/-!
# Reduced homology and cohomology

Reduced homology and cohomology functors for pointed spaces via the pointed pair
construction.
-/
@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace TopPair

namespace HomologyTheoryData

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Reduced homology of a pointed space, given by the homology of its basepoint pair. -/
abbrev reducedH (E : HomologyTheoryData.{w} C) (n : ℤ) : PointedTopCat.{w} ⥤ C :=
  PointedTopCat.pointedPair ⋙ E.Hₚ n

/-- Reduced homology in degree `n`, functorial in the homology theory data. -/
def reducedHFunctor (n : ℤ) : HomologyTheoryData.{w} C ⥤ (PointedTopCat.{w} ⥤ C) :=
  HomologyPretheory.hₚFunctor n ⋙
    (Functor.whiskeringLeft PointedTopCat TopPair C).obj PointedTopCat.pointedPair

/-- Absolute homology of the underlying space of a pointed space. -/
abbrev pointedH (E : HomologyTheoryData.{w} C) (n : ℤ) : PointedTopCat.{w} ⥤ C :=
  PointedTopCat.pointedPair ⋙ TopPair.proj₁ ⋙ E.H n

theorem pointedH_map (E : HomologyTheoryData.{w} C) (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (pointedH E n).map f =
      (E.H n).map (TopPair.Hom.fst (PointedTopCat.pointedPair.map f)) := rfl

section

variable [HasBinaryBiproducts C]

/-- The coefficient object plus reduced homology, functorial in the pointed space. -/
noncomputable def coefficientBiprodReduced
    (E : HomologyTheoryData.{w} C) (n : ℤ) : PointedTopCat.{w} ⥤ C where
  obj X := E.coefficientObject n ⊞ (E.reducedH n).obj X
  map f := biprod.map (𝟙 _) ((E.reducedH n).map f)
  map_id X := by
    ext <;> simp
  map_comp f g := by
    ext <;> simp

@[simp, reassoc]
theorem coefficientBiprodReduced_map_fst
    (E : HomologyTheoryData.{w} C) (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (coefficientBiprodReduced E n).map f ≫
        (biprod.fst : E.coefficientObject n ⊞
          (E.Hₚ n).obj (PointedTopCat.pointedPair.obj Y) ⟶ E.coefficientObject n) =
      biprod.fst := by
  change biprod.map (𝟙 _) ((E.reducedH n).map f) ≫ biprod.fst = _
  simp

@[simp, reassoc]
theorem coefficientBiprodReduced_map_snd
    (E : HomologyTheoryData.{w} C) (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (coefficientBiprodReduced E n).map f ≫
        (biprod.snd : E.coefficientObject n ⊞
          (E.Hₚ n).obj (PointedTopCat.pointedPair.obj Y) ⟶
            (E.Hₚ n).obj (PointedTopCat.pointedPair.obj Y)) =
      biprod.snd ≫ (E.reducedH n).map f := by
  change biprod.map (𝟙 _) ((E.reducedH n).map f) ≫ biprod.snd = _
  simp

end

end HomologyTheoryData

namespace HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem isZero_reducedH_of_isIso_basepoint
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) (X : PointedTopCat.{w})
    [IsIso X.hom] : Limits.IsZero ((E.reducedH n).obj X) := by
  have h_eq : (PointedTopCat.pointedPair.obj X).map = X.hom := rfl
  have : IsIso (PointedTopCat.pointedPair.obj X).map :=
    h_eq.symm ▸ ‹IsIso X.hom›
  exact isZero_relative_of_isIso_map (E := E) n (PointedTopCat.pointedPair.obj X)

/-- The short complex from the coefficient object through absolute homology to reduced homology. -/
noncomputable def reducedShortComplex (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (X : PointedTopCat.{w}) : ShortComplex C :=
  ShortComplex.mk (E.subspaceMap n (PointedTopCat.pointedPair.obj X))
    (E.toRelative n (PointedTopCat.pointedPair.obj X))
    (subspaceMap_comp_toRelative E n (PointedTopCat.pointedPair.obj X))

theorem reducedShortComplex_exact (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (X : PointedTopCat.{w}) : (reducedShortComplex E n X).Exact :=
  exact_subspaceMap_toRelative E n (PointedTopCat.pointedPair.obj X)

/-- The homology map induced by the basepoint inclusion is split by the map induced by
collapse to the point. This uses only functoriality, so no exactness assumption is required. -/
noncomputable def basepointSplitMono (E : HomologyTheoryData.{w} C) (n : ℤ)
    (X : PointedTopCat.{w}) : SplitMono (E.subspaceMap n (PointedTopCat.pointedPair.obj X)) where
  retraction := (E.H n).map (TopCat.isTerminalPUnit.from X.right)
  id := by
    change (E.H n).map X.hom ≫ (E.H n).map (TopCat.isTerminalPUnit.from X.right) = 𝟙 _
    rw [← (E.H n).map_comp]
    have h : X.hom ≫ TopCat.isTerminalPUnit.from X.right = 𝟙 _ := by
      apply TopCat.isTerminalPUnit.hom_ext
    rw [h, (E.H n).map_id]

/-- The reduced homology short complex splits using collapse to the point as the retraction. -/
noncomputable def reducedSplitting (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    (X : PointedTopCat.{w}) : (reducedShortComplex E n X).Splitting := by
  have hBoundary : E.boundary n (PointedTopCat.pointedPair.obj X) = 0 := by
    let _ : Mono (E.subspaceMap (n - 1) (PointedTopCat.pointedPair.obj X)) :=
      (basepointSplitMono E (n - 1) X).mono
    exact (exact_boundary_subspaceMap E n (PointedTopCat.pointedPair.obj X)).mono_g_iff.mp
      inferInstance
  let _ : Epi (reducedShortComplex E n X).g :=
    (exact_toRelative_boundary E n (PointedTopCat.pointedPair.obj X)).epi_f_iff.mpr hBoundary
  exact ShortComplex.Splitting.ofExactOfRetraction (reducedShortComplex E n X)
    (reducedShortComplex_exact E n X) (basepointSplitMono E n X).retraction
    (basepointSplitMono E n X).id inferInstance

/-- Absolute homology of a pointed space splits as its coefficient object plus reduced homology. -/
noncomputable def homologyIsoCoefficientBiprodReduced (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (E.H n).obj X.right ≅ E.coefficientObject n ⊞ (E.reducedH n).obj X :=
  (reducedSplitting E n X).isoBinaryBiproduct

@[reassoc (attr := simp)]
theorem homologyIsoCoefficientBiprodReduced_hom_fst (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (homologyIsoCoefficientBiprodReduced E n X).hom ≫
        (biprod.fst : E.coefficientObject n ⊞
          (E.Hₚ n).obj (PointedTopCat.pointedPair.obj X) ⟶ E.coefficientObject n) =
      (E.H n).map (TopCat.isTerminalPUnit.from X.right) := by
  simp only [homologyIsoCoefficientBiprodReduced, ShortComplex.Splitting.isoBinaryBiproduct_hom]
  exact CategoryTheory.Limits.biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem homologyIsoCoefficientBiprodReduced_hom_snd (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (homologyIsoCoefficientBiprodReduced E n X).hom ≫
        (biprod.snd : E.coefficientObject n ⊞
          (E.Hₚ n).obj (PointedTopCat.pointedPair.obj X) ⟶
            (E.Hₚ n).obj (PointedTopCat.pointedPair.obj X)) =
      E.toRelative n (PointedTopCat.pointedPair.obj X) := by
  simp only [homologyIsoCoefficientBiprodReduced, ShortComplex.Splitting.isoBinaryBiproduct_hom]
  exact CategoryTheory.Limits.biprod.lift_snd _ _

set_option backward.isDefEq.respectTransparency false in
theorem homologyIsoCoefficientBiprodReduced_hom_naturality
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (pointedH E n).map f ≫ (homologyIsoCoefficientBiprodReduced E n Y).hom =
      (homologyIsoCoefficientBiprodReduced E n X).hom ≫
        (coefficientBiprodReduced E n).map f := by
  let RX : C := (E.Hₚ n).obj (PointedTopCat.pointedPair.obj X)
  let RY : C := (E.Hₚ n).obj (PointedTopCat.pointedPair.obj Y)
  let eX : (E.H n).obj X.right ≅ E.coefficientObject n ⊞ RX :=
    homologyIsoCoefficientBiprodReduced E n X
  let eY : (E.H n).obj Y.right ≅ E.coefficientObject n ⊞ RY :=
    homologyIsoCoefficientBiprodReduced E n Y
  let p : (E.H n).obj X.right ⟶ (E.H n).obj Y.right := (E.H n).map f.right
  let r : RX ⟶ RY := (E.Hₚ n).map (PointedTopCat.pointedPair.map f)
  let qX : (E.H n).obj X.right ⟶ E.coefficientObject n :=
    (E.H n).map (TopCat.isTerminalPUnit.from X.right)
  let qY : (E.H n).obj Y.right ⟶ E.coefficientObject n :=
    (E.H n).map (TopCat.isTerminalPUnit.from Y.right)
  let tX : (E.H n).obj X.right ⟶ RX := E.toRelative n (PointedTopCat.pointedPair.obj X)
  let tY : (E.H n).obj Y.right ⟶ RY := E.toRelative n (PointedTopCat.pointedPair.obj Y)
  have heX_fst : eX.hom ≫ biprod.fst = qX :=
    homologyIsoCoefficientBiprodReduced_hom_fst E n X
  have heY_fst : eY.hom ≫ biprod.fst = qY :=
    homologyIsoCoefficientBiprodReduced_hom_fst E n Y
  have heX_snd : eX.hom ≫ biprod.snd = tX :=
    homologyIsoCoefficientBiprodReduced_hom_snd E n X
  have heY_snd : eY.hom ≫ biprod.snd = tY :=
    homologyIsoCoefficientBiprodReduced_hom_snd E n Y
  have hpq : p ≫ qY = qX := by
    change (E.H n).map f.right ≫ (E.H n).map (TopCat.isTerminalPUnit.from Y.right) =
      (E.H n).map (TopCat.isTerminalPUnit.from X.right)
    rw [← (E.H n).map_comp]
    exact congrArg (E.H n).map (TopCat.isTerminalPUnit.hom_ext _ _)
  have hpt : p ≫ tY = tX ≫ r := by
    have h := (E.toRelativeNatTrans n).naturality (PointedTopCat.pointedPair.map f)
    change p ≫ tY = tX ≫ r at h
    exact h
  change p ≫ eY.hom = eX.hom ≫ biprod.map (𝟙 _) r
  apply biprod.hom_ext
  · rw [Category.assoc, heY_fst, Category.assoc, biprod.map_fst,
      Category.comp_id, heX_fst]
    exact hpq
  · rw [Category.assoc, heY_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc, heX_snd]
    exact hpt

set_option backward.isDefEq.respectTransparency false in
/-- The reduced splitting is natural in pointed spaces. -/
noncomputable def homologyIsoCoefficientBiprodReducedNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) :
    pointedH E n ≅ coefficientBiprodReduced E n :=
  NatIso.ofComponents (fun X ↦ homologyIsoCoefficientBiprodReduced E n X)
    (fun f ↦ homologyIsoCoefficientBiprodReduced_hom_naturality E n f)

@[simp]
theorem homologyIsoCoefficientBiprodReducedNatIso_app
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) (X : PointedTopCat.{w}) :
    (homologyIsoCoefficientBiprodReducedNatIso E n).app X =
      homologyIsoCoefficientBiprodReduced E n X := rfl

set_option backward.isDefEq.respectTransparency false in
theorem homologyIsoCoefficientBiprodReduced_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [F.IsExact]
    (f : E ⟶ F) (n : ℤ) (X : PointedTopCat.{w}) :
    (f.hom n).app (PointedTopCat.pointedPair.obj X).fst ≫
        (homologyIsoCoefficientBiprodReduced F n X).hom =
      (homologyIsoCoefficientBiprodReduced E n X).hom ≫
        biprod.map ((f.hom n).app (TopCat.of PUnit))
          ((f.homₚ n).app (PointedTopCat.pointedPair.obj X)) := by
  let RE : C := (E.Hₚ n).obj (PointedTopCat.pointedPair.obj X)
  let RF : C := (F.Hₚ n).obj (PointedTopCat.pointedPair.obj X)
  let eE : (E.H n).obj X.right ≅ E.coefficientObject n ⊞ RE :=
    homologyIsoCoefficientBiprodReduced E n X
  let eF : (F.H n).obj X.right ≅ F.coefficientObject n ⊞ RF :=
    homologyIsoCoefficientBiprodReduced F n X
  let τ : (E.H n).obj X.right ⟶ (F.H n).obj X.right := (f.hom n).app X.right
  let τ₀ : E.coefficientObject n ⟶ F.coefficientObject n :=
    (f.hom n).app (TopCat.of PUnit)
  let τR : RE ⟶ RF := (f.homₚ n).app (PointedTopCat.pointedPair.obj X)
  let qE : (E.H n).obj X.right ⟶ E.coefficientObject n :=
    (E.H n).map (TopCat.isTerminalPUnit.from X.right)
  let qF : (F.H n).obj X.right ⟶ F.coefficientObject n :=
    (F.H n).map (TopCat.isTerminalPUnit.from X.right)
  let tE : (E.H n).obj X.right ⟶ RE := E.toRelative n (PointedTopCat.pointedPair.obj X)
  let tF : (F.H n).obj X.right ⟶ RF := F.toRelative n (PointedTopCat.pointedPair.obj X)
  have heE_fst : eE.hom ≫ biprod.fst = qE :=
    homologyIsoCoefficientBiprodReduced_hom_fst E n X
  have heF_fst : eF.hom ≫ biprod.fst = qF :=
    homologyIsoCoefficientBiprodReduced_hom_fst F n X
  have heE_snd : eE.hom ≫ biprod.snd = tE :=
    homologyIsoCoefficientBiprodReduced_hom_snd E n X
  have heF_snd : eF.hom ≫ biprod.snd = tF :=
    homologyIsoCoefficientBiprodReduced_hom_snd F n X
  have hq : τ ≫ qF = qE ≫ τ₀ :=
    ((f.hom n).naturality (TopCat.isTerminalPUnit.from X.right)).symm
  have ht : τ ≫ tF = tE ≫ τR :=
    toRelative_naturality_theory f n (PointedTopCat.pointedPair.obj X)
  change τ ≫ eF.hom = eE.hom ≫ biprod.map τ₀ τR
  apply biprod.hom_ext
  · rw [Category.assoc, heF_fst, Category.assoc, biprod.map_fst,
      ← Category.assoc, heE_fst]
    exact hq
  · rw [Category.assoc, heF_snd, Category.assoc, biprod.map_snd,
      ← Category.assoc, heE_snd]
    exact ht

set_option backward.isDefEq.respectTransparency false in
/-- The canonical inclusion of reduced homology into absolute homology of a
pointed space. -/
noncomputable def reducedToPointedH
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) :
    E.reducedH n ⟶ E.pointedH n where
  app X := biprod.inr ≫ (homologyIsoCoefficientBiprodReduced E n X).inv
  naturality {X Y} f := by
    apply (cancel_mono (homologyIsoCoefficientBiprodReduced E n Y).hom).mp
    calc
      ((E.reducedH n).map f ≫ biprod.inr ≫
          (homologyIsoCoefficientBiprodReduced E n Y).inv) ≫
            (homologyIsoCoefficientBiprodReduced E n Y).hom =
          (E.reducedH n).map f ≫
            (biprod.inr : (E.reducedH n).obj Y ⟶
              E.coefficientObject n ⊞ (E.reducedH n).obj Y) := by simp
      _ = (biprod.inr : (E.reducedH n).obj X ⟶
              E.coefficientObject n ⊞ (E.reducedH n).obj X) ≫
          (coefficientBiprodReduced E n).map f := by
        change (E.reducedH n).map f ≫ biprod.inr =
          biprod.inr ≫ biprod.map (𝟙 _) ((E.reducedH n).map f)
        exact (biprod.inr_map (𝟙 _) ((E.reducedH n).map f)).symm
      _ = ((biprod.inr ≫ (homologyIsoCoefficientBiprodReduced E n X).inv) ≫
          (E.pointedH n).map f) ≫
            (homologyIsoCoefficientBiprodReduced E n Y).hom := by
        symm
        calc
          ((biprod.inr ≫ (homologyIsoCoefficientBiprodReduced E n X).inv) ≫
              (E.pointedH n).map f) ≫
                (homologyIsoCoefficientBiprodReduced E n Y).hom =
            biprod.inr ≫ (homologyIsoCoefficientBiprodReduced E n X).inv ≫
              ((E.pointedH n).map f ≫
                (homologyIsoCoefficientBiprodReduced E n Y).hom) := by
                  simp only [Category.assoc]
          _ = biprod.inr ≫ (homologyIsoCoefficientBiprodReduced E n X).inv ≫
              ((homologyIsoCoefficientBiprodReduced E n X).hom ≫
                (coefficientBiprodReduced E n).map f) := by
                  rw [homologyIsoCoefficientBiprodReduced_hom_naturality E n f]
          _ = biprod.inr ≫ (coefficientBiprodReduced E n).map f := by simp

theorem reducedToPointedH_app
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E n).app X =
      biprod.inr ≫ (homologyIsoCoefficientBiprodReduced E n X).inv := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem reducedToPointedH_app_comp_toRelative
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (q : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E q).app X ≫
        E.toRelative q (PointedTopCat.pointedPair.obj X) =
      𝟙 ((E.reducedH q).obj X) := by
  rw [reducedToPointedH_app,
    ← homologyIsoCoefficientBiprodReduced_hom_snd E q X]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact biprod.inr_snd (X := E.coefficientObject q)
    (Y := (E.Hₚ q).obj (PointedTopCat.pointedPair.obj X))

theorem reducedToPointedH_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [F.IsExact]
    (f : E ⟶ F) (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E n).app X ≫ (f.hom n).app X.right =
      (f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
        (reducedToPointedH F n).app X := by
  let eE := homologyIsoCoefficientBiprodReduced E n X
  let eF := homologyIsoCoefficientBiprodReduced F n X
  let a : (E.reducedH n).obj X ⟶ (E.H n).obj X.right :=
    biprod.inr ≫ eE.inv
  let b : (F.reducedH n).obj X ⟶ (F.H n).obj X.right :=
    biprod.inr ≫ eF.inv
  let r : E.coefficientObject n ⊞ (E.reducedH n).obj X ⟶
      F.coefficientObject n ⊞ (F.reducedH n).obj X :=
    biprod.map ((f.hom n).app (TopCat.of PUnit))
      ((f.homₚ n).app (PointedTopCat.pointedPair.obj X))
  change a ≫ (f.hom n).app X.right = (f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫ b
  have h_eq : (PointedTopCat.pointedPair.obj X).fst = X.right := rfl
  have h : (f.hom n).app X.right ≫ eF.hom = eE.hom ≫ r := by
    cases h_eq
    exact homologyIsoCoefficientBiprodReduced_hom_naturality_theory f n X
  apply (cancel_mono eF.hom).mp
  calc
    (a ≫ (f.hom n).app X.right) ≫ eF.hom =
        a ≫ ((f.hom n).app X.right ≫ eF.hom) := by
      simp only [Category.assoc]
    _ = a ≫ (eE.hom ≫ r) := by rw [h]
    _ = biprod.inr ≫ r := by simp [a]
    _ = (f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫ biprod.inr := by
      simp only [r]
      exact biprod.inr_map _ _
    _ = ((f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫ b) ≫ eF.hom := by
      simp [b]

/-- Abstract reduced homology is the kernel of the map to the point. -/
noncomputable def reducedHKernelIsoToPoint
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) (X : PointedTopCat.{w}) :
    (E.reducedH n).obj X ≅
      kernel ((E.H n).map (TopCat.isTerminalPUnit.from X.right)) := by
  let e := homologyIsoCoefficientBiprodReduced E n X
  let q : E.coefficientObject n ⊞ (E.reducedH n).obj X ⟶
      E.coefficientObject n := biprod.fst
  have h : e.hom ≫ q =
      (E.H n).map (TopCat.isTerminalPUnit.from X.right) :=
    homologyIsoCoefficientBiprodReduced_hom_fst E n X
  exact (kernelBiprodFstIso (X := E.coefficientObject n)
      (Y := (E.reducedH n).obj X)).symm ≪≫
    (kernelIsIsoComp e.hom q).symm ≪≫
    kernelIsoOfEq h

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem reducedHKernelIsoToPoint_hom_ι
    (E : HomologyTheoryData.{w} C) [E.IsExact] (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedHKernelIsoToPoint E n X).hom ≫
      kernel.ι ((E.H n).map (TopCat.isTerminalPUnit.from X.right)) =
      (reducedToPointedH E n).app X := by
  let e := homologyIsoCoefficientBiprodReduced E n X
  let q : E.coefficientObject n ⊞ (E.reducedH n).obj X ⟶
      E.coefficientObject n := biprod.fst
  have h : e.hom ≫ q =
      (E.H n).map (TopCat.isTerminalPUnit.from X.right) :=
    homologyIsoCoefficientBiprodReduced_hom_fst E n X
  change (((kernelBiprodFstIso (X := E.coefficientObject n)
      (Y := (E.reducedH n).obj X)).symm ≪≫
      (kernelIsIsoComp e.hom q).symm ≪≫ kernelIsoOfEq h).hom ≫
        kernel.ι ((E.H n).map (TopCat.isTerminalPUnit.from X.right))) =
      biprod.inr ≫ e.inv
  simp only [Iso.trans_hom]
  rw [Category.assoc, Category.assoc, kernelIsoOfEq_hom_comp_ι]
  change kernelBiprodFstIso.inv ≫ (kernelIsIsoComp e.hom q).inv ≫
      kernel.ι (e.hom ≫ q) = biprod.inr ≫ e.inv
  rw [kernelIsIsoComp_inv, kernel.lift_ι]
  rw [← Category.assoc]
  have hk : kernelBiprodFstIso.inv ≫ kernel.ι q = biprod.inr := by
    simp [q, kernelBiprodFstIso_inv]
  rw [hk]
  rw [IsIso.inv_eq_of_hom_inv_id e.hom_inv_id]

/-- Abstract reduced homology is the kernel of any pointed map to a contractible target. -/
noncomputable def reducedHKernelIsoOfContractibleTarget
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X) [ContractibleSpace X.right] :
    (E.reducedH n).obj A ≅ kernel ((E.H n).map f.right) := by
  let p := (E.H n).map f.right
  let g := (E.H n).map (TopCat.isTerminalPUnit.from X.right)
  let h := (E.H n).map (TopCat.isTerminalPUnit.from A.right)
  have hpg : p ≫ g = h := by
    dsimp [p, g, h]
    rw [← (E.H n).map_comp]
    congr 1
  letI : Mono g := by infer_instance
  exact reducedHKernelIsoToPoint E n A ≪≫
    kernelIsoOfEq hpg.symm ≪≫ kernelCompMono p g

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem reducedHKernelIsoOfContractibleTarget_hom_ι
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X) [ContractibleSpace X.right] :
    (reducedHKernelIsoOfContractibleTarget E n f).hom ≫
      kernel.ι ((E.H n).map f.right) =
      (reducedToPointedH E n).app A := by
  let p := (E.H n).map f.right
  let g := (E.H n).map (TopCat.isTerminalPUnit.from X.right)
  let h := (E.H n).map (TopCat.isTerminalPUnit.from A.right)
  have hpg : p ≫ g = h := by
    dsimp [p, g, h]
    rw [← (E.H n).map_comp]
    congr 1
  let _ : Mono g := by infer_instance
  change ((reducedHKernelIsoToPoint E n A ≪≫
      kernelIsoOfEq hpg.symm ≪≫ kernelCompMono p g).hom ≫
        kernel.ι p) = biprod.inr ≫
          (homologyIsoCoefficientBiprodReduced E n A).inv
  simp only [Iso.trans_hom, Category.assoc]
  rw [kernelCompMono_hom, kernel.lift_ι]
  rw [kernelIsoOfEq_hom_comp_ι]
  exact reducedHKernelIsoToPoint_hom_ι E n A

/-- If ambient absolute homology vanishes in degree `n`, then relative
homology in that degree is the kernel of the degree-`n - 1` subspace map. -/
noncomputable def relativeHKernelIsoOfIsZeroAmbient
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) (hAmbient : IsZero ((E.H n).obj P.fst)) :
    (E.Hₚ n).obj P ≅ kernel (E.subspaceMap (n - 1) P) := by
  have hToRelative : E.toRelative n P = 0 :=
    hAmbient.eq_of_src _ _
  have hMono : Mono (E.boundary n P) :=
    (ShortComplex.exact_iff_mono
      (ShortComplex.mk (E.toRelative n P) (E.boundary n P)
        (toRelative_comp_boundary E n P)) hToRelative).mp
      (exact_toRelative_boundary E n P)
  let _ : Mono (E.boundary n P) := hMono
  exact IsLimit.conePointUniqueUpToIso
    (exact_boundary_subspaceMap E n P).fIsKernel
    (limit.isLimit _)

@[reassoc (attr := simp)]
theorem relativeHKernelIsoOfIsZeroAmbient_hom_ι
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w}) (hAmbient : IsZero ((E.H n).obj P.fst)) :
    (relativeHKernelIsoOfIsZeroAmbient E n P hAmbient).hom ≫
      kernel.ι (E.subspaceMap (n - 1) P) = E.boundary n P := by
  have hToRelative : E.toRelative n P = 0 := hAmbient.eq_of_src _ _
  have hMono : Mono (E.boundary n P) :=
    (ShortComplex.exact_iff_mono
      (ShortComplex.mk (E.toRelative n P) (E.boundary n P)
        (toRelative_comp_boundary E n P)) hToRelative).mp
      (exact_toRelative_boundary E n P)
  let _ : Mono (E.boundary n P) := hMono
  dsimp [relativeHKernelIsoOfIsZeroAmbient]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    ((exact_boundary_subspaceMap E n P).fIsKernel)
    (limit.isLimit _) WalkingParallelPair.zero

private theorem pointedContractible_toRelative_zero
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    E.toRelative k (TopPair.of f.right hf) = 0 := by
  let P : TopPair.{w} := TopPair.of f.right hf
  let a : E.coefficientObject k ⟶ (E.H k).obj A.right := (E.H k).map A.hom
  let b : E.coefficientObject k ⟶ (E.H k).obj X.right := (E.H k).map X.hom
  let q : (E.H k).obj X.right ⟶ E.coefficientObject k :=
    (E.H k).map (TopCat.isTerminalPUnit.from X.right)
  let p : (E.H k).obj A.right ⟶ (E.H k).obj X.right := (E.H k).map f.right
  let t : (E.H k).obj X.right ⟶ (E.Hₚ k).obj P := by
    with_unfolding_all exact E.toRelative k P
  have hab : a ≫ p = b := by
    with_unfolding_all change (E.H k).map A.hom ≫ (E.H k).map f.right = (E.H k).map X.hom
    rw [← (E.H k).map_comp]
    exact congrArg (E.H k).map (Under.w f)
  have hbq : b ≫ q = 𝟙 _ := by
    with_unfolding_all change ((E.H k).map X.hom ≫
      (E.H k).map (TopCat.isTerminalPUnit.from X.right) = 𝟙 _)
    rw [← (E.H k).map_comp]
    have hx : X.hom ≫ TopCat.isTerminalPUnit.from X.right = 𝟙 _ :=
      TopCat.isTerminalPUnit.hom_ext _ _
    rw [hx, (E.H k).map_id]
  have : IsIso q := by
    with_unfolding_all change IsIso ((E.H k).map (TopCat.isTerminalPUnit.from X.right))
    infer_instance
  have hqb : q ≫ b = 𝟙 _ := by
    apply (cancel_mono q).mp
    simp only [Category.assoc, hbq, Category.comp_id, Category.id_comp]
  have hpt : p ≫ t = 0 :=
    by with_unfolding_all exact HomologyTheoryData.IsExact.subspaceMap_comp_toRelative E k P
  have hbt : b ≫ t = 0 := by
    exact (congrArg (fun z : E.coefficientObject k ⟶ (E.H k).obj X.right => z ≫ t)
      hab.symm).trans ((Category.assoc a p t).trans
        ((congrArg (fun z : (E.H k).obj A.right ⟶ (E.Hₚ k).obj P => a ≫ z)
          hpt).trans (comp_zero (f := a))))
  with_unfolding_all change t = 0
  calc
    t = (𝟙 ((E.H k).obj X.right)) ≫ t := (Category.id_comp t).symm
    _ = (q ≫ b) ≫ t :=
      congrArg (fun z : (E.H k).obj X.right ⟶ (E.H k).obj X.right => z ≫ t) hqb.symm
    _ = q ≫ (b ≫ t) := Category.assoc q b t
    _ = q ≫ 0 :=
      congrArg (fun z : E.coefficientObject k ⟶ (E.Hₚ k).obj P => q ≫ z) hbt
    _ = 0 := comp_zero (f := q)

private noncomputable def pointedContractible_relativeKernelIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    (E.Hₚ k).obj (TopPair.of f.right hf) ≅
      kernel ((E.H (k - 1)).map f.right) := by
  let P : TopPair.{w} := TopPair.of f.right hf
  let t : (E.H k).obj X.right ⟶ (E.Hₚ k).obj P := by
    with_unfolding_all exact E.toRelative k P
  let δ : (E.Hₚ k).obj P ⟶ (E.H (k - 1)).obj A.right := by
    with_unfolding_all exact E.boundary k P
  let p : (E.H (k - 1)).obj A.right ⟶ (E.H (k - 1)).obj X.right :=
    (E.H (k - 1)).map f.right
  have ht : t = 0 := by
    with_unfolding_all exact pointedContractible_toRelative_zero E k f hf
  have htd : t ≫ δ = 0 := by
    with_unfolding_all exact HomologyTheoryData.IsExact.toRelative_comp_boundary E k P
  have hdp : δ ≫ p = 0 := by
    with_unfolding_all exact HomologyTheoryData.IsExact.boundary_comp_subspaceMap E k P
  let S₁ : ShortComplex C := ShortComplex.mk t δ htd
  let S₂ : ShortComplex C := ShortComplex.mk δ p hdp
  have hS₁ : S₁.Exact := by
    with_unfolding_all exact HomologyTheoryData.IsExact.exact_toRelative_boundary E k P
  have hS₂ : S₂.Exact := by
    with_unfolding_all exact HomologyTheoryData.IsExact.exact_boundary_subspaceMap E k P
  have : Mono δ := (ShortComplex.exact_iff_mono S₁ ht).mp hS₁
  have : Mono S₂.f := by change Mono δ; infer_instance
  exact IsLimit.conePointUniqueUpToIso
    hS₂.fIsKernel
    (limit.isLimit _)

private theorem pointedContractible_relativeKernelIso_hom_ι
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    (pointedContractible_relativeKernelIso E k f hf).hom ≫
        kernel.ι ((E.H (k - 1)).map f.right) =
      E.boundary k (TopPair.of f.right hf) := by
  let P : TopPair.{w} := TopPair.of f.right hf
  let t : (E.H k).obj X.right ⟶ (E.Hₚ k).obj P := by
    with_unfolding_all exact E.toRelative k P
  let δ : (E.Hₚ k).obj P ⟶ (E.H (k - 1)).obj A.right := by
    with_unfolding_all exact E.boundary k P
  let p : (E.H (k - 1)).obj A.right ⟶ (E.H (k - 1)).obj X.right :=
    (E.H (k - 1)).map f.right
  have ht : t = 0 := by
    with_unfolding_all exact pointedContractible_toRelative_zero E k f hf
  have htd : t ≫ δ = 0 := by
    with_unfolding_all exact HomologyTheoryData.IsExact.toRelative_comp_boundary E k P
  have hdp : δ ≫ p = 0 := by
    with_unfolding_all exact HomologyTheoryData.IsExact.boundary_comp_subspaceMap E k P
  let S₁ : ShortComplex C := ShortComplex.mk t δ htd
  let S₂ : ShortComplex C := ShortComplex.mk δ p hdp
  have hS₁ : S₁.Exact := by
    with_unfolding_all exact HomologyTheoryData.IsExact.exact_toRelative_boundary E k P
  have hS₂ : S₂.Exact := by
    with_unfolding_all exact HomologyTheoryData.IsExact.exact_boundary_subspaceMap E k P
  have : Mono δ := (ShortComplex.exact_iff_mono S₁ ht).mp hS₁
  have : Mono S₂.f := by change Mono δ; infer_instance
  with_unfolding_all change
    (IsLimit.conePointUniqueUpToIso hS₂.fIsKernel (limit.isLimit _)).hom ≫ kernel.ι p = δ
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    hS₂.fIsKernel
    (limit.isLimit _) WalkingParallelPair.zero

/-- Relative homology of a pointed inclusion into a contractible target is reduced
homology of the source one degree lower. All integer degrees are allowed, with
no vanishing hypothesis on the ambient homology. -/
@[no_expose]
noncomputable def relativeHIsoReducedOfPointedContractibleAmbient
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    (E.Hₚ k).obj (TopPair.of f.right hf) ≅ (E.reducedH (k - 1)).obj A := by
  let K : C := kernel ((E.H (k - 1)).map f.right)
  let eK : (E.Hₚ k).obj (TopPair.of f.right hf) ≅ K :=
    pointedContractible_relativeKernelIso E k f hf
  let eR : (E.reducedH (k - 1)).obj A ≅ K :=
    HomologyTheoryData.IsExact.reducedHKernelIsoOfContractibleTarget E (k - 1) f
  exact eK ≪≫ eR.symm

/-- The pointed contractible comparison retains the actual boundary map. -/
@[reassoc]
theorem relativeHIsoReducedOfPointedContractibleAmbient_hom_inclusion
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    (relativeHIsoReducedOfPointedContractibleAmbient E k f hf).hom ≫
        (HomologyTheoryData.IsExact.reducedToPointedH E (k - 1)).app A =
      E.boundary k (TopPair.of f.right hf) := by
  let P : TopPair.{w} := TopPair.of f.right hf
  let K : C := kernel ((E.H (k - 1)).map f.right)
  let eK : (E.Hₚ k).obj P ≅ K := pointedContractible_relativeKernelIso E k f hf
  let eR : (E.reducedH (k - 1)).obj A ≅ K :=
    HomologyTheoryData.IsExact.reducedHKernelIsoOfContractibleTarget E (k - 1) f
  let κ : K ⟶ (E.H (k - 1)).obj A.right := kernel.ι ((E.H (k - 1)).map f.right)
  let i : (E.reducedH (k - 1)).obj A ⟶ (E.H (k - 1)).obj A.right := by
    with_unfolding_all exact (HomologyTheoryData.IsExact.reducedToPointedH E (k - 1)).app A
  let δ : (E.Hₚ k).obj P ⟶ (E.H (k - 1)).obj A.right := by
    with_unfolding_all exact E.boundary k P
  have hR : eR.hom ≫ κ = i := by
    with_unfolding_all exact
      HomologyTheoryData.IsExact.reducedHKernelIsoOfContractibleTarget_hom_ι E (k - 1) f
  have hRi : eR.inv ≫ i = κ := eR.inv_comp_eq.mpr hR.symm
  have hK : eK.hom ≫ κ = δ := by
    with_unfolding_all exact pointedContractible_relativeKernelIso_hom_ι E k f hf
  with_unfolding_all change (eK.hom ≫ eR.inv) ≫ i = δ
  exact (Category.assoc eK.hom eR.inv i).trans
    ((congrArg (fun z : K ⟶ (E.H (k - 1)).obj A.right => eK.hom ≫ z) hRi).trans hK)

/-- The inverse pointed contractible comparison carries boundary to reduced inclusion. -/
@[reassoc (attr := simp)]
theorem relativeHIsoReducedOfPointedContractibleAmbient_inv_boundary
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    (relativeHIsoReducedOfPointedContractibleAmbient E k f hf).inv ≫
        E.boundary k (TopPair.of f.right hf) =
      (reducedToPointedH E (k - 1)).app A := by
  exact (relativeHIsoReducedOfPointedContractibleAmbient E k f hf).inv_comp_eq.mpr
    (relativeHIsoReducedOfPointedContractibleAmbient_hom_inclusion E k f hf).symm

private theorem reducedInclusion_mono
    (E : HomologyTheoryData.{w} C) [E.IsExact] (k : ℤ) (A : PointedTopCat.{w}) :
    Mono ((HomologyTheoryData.IsExact.reducedToPointedH E k).app A) := by
  let p : (E.H k).obj A.right ⟶ E.coefficientObject k :=
    (E.H k).map (TopCat.isTerminalPUnit.from A.right)
  let e : (E.reducedH k).obj A ≅ kernel p := by
    with_unfolding_all exact HomologyTheoryData.IsExact.reducedHKernelIsoToPoint E k A
  let κ : kernel p ⟶ (E.H k).obj A.right := kernel.ι p
  let i : (E.reducedH k).obj A ⟶ (E.H k).obj A.right := by
    with_unfolding_all exact (HomologyTheoryData.IsExact.reducedToPointedH E k).app A
  have : IsIso e.hom := e.isIso_hom
  have : Mono κ := by dsimp only [κ]; infer_instance
  have hMono : Mono (e.hom ≫ κ) := inferInstance
  have hFac : e.hom ≫ κ = i := by
    with_unfolding_all exact HomologyTheoryData.IsExact.reducedHKernelIsoToPoint_hom_ι E k A
  with_unfolding_all change Mono i
  exact hFac ▸ hMono

/-- The pointed contractible comparison is natural in the homology theory. -/
theorem relativeHIsoReducedOfPointedContractibleAmbient_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [E.IsHomotopyInvariant]
    [F.IsExact] [F.IsHomotopyInvariant] (φ : E ⟶ F)
    (k : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right] :
    (φ.homₚ k).app (TopPair.of f.right hf) ≫
        (relativeHIsoReducedOfPointedContractibleAmbient F k f hf).hom =
      (relativeHIsoReducedOfPointedContractibleAmbient E k f hf).hom ≫
        (φ.homₚ (k - 1)).app (PointedTopCat.pointedPair.obj A) := by
  let P : TopPair.{w} := TopPair.of f.right hf
  let RE : C := (E.Hₚ k).obj P
  let RF : C := (F.Hₚ k).obj P
  let eE : RE ≅ (E.reducedH (k - 1)).obj A :=
    relativeHIsoReducedOfPointedContractibleAmbient E k f hf
  let eF : RF ≅ (F.reducedH (k - 1)).obj A :=
    relativeHIsoReducedOfPointedContractibleAmbient F k f hf
  let τP : RE ⟶ RF := (φ.homₚ k).app P
  let τA : (E.H (k - 1)).obj A.right ⟶ (F.H (k - 1)).obj A.right :=
    (φ.hom (k - 1)).app A.right
  let τR : (E.reducedH (k - 1)).obj A ⟶ (F.reducedH (k - 1)).obj A :=
    (φ.homₚ (k - 1)).app (PointedTopCat.pointedPair.obj A)
  let iE : (E.reducedH (k - 1)).obj A ⟶ (E.H (k - 1)).obj A.right := by
    with_unfolding_all exact (HomologyTheoryData.IsExact.reducedToPointedH E (k - 1)).app A
  let iF : (F.reducedH (k - 1)).obj A ⟶ (F.H (k - 1)).obj A.right := by
    with_unfolding_all exact (HomologyTheoryData.IsExact.reducedToPointedH F (k - 1)).app A
  let δE : RE ⟶ (E.H (k - 1)).obj A.right := by
    with_unfolding_all exact E.boundary k P
  let δF : RF ⟶ (F.H (k - 1)).obj A.right := by
    with_unfolding_all exact F.boundary k P
  have hE : eE.hom ≫ iE = δE := by
    with_unfolding_all exact relativeHIsoReducedOfPointedContractibleAmbient_hom_inclusion E k f hf
  have hF : eF.hom ≫ iF = δF := by
    with_unfolding_all exact relativeHIsoReducedOfPointedContractibleAmbient_hom_inclusion F k f hf
  have hδ : τP ≫ δF = δE ≫ τA := by
    with_unfolding_all exact (φ.w_app k (k - 1) P).symm
  have hi : iE ≫ τA = τR ≫ iF := by
    with_unfolding_all exact
      HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory φ (k - 1) A
  have : Mono iF := by with_unfolding_all exact reducedInclusion_mono F (k - 1) A
  with_unfolding_all change τP ≫ eF.hom = eE.hom ≫ τR
  apply (cancel_mono iF).mp
  calc
    (τP ≫ eF.hom) ≫ iF = τP ≫ (eF.hom ≫ iF) := Category.assoc τP eF.hom iF
    _ = τP ≫ δF := congrArg (fun z : RF ⟶ (F.H (k - 1)).obj A.right => τP ≫ z) hF
    _ = δE ≫ τA := hδ
    _ = (eE.hom ≫ iE) ≫ τA :=
      congrArg (fun z : RE ⟶ (E.H (k - 1)).obj A.right => z ≫ τA) hE.symm
    _ = eE.hom ≫ (iE ≫ τA) := Category.assoc eE.hom iE τA
    _ = eE.hom ≫ (τR ≫ iF) :=
      congrArg (fun z : (E.reducedH (k - 1)).obj A ⟶ (F.H (k - 1)).obj A.right =>
        eE.hom ≫ z) hi
    _ = (eE.hom ≫ τR) ≫ iF := (Category.assoc eE.hom τR iF).symm

/-- If a pointed map has contractible target and ambient homology vanishes in
degree `n`, relative degree-`n` homology is reduced degree-`n - 1` homology of
the source. -/
noncomputable def relativeHIsoReducedOfContractibleAmbient
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right]
    (hAmbient : IsZero ((E.H n).obj X.right)) :
    (E.Hₚ n).obj (TopPair.of f.right hf) ≅ (E.reducedH (n - 1)).obj A :=
  relativeHKernelIsoOfIsZeroAmbient E n (TopPair.of f.right hf) hAmbient ≪≫
    (reducedHKernelIsoOfContractibleTarget E (n - 1) f).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem relativeHIsoReducedOfContractibleAmbient_hom_inclusion
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) {A X : PointedTopCat.{w}} (f : A ⟶ X)
    (hf : Topology.IsEmbedding f.right) [ContractibleSpace X.right]
    (hAmbient : IsZero ((E.H n).obj X.right)) :
    (relativeHIsoReducedOfContractibleAmbient E n f hf hAmbient).hom ≫
        (reducedToPointedH E (n - 1)).app A =
      E.boundary n (TopPair.of f.right hf) := by
  let P := TopPair.of f.right hf
  let eK := relativeHKernelIsoOfIsZeroAmbient E n P hAmbient
  let eR := reducedHKernelIsoOfContractibleTarget E (n - 1) f
  have hK : eK.hom ≫ kernel.ι (E.subspaceMap (n - 1) P) =
      E.boundary n P := relativeHKernelIsoOfIsZeroAmbient_hom_ι E n P hAmbient
  have hR : eR.hom ≫ kernel.ι ((E.H (n - 1)).map f.right) =
      (reducedToPointedH E (n - 1)).app A :=
    reducedHKernelIsoOfContractibleTarget_hom_ι E (n - 1) f
  have hSymm : eR.inv ≫ (reducedToPointedH E (n - 1)).app A =
      kernel.ι ((E.H (n - 1)).map f.right) :=
    eR.inv_comp_eq.mpr hR.symm
  change eK.hom ≫ kernel.ι ((E.H (n - 1)).map f.right) =
      E.boundary n P at hK
  change (eK.hom ≫ eR.inv) ≫ (reducedToPointedH E (n - 1)).app A =
      E.boundary n P
  calc
    (eK.hom ≫ eR.inv) ≫ (reducedToPointedH E (n - 1)).app A =
      eK.hom ≫ (eR.inv ≫ (reducedToPointedH E (n - 1)).app A) :=
      Category.assoc _ _ _
    _ = eK.hom ≫ kernel.ι ((E.H (n - 1)).map f.right) := by rw [hSymm]
    _ = E.boundary n P := hK

set_option backward.isDefEq.respectTransparency false in
theorem reducedHKernelIsoToPoint_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [F.IsExact]
    (f : E ⟶ F) (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedHKernelIsoToPoint E n X).hom ≫
        kernel.map ((E.H n).map (TopCat.isTerminalPUnit.from X.right))
          ((F.H n).map (TopCat.isTerminalPUnit.from X.right))
          ((f.hom n).app X.right) ((f.hom n).app (TopCat.of PUnit))
          ((f.hom n).naturality (TopCat.isTerminalPUnit.from X.right)) =
      (f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
        (reducedHKernelIsoToPoint F n X).hom := by
  apply (cancel_mono (kernel.ι ((F.H n).map (TopCat.isTerminalPUnit.from X.right)))).mp
  calc
    ((reducedHKernelIsoToPoint E n X).hom ≫
        kernel.map ((E.H n).map (TopCat.isTerminalPUnit.from X.right))
          ((F.H n).map (TopCat.isTerminalPUnit.from X.right))
          ((f.hom n).app X.right) ((f.hom n).app (TopCat.of PUnit))
          ((f.hom n).naturality (TopCat.isTerminalPUnit.from X.right))) ≫
        kernel.ι ((F.H n).map (TopCat.isTerminalPUnit.from X.right))
      = (reducedHKernelIsoToPoint E n X).hom ≫
          kernel.ι ((E.H n).map (TopCat.isTerminalPUnit.from X.right)) ≫
            (f.hom n).app X.right := by
        simp only [Category.assoc]
        simp
    _ = (reducedToPointedH E n).app X ≫ (f.hom n).app X.right := by
        simp
    _ = (f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
          (reducedToPointedH F n).app X := by
        rw [reducedToPointedH_naturality_theory]
    _ = (f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
          (reducedHKernelIsoToPoint F n X).hom ≫
            kernel.ι ((F.H n).map (TopCat.isTerminalPUnit.from X.right)) := by
        rw [← reducedHKernelIsoToPoint_hom_ι]
    _ = ((f.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
          (reducedHKernelIsoToPoint F n X).hom) ≫
          kernel.ι ((F.H n).map (TopCat.isTerminalPUnit.from X.right)) := by
        simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem reducedHKernelIsoOfContractibleTarget_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [E.IsHomotopyInvariant]
    [F.IsExact] [F.IsHomotopyInvariant]
    (φ : E ⟶ F) (n : ℤ) {A X : PointedTopCat.{w}} (g : A ⟶ X)
    [ContractibleSpace X.right] :
    (reducedHKernelIsoOfContractibleTarget E n g).hom ≫
        kernel.map ((E.H n).map g.right) ((F.H n).map g.right)
          ((φ.hom n).app A.right) ((φ.hom n).app X.right)
          ((φ.hom n).naturality g.right) =
      (φ.homₚ n).app (PointedTopCat.pointedPair.obj A) ≫
        (reducedHKernelIsoOfContractibleTarget F n g).hom := by
  apply (cancel_mono (kernel.ι ((F.H n).map g.right))).mp
  calc
    ((reducedHKernelIsoOfContractibleTarget E n g).hom ≫
        kernel.map ((E.H n).map g.right) ((F.H n).map g.right)
          ((φ.hom n).app A.right) ((φ.hom n).app X.right)
          ((φ.hom n).naturality g.right)) ≫
        kernel.ι ((F.H n).map g.right)
      = (reducedHKernelIsoOfContractibleTarget E n g).hom ≫
          kernel.ι ((E.H n).map g.right) ≫ (φ.hom n).app A.right := by
        simp only [Category.assoc]
        simp
    _ = (reducedToPointedH E n).app A ≫ (φ.hom n).app A.right := by
        simp
    _ = (φ.homₚ n).app (PointedTopCat.pointedPair.obj A) ≫
          (reducedToPointedH F n).app A := by
        rw [reducedToPointedH_naturality_theory]
    _ = (φ.homₚ n).app (PointedTopCat.pointedPair.obj A) ≫
          (reducedHKernelIsoOfContractibleTarget F n g).hom ≫
            kernel.ι ((F.H n).map g.right) := by
        rw [← reducedHKernelIsoOfContractibleTarget_hom_ι (E := F) (f := g)]
    _ = ((φ.homₚ n).app (PointedTopCat.pointedPair.obj A) ≫
          (reducedHKernelIsoOfContractibleTarget F n g).hom) ≫
          kernel.ι ((F.H n).map g.right) := by
        simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem relativeHIsoReducedOfContractibleAmbient_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [E.IsHomotopyInvariant]
    [F.IsExact] [F.IsHomotopyInvariant]
    (φ : E ⟶ F) (n : ℤ) {A X : PointedTopCat.{w}} (g : A ⟶ X)
    (hg : Topology.IsEmbedding g.right) [ContractibleSpace X.right]
    (hE : IsZero ((E.H n).obj X.right)) (hF : IsZero ((F.H n).obj X.right)) :
    (φ.homₚ n).app (TopPair.of g.right hg) ≫
        (relativeHIsoReducedOfContractibleAmbient F n g hg hF).hom =
      (relativeHIsoReducedOfContractibleAmbient E n g hg hE).hom ≫
        (φ.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj A) := by
  let _ : Mono ((reducedToPointedH F (n - 1)).app A) := by
    dsimp [reducedToPointedH]
    infer_instance
  apply (cancel_mono ((reducedToPointedH F (n - 1)).app A)).mp
  calc
    ((φ.homₚ n).app (TopPair.of g.right hg) ≫
        (relativeHIsoReducedOfContractibleAmbient F n g hg hF).hom) ≫
        (reducedToPointedH F (n - 1)).app A
      = (φ.homₚ n).app (TopPair.of g.right hg) ≫
          ((relativeHIsoReducedOfContractibleAmbient F n g hg hF).hom ≫
            (reducedToPointedH F (n - 1)).app A) := by
        simp only [Category.assoc]
    _ = (φ.homₚ n).app (TopPair.of g.right hg) ≫
          F.boundary n (TopPair.of g.right hg) := by
        rw [relativeHIsoReducedOfContractibleAmbient_hom_inclusion]
    _ = E.boundary n (TopPair.of g.right hg) ≫ (φ.hom (n - 1)).app A.right := by
        have hW : (φ.homₚ n).app (TopPair.of g.right hg) ≫
              F.boundary n (TopPair.of g.right hg) =
            E.boundary n (TopPair.of g.right hg) ≫
              (φ.hom (n - 1)).app A.right := by
          have h := φ.w n (n - 1)
          have hP := congrArg (fun α => α.app (TopPair.of g.right hg)) h
          exact hP.symm
        exact hW
    _ = ((relativeHIsoReducedOfContractibleAmbient E n g hg hE).hom ≫
          (reducedToPointedH E (n - 1)).app A) ≫
          (φ.hom (n - 1)).app A.right := by
        rw [← relativeHIsoReducedOfContractibleAmbient_hom_inclusion]
    _ = (relativeHIsoReducedOfContractibleAmbient E n g hg hE).hom ≫
          ((reducedToPointedH E (n - 1)).app A ≫
            (φ.hom (n - 1)).app A.right) := by
        simp only [Category.assoc]
    _ = (relativeHIsoReducedOfContractibleAmbient E n g hg hE).hom ≫
          ((φ.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj A) ≫
            (reducedToPointedH F (n - 1)).app A) := by
        rw [reducedToPointedH_naturality_theory]
    _ = ((relativeHIsoReducedOfContractibleAmbient E n g hg hE).hom ≫
          (φ.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj A)) ≫
          (reducedToPointedH F (n - 1)).app A := by
        simp only [Category.assoc]

end HomologyTheoryData.IsExact

namespace GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Reduced homology of pointed spaces for a generalized homology theory. -/
abbrev reducedH (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    PointedTopCat.{w} ⥤ C :=
  HomologyTheoryData.reducedH E.obj n

/-- Reduced homology in degree `n`, functorial in the generalized homology theory. -/
def reducedHFunctor (n : ℤ) :
    GeneralizedHomologyTheory.{u, v, w} C ⥤ (PointedTopCat.{w} ⥤ C) :=
  (HomologyTheoryData.isGeneralizedHomologyTheory (C := C)).ι ⋙
    HomologyTheoryData.reducedHFunctor n

/-- Absolute homology of the underlying space of a pointed space. -/
abbrev pointedH (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    PointedTopCat.{w} ⥤ C :=
  HomologyTheoryData.pointedH E.obj n

theorem pointedH_map (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (E.pointedH n).map f =
      (E.obj.H n).map (TopPair.Hom.fst (PointedTopCat.pointedPair.map f)) := rfl

section

variable [HasBinaryBiproducts C]

/-- The coefficient object plus reduced homology, functorial in the pointed space. -/
noncomputable abbrev coefficientBiprodReduced
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) : PointedTopCat.{w} ⥤ C :=
  HomologyTheoryData.coefficientBiprodReduced E.obj n

@[reassoc]
theorem coefficientBiprodReduced_map_fst
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (E.coefficientBiprodReduced n).map f ≫ biprod.fst = biprod.fst :=
  HomologyTheoryData.coefficientBiprodReduced_map_fst E.obj n f

@[reassoc]
theorem coefficientBiprodReduced_map_snd
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (E.coefficientBiprodReduced n).map f ≫ biprod.snd =
      biprod.snd ≫ (E.reducedH n).map f :=
  HomologyTheoryData.coefficientBiprodReduced_map_snd E.obj n f

end

/-- The natural reduced splitting for a generalized homology theory. -/
noncomputable def homologyIsoCoefficientBiprodReducedNatIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    E.pointedH n ≅ E.coefficientBiprodReduced n :=
  HomologyTheoryData.IsExact.homologyIsoCoefficientBiprodReducedNatIso E.obj n

@[simp]
theorem homologyIsoCoefficientBiprodReducedNatIso_app
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w}) :
    (E.homologyIsoCoefficientBiprodReducedNatIso n).app X =
      HomologyTheoryData.IsExact.homologyIsoCoefficientBiprodReduced E.obj n X := rfl

set_option backward.isDefEq.respectTransparency false in
theorem homologyIsoCoefficientBiprodReduced_hom_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : GeneralizedHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (f.hom.hom n).app (PointedTopCat.pointedPair.obj X).fst ≫
        (F.homologyIsoCoefficientBiprodReducedNatIso n).hom.app X =
      (E.homologyIsoCoefficientBiprodReducedNatIso n).hom.app X ≫
        biprod.map ((f.hom.hom n).app (TopCat.of PUnit))
          ((f.hom.homₚ n).app (PointedTopCat.pointedPair.obj X)) :=
  HomologyTheoryData.IsExact.homologyIsoCoefficientBiprodReduced_hom_naturality_theory
    f.hom n X

/-- The natural inclusion of reduced homology into absolute homology of pointed spaces. -/
noncomputable def reducedToPointedH
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    E.reducedH n ⟶ E.pointedH n :=
  HomologyTheoryData.IsExact.reducedToPointedH E.obj n

@[simp]
theorem reducedToPointedH_app
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E n).app X =
      (HomologyTheoryData.IsExact.reducedToPointedH E.obj n).app X := rfl

theorem reducedToPointedH_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : GeneralizedHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E n).app X ≫ (f.hom.hom n).app X.right =
      (f.hom.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
        (reducedToPointedH F n).app X :=
  HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory f.hom n X

theorem isZero_reducedH_of_isIso_basepoint {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w})
    [IsIso X.hom] : Limits.IsZero ((E.reducedH n).obj X) :=
  HomologyTheoryData.IsExact.isZero_reducedH_of_isIso_basepoint E.obj n X

end GeneralizedHomologyTheory

namespace OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Reduced homology of pointed spaces for an ordinary homology theory. -/
abbrev reducedH (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) :
    PointedTopCat.{w} ⥤ C :=
  GeneralizedHomologyTheory.reducedH (forgetDimension.obj E) n

/-- Reduced homology in degree `n`, functorial in the ordinary homology theory. -/
def reducedHFunctor (n : ℤ) :
    OrdinaryHomologyTheory.{u, v, w} C ⥤ (PointedTopCat.{w} ⥤ C) :=
  forgetDimension ⋙ GeneralizedHomologyTheory.reducedHFunctor n

/-- Absolute homology of the underlying space of a pointed space. -/
abbrev pointedH {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) :
    PointedTopCat.{w} ⥤ C :=
  GeneralizedHomologyTheory.pointedH (forgetDimension.obj E) n

/-- In nonzero degree, absolute and reduced ordinary homology are naturally isomorphic. -/
noncomputable def homologyIsoReducedNatIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) (hn : n ≠ 0) :
    E.pointedH n ≅ E.reducedH n :=
  (forgetDimension.obj E).homologyIsoCoefficientBiprodReducedNatIso n ≪≫
    NatIso.ofComponents
      (fun _ => (isoZeroBiprod (E.property.2.isZero_point n hn)).symm)
      (fun f => GeneralizedHomologyTheory.coefficientBiprodReduced_map_snd
        (forgetDimension.obj E) n f)

@[simp]
theorem homologyIsoReducedNatIso_app
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) (hn : n ≠ 0)
    (X : PointedTopCat.{w}) :
    (E.homologyIsoReducedNatIso n hn).app X =
      ((forgetDimension.obj E).homologyIsoCoefficientBiprodReducedNatIso n).app X ≪≫
        (isoZeroBiprod (E.property.2.isZero_point n hn)).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The nonzero-degree absolute-to-reduced isomorphism is natural in ordinary
homology theories. -/
theorem homologyIsoReduced_hom_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (hn : n ≠ 0) (X : PointedTopCat.{w}) :
    (f.hom.hom n).app X.right ≫
        (F.homologyIsoReducedNatIso n hn).hom.app X =
      (E.homologyIsoReducedNatIso n hn).hom.app X ≫
        (f.hom.homₚ n).app (PointedTopCat.pointedPair.obj X) := by
  have hf : ((forgetDimension.map f).hom.homₚ n).app
      (PointedTopCat.pointedPair.obj X) =
      (f.hom.homₚ n).app (PointedTopCat.pointedPair.obj X) := rfl
  change (f.hom.hom n).app X.right ≫
      (((forgetDimension.obj F).homologyIsoCoefficientBiprodReducedNatIso n).hom.app X ≫
        biprod.snd) =
    (((forgetDimension.obj E).homologyIsoCoefficientBiprodReducedNatIso n).hom.app X ≫
        biprod.snd) ≫
      (f.hom.homₚ n).app (PointedTopCat.pointedPair.obj X)
  rw [← Category.assoc]
  erw [GeneralizedHomologyTheory.homologyIsoCoefficientBiprodReduced_hom_naturality_theory
      (forgetDimension.map f) n X]
  rw [Category.assoc]
  erw [biprod.map_snd]
  simp only [Category.assoc]
  rw [hf]

/-- The natural inclusion of reduced homology into absolute homology of pointed spaces. -/
noncomputable def reducedToPointedH
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) :
    E.reducedH n ⟶ E.pointedH n :=
  HomologyTheoryData.IsExact.reducedToPointedH E.obj n

@[simp]
theorem reducedToPointedH_app
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E n).app X =
      (HomologyTheoryData.IsExact.reducedToPointedH E.obj n).app X := rfl

theorem reducedToPointedH_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedToPointedH E n).app X ≫ (f.hom.hom n).app X.right =
      (f.hom.homₚ n).app (PointedTopCat.pointedPair.obj X) ≫
        (reducedToPointedH F n).app X :=
  HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory f.hom n X

/-- Relative homology of a pointed inclusion into a contractible ambient space
is the reduced homology of the source, provided the next-degree coefficient
object vanishes. -/
noncomputable def relativeHIsoReducedOfContractibleAmbient
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (n : ℤ) (hn : n ≠ 0) {A X : PointedTopCat.{w}}
    (f : A ⟶ X) (hf : Topology.IsEmbedding f.right)
    [ContractibleSpace X.right] :
    (E.Hₚ n).obj (TopPair.of f.right hf) ≅ (E.reducedH (n - 1)).obj A := by
  let P := TopPair.of f.right hf
  have hAmbient : IsZero ((E.H n).obj P.fst) :=
    E.isZero_of_contractible n hn X.right
  exact HomologyTheoryData.IsExact.relativeHIsoReducedOfContractibleAmbient
    E.obj n f hf hAmbient

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem relativeHIsoReducedOfContractibleAmbient_hom_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (n : ℤ) (hn : n ≠ 0) {A X : PointedTopCat.{w}}
    (f : A ⟶ X) (hf : Topology.IsEmbedding f.right)
    [ContractibleSpace X.right] :
    (relativeHIsoReducedOfContractibleAmbient E n hn f hf).hom ≫
        (HomologyTheoryData.IsExact.reducedToPointedH E.obj (n - 1)).app A =
      E.obj.boundary n (TopPair.of f.right hf) := by
  let P := TopPair.of f.right hf
  have hAmbient : IsZero ((E.H n).obj P.fst) :=
    E.isZero_of_contractible n hn X.right
  exact HomologyTheoryData.IsExact.relativeHIsoReducedOfContractibleAmbient_hom_inclusion
    E.obj n f hf hAmbient

set_option backward.isDefEq.respectTransparency false in
theorem relativeHIsoReducedOfContractibleAmbient_hom_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (φ : E ⟶ F) (n : ℤ) (hn : n ≠ 0)
    {A X : PointedTopCat.{w}} (g : A ⟶ X) (hg : Topology.IsEmbedding g.right)
    [ContractibleSpace X.right] :
    (φ.hom.homₚ n).app (TopPair.of g.right hg) ≫
        (relativeHIsoReducedOfContractibleAmbient F n hn g hg).hom =
      (relativeHIsoReducedOfContractibleAmbient E n hn g hg).hom ≫
        (φ.hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj A) := by
  have hE : IsZero ((E.H n).obj X.right) := E.isZero_of_contractible n hn X.right
  have hF : IsZero ((F.H n).obj X.right) := F.isZero_of_contractible n hn X.right
  exact HomologyTheoryData.IsExact.relativeHIsoReducedOfContractibleAmbient_hom_naturality_theory
    φ.hom n g hg hE hF

theorem isZero_reducedH_of_isIso_basepoint {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w})
    [IsIso X.hom] : Limits.IsZero ((E.reducedH n).obj X) :=
  TopPair.GeneralizedHomologyTheory.isZero_reducedH_of_isIso_basepoint
    (forgetDimension.obj E) n X

end OrdinaryHomologyTheory

namespace CohomologyTheoryData

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Reduced cohomology for raw cohomology-theory data. -/
abbrev reducedH (E : CohomologyTheoryData.{w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  (E.unop.reducedH n).leftOp

/-- Evaluation of raw reduced cohomology in degree `n`. -/
def reducedHFunctor (n : ℤ) :
    CohomologyTheoryData.{w} C ⥤ ((PointedTopCat.{w})ᵒᵖ ⥤ C) :=
  hₚFunctor n ⋙
    (Functor.whiskeringLeft (PointedTopCatᵒᵖ) (TopPairᵒᵖ) C).obj
      PointedTopCat.pointedPair.op

end CohomologyTheoryData

namespace CohomologyTheoryData

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Absolute cohomology of the underlying space of a pointed space. -/
abbrev pointedH (E : CohomologyTheoryData.{w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  (E.unop.pointedH n).leftOp

theorem pointedH_map (E : CohomologyTheoryData.{w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (E.pointedH n).map f =
      ((E.unop.H n).map
        (TopPair.Hom.fst (PointedTopCat.pointedPair.map f.unop))).unop := rfl

section

variable [HasBinaryBiproducts C]

/-- The coefficient object plus reduced cohomology, obtained by duality. -/
noncomputable abbrev coefficientBiprodReduced
    (E : CohomologyTheoryData.{w} C) (n : ℤ) : (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  (E.unop.coefficientBiprodReduced n).leftOp

@[simp]
theorem coefficientBiprodReduced_map
    (E : CohomologyTheoryData.{w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (E.coefficientBiprodReduced n).map f =
      ((E.unop.coefficientBiprodReduced n).map f.unop).unop := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem coefficientBiprodReduced_inl_map
    (E : CohomologyTheoryData.{w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (biprod.fst :
        E.unop.coefficientObject n ⊞
            (E.unop.Hₚ n).obj (PointedTopCat.pointedPair.obj X.unop) ⟶
          E.unop.coefficientObject n).unop ≫
      ((E.unop.coefficientBiprodReduced n).map f.unop).unop =
    (biprod.fst :
        E.unop.coefficientObject n ⊞
            (E.unop.Hₚ n).obj (PointedTopCat.pointedPair.obj Y.unop) ⟶
          E.unop.coefficientObject n).unop := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.coefficientBiprodReduced_map_fst E.unop n f.unop

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem coefficientBiprodReduced_inr_map
    (E : CohomologyTheoryData.{w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (biprod.snd :
        E.unop.coefficientObject n ⊞
            (E.unop.Hₚ n).obj (PointedTopCat.pointedPair.obj X.unop) ⟶
          (E.unop.Hₚ n).obj (PointedTopCat.pointedPair.obj X.unop)).unop ≫
      ((E.unop.coefficientBiprodReduced n).map f.unop).unop =
    (E.reducedH n).map f ≫
      (biprod.snd :
        E.unop.coefficientObject n ⊞
            (E.unop.Hₚ n).obj (PointedTopCat.pointedPair.obj Y.unop) ⟶
          (E.unop.Hₚ n).obj (PointedTopCat.pointedPair.obj Y.unop)).unop := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.coefficientBiprodReduced_map_snd E.unop n f.unop

end

end CohomologyTheoryData

namespace CohomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The reduced cohomology short complex, obtained by categorical duality. -/
noncomputable def reducedShortComplex
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) : ShortComplex C :=
  (HomologyTheoryData.IsExact.reducedShortComplex E.unop n X).unop

/-- The reduced cohomology short complex is split, by categorical duality. -/
noncomputable def reducedSplitting
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedShortComplex E n X).Splitting :=
  (HomologyTheoryData.IsExact.reducedSplitting E.unop n X).unop

/-- Reduced cohomology vanishes when the basepoint inclusion is an isomorphism. -/
theorem isZero_reducedH_of_isIso_basepoint
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) [IsIso X.hom] :
    Limits.IsZero ((E.reducedH n).obj (Opposite.op X)) :=
  (TopPair.HomologyTheoryData.IsExact.isZero_reducedH_of_isIso_basepoint
    E.unop n X).unop

/-- The reduced cohomology splitting, natural in pointed spaces and obtained by duality. -/
noncomputable def coefficientBiprodReducedIsoCohomologyNatIso
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact] (n : ℤ) :
    E.coefficientBiprodReduced n ≅ E.pointedH n :=
  NatIso.leftOp
    (HomologyTheoryData.IsExact.homologyIsoCoefficientBiprodReducedNatIso E.unop n)

@[simp]
theorem coefficientBiprodReducedIsoCohomologyNatIso_app
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    (n : ℤ) (X : (PointedTopCat.{w})ᵒᵖ) :
    (coefficientBiprodReducedIsoCohomologyNatIso E n).app X =
      Iso.unop ((HomologyTheoryData.IsExact.homologyIsoCoefficientBiprodReducedNatIso
        E.unop n).app X.unop) := rfl

theorem coefficientBiprodReducedIsoCohomology_hom_naturality
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact] (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (E.coefficientBiprodReduced n).map f ≫
        (coefficientBiprodReducedIsoCohomologyNatIso E n).hom.app Y =
      (coefficientBiprodReducedIsoCohomologyNatIso E n).hom.app X ≫
        (E.pointedH n).map f :=
  (coefficientBiprodReducedIsoCohomologyNatIso E n).hom.naturality f

set_option backward.isDefEq.respectTransparency false in
theorem coefficientBiprodReducedIsoCohomology_hom_naturality_theory
    {E F : CohomologyTheoryData.{w} C} [E.unop.IsExact] [F.unop.IsExact]
    (f : E ⟶ F) (n : ℤ) (X : PointedTopCat.{w}) :
    (coefficientBiprodReducedIsoCohomologyNatIso E n).hom.app (Opposite.op X) ≫
        ((f.unop.hom n).app X.right).unop =
      (biprod.map ((f.unop.hom n).app (TopCat.of PUnit))
          ((f.unop.homₚ n).app (PointedTopCat.pointedPair.obj X))).unop ≫
        (coefficientBiprodReducedIsoCohomologyNatIso F n).hom.app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  exact
    HomologyTheoryData.IsExact.homologyIsoCoefficientBiprodReduced_hom_naturality_theory
      f.unop n X

/-- The natural projection from absolute to reduced cohomology of pointed spaces. -/
noncomputable def pointedHToReduced (E : CohomologyTheoryData.{w} C) [E.unop.IsExact] (n : ℤ) :
    E.pointedH n ⟶ E.reducedH n :=
  NatTrans.leftOp (HomologyTheoryData.IsExact.reducedToPointedH E.unop n)

theorem pointedHToReduced_app (E : CohomologyTheoryData.{w} C) [E.unop.IsExact] (n : ℤ)
    (X : PointedTopCat.{w}) :
    (pointedHToReduced E n).app (Opposite.op X) =
      ((HomologyTheoryData.IsExact.reducedToPointedH E.unop n).app X).unop := rfl

theorem pointedHToReduced_naturality_theory
    {E F : CohomologyTheoryData.{w} C} [E.unop.IsExact] [F.unop.IsExact]
    (f : E ⟶ F) (n : ℤ) (X : PointedTopCat.{w}) :
    ((f.unop.hom n).app X.right).unop ≫
        (pointedHToReduced F n).app (Opposite.op X) =
      (pointedHToReduced E n).app (Opposite.op X) ≫
        ((f.unop.homₚ n).app (PointedTopCat.pointedPair.obj X)).unop := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory f.unop n X

/-- The cokernel of pullback along collapse to the point is reduced cohomology. -/
noncomputable def pointCokernelIsoReducedH
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) :
    cokernel (((E.unop.H n).map (TopCat.isTerminalPUnit.from X.right)).unop) ≅
      (E.reducedH n).obj (Opposite.op X) :=
  (kernelOpUnop
    (((E.unop.H n).map (TopCat.isTerminalPUnit.from X.right)).unop)).symm ≪≫
    (HomologyTheoryData.IsExact.reducedHKernelIsoToPoint E.unop n X).unop

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pointCokernelIsoReducedH_π_hom
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    (n : ℤ) (X : PointedTopCat.{w}) :
    cokernel.π (((E.unop.H n).map
        (TopCat.isTerminalPUnit.from X.right)).unop) ≫
        (pointCokernelIsoReducedH E n X).hom =
      (pointedHToReduced E n).app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  simp [pointCokernelIsoReducedH, pointedHToReduced_app,
    HomologyTheoryData.IsExact.reducedHKernelIsoToPoint_hom_ι]

set_option backward.isDefEq.respectTransparency false in
theorem pointCokernelIsoReducedH_hom_naturality_theory
    {E F : CohomologyTheoryData.{w} C} [E.unop.IsExact] [F.unop.IsExact]
    (f : E ⟶ F) (n : ℤ) (X : PointedTopCat.{w}) :
    cokernel.map
        (((E.unop.H n).map (TopCat.isTerminalPUnit.from X.right)).unop)
        (((F.unop.H n).map (TopCat.isTerminalPUnit.from X.right)).unop)
        (((f.unop.hom n).app (TopCat.of PUnit)).unop)
        (((f.unop.hom n).app X.right).unop)
        (by
          apply Quiver.Hom.op_inj
          exact ((f.unop.hom n).naturality
            (TopCat.isTerminalPUnit.from X.right)).symm) ≫
        (pointCokernelIsoReducedH F n X).hom =
      (pointCokernelIsoReducedH E n X).hom ≫
        ((f.unop.homₚ n).app (PointedTopCat.pointedPair.obj X)).unop := by
  apply (cancel_epi (cokernel.π (((E.unop.H n).map (TopCat.isTerminalPUnit.from X.right)).unop))).mp
  simpa using pointedHToReduced_naturality_theory f n X

/-- The cokernel of pullback along a pointed map to a contractible space is reduced
cohomology of its source. -/
noncomputable def contractibleTargetCokernelIsoReducedH
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    [E.unop.IsHomotopyInvariant] (n : ℤ)
    {A X : PointedTopCat.{w}} (g : A ⟶ X) [ContractibleSpace X.right] :
    cokernel (((E.unop.H n).map g.right).unop) ≅
      (E.reducedH n).obj (Opposite.op A) :=
  (kernelOpUnop (((E.unop.H n).map g.right).unop)).symm ≪≫
    (HomologyTheoryData.IsExact.reducedHKernelIsoOfContractibleTarget
      E.unop n g).unop

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem contractibleTargetCokernelIsoReducedH_π_hom
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    [E.unop.IsHomotopyInvariant] (n : ℤ)
    {A X : PointedTopCat.{w}} (g : A ⟶ X) [ContractibleSpace X.right] :
    cokernel.π (((E.unop.H n).map g.right).unop) ≫
        (contractibleTargetCokernelIsoReducedH E n g).hom =
      (pointedHToReduced E n).app (Opposite.op A) := by
  apply Quiver.Hom.op_inj
  simp [contractibleTargetCokernelIsoReducedH, pointedHToReduced_app,
    HomologyTheoryData.IsExact.reducedHKernelIsoOfContractibleTarget_hom_ι]

set_option backward.isDefEq.respectTransparency false in
theorem contractibleTargetCokernelIsoReducedH_hom_naturality_theory
    {E F : CohomologyTheoryData.{w} C} [E.unop.IsExact] [E.unop.IsHomotopyInvariant]
    [F.unop.IsExact] [F.unop.IsHomotopyInvariant]
    (f : E ⟶ F) (n : ℤ) {A X : PointedTopCat.{w}} (g : A ⟶ X)
    [ContractibleSpace X.right] :
    cokernel.map (((E.unop.H n).map g.right).unop)
        (((F.unop.H n).map g.right).unop)
        (((f.unop.hom n).app X.right).unop)
        (((f.unop.hom n).app A.right).unop)
        (by
          apply Quiver.Hom.op_inj
          exact ((f.unop.hom n).naturality g.right).symm) ≫
        (contractibleTargetCokernelIsoReducedH F n g).hom =
      (contractibleTargetCokernelIsoReducedH E n g).hom ≫
        ((f.unop.homₚ n).app
          (PointedTopCat.pointedPair.obj A)).unop := by
  apply (cancel_epi (cokernel.π (((E.unop.H n).map g.right).unop))).mp
  simpa using pointedHToReduced_naturality_theory f n A

/-- Reduced cohomology in degree `n - 1` of a pointed subspace is isomorphic to relative
cohomology in degree `n`, when the ambient space is contractible and its cohomology in degree
`n` vanishes. -/
noncomputable def reducedHIsoRelativeOfContractibleAmbient
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    [E.unop.IsHomotopyInvariant] (n : ℤ)
    {A X : PointedTopCat.{w}} (g : A ⟶ X)
    (hg : Topology.IsEmbedding g.right) [ContractibleSpace X.right]
    (hAmbient : IsZero ((E.H n).obj (Opposite.op X.right))) :
    (E.reducedH (n - 1)).obj (Opposite.op A) ≅
      (E.Hₚ n).obj (Opposite.op (TopPair.of g.right hg)) :=
  (HomologyTheoryData.IsExact.relativeHIsoReducedOfContractibleAmbient
    E.unop n g hg hAmbient.op).unop

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pointedHToReduced_comp_reducedHIsoRelativeOfContractibleAmbient_hom
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExact]
    [E.unop.IsHomotopyInvariant] (n : ℤ)
    {A X : PointedTopCat.{w}} (g : A ⟶ X)
    (hg : Topology.IsEmbedding g.right) [ContractibleSpace X.right]
    (hAmbient : IsZero ((E.H n).obj (Opposite.op X.right))) :
    (pointedHToReduced E (n - 1)).app (Opposite.op A) ≫
        (reducedHIsoRelativeOfContractibleAmbient E n g hg hAmbient).hom =
      (E.unop.boundary n (TopPair.of g.right hg)).unop := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.relativeHIsoReducedOfContractibleAmbient_hom_inclusion
    E.unop n g hg hAmbient.op

set_option backward.isDefEq.respectTransparency false in
theorem reducedHIsoRelativeOfContractibleAmbient_hom_naturality_theory
    {E F : CohomologyTheoryData.{w} C} [E.unop.IsExact] [E.unop.IsHomotopyInvariant]
    [F.unop.IsExact] [F.unop.IsHomotopyInvariant] (f : E ⟶ F) (n : ℤ)
    {A X : PointedTopCat.{w}} (g : A ⟶ X)
    (hg : Topology.IsEmbedding g.right) [ContractibleSpace X.right]
    (hE : IsZero ((E.H n).obj (Opposite.op X.right)))
    (hF : IsZero ((F.H n).obj (Opposite.op X.right))) :
    (reducedHIsoRelativeOfContractibleAmbient E n g hg hE).hom ≫
        ((f.unop.homₚ n).app (TopPair.of g.right hg)).unop =
      ((f.unop.homₚ (n - 1)).app
          (PointedTopCat.pointedPair.obj A)).unop ≫
        (reducedHIsoRelativeOfContractibleAmbient F n g hg hF).hom := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.relativeHIsoReducedOfContractibleAmbient_hom_naturality_theory
    f.unop n g hg hF.op hE.op

end CohomologyTheoryData.IsExact

namespace GeneralizedCohomologyTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Reduced cohomology of pointed spaces for a generalized cohomology theory. -/
abbrev reducedH (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  PointedTopCat.pointedPair.op ⋙ E.Hₚ n

/-- Reduced cohomology in degree `n`, functorial in the generalized cohomology theory. -/
def reducedHFunctor (n : ℤ) :
    GeneralizedCohomologyTheory.{u, v, w} C ⥤ ((PointedTopCat.{w})ᵒᵖ ⥤ C) :=
  hₚFunctor n ⋙ (Functor.whiskeringLeft (PointedTopCatᵒᵖ) (TopPairᵒᵖ) C).obj
    PointedTopCat.pointedPair.op

/-- Absolute cohomology of the underlying space of a pointed space. -/
abbrev pointedH (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  (E.unop.pointedH n).leftOp

theorem pointedH_map (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (E.pointedH n).map f =
      ((E.unop.obj.H n).map
        (TopPair.Hom.fst (PointedTopCat.pointedPair.map f.unop))).unop := rfl

section

variable [HasBinaryBiproducts C]

/-- The coefficient object plus reduced cohomology, obtained by duality. -/
noncomputable abbrev coefficientBiprodReduced
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  (E.unop.coefficientBiprodReduced n).leftOp

@[simp]
theorem coefficientBiprodReduced_map
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (E.coefficientBiprodReduced n).map f =
      ((E.unop.coefficientBiprodReduced n).map f.unop).unop := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coefficientBiprodReduced_inl_map
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (biprod.fst :
        (E.unop.coefficientBiprodReduced n).obj X.unop ⟶
          E.unop.obj.coefficientObject n).unop ≫
      (E.coefficientBiprodReduced n).map f =
    (biprod.fst :
        (E.unop.coefficientBiprodReduced n).obj Y.unop ⟶
          E.unop.obj.coefficientObject n).unop := by
  apply Quiver.Hom.op_inj
  exact GeneralizedHomologyTheory.coefficientBiprodReduced_map_fst E.unop n f.unop

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coefficientBiprodReduced_inr_map
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (biprod.snd :
        (E.unop.coefficientBiprodReduced n).obj X.unop ⟶
          (E.unop.reducedH n).obj X.unop).unop ≫
      (E.coefficientBiprodReduced n).map f =
    (E.reducedH n).map f ≫
      (biprod.snd :
        (E.unop.coefficientBiprodReduced n).obj Y.unop ⟶
          (E.unop.reducedH n).obj Y.unop).unop := by
  apply Quiver.Hom.op_inj
  exact GeneralizedHomologyTheory.coefficientBiprodReduced_map_snd E.unop n f.unop

end


/-- The natural reduced splitting for a generalized cohomology theory, by duality. -/
noncomputable def coefficientBiprodReducedIsoCohomologyNatIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    E.coefficientBiprodReduced n ≅ E.pointedH n :=
  NatIso.leftOp (E.unop.homologyIsoCoefficientBiprodReducedNatIso n)

@[simp]
theorem coefficientBiprodReducedIsoCohomologyNatIso_app
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedCohomologyTheory.{u, v, w} C)
    (n : ℤ) (X : (PointedTopCat.{w})ᵒᵖ) :
    (E.coefficientBiprodReducedIsoCohomologyNatIso n).app X =
      Iso.unop ((E.unop.homologyIsoCoefficientBiprodReducedNatIso n).app X.unop) := rfl

theorem coefficientBiprodReducedIsoCohomology_hom_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ)
    {X Y : (PointedTopCat.{w})ᵒᵖ} (f : X ⟶ Y) :
    (E.coefficientBiprodReduced n).map f ≫
        (E.coefficientBiprodReducedIsoCohomologyNatIso n).hom.app Y =
      (E.coefficientBiprodReducedIsoCohomologyNatIso n).hom.app X ≫
        (E.pointedH n).map f :=
  (E.coefficientBiprodReducedIsoCohomologyNatIso n).hom.naturality f

set_option backward.isDefEq.respectTransparency false in
theorem coefficientBiprodReducedIsoCohomology_hom_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : GeneralizedCohomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (E.coefficientBiprodReducedIsoCohomologyNatIso n).hom.app (Opposite.op X) ≫
        ((f.unop.hom.hom n).app X.right).unop =
      (biprod.map ((f.unop.hom.hom n).app (TopCat.of PUnit))
          ((f.unop.hom.homₚ n).app (PointedTopCat.pointedPair.obj X))).unop ≫
        (F.coefficientBiprodReducedIsoCohomologyNatIso n).hom.app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  exact GeneralizedHomologyTheory.homologyIsoCoefficientBiprodReduced_hom_naturality_theory
    f.unop n X

/-- The natural projection from absolute to reduced cohomology of pointed spaces. -/
noncomputable def pointedHToReduced {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    E.pointedH n ⟶ E.reducedH n :=
  NatTrans.leftOp (E.unop.reducedToPointedH n)

@[simp]
theorem pointedHToReduced_app {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w}) :
    (pointedHToReduced E n).app (Opposite.op X) =
      ((E.unop.reducedToPointedH n).app X).unop := rfl

theorem pointedHToReduced_naturality_theory {C : Type u} [Category.{v} C] [Abelian C]
    {E F : GeneralizedCohomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    ((f.unop.hom.hom n).app X.right).unop ≫
        (pointedHToReduced F n).app (Opposite.op X) =
      (pointedHToReduced E n).app (Opposite.op X) ≫
        ((f.unop.hom.homₚ n).app (PointedTopCat.pointedPair.obj X)).unop := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory f.unop.hom n X

theorem isZero_reducedH_of_isIso_basepoint {C : Type u} [Category.{v} C] [Abelian C]
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w})
    [IsIso X.hom] : Limits.IsZero ((E.reducedH n).obj (Opposite.op X)) := by
  have h : (forgetData.obj E).unop.IsExact := E.unop.property.2.1
  exact CohomologyTheoryData.IsExact.isZero_reducedH_of_isIso_basepoint
    (forgetData.obj E) n X

end GeneralizedCohomologyTheory

namespace OrdinaryCohomologyTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Reduced cohomology of pointed spaces for an ordinary cohomology theory. -/
abbrev reducedH (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  GeneralizedCohomologyTheory.reducedH (forgetDimension.obj E) n

/-- Reduced cohomology in degree `n`, functorial in the ordinary cohomology theory. -/
def reducedHFunctor (n : ℤ) :
    OrdinaryCohomologyTheory.{u, v, w} C ⥤ ((PointedTopCat.{w})ᵒᵖ ⥤ C) :=
  forgetDimension ⋙ GeneralizedCohomologyTheory.reducedHFunctor n

/-- Absolute cohomology of the underlying space of a pointed space. -/
abbrev pointedH {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) :
    (PointedTopCat.{w})ᵒᵖ ⥤ C :=
  (E.unop.pointedH n).leftOp

/-- In nonzero degree, reduced and absolute ordinary cohomology are naturally isomorphic,
by duality from ordinary homology. -/
noncomputable def reducedIsoCohomologyNatIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) (hn : n ≠ 0) :
    E.reducedH n ≅ E.pointedH n :=
  NatIso.leftOp (E.unop.homologyIsoReducedNatIso n hn)

@[simp]
theorem reducedIsoCohomologyNatIso_app
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) (hn : n ≠ 0)
    (X : (PointedTopCat.{w})ᵒᵖ) :
    (E.reducedIsoCohomologyNatIso n hn).app X =
      Iso.unop ((E.unop.homologyIsoReducedNatIso n hn).app X.unop) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The nonzero-degree reduced-to-absolute isomorphism is natural in ordinary
cohomology theories. -/
theorem reducedIsoCohomology_hom_naturality_theory
    {C : Type u} [Category.{v} C] [Abelian C]
    {E F : OrdinaryCohomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (hn : n ≠ 0) (X : PointedTopCat.{w}) :
    (E.reducedIsoCohomologyNatIso n hn).hom.app (Opposite.op X) ≫
        ((f.unop.hom.hom n).app X.right).unop =
      ((f.unop.hom.homₚ n).app (PointedTopCat.pointedPair.obj X)).unop ≫
        (F.reducedIsoCohomologyNatIso n hn).hom.app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  exact OrdinaryHomologyTheory.homologyIsoReduced_hom_naturality_theory
    f.unop n hn X

/-- The natural projection from absolute to reduced cohomology of pointed spaces. -/
noncomputable def pointedHToReduced {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) :
    E.pointedH n ⟶ E.reducedH n :=
  NatTrans.leftOp (E.unop.reducedToPointedH n)

@[simp]
theorem pointedHToReduced_app {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w}) :
    (pointedHToReduced E n).app (Opposite.op X) =
      ((E.unop.reducedToPointedH n).app X).unop := rfl

theorem pointedHToReduced_naturality_theory {C : Type u} [Category.{v} C] [Abelian C]
    {E F : OrdinaryCohomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    ((f.unop.hom.hom n).app X.right).unop ≫
        (pointedHToReduced F n).app (Opposite.op X) =
      (pointedHToReduced E n).app (Opposite.op X) ≫
        ((f.unop.hom.homₚ n).app (PointedTopCat.pointedPair.obj X)).unop := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory f.unop.hom n X

theorem isZero_reducedH_of_isIso_basepoint {C : Type u} [Category.{v} C] [Abelian C]
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) (X : PointedTopCat.{w})
    [IsIso X.hom] : Limits.IsZero ((E.reducedH n).obj (Opposite.op X)) :=
  TopPair.GeneralizedCohomologyTheory.isZero_reducedH_of_isIso_basepoint
    (forgetDimension.obj E) n X

end OrdinaryCohomologyTheory

end TopPair
