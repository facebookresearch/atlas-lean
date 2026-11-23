/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Cone
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Reduced

/-!
# The pointed-cone boundary as reduced homology

The exact-triple boundary for `* ⟶ X ⟶ CX` identifies the relative
homology of `(CX, X)` with the reduced homology of `X`, naturally in both the
pointed space and the homology theory.
-/

@[expose] public section

open CategoryTheory

universe w u v

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The pointed-cone boundary, with its target expressed as reduced homology. -/
noncomputable def pointedConeRelativeReducedNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) :
    TopCat.pointedConeTripleFunctor ⋙ AlgebraicTopology.topTriplePair12 ⋙ E.Hₚ n ≅
      E.reducedH (n - 1) :=
  pointedConeTripleBoundaryNatIso E n

/-- The pointed-cone reduced isomorphism is natural in raw homology theories. -/
theorem pointedConeRelativeReducedNatIso_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} (f : E ⟶ F)
    [E.IsExact] [E.IsHomotopyInvariant]
    [F.IsExact] [F.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (f.homₚ n).app
          (AlgebraicTopology.topTriplePair12.obj
            (TopCat.pointedConeTripleFunctor.obj X)) ≫
        (pointedConeRelativeReducedNatIso F n).hom.app X =
      (pointedConeRelativeReducedNatIso E n).hom.app X ≫
        (f.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X) := by
  set_option backward.isDefEq.respectTransparency false in
  exact (ComposableArrows.naturality'
    (HomologyTheoryData.tripleSequenceHom f n
      (TopCat.pointedConeTripleFunctor.obj X)) 2 3).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pointedConeRelativeReducedNatIso_hom_app_comp_reducedToPointedH
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (pointedConeRelativeReducedNatIso E n).hom.app X ≫
        (reducedToPointedH E (n - 1)).app X =
      E.boundary n
        (AlgebraicTopology.topTriplePair12.obj
          (TopCat.pointedConeTripleFunctor.obj X)) := by
  let P := AlgebraicTopology.topTriplePair12.obj (TopCat.pointedConeTripleFunctor.obj X)
  let b : (E.Hₚ n).obj P ⟶ (E.H (n - 1)).obj X.right := E.boundary n P
  let t : (E.H (n - 1)).obj X.right ⟶ (E.Hₚ (n - 1)).obj (PointedTopCat.pointedPair.obj X) :=
    E.toRelative (n - 1) (PointedTopCat.pointedPair.obj X)
  let e := homologyIsoCoefficientBiprodReduced E (n - 1) X
  have he_fst : e.hom ≫ Limits.biprod.fst =
      (E.H (n - 1)).map (TopCat.isTerminalPUnit.from X.right) :=
    homologyIsoCoefficientBiprodReduced_hom_fst E (n - 1) X
  have he_snd : e.hom ≫ Limits.biprod.snd = t :=
    homologyIsoCoefficientBiprodReduced_hom_snd E (n - 1) X
  have hmap : TopCat.isTerminalPUnit.from X.right =
      P.map ≫ TopCat.isTerminalPUnit.from P.fst := by apply TopCat.isTerminalPUnit.hom_ext
  have hzero : b ≫ (E.H (n - 1)).map (TopCat.isTerminalPUnit.from X.right) = 0 := by
    rw [hmap, (E.H (n - 1)).map_comp]
    change E.boundary n P ≫ E.subspaceMap (n - 1) P ≫
      (E.H (n - 1)).map (TopCat.isTerminalPUnit.from P.fst) = 0
    rw [← Category.assoc, boundary_comp_subspaceMap]
    simp
  change (b ≫ t) ≫ (Limits.biprod.inr ≫ e.inv) = b
  apply (cancel_mono e.hom).mp
  calc
    ((b ≫ t) ≫ (Limits.biprod.inr ≫ e.inv)) ≫ e.hom =
        (b ≫ t) ≫ Limits.biprod.inr := by simp
    _ = b ≫ e.hom := by
      ext
      · rw [Category.assoc, Category.assoc, Limits.biprod.inr_fst]
        simp only [Limits.comp_zero]
        exact (hzero.symm.trans (congrArg (fun z ↦ b ≫ z) he_fst).symm).trans
          (Category.assoc _ _ _).symm
      · rw [Category.assoc, Category.assoc, Limits.biprod.inr_snd, Category.comp_id]
        exact (congrArg (fun z ↦ b ≫ z) he_snd).symm.trans (Category.assoc _ _ _).symm

end TopPair.HomologyTheoryData.IsExact

namespace TopPair.GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The pointed-cone reduced isomorphism for a generalized homology theory. -/
noncomputable def pointedConeRelativeReducedNatIso
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    TopCat.pointedConeTripleFunctor ⋙ AlgebraicTopology.topTriplePair12 ⋙ E.Hₚ n ≅
      E.reducedH (n - 1) :=
  HomologyTheoryData.IsExact.pointedConeRelativeReducedNatIso E.obj n

/-- The generalized pointed-cone reduced isomorphism is natural in theories. -/
theorem pointedConeRelativeReducedNatIso_hom_naturality_theory
    {E F : GeneralizedHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (f.hom.homₚ n).app
          (AlgebraicTopology.topTriplePair12.obj
            (TopCat.pointedConeTripleFunctor.obj X)) ≫
        (F.pointedConeRelativeReducedNatIso n).hom.app X =
      (E.pointedConeRelativeReducedNatIso n).hom.app X ≫
        (f.hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X) :=
  HomologyTheoryData.IsExact.pointedConeRelativeReducedNatIso_hom_naturality_theory
    f.hom n X

end TopPair.GeneralizedHomologyTheory

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cone-pair to suspension-pair comparison is a natural isomorphism on
relative homology. -/
noncomputable def conePairToSuspensionPairNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) :
    TopCat.pointedConeTripleFunctor ⋙ AlgebraicTopology.topTriplePair12 ⋙ E.Hₚ n ≅
      Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair ⋙ E.Hₚ n := by
  let α := Functor.whiskerRight TopPair.conePairToSuspensionPairNatTrans (E.Hₚ n)
  let _ (X : PointedTopCat.{w}) : IsIso (α.app X) :=
    isIso_map_conePairToSuspensionPair E n X
  exact NatIso.ofComponents (fun X => asIso (α.app X)) (fun f => α.naturality f)

/-- Reduced homology of the suspension is reduced homology shifted by one. -/
noncomputable def reducedSuspensionNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) :
    Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙ E.reducedH n ≅
      E.reducedH (n - 1) :=
  (conePairToSuspensionPairNatIso E n).symm ≪≫ pointedConeRelativeReducedNatIso E n

@[simp]
theorem reducedSuspensionNatIso_hom_app
    (E : HomologyTheoryData.{w} C) [E.IsExcisive] [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedSuspensionNatIso (C := C) E n).hom.app X =
      (conePairToSuspensionPairNatIso (C := C) E n).inv.app X ≫
        (pointedConeRelativeReducedNatIso (C := C) E n).hom.app X := rfl

set_option backward.isDefEq.respectTransparency false in
theorem reducedSuspensionNatIso_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} (f : E ⟶ F)
    [E.IsExcisive] [E.IsExact] [E.IsHomotopyInvariant]
    [F.IsExcisive] [F.IsExact] [F.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (f.homₚ n).app ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair).obj X) ≫
        (reducedSuspensionNatIso (C := C) F n).hom.app X =
      (reducedSuspensionNatIso (C := C) E n).hom.app X ≫
        (f.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X) := by
  let φ := TopPair.conePairToSuspensionPairNatTrans.app X
  let αE := (conePairToSuspensionPairNatIso (C := C) E n).app X
  let αF := (conePairToSuspensionPairNatIso (C := C) F n).app X
  let βE := (pointedConeRelativeReducedNatIso (C := C) E n).hom.app X
  let βF := (pointedConeRelativeReducedNatIso (C := C) F n).hom.app X
  let fSusp := (f.homₚ n).app ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair).obj X)
  let fCone := (f.homₚ n).app
      (AlgebraicTopology.topTriplePair12.obj (TopCat.pointedConeTripleFunctor.obj X))
  let fRed := (f.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X)
  let _ : IsIso ((E.Hₚ n).map φ) := isIso_map_conePairToSuspensionPair E n X
  let _ : IsIso ((F.Hₚ n).map φ) := isIso_map_conePairToSuspensionPair F n X
  have hNatPair : αE.hom ≫ fSusp = fCone ≫ αF.hom :=
    (f.homₚ n).naturality φ
  have hConeRed : fCone ≫ βF = βE ≫ fRed :=
    pointedConeRelativeReducedNatIso_hom_naturality_theory f n X
  have hE : (reducedSuspensionNatIso (C := C) E n).hom.app X = αE.inv ≫ βE :=
    reducedSuspensionNatIso_hom_app E n X
  have hF : (reducedSuspensionNatIso (C := C) F n).hom.app X = αF.inv ≫ βF :=
    reducedSuspensionNatIso_hom_app F n X
  rw [hE, hF]
  have h1 : αE.hom ≫ fSusp ≫ (αF.inv ≫ βF) = αE.hom ≫ ((αE.inv ≫ βE) ≫ fRed) := by
    calc
      αE.hom ≫ fSusp ≫ (αF.inv ≫ βF) = (αE.hom ≫ fSusp ≫ αF.inv) ≫ βF := by
        simp only [Category.assoc]
      _ = (fCone ≫ αF.hom ≫ αF.inv) ≫ βF := by
        have h2 : αE.hom ≫ fSusp ≫ αF.inv = fCone ≫ αF.hom ≫ αF.inv := by
          calc
            αE.hom ≫ fSusp ≫ αF.inv = (αE.hom ≫ fSusp) ≫ αF.inv := by
              simp only [Category.assoc]
            _ = (fCone ≫ αF.hom) ≫ αF.inv := by rw [hNatPair]
            _ = fCone ≫ αF.hom ≫ αF.inv := by simp only [Category.assoc]
        rw [h2]
      _ = fCone ≫ βF := by simp
      _ = βE ≫ fRed := hConeRed
      _ = αE.hom ≫ ((αE.inv ≫ βE) ≫ fRed) := by simp
  exact (cancel_epi αE.hom).mp h1

end TopPair.HomologyTheoryData.IsExact

namespace TopPair.GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reduced suspension isomorphism for a generalized homology theory. -/
noncomputable def reducedSuspensionNatIso
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙ E.reducedH n ≅
      E.reducedH (n - 1) :=
  HomologyTheoryData.IsExact.reducedSuspensionNatIso E.obj n

end TopPair.GeneralizedHomologyTheory

namespace TopPair.GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem reducedSuspensionNatIso_hom_naturality_theory
    {E F : GeneralizedHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (f.hom.homₚ n).app ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair).obj X) ≫
        (F.reducedSuspensionNatIso n).hom.app X =
      (E.reducedSuspensionNatIso n).hom.app X ≫
        (f.hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X) :=
  HomologyTheoryData.IsExact.reducedSuspensionNatIso_hom_naturality_theory f.hom n X

end TopPair.GeneralizedHomologyTheory

namespace TopPair.OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def reducedSuspensionNatIso
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) :
    Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙ E.reducedH n ≅
      E.reducedH (n - 1) :=
  (forgetDimension.obj E).reducedSuspensionNatIso n

theorem reducedSuspensionNatIso_hom_naturality_theory
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (f.hom.homₚ n).app ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair).obj X) ≫
        (F.reducedSuspensionNatIso n).hom.app X =
      (E.reducedSuspensionNatIso n).hom.app X ≫
        (f.hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X) :=
  HomologyTheoryData.IsExact.reducedSuspensionNatIso_hom_naturality_theory f.hom n X

end TopPair.OrdinaryHomologyTheory

namespace TopPair.CohomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def reducedSuspensionNatIso
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExcisive] [E.unop.IsExact]
    [E.unop.IsHomotopyInvariant] (n : ℤ) :
    E.reducedH (n - 1) ≅
      (Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor).op ⋙ E.reducedH n :=
  NatIso.leftOp (HomologyTheoryData.IsExact.reducedSuspensionNatIso (C := Cᵒᵖ) E.unop n)

@[simp]
theorem reducedSuspensionNatIso_app
    (E : CohomologyTheoryData.{w} C) [E.unop.IsExcisive] [E.unop.IsExact]
    [E.unop.IsHomotopyInvariant] (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedSuspensionNatIso (C := C) E n).app (Opposite.op X) =
      Iso.unop ((HomologyTheoryData.IsExact.reducedSuspensionNatIso (C := Cᵒᵖ) E.unop n).app X) :=
  rfl

theorem reducedSuspensionNatIso_hom_naturality_theory
    {E F : CohomologyTheoryData.{w} C} (f : E ⟶ F)
    [E.unop.IsExcisive] [E.unop.IsExact] [E.unop.IsHomotopyInvariant]
    [F.unop.IsExcisive] [F.unop.IsExact] [F.unop.IsHomotopyInvariant]
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedSuspensionNatIso (C := C) E n).hom.app (Opposite.op X) ≫
        ((f.unop.homₚ n).app
          ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
            PointedTopCat.pointedPair).obj X)).unop =
      ((f.unop.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X)).unop ≫
        (reducedSuspensionNatIso (C := C) F n).hom.app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.reducedSuspensionNatIso_hom_naturality_theory f.unop n X

end TopPair.CohomologyTheoryData.IsExact

namespace TopPair.GeneralizedCohomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def reducedSuspensionNatIso
    (E : GeneralizedCohomologyTheory.{u, v, w} C) (n : ℤ) :
    E.reducedH (n - 1) ≅
      (Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor).op ⋙ E.reducedH n :=
  NatIso.leftOp (E.unop.reducedSuspensionNatIso n)

theorem reducedSuspensionNatIso_hom_naturality_theory
    {E F : GeneralizedCohomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedSuspensionNatIso (C := C) E n).hom.app (Opposite.op X) ≫
        ((f.unop.hom.homₚ n).app
          ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
            PointedTopCat.pointedPair).obj X)).unop =
      ((f.unop.hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X)).unop ≫
        (reducedSuspensionNatIso (C := C) F n).hom.app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.reducedSuspensionNatIso_hom_naturality_theory f.unop.hom n X

end TopPair.GeneralizedCohomologyTheory

namespace TopPair.OrdinaryCohomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

noncomputable def reducedSuspensionNatIso
    (E : OrdinaryCohomologyTheory.{u, v, w} C) (n : ℤ) :
    E.reducedH (n - 1) ≅
      (Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor).op ⋙ E.reducedH n :=
  (forgetDimension.obj E).reducedSuspensionNatIso n

theorem reducedSuspensionNatIso_hom_naturality_theory
    {E F : OrdinaryCohomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (X : PointedTopCat.{w}) :
    (reducedSuspensionNatIso (C := C) E n).hom.app (Opposite.op X) ≫
        ((f.unop.hom.homₚ n).app
          ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
            PointedTopCat.pointedPair).obj X)).unop =
      ((f.unop.hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X)).unop ≫
        (reducedSuspensionNatIso (C := C) F n).hom.app (Opposite.op X) := by
  apply Quiver.Hom.op_inj
  exact HomologyTheoryData.IsExact.reducedSuspensionNatIso_hom_naturality_theory f.unop.hom n X

end TopPair.OrdinaryCohomologyTheory
