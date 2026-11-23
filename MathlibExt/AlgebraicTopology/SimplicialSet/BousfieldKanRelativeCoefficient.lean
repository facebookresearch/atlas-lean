/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.RelativeCoefficientTotal
public import MathlibExt.CategoryTheory.CategoryHomology.WeightedBar
public import MathlibExt.CategoryTheory.Enriched.WeightedBarMapPostcomp
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexColimits

/-!
# The original BK bicomplex as the bar of its chain coefficients

The existing weighted-bar postcomposition comparison moves simplicial
chains through the original degreewise coproducts. Removing the terminal
weight then gives the coefficient-chain bar. This comparison is natural
for the original diagram map, including its actual summand maps.

The total comparison and the stock cokernel comparison identify the
original relative BK total with the signed total of its relative chain
diagram. The whole quotient square is certified, rather than supplying a
relative-model or homology-comparison witness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology Opposite
open scoped Simplicial

universe w

public section

local instance : HasCoproducts.{w} (ChainComplex AddCommGrpCat.{w} ℕ) := fun I =>
  let : Small.{w} (Discrete I) := small_self (Discrete I)
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  HomologicalComplex.instHasColimitsOfShape

namespace SSet

variable {J : Type w} [Category.{0} J]
  (R : AddCommGrpCat.{w}) (D : J ⥤ SSet.{w})

private abbrev chains : SSet.{w} ⥤ ChainComplex AddCommGrpCat.{w} ℕ :=
  (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R

/-- The original bicomplex is the alternating bar of the original chain diagram. -/
def bkCoefficientChainIso :
    bkAlternatingBicomplex AddCommGrpCat.{w} R D ≅
      coefficientBarComplex
        (D ⋙ (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{w})).app
        ((bisimplicialLinearizationFunctor AddCommGrpCat.{w} R).obj (bkBarBisimplicial D)) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex
        (ChainComplex AddCommGrpCat.{w} ℕ)).mapIso
      (Functor.associator
        (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D)
        (coproductLinearizationFunctor AddCommGrpCat.{w} R)
        (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{w})) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex
        (ChainComplex AddCommGrpCat.{w} ℕ)).mapIso
      (StrictOrdinaryWeightedBar.wbarSimplicialMapPostcompIso
        (W := CategoryBar.replUnit J) (F := D) (G := chains R)) ≪≫
    terminalWeightCoefficientBarComplexIso (D ⋙ chains R)

private theorem bkCoefficientChainIso_hom_f (p : ℕ) :
    (bkCoefficientChainIso R D).hom.f p =
      (StrictOrdinaryWeightedBar.wbarObjMapIso
        (W := CategoryBar.replUnit J) (F := D) (G := chains R) p).hom ≫
        (terminalWeightCoefficientBarDegreeIso (D ⋙ chains R) p).hom := by
  change (((𝟙 _ ≫ 𝟙 _) ≫
      (StrictOrdinaryWeightedBar.wbarSimplicialMapPostcompIso
        (W := CategoryBar.replUnit J) (F := D) (G := chains R)).hom.app (op ⦋p⦌)) ≫
      (terminalWeightCoefficientBarDegreeIso (D ⋙ chains R) p).hom) = _
  rw [Category.id_comp, Category.id_comp,
    StrictOrdinaryWeightedBar.wbarSimplicialMapPostcompIso_hom_app_mk]
  rfl

/-- Every original weighted summand retains its original chain and coefficient. -/
theorem bkCoefficientChainIso_summand (p : ℕ)
    (s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p) :
    SSet.chainComplexMap
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s) R ≫
      (bkCoefficientChainIso R D).hom.f p =
    coefficientBarι (D ⋙ (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R) s.1 := by
  let e := StrictOrdinaryWeightedBar.wbarObjMapIso
    (W := CategoryBar.replUnit J) (F := D) (G := chains R) p
  have h : (chains R).map
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s) ≫ e.hom =
      StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) (D ⋙ chains R) p s := by
    apply (cancel_mono e.inv).mp
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    exact (StrictOrdinaryWeightedBar.wbarObjMapIso_inv_ι
      (W := CategoryBar.replUnit J) (F := D) (G := chains R) p s).symm
  let V := (D.obj s.1.left).chainComplex R
  let U := (bkAlternatingBicomplex AddCommGrpCat.{w} R D).X p
  let T := StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) (D ⋙ chains R) p
  let Z := coefficientBarObj (D ⋙ chains R) p
  let l : V ⟶ U := SSet.chainComplexMap
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s) R
  let t : T ⟶ Z := (terminalWeightCoefficientBarDegreeIso (D ⋙ chains R) p).hom
  let j : V ⟶ T :=
    StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) (D ⋙ chains R) p s
  let k : U ⟶ Z := (bkCoefficientChainIso R D).hom.f p
  let i : V ⟶ Z := coefficientBarι (D ⋙ chains R) s.1
  have hk : k = e.hom ≫ t := bkCoefficientChainIso_hom_f R D p
  have hj : l ≫ e.hom = j := h
  have ht : j ≫ t = i :=
    wbarIncl_terminalWeightCoefficientBarDegreeIso_hom (D ⋙ chains R) p s
  change l ≫ k = i
  exact (congrArg (fun m => l ≫ m) hk).trans
    ((Category.assoc l e.hom t).symm.trans
      ((congrArg (fun m => m ≫ t) hj).trans ht))

variable {D} {E : J ⥤ SSet.{w}} (α : D ⟶ E)

/-- The whole bicomplex square uses the actual original diagram map. -/
theorem bkCoefficientChainIso_naturality :
    (bkAlternatingBicomplexFunctor AddCommGrpCat.{w} R).map α ≫
        (bkCoefficientChainIso R E).hom =
      (bkCoefficientChainIso R D).hom ≫
        (alternatingCoefficientBarFunctor (J := J)
          (A := ChainComplex AddCommGrpCat.{w} ℕ)).map
            (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R)) := by
  apply HomologicalComplex.hom_ext
  intro p
  change (chains R).map
      (StrictOrdinaryWeightedBar.wbarMapF (W := CategoryBar.replUnit J) p α) ≫
        (bkCoefficientChainIso R E).hom.f p =
      (bkCoefficientChainIso R D).hom.f p ≫
        coefficientBarMap (Functor.whiskerRight α (chains R)) p
  apply (isColimitOfHasCoproductOfPreservesColimit
    (chains R) (fun s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p =>
      D.obj s.1.left)).hom_ext
  rintro ⟨s⟩
  let V := (D.obj s.1.left).chainComplex R
  let W := (E.obj s.1.left).chainComplex R
  let Z := coefficientBarObj (E ⋙ chains R) p
  let lD : V ⟶ (bkAlternatingBicomplex AddCommGrpCat.{w} R D).X p :=
    SSet.chainComplexMap (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s) R
  let lE : W ⟶ (bkAlternatingBicomplex AddCommGrpCat.{w} R E).X p :=
    SSet.chainComplexMap (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s) R
  let a : V ⟶ W := SSet.chainComplexMap (α.app s.1.left) R
  let b := SSet.chainComplexMap
    (StrictOrdinaryWeightedBar.wbarMapF (W := CategoryBar.replUnit J) p α) R
  let eD := (bkCoefficientChainIso R D).hom.f p
  let eE : (bkAlternatingBicomplex AddCommGrpCat.{w} R E).X p ⟶ Z :=
    (bkCoefficientChainIso R E).hom.f p
  let jD : V ⟶ coefficientBarObj (D ⋙ chains R) p := coefficientBarι (D ⋙ chains R) s.1
  let jE : W ⟶ Z := coefficientBarι (E ⋙ chains R) s.1
  let m : coefficientBarObj (D ⋙ chains R) p ⟶ Z :=
    coefficientBarMap (Functor.whiskerRight α (chains R)) p
  have hMap : lD ≫ b = a ≫ lE :=
    ((chains R).map_comp _ _).symm.trans
      ((congrArg (chains R).map (StrictOrdinaryWeightedBar.wbarMapF_ι p α s)).trans
        ((chains R).map_comp _ _))
  have hE : lE ≫ eE = jE := bkCoefficientChainIso_summand R E p s
  have hD : lD ≫ eD = jD := bkCoefficientChainIso_summand R D p s
  have hCoefficient : jD ≫ m = a ≫ jE :=
    coefficientBarι_map (Functor.whiskerRight α (chains R)) s.1
  change lD ≫ (b ≫ eE) = lD ≫ (eD ≫ m)
  exact (Category.assoc lD b eE).symm.trans
    ((congrArg (fun k => k ≫ eE) hMap).trans
      ((Category.assoc a lE eE).trans
        ((congrArg (fun k => a ≫ k) hE).trans
          (hCoefficient.symm.trans
            ((congrArg (fun k => k ≫ m) hD).symm.trans (Category.assoc lD eD m))))))

/-- The comparison of the actual signed totals. -/
def bkCoefficientChainTotalIso (D : J ⥤ SSet.{w}) :
    bkAlternatingTotalComplex AddCommGrpCat.{w} R D ≅
      (coefficientChainTotalFunctor (J := J)).obj
        (D ⋙ (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R) :=
  (HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).mapIso (bkCoefficientChainIso R D)

/-- Naturality of the total comparison, with the entire original maps. -/
theorem bkCoefficientChainTotalIso_naturality :
    (bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α ≫
        (bkCoefficientChainTotalIso R E).hom =
      (bkCoefficientChainTotalIso R D).hom ≫
        (coefficientChainTotalFunctor (J := J)).map
          (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R)) := by
  let T := HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bkCoefficientChainIso_naturality R α)).trans (T.map_comp _ _))

/-- The original relative BK total is the total of the actual relative chain diagram. -/
def bkRelativeCoefficientTotalIso :
    cokernel ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≅
      (coefficientChainTotalFunctor (J := J)).obj
        (cokernel
          (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R))) :=
  cokernel.mapIso
      ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α)
      ((coefficientChainTotalFunctor (J := J)).map (Functor.whiskerRight α (chains R)))
      (bkCoefficientChainTotalIso R D) (bkCoefficientChainTotalIso R E)
      (bkCoefficientChainTotalIso_naturality R α) ≪≫
    (coefficientRelativeTotalIso (Functor.whiskerRight α (chains R))).symm

/-- The relative comparison retains the original BK and coefficient quotient projections. -/
theorem bkRelativeCoefficientTotalIso_projection :
    cokernel.π ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α) ≫
        (bkRelativeCoefficientTotalIso R α).hom =
      (bkCoefficientChainTotalIso R E).hom ≫
        (coefficientChainTotalFunctor (J := J)).map
          (cokernel.π
            (Functor.whiskerRight α ((SSet.chainComplexFunctor AddCommGrpCat.{w}).obj R))) := by
  let e := coefficientRelativeTotalIso (Functor.whiskerRight α (chains R))
  let b := cokernel.mapIso
    ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α)
    ((coefficientChainTotalFunctor (J := J)).map (Functor.whiskerRight α (chains R)))
    (bkCoefficientChainTotalIso R D) (bkCoefficientChainTotalIso R E)
    (bkCoefficientChainTotalIso_naturality R α)
  let q := cokernel.π ((bkAlternatingTotalComplexFunctor AddCommGrpCat.{w} R).map α)
  have hb : q ≫ b.hom = (bkCoefficientChainTotalIso R E).hom ≫
      cokernel.π
        ((coefficientChainTotalFunctor (J := J)).map (Functor.whiskerRight α (chains R))) :=
    cokernel.π_desc _ _ _
  apply (cancel_mono e.hom).mp
  change (q ≫ (b.hom ≫ e.inv)) ≫ e.hom = _
  have hLeft : (q ≫ (b.hom ≫ e.inv)) ≫ e.hom = q ≫ b.hom :=
    (Category.assoc q (b.hom ≫ e.inv) e.hom).trans
      ((congrArg (fun k => q ≫ k) (Category.assoc b.hom e.inv e.hom)).trans
        ((congrArg (fun k => q ≫ (b.hom ≫ k)) e.inv_hom_id).trans
          (congrArg (fun k => q ≫ k) (Category.comp_id b.hom))))
  have hRight :
      ((bkCoefficientChainTotalIso R E).hom ≫
        (coefficientChainTotalFunctor (J := J)).map
          (cokernel.π (Functor.whiskerRight α (chains R)))) ≫ e.hom =
      (bkCoefficientChainTotalIso R E).hom ≫
        cokernel.π
          ((coefficientChainTotalFunctor (J := J)).map
            (Functor.whiskerRight α (chains R))) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => (bkCoefficientChainTotalIso R E).hom ≫ k)
        (coefficientRelativeTotalIso_projection (Functor.whiskerRight α (chains R))))
  exact hLeft.trans (hb.trans hRight.symm)

end SSet
