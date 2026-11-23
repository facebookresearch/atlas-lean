/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.HomologyEquivalence
public import MathlibExt.AlgebraicTopology.LocalCoefficient.WeakSquare
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalence

/-!
# Actual plus data through a pointed homotopy-equivalence square

The actual source and target comparisons have genuine inverse families.
The ORIGINAL strict square transfers all integer systems through its
actual ending-fiber map. The based group square and the actual comparison
equivalences compute the original kernel, normality and perfectness of
the pulled subgroup. No expected kernel or plus witness for the new map
is given.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u

namespace TopCat

/-- Both genuine pointed comparison equivalences and the ORIGINAL square
derive plusness of the ORIGINAL new map with its computed pulled subgroup.
All target integer systems and the actual based kernel are retained. -/
public theorem IsPlusConstructionAt.of_homotopyEquiv_square
    {X Y X' Y' : TopCat.{u}} [PathConnectedSpace Y] [PathConnectedSpace Y']
    {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : X ≃ₕ X') (t : Y ≃ₕ Y')
    (comm : f ≫ TopCat.ofHom t.toFun = TopCat.ofHom s.toFun ≫ g)
    (x : X) (y : Y) (x' : X') (y' : Y')
    (hfx : f x = y) (hsx : s.toFun x = x') (hty : t.toFun y = y')
    (hgx : g x' = y')
    (P : Subgroup (FundamentalGroup X' x')) [P.Normal] [Group.IsPerfect P]
    (hg : IsPlusConstructionAt g x' y' hgx P) :
    let Q := P.comap (FundamentalGroup.mapOfEq s.toFun hsx)
    ∃ hN : Q.Normal, ∃ hP : Group.IsPerfect Q,
      letI := hN
      letI := hP
      IsPlusConstructionAt f x y hfx Q := by
  let ms := FundamentalGroup.mapOfEq s.toFun hsx
  let mt := FundamentalGroup.mapOfEq t.toFun hty
  let mf := FundamentalGroup.mapOfEq f.hom hfx
  let mg := FundamentalGroup.mapOfEq g.hom hgx
  let es := FundamentalGroup.mulEquivOfHomotopyEquivAt s x x' hsx
  let et := FundamentalGroup.mulEquivOfHomotopyEquivAt t y y' hty
  have hes : ms = es.toMonoidHom := by
    apply MonoidHom.ext
    intro p
    exact (FundamentalGroup.mulEquivOfHomotopyEquivAt_apply s x x' hsx p).symm
  have het : mt = et.toMonoidHom := by
    apply MonoidHom.ext
    intro p
    exact (FundamentalGroup.mulEquivOfHomotopyEquivAt_apply t y y' hty p).symm
  have hti : Function.Injective mt := by rw [het]; exact et.injective
  let Q := P.comap ms
  have hN : Q.Normal := inferInstance
  have hP : Group.IsPerfect Q := by
    change Group.IsPerfect (P.comap ms)
    rw [hes, Subgroup.comap_equiv_eq_map_symm']
    exact Group.IsPerfect.map es.symm.toMonoidHom
  letI : Q.Normal := hN
  letI : Group.IsPerfect Q := hP
  have hft : t.toFun (f x) = y' := (congrArg t.toFun hfx).trans hty
  have hsg : g (s.toFun x) = y' := (congrArg g hsx).trans hgx
  have hc : t.toFun.comp f.hom = g.hom.comp s.toFun := by
    simpa only [TopCat.hom_comp, TopCat.hom_ofHom] using congrArg TopCat.Hom.hom comm
  have hfComp := FundamentalGroup.mapOfEq_comp f.hom t.toFun hfx hty hft
  have hgComp := FundamentalGroup.mapOfEq_comp s.toFun g.hom hsx hgx hsg
  have hSquare : mt.comp mf = mg.comp ms :=
    hfComp.symm.trans ((FundamentalGroup.mapOfEq_congr hc hft hsg).trans hgComp)
  have hlocal : IsLocalCoefficientHomologyEquivalence f :=
    localCoefficientHomologyEquivalence_of_weakSquare (TopCat.ofHom s.toFun)
      (TopCat.ofHom t.toFun) comm (homotopyEquiv_toFun_mem s) (homotopyEquiv_toFun_mem t)
      hg.localCoefficientHomologyEquivalence
  refine ⟨hN, hP, ?_⟩
  refine ⟨isAcyclicMapAt_of_localCoefficientHomologyEquivalence f hlocal y, ?_⟩
  apply Subgroup.ext
  intro p
  change mf p = 1 ↔ ms p ∈ P
  have he : mt (mf p) = mg (ms p) :=
    congrArg (fun k : FundamentalGroup X x →* FundamentalGroup Y' y' => k p) hSquare
  have hinj : mt (mf p) = 1 ↔ mf p = 1 := by
    have h : mt (mf p) = mt 1 ↔ mf p = 1 := hti.eq_iff
    simpa only [map_one] using h
  calc
    mf p = 1 ↔ mt (mf p) = 1 := hinj.symm
    _ ↔ mg (ms p) = 1 := by rw [he]
    _ ↔ ms p ∈ mg.ker := Iff.rfl
    _ ↔ ms p ∈ P := by rw [hg.kernel_eq]

/-- The actual source Iso and actual target homotopy equivalence transfer
plusness through an ORIGINAL whole homotopy square. The original point
trace transports kernel membership; no based comparison or desired
all-system consequence is an extra input. -/
public theorem IsPlusConstructionAt.of_sourceIso_targetEquiv_homotopySquare
    {X Y X' Y' : TopCat.{u}} [PathConnectedSpace Y] [PathConnectedSpace Y']
    {f : X ⟶ Y} {g : X' ⟶ Y'} (s : X ≅ X') (t : Y ≃ₕ Y')
    (H : ContinuousMap.Homotopy (f ≫ TopCat.ofHom t.toFun).hom (s.hom ≫ g).hom)
    (x : X) (y : Y) (x' : X') (y' : Y')
    (hfx : f x = y) (hsx : s.hom x = x') (hty : t.toFun y = y')
    (hgx : g x' = y')
    (P : Subgroup (FundamentalGroup X' x')) [P.Normal] [Group.IsPerfect P]
    (hg : IsPlusConstructionAt g x' y' hgx P) :
    let Q := P.comap (FundamentalGroup.mapOfEq s.hom.hom hsx)
    ∃ hN : Q.Normal, ∃ hP : Group.IsPerfect Q,
      letI := hN
      letI := hP
      IsPlusConstructionAt f x y hfx Q := by
  let S := s.hom
  let T := TopCat.ofHom t.toFun
  have hT : T.hom = t.toFun := by
    change (TopCat.ofHom t.toFun).hom = t.toFun
    exact TopCat.hom_ofHom t.toFun
  let ms := FundamentalGroup.mapOfEq S.hom hsx
  let mt := FundamentalGroup.mapOfEq t.toFun hty
  let mf := FundamentalGroup.mapOfEq f.hom hfx
  let mg := FundamentalGroup.mapOfEq g.hom hgx
  let es := FundamentalGroup.mulEquivOfIsoAt s x x' hsx
  let et := FundamentalGroup.mulEquivOfHomotopyEquivAt t y y' hty
  have hes : ms = es.toMonoidHom := by
    apply MonoidHom.ext
    intro p
    exact (FundamentalGroup.mulEquivOfIsoAt_apply s x x' hsx p).symm
  have het : mt = et.toMonoidHom := by
    apply MonoidHom.ext
    intro p
    exact (FundamentalGroup.mulEquivOfHomotopyEquivAt_apply t y y' hty p).symm
  have hti : Function.Injective mt := by rw [het]; exact et.injective
  let Q := P.comap ms
  have hN : Q.Normal := inferInstance
  have hP : Group.IsPerfect Q := by
    change Group.IsPerfect (P.comap ms)
    rw [hes, Subgroup.comap_equiv_eq_map_symm']
    exact Group.IsPerfect.map es.symm.toMonoidHom
  letI : Q.Normal := hN
  letI : Group.IsPerfect Q := hP
  have hS : IsLocalCoefficientHomologyEquivalence S :=
    IsLocalCoefficientHomologyEquivalence.of_isIso S
  have hComposite : IsLocalCoefficientHomologyEquivalence (f ≫ T) :=
    (hS.comp hg.localCoefficientHomologyEquivalence).of_homotopy H
  have hlocal : IsLocalCoefficientHomologyEquivalence f :=
    localCoefficientHomologyEquivalence_of_weakSquare (𝟙 X) T
      (Category.id_comp (f ≫ T)).symm (weakHomotopyEquivalences.id_mem X)
      (homotopyEquiv_toFun_mem t) hComposite
  refine ⟨hN, hP, ?_⟩
  refine ⟨isAcyclicMapAt_of_localCoefficientHomologyEquivalence f hlocal y, ?_⟩
  apply Subgroup.ext
  intro p
  let hft : (f ≫ T) x = y' := (congrArg t.toFun hfx).trans hty
  let hsg : (S ≫ g) x = y' := (congrArg g hsx).trans hgx
  have hCompF := FundamentalGroup.mapOfEq_comp f.hom t.toFun hfx hty hft
  have hCompG := FundamentalGroup.mapOfEq_comp S.hom g.hom hsx hgx hsg
  have hCompositeF : (f ≫ T).hom = t.toFun.comp f.hom :=
    (TopCat.hom_comp f T).trans
      (congrArg (fun k : C(Y, Y') => k.comp f.hom) hT)
  have hCompF' : FundamentalGroup.mapOfEq (f ≫ T).hom hft = mt.comp mf :=
    (FundamentalGroup.mapOfEq_congr hCompositeF hft hft).trans hCompF
  have hCompG' : FundamentalGroup.mapOfEq (S ≫ g).hom hsg = mg.comp ms := by
    simpa only [TopCat.hom_comp] using hCompG
  have hCompFValue : FundamentalGroup.mapOfEq (f ≫ T).hom hft p = mt (mf p) :=
    (DFunLike.congr_fun hCompF' p).trans (MonoidHom.comp_apply mt mf p)
  have hCompGValue : FundamentalGroup.mapOfEq (S ≫ g).hom hsg p = mg (ms p) :=
    (DFunLike.congr_fun hCompG' p).trans (MonoidHom.comp_apply mg ms p)
  have hUnit : FundamentalGroup.mapOfEq (f ≫ T).hom hft p = 1 ↔
      FundamentalGroup.mapOfEq (S ≫ g).hom hsg p = 1 :=
    (FundamentalGroup.mapOfEq_eq_one_iff (f ≫ T).hom hft p).trans
      ((FundamentalGroup.mapOfEq_eq_one_iff_of_homotopy H x p).trans
        (FundamentalGroup.mapOfEq_eq_one_iff (S ≫ g).hom hsg p).symm)
  have hinj : mt (mf p) = 1 ↔ mf p = 1 := by
    have h : mt (mf p) = mt 1 ↔ mf p = 1 := hti.eq_iff
    simpa only [map_one] using h
  change mf p = 1 ↔ ms p ∈ P
  calc
    mf p = 1 ↔ mt (mf p) = 1 := hinj.symm
    _ ↔ FundamentalGroup.mapOfEq (f ≫ T).hom hft p = 1 :=
      Iff.of_eq (congrArg (fun q : FundamentalGroup Y' y' => q = 1) hCompFValue.symm)
    _ ↔ FundamentalGroup.mapOfEq (S ≫ g).hom hsg p = 1 := hUnit
    _ ↔ mg (ms p) = 1 :=
      Iff.of_eq (congrArg (fun q : FundamentalGroup Y' y' => q = 1) hCompGValue)
    _ ↔ ms p ∈ mg.ker := Iff.rfl
    _ ↔ ms p ∈ P := by rw [hg.kernel_eq]

end TopCat

end
