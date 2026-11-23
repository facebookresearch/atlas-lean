/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarBaseFunctoriality
public import MathlibExt.CategoryTheory.Limits.Shapes.CoproductUnion
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The actual coefficient bar on an intersection and a union

A fixed nerve map and coefficient functor restrict to each subcomplex.
The maps below are the existing base maps with their actual source equality.
The weighted simplex coproducts give the chain pushout and the induced
relative-cokernel Iso. No quasi-isomorphism, excision, flatness or plus witness
is assumed. An ambient-cover comparison is a separate homological step.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe uG vG uA vA

namespace CategoryTheory.CategoryHomology

variable {G : Type uG} [Category.{vG} G]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max uG vG} A]
  {T : SSet.{max uG vG}} (φ : T ⟶ nerve G) (M : G ⥤ A)

private theorem subcomplexNerveSquare {U V : T.Subcomplex} (h : U ≤ V) :
    U.ι ≫ φ = SSet.Subcomplex.homOfLE h ≫ (V.ι ≫ φ) := by
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]

omit [Preadditive A] [HasCoproducts.{max uG vG} A] in
private theorem subcomplexFamily_eq (U : T.Subcomplex) (n : ℕ)
    (σ : (U : SSet.{max uG vG}) _⦋n⦌) :
    nervePullbackCoefficientFamily (U.ι ≫ φ) M n σ =
      nervePullbackCoefficientFamily φ M n σ.1 := by
  change M.obj (((U.ι ≫ φ).app (op ⦋n⦌) σ).left) =
    M.obj ((φ.app (op ⦋n⦌) σ.1).left)
  apply congrArg (fun τ : ComposableArrows G n => M.obj τ.left)
  change (NatTrans.vcomp U.ι φ).app (op ⦋n⦌) σ = φ.app (op ⦋n⦌) σ.1
  rw [NatTrans.vcomp_app]
  simp only [Subfunctor.ι_app, ConcreteCategory.comp_apply]
  rfl

private def subcomplexFamilyIso (U : T.Subcomplex) (n : ℕ) :
    nervePullbackCoefficientObj (U.ι ≫ φ) M n ≅
      ∐ fun σ : ↥(U.obj (op ⦋n⦌)) => nervePullbackCoefficientFamily φ M n σ.1 :=
  Sigma.mapIso (fun σ => eqToIso (subcomplexFamily_eq φ M U n σ))

omit [Preadditive A] in
@[reassoc]
private theorem subcomplexFamilyIso_ι (U : T.Subcomplex) (n : ℕ)
    (σ : (U : SSet.{max uG vG}) _⦋n⦌) :
    nervePullbackCoefficientι (U.ι ≫ φ) M σ ≫
      (subcomplexFamilyIso φ M U n).hom =
    eqToHom (subcomplexFamily_eq φ M U n σ) ≫
      Sigma.ι (fun τ : ↥(U.obj (op ⦋n⦌)) =>
        nervePullbackCoefficientFamily φ M n τ.1) σ := by
  exact Sigma.ι_mapIso_hom _ σ

omit [Preadditive A] in
@[reassoc]
private theorem coefficientι_eqToHom_nerve
    {X : SSet.{max uG vG}} {ψ χ : X ⟶ nerve G}
    (he : ψ = χ) (n : ℕ) (σ : X _⦋n⦌) :
    nervePullbackCoefficientι ψ M σ ≫
      eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he) =
    eqToHom (congrArg (fun θ => nervePullbackCoefficientFamily θ M n σ) he) ≫
      nervePullbackCoefficientι χ M σ := by
  subst χ
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem sourceComplex_eqToHom_degree
    {X : SSet.{max uG vG}} {ψ χ : X ⟶ nerve G}
    (he : ψ = χ) (n : ℕ) :
    (eqToIso (nervePullbackCoefficientComplex_X ψ M n)).inv ≫
      (eqToHom (congrArg (fun θ => nervePullbackCoefficientComplex θ M) he)).f n =
    eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he) ≫
      (eqToIso (nervePullbackCoefficientComplex_X χ M n)).inv := by
  subst χ
  simp only [eqToHom_refl, HomologicalComplex.id_f,
    Category.comp_id, Category.id_comp]

private theorem baseComplexMap_degree
    {X Y : SSet.{max uG vG}} (f : X ⟶ Y) (ψ : Y ⟶ nerve G) (n : ℕ) :
    (eqToIso (nervePullbackCoefficientComplex_X (f ≫ ψ) M n)).inv ≫
      (nervePullbackCoefficientBaseComplexMap f ψ M).f n ≫
      (eqToIso (nervePullbackCoefficientComplex_X ψ M n)).hom =
    nervePullbackCoefficientBaseMap f ψ M n := by
  let eS := eqToIso (nervePullbackCoefficientComplex_X (f ≫ ψ) M n)
  let eT := eqToIso (nervePullbackCoefficientComplex_X ψ M n)
  have hactual : (nervePullbackCoefficientBaseComplexMap f ψ M).f n ≍
      nervePullbackCoefficientBaseMap f ψ M n :=
    heq_of_eq (nervePullbackCoefficientBaseComplexMap_f f ψ M n)
  have hformula : (nervePullbackCoefficientBaseComplexMap f ψ M).f n =
      eS.hom ≫ nervePullbackCoefficientBaseMap f ψ M n ≫ eT.inv := by
    change (nervePullbackCoefficientBaseComplexMap f ψ M).f n =
      eqToHom (nervePullbackCoefficientComplex_X (f ≫ ψ) M n) ≫
        nervePullbackCoefficientBaseMap f ψ M n ≫
        eqToHom ((nervePullbackCoefficientComplex_X ψ M n).symm)
    exact (conj_eqToHom_iff_heq
      ((nervePullbackCoefficientBaseComplexMap f ψ M).f n)
      (nervePullbackCoefficientBaseMap f ψ M n)
      (nervePullbackCoefficientComplex_X (f ≫ ψ) M n)
      (nervePullbackCoefficientComplex_X ψ M n)).mpr hactual
  change eS.inv ≫ (nervePullbackCoefficientBaseComplexMap f ψ M).f n ≫ eT.hom = _
  calc
    _ = eS.inv ≫ (eS.hom ≫ nervePullbackCoefficientBaseMap f ψ M n ≫ eT.inv) ≫
        eT.hom :=
      congrArg (fun k : (nervePullbackCoefficientComplex (f ≫ ψ) M).X n ⟶
          (nervePullbackCoefficientComplex ψ M).X n => eS.inv ≫ k ≫ eT.hom) hformula
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

omit [Preadditive A] in
private theorem subcomplexFamilyIso_base (U V : T.Subcomplex) (h : U ≤ V) (n : ℕ) :
    (subcomplexFamilyIso φ M U n).inv ≫
      eqToHom (congrArg (fun ψ => nervePullbackCoefficientObj ψ M n)
        (subcomplexNerveSquare φ h)) ≫
      nervePullbackCoefficientBaseMap (SSet.Subcomplex.homOfLE h) (V.ι ≫ φ) M n ≫
      (subcomplexFamilyIso φ M V n).hom =
    Sigma.subtypeMap (nervePullbackCoefficientFamily φ M n) (h (op ⦋n⦌)) := by
  let F : T _⦋n⦌ → A := nervePullbackCoefficientFamily φ M n
  let FU : ↥(U.obj (op ⦋n⦌)) → A := fun σ => F σ.1
  let FV : ↥(V.obj (op ⦋n⦌)) → A := fun σ => F σ.1
  let hUV : U.obj (op ⦋n⦌) ⊆ V.obj (op ⦋n⦌) := h (op ⦋n⦌)
  let f : (U : SSet.{max uG vG}) ⟶ (V : SSet.{max uG vG}) :=
    SSet.Subcomplex.homOfLE h
  let ψ : (V : SSet.{max uG vG}) ⟶ nerve G := V.ι ≫ φ
  let he : U.ι ≫ φ = f ≫ ψ := subcomplexNerveSquare φ h
  let a : nervePullbackCoefficientObj (U.ι ≫ φ) M n ⟶
      nervePullbackCoefficientObj (f ≫ ψ) M n :=
    eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he)
  let b : nervePullbackCoefficientObj (f ≫ ψ) M n ⟶
      nervePullbackCoefficientObj ψ M n := nervePullbackCoefficientBaseMap f ψ M n
  let eU : nervePullbackCoefficientObj (U.ι ≫ φ) M n ≅ ∐ FU :=
    subcomplexFamilyIso φ M U n
  let eV : nervePullbackCoefficientObj ψ M n ≅ ∐ FV :=
    subcomplexFamilyIso φ M V n
  change eU.inv ≫ a ≫ b ≫ eV.hom = Sigma.subtypeMap F hUV
  apply Sigma.hom_ext
  intro σ
  let σ' : ↥(V.obj (op ⦋n⦌)) := f.app (op ⦋n⦌) σ
  let τ : ↥(V.obj (op ⦋n⦌)) := ⟨σ.1, hUV σ.2⟩
  let pU : nervePullbackCoefficientFamily (U.ι ≫ φ) M n σ = FU σ :=
    subcomplexFamily_eq φ M U n σ
  let pV : nervePullbackCoefficientFamily ψ M n σ' = FV σ' :=
    subcomplexFamily_eq φ M V n σ'
  let p : nervePullbackCoefficientFamily (U.ι ≫ φ) M n σ =
      nervePullbackCoefficientFamily (f ≫ ψ) M n σ :=
    congrArg (fun θ => nervePullbackCoefficientFamily θ M n σ) he
  have hc : (eqToIso pU).inv ≫ eqToHom p ≫ (eqToIso pV).hom =
      eqToHom (congrArg F
        (SSet.Subcomplex.homOfLE_app_val h (op ⦋n⦌) σ).symm) := by
    have q : nervePullbackCoefficientFamily (f ≫ ψ) M n σ = FV σ' := by
      change nervePullbackCoefficientFamily ψ M n (f.app (op ⦋n⦌) σ) = FV σ'
      exact pV
    change eqToHom pU.symm ≫ eqToHom p ≫ eqToHom q = _
    calc
      _ = (eqToHom pU.symm ≫ eqToHom p) ≫ eqToHom q :=
        (Category.assoc _ _ _).symm
      _ = eqToHom (pU.symm.trans p) ≫ eqToHom q :=
        congrArg (fun k => k ≫ eqToHom q) (eqToHom_trans pU.symm p)
      _ = eqToHom ((pU.symm.trans p).trans q) :=
        eqToHom_trans (pU.symm.trans p) q
      _ = _ := rfl
  have hτ : τ = σ' := by
    apply Subtype.ext
    exact (SSet.Subcomplex.homOfLE_app_val h (op ⦋n⦌) σ).symm
  have hi : eqToHom (congrArg F
        (SSet.Subcomplex.homOfLE_app_val h (op ⦋n⦌) σ).symm) ≫
      Sigma.ι FV σ' = Sigma.ι FV τ := by
    exact Sigma.eqToHom_comp_ι FV hτ.symm
  have hU : Sigma.ι FU σ ≫ eU.inv =
      (eqToIso pU).inv ≫ nervePullbackCoefficientι (U.ι ≫ φ) M σ := by
    exact Sigma.ι_mapIso_inv
      (fun ρ : ↥(U.obj (op ⦋n⦌)) => eqToIso (subcomplexFamily_eq φ M U n ρ)) σ
  have ha : nervePullbackCoefficientι (U.ι ≫ φ) M σ ≫ a =
      eqToHom p ≫ nervePullbackCoefficientι (f ≫ ψ) M σ :=
    coefficientι_eqToHom_nerve M he n σ
  have hb : nervePullbackCoefficientι (f ≫ ψ) M σ ≫ b =
      nervePullbackCoefficientι ψ M σ' := nervePullbackCoefficientι_baseMap f ψ M σ
  have hV : nervePullbackCoefficientι ψ M σ' ≫ eV.hom =
      (eqToIso pV).hom ≫ Sigma.ι FV σ' := by
    simpa only [eqToIso.hom] using subcomplexFamilyIso_ι φ M V n σ'
  calc
    Sigma.ι FU σ ≫ (eU.inv ≫ a ≫ b ≫ eV.hom) =
        (Sigma.ι FU σ ≫ eU.inv) ≫ (a ≫ b ≫ eV.hom) :=
      (Category.assoc _ _ _).symm
    _ = ((eqToIso pU).inv ≫ nervePullbackCoefficientι (U.ι ≫ φ) M σ) ≫
        (a ≫ b ≫ eV.hom) :=
      congrArg (fun k => k ≫ (a ≫ b ≫ eV.hom)) hU
    _ = (eqToIso pU).inv ≫
        (nervePullbackCoefficientι (U.ι ≫ φ) M σ ≫ a) ≫ b ≫ eV.hom := by
      simp only [Category.assoc]
    _ = (eqToIso pU).inv ≫
        (eqToHom p ≫ nervePullbackCoefficientι (f ≫ ψ) M σ) ≫ b ≫ eV.hom :=
      congrArg (fun k => (eqToIso pU).inv ≫ k ≫ b ≫ eV.hom) ha
    _ = (eqToIso pU).inv ≫ eqToHom p ≫
        (nervePullbackCoefficientι (f ≫ ψ) M σ ≫ b) ≫ eV.hom := by
      simp only [Category.assoc]
    _ = (eqToIso pU).inv ≫ eqToHom p ≫
        nervePullbackCoefficientι ψ M σ' ≫ eV.hom :=
      congrArg (fun k => (eqToIso pU).inv ≫ eqToHom p ≫ k ≫ eV.hom) hb
    _ = (eqToIso pU).inv ≫ eqToHom p ≫
        ((eqToIso pV).hom ≫ Sigma.ι FV σ') :=
      congrArg (fun k => (eqToIso pU).inv ≫ eqToHom p ≫ k) hV
    _ = ((eqToIso pU).inv ≫ eqToHom p ≫ (eqToIso pV).hom) ≫ Sigma.ι FV σ' :=
      (congrArg (fun k => (eqToIso pU).inv ≫ k)
        (Category.assoc (eqToHom p) (eqToIso pV).hom (Sigma.ι FV σ')).symm).trans
          (Category.assoc (eqToIso pU).inv
            (eqToHom p ≫ (eqToIso pV).hom) (Sigma.ι FV σ')).symm
    _ = eqToHom (congrArg F
        (SSet.Subcomplex.homOfLE_app_val h (op ⦋n⦌) σ).symm) ≫ Sigma.ι FV σ' :=
      congrArg (fun k => k ≫ Sigma.ι FV σ') hc
    _ = Sigma.ι FV τ := hi
    _ = Sigma.ι FU σ ≫ Sigma.subtypeMap F hUV :=
      (Sigma.ι_subtypeMap F hUV σ).symm

public section

/-- The degree chart also identifies the actual coefficient summands with
the ambient weighted family; it is built from their proved equality. -/
def nervePullbackCoefficientSubcomplexDegreeIso (U : T.Subcomplex) (n : ℕ) :
    (nervePullbackCoefficientComplex (U.ι ≫ φ) M).X n ≅
      ∐ fun σ : ↥(U.obj (op ⦋n⦌)) => nervePullbackCoefficientFamily φ M n σ.1 :=
  eqToIso (nervePullbackCoefficientComplex_X (U.ι ≫ φ) M n) ≪≫
    subcomplexFamilyIso φ M U n

/-- The actual existing coefficient base map, with its source transported
along the original subcomplex inclusion square. -/
def nervePullbackCoefficientSubcomplexComplexMap
    {U V : T.Subcomplex} (h : U ≤ V) :
    nervePullbackCoefficientComplex (U.ι ≫ φ) M ⟶
      nervePullbackCoefficientComplex (V.ι ≫ φ) M :=
  eqToHom (congrArg (fun ψ => nervePullbackCoefficientComplex ψ M)
      (subcomplexNerveSquare φ h)) ≫
    nervePullbackCoefficientBaseComplexMap (SSet.Subcomplex.homOfLE h) (V.ι ≫ φ) M

/-- Every component is the weighted inclusion on the SAME ambient simplex
after the named existing degree charts. -/
theorem nervePullbackCoefficientSubcomplexComplexMap_f
    {U V : T.Subcomplex} (h : U ≤ V) (n : ℕ) :
    let eU := nervePullbackCoefficientSubcomplexDegreeIso φ M U n
    let eV := nervePullbackCoefficientSubcomplexDegreeIso φ M V n
    eU.inv ≫ (nervePullbackCoefficientSubcomplexComplexMap φ M h).f n ≫ eV.hom =
      Sigma.subtypeMap (nervePullbackCoefficientFamily φ M n) (h (op ⦋n⦌)) := by
  dsimp only
  let f := SSet.Subcomplex.homOfLE h
  let ψ := V.ι ≫ φ
  let he := subcomplexNerveSquare φ h
  let eU := eqToIso (nervePullbackCoefficientComplex_X (U.ι ≫ φ) M n)
  let eV := eqToIso (nervePullbackCoefficientComplex_X ψ M n)
  let eF := eqToIso (nervePullbackCoefficientComplex_X (f ≫ ψ) M n)
  have hx : eU.inv ≫ (nervePullbackCoefficientSubcomplexComplexMap φ M h).f n ≫
      eV.hom = eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he) ≫
        nervePullbackCoefficientBaseMap f ψ M n := by
    unfold nervePullbackCoefficientSubcomplexComplexMap
    rw [HomologicalComplex.comp_f]
    calc
      _ = (eU.inv ≫ (eqToHom (congrArg
          (fun θ => nervePullbackCoefficientComplex θ M) he)).f n) ≫
        ((nervePullbackCoefficientBaseComplexMap f ψ M).f n ≫ eV.hom) := by
          simp only [Category.assoc, f, ψ]
      _ = (eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he) ≫
          eF.inv) ≫ ((nervePullbackCoefficientBaseComplexMap f ψ M).f n ≫ eV.hom) := by
          rw [sourceComplex_eqToHom_degree M he n]
      _ = eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he) ≫
          (eF.inv ≫ (nervePullbackCoefficientBaseComplexMap f ψ M).f n ≫ eV.hom) := by
          simp only [Category.assoc]
      _ = _ := by rw [baseComplexMap_degree M f ψ n]
  calc
    _ = (subcomplexFamilyIso φ M U n).inv ≫
        (eU.inv ≫ (nervePullbackCoefficientSubcomplexComplexMap φ M h).f n ≫ eV.hom) ≫
          (subcomplexFamilyIso φ M V n).hom := by
      simp only [nervePullbackCoefficientSubcomplexDegreeIso,
        Iso.trans_inv, Iso.trans_hom, Category.assoc, eU, eV, ψ]
    _ = (subcomplexFamilyIso φ M U n).inv ≫
        (eqToHom (congrArg (fun θ => nervePullbackCoefficientObj θ M n) he) ≫
          nervePullbackCoefficientBaseMap f ψ M n) ≫
            (subcomplexFamilyIso φ M V n).hom := by rw [hx]
    _ = _ := by
      simpa only [Category.assoc] using subcomplexFamilyIso_base φ M U V h n

/-- The WHOLE chain map is the original base-reindexing map and actual
source equality, not just an isomorphism of its carriers. -/
theorem nervePullbackCoefficientSubcomplexComplexMap_base
    {U V : T.Subcomplex} (h : U ≤ V) :
    let f := SSet.Subcomplex.homOfLE h
    let he : U.ι ≫ φ = f ≫ (V.ι ≫ φ) := by
      rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    nervePullbackCoefficientSubcomplexComplexMap φ M h =
      eqToHom (congrArg (fun ψ => nervePullbackCoefficientComplex ψ M) he) ≫
        nervePullbackCoefficientBaseComplexMap f (V.ι ≫ φ) M := by
  rfl

end

private def subcomplexDegreeIso (U : T.Subcomplex) (n : ℕ) :
    (nervePullbackCoefficientComplex (U.ι ≫ φ) M).X n ≅
      ∐ fun σ : ↥(U.obj (op ⦋n⦌)) => nervePullbackCoefficientFamily φ M n σ.1 :=
  nervePullbackCoefficientSubcomplexDegreeIso φ M U n

private theorem subcomplexMap_degreeSquare
    {U V : T.Subcomplex} (h : U ≤ V) (n : ℕ) :
    (subcomplexDegreeIso φ M U n).hom ≫
        Sigma.subtypeMap (nervePullbackCoefficientFamily φ M n) (h (op ⦋n⦌)) =
      (nervePullbackCoefficientSubcomplexComplexMap φ M h).f n ≫
        (subcomplexDegreeIso φ M V n).hom := by
  change (nervePullbackCoefficientSubcomplexDegreeIso φ M U n).hom ≫
      Sigma.subtypeMap (nervePullbackCoefficientFamily φ M n) (h (op ⦋n⦌)) =
    (nervePullbackCoefficientSubcomplexComplexMap φ M h).f n ≫
      (nervePullbackCoefficientSubcomplexDegreeIso φ M V n).hom
  rw [← nervePullbackCoefficientSubcomplexComplexMap_f φ M h n]
  simp only [Iso.hom_inv_id_assoc]

public section

/-- Monicity of the original coefficient subcomplex map is DERIVED from
its actual degree charts and the weighted subset inclusions. -/
theorem nervePullbackCoefficientSubcomplexComplexMap_mono
    {U V : T.Subcomplex} (h : U ≤ V) :
    Mono (nervePullbackCoefficientSubcomplexComplexMap φ M h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let eU := subcomplexDegreeIso φ M U n
  let eV := subcomplexDegreeIso φ M V n
  let f := (nervePullbackCoefficientSubcomplexComplexMap φ M h).f n
  let g := Sigma.subtypeMap (nervePullbackCoefficientFamily φ M n) (h (op ⦋n⦌))
  let e : Arrow.mk f ≅ Arrow.mk g :=
    Arrow.isoMk eU eV (subcomplexMap_degreeSquare φ M h n)
  exact ((MorphismProperty.monomorphisms A).arrow_mk_iso_iff e).mpr
    (Sigma.mono_subtypeMap (nervePullbackCoefficientFamily φ M n) (h (op ⦋n⦌)))

end

private theorem subcomplexMap_degree_isPushout (U V : T.Subcomplex) (n : ℕ) :
    IsPushout
      ((nervePullbackCoefficientSubcomplexComplexMap φ M
        (inf_le_left : U ⊓ V ≤ U)).f n)
      ((nervePullbackCoefficientSubcomplexComplexMap φ M
        (inf_le_right : U ⊓ V ≤ V)).f n)
      ((nervePullbackCoefficientSubcomplexComplexMap φ M
        (le_sup_left : U ≤ U ⊔ V)).f n)
      ((nervePullbackCoefficientSubcomplexComplexMap φ M
        (le_sup_right : V ≤ U ⊔ V)).f n) := by
  let sq := Sigma.isPushout_subtypeUnion (nervePullbackCoefficientFamily φ M n)
    (U.obj (op ⦋n⦌)) (V.obj (op ⦋n⦌))
  exact sq.of_iso'
    (subcomplexDegreeIso φ M (U ⊓ V) n)
    (subcomplexDegreeIso φ M U n)
    (subcomplexDegreeIso φ M V n)
    (subcomplexDegreeIso φ M (U ⊔ V) n)
    (subcomplexMap_degreeSquare φ M inf_le_left n)
    (subcomplexMap_degreeSquare φ M inf_le_right n)
    (subcomplexMap_degreeSquare φ M le_sup_left n)
    (subcomplexMap_degreeSquare φ M le_sup_right n)

public section

/-- The coefficient complexes of the actual intersection and union form
a pushout. The coefficient functor and its object/Hom universes are arbitrary. -/
theorem nervePullbackCoefficientSubcomplex_isPushout (U V : T.Subcomplex) :
    IsPushout
      (nervePullbackCoefficientSubcomplexComplexMap φ M (inf_le_left : U ⊓ V ≤ U))
      (nervePullbackCoefficientSubcomplexComplexMap φ M (inf_le_right : U ⊓ V ≤ V))
      (nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_left : U ≤ U ⊔ V))
      (nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_right : V ≤ U ⊔ V)) := by
  let sq : CommSq
      (nervePullbackCoefficientSubcomplexComplexMap φ M (inf_le_left : U ⊓ V ≤ U))
      (nervePullbackCoefficientSubcomplexComplexMap φ M (inf_le_right : U ⊓ V ≤ V))
      (nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_left : U ≤ U ⊔ V))
      (nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_right : V ≤ U ⊔ V)) :=
    ⟨by
      ext n : 1
      exact (subcomplexMap_degree_isPushout φ M U V n).w⟩
  refine IsPushout.of_isColimit' sq ?_
  exact HomologicalComplex.isColimitOfEval _ _ (fun n =>
    (PushoutCocone.isColimitMapCoconeEquiv sq.cocone
      (HomologicalComplex.eval A (ComplexShape.down ℕ) n)).symm
        (subcomplexMap_degree_isPushout φ M U V n).isColimit)

section Relative

variable [HasCokernels (ChainComplex A ℕ)]

/-- The original relative quotient map is an Iso by the actual chain
pushout and the stock cokernel universal property. -/
def nervePullbackCoefficientSubcomplexRelativeIso (U V : T.Subcomplex) :
    cokernel (nervePullbackCoefficientSubcomplexComplexMap φ M
      (inf_le_left : U ⊓ V ≤ U)) ≅
    cokernel (nervePullbackCoefficientSubcomplexComplexMap φ M
      (le_sup_right : V ≤ U ⊔ V)) := by
  let sq := nervePullbackCoefficientSubcomplex_isPushout φ M U V
  let m := cokernel.map _ _ _ _ sq.w
  have hm : IsIso m := isIso_cokernel_map_of_isPushout sq
  exact @asIso _ _ _ _ m hm

/-- The computed relative Iso retains the WHOLE original inclusion and
quotient projection square. -/
@[reassoc]
theorem nervePullbackCoefficientSubcomplexRelativeIso_π (U V : T.Subcomplex) :
    cokernel.π (nervePullbackCoefficientSubcomplexComplexMap φ M
        (inf_le_left : U ⊓ V ≤ U)) ≫
      (nervePullbackCoefficientSubcomplexRelativeIso φ M U V).hom =
    nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_left : U ≤ U ⊔ V) ≫
      cokernel.π (nervePullbackCoefficientSubcomplexComplexMap φ M
        (le_sup_right : V ≤ U ⊔ V)) := by
  let f := nervePullbackCoefficientSubcomplexComplexMap φ M (inf_le_left : U ⊓ V ≤ U)
  let g := nervePullbackCoefficientSubcomplexComplexMap φ M (inf_le_right : U ⊓ V ≤ V)
  let a := nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_left : U ≤ U ⊔ V)
  let b := nervePullbackCoefficientSubcomplexComplexMap φ M (le_sup_right : V ≤ U ⊔ V)
  let sq := nervePullbackCoefficientSubcomplex_isPushout φ M U V
  change cokernel.π f ≫ (nervePullbackCoefficientSubcomplexRelativeIso φ M U V).hom =
    a ≫ cokernel.π b
  have hm : (nervePullbackCoefficientSubcomplexRelativeIso φ M U V).hom =
      cokernel.map f b g a sq.w := by
    rfl
  rw [hm]
  exact cokernel.π_desc f (a ≫ cokernel.π b) _

end Relative

end

end CategoryTheory.CategoryHomology

end
