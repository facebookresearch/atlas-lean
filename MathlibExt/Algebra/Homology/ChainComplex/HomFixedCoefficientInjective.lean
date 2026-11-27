/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.HomFixedCoefficient
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Canonical Hom cohomology restriction for an injective coefficient

Let C be abelian, P an arbitrary integer chain complex and M an injective object. The canonical
cycle restriction is an isomorphism Hⁿ Hom(P,M) ≅ Hom_C(Hₙ(P),M), for every integer n, using the
positive precomposition differential of fixed-coefficient Hom.

These isomorphisms and their inverses commute with source precomposition and coefficient
postcomposition. A quasi-isomorphism of source complexes therefore induces a quasi-isomorphism
on Hom with injective coefficient M. No term or image projectivity, boundedness, resolution or
Ext group is needed.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex

namespace ChainComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma homFixedCoefficient_injective_preservesHomology (M : C) [Injective M] :
    (preadditiveYoneda.obj M).PreservesHomology := by
  let F : Cᵒᵖ ⥤ AddCommGrpCat.{v} := preadditiveYoneda.obj M
  letI : F.PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj M).1
      (inferInstance : Injective M)
  change F.PreservesHomology
  exact Functor.preservesHomology_of_preservesEpis_and_kernels F

/-- Let C be an abelian category. Let P be an arbitrary integer chain complex, M an injective object
and n ∈ ℤ. Canonical cycle restriction ρₙ : Hⁿ Hom(P,M) → Hom_C(Hₙ(P),M) is an isomorphism. The
Hom differential is positive precomposition; no projectivity or boundedness of P is assumed. -/
instance homFixedCoefficientRestrictionIsIso
    (P : ChainComplex C ℤ) (M : C) [Injective M] (n : ℤ) :
    IsIso (homFixedCoefficientRestriction P M n) := by
  let S : ShortComplex C := P.sc n
  let F : Cᵒᵖ ⥤ AddCommGrpCat.{v} := preadditiveYoneda.obj M
  letI : F.PreservesHomology := homFixedCoefficient_injective_preservesHomology M
  let K : CochainComplex AddCommGrpCat.{v} ℤ := homFixedCoefficient P M
  let T : ShortComplex AddCommGrpCat.{v} := S.op.map F
  let d : S.RightHomologyData := S.rightHomologyData
  let h : T.LeftHomologyData := d.op.map F
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of (S.homology ⟶ M)
  let B : AddCommGrpCat.{v} := AddCommGrpCat.of (d.Q ⟶ M)
  let D : AddCommGrpCat.{v} := AddCommGrpCat.of (d.H ⟶ M)
  let π : K.cycles n ⟶ K.homology n := K.homologyπ n
  let j : K.cycles n ⟶ K.X n := K.iCycles n
  let k : K.cycles n ⟶ B := h.cyclesIso.hom
  let p : B ⟶ K.X n := F.map d.p.op
  let q : B ⟶ D := F.map d.ι.op
  let a : D ⟶ A := F.map d.homologyIso.hom.op
  let e₀ : K.homology n ≅ D := h.homologyIso
  let e : K.homology n ≅ A := e₀ ≪≫ F.mapIso d.homologyIso.op
  let Γ : K.homology n ⟶ A := homFixedCoefficientRestriction P M n
  let r : K.cycles n ⟶ A := homFixedCoefficientCycleRestriction P M n
  have hi : k ≫ p = j := by
    change h.cyclesIso.hom ≫ h.i = T.iCycles
    exact h.cyclesIso_hom_comp_i
  have hπ₀ : π ≫ e₀.hom = k ≫ q := by
    change T.homologyπ ≫ h.homologyIso.hom = h.cyclesIso.hom ≫ h.π
    exact h.homologyπ_comp_homologyIso_hom
  have he : e.hom = e₀.hom ≫ a := rfl
  have hπ : π ≫ e.hom = (k ≫ q) ≫ a :=
    (congrArg (fun w : K.homology n ⟶ A => π ≫ w) he).trans
      ((Category.assoc π e₀.hom a).symm.trans
        (congrArg (fun w : K.cycles n ⟶ D => w ≫ a) hπ₀))
  have hΓ : π ≫ Γ = r := homologyπ_homFixedCoefficientRestriction P M n
  have hR₀ : S.homologyπ ≫ (d.homologyIso.hom ≫ d.ι) =
      S.homologyπ ≫ (S.homologyι ≫ d.opcyclesIso.hom) :=
    congrArg (fun w : S.homology ⟶ d.Q => S.homologyπ ≫ w)
      d.homologyIso_hom_comp_ι
  have hR₁ : S.homologyπ ≫ (S.homologyι ≫ d.opcyclesIso.hom) =
      (S.homologyπ ≫ S.homologyι) ≫ d.opcyclesIso.hom :=
    (Category.assoc S.homologyπ S.homologyι d.opcyclesIso.hom).symm
  have hR₂ : (S.homologyπ ≫ S.homologyι) ≫ d.opcyclesIso.hom =
      (S.iCycles ≫ S.pOpcycles) ≫ d.opcyclesIso.hom :=
    congrArg (fun w : S.cycles ⟶ S.opcycles => w ≫ d.opcyclesIso.hom)
      S.homology_π_ι
  have hR₃ : (S.iCycles ≫ S.pOpcycles) ≫ d.opcyclesIso.hom =
      S.iCycles ≫ (S.pOpcycles ≫ d.opcyclesIso.hom) :=
    Category.assoc S.iCycles S.pOpcycles d.opcyclesIso.hom
  have hR₄ : S.iCycles ≫ (S.pOpcycles ≫ d.opcyclesIso.hom) = S.iCycles ≫ d.p :=
    congrArg (fun w : S.X₂ ⟶ d.Q => S.iCycles ≫ w) d.pOpcycles_comp_opcyclesIso_hom
  have hR : S.homologyπ ≫ (d.homologyIso.hom ≫ d.ι) = S.iCycles ≫ d.p :=
    hR₀.trans (hR₁.trans (hR₂.trans (hR₃.trans hR₄)))
  have heΓ : e.hom = Γ := by
    apply (cancel_epi π).1
    apply AddCommGrpCat.ext
    intro z
    let c : d.Q ⟶ M := k.hom z
    have hp : p.hom c = d.p ≫ c := rfl
    have hc : d.p ≫ c = j.hom z :=
      ((AddCommGrpCat.comp_apply k p z).trans hp).symm.trans
        (ConcreteCategory.congr_hom hi z)
    have hq : a.hom (q.hom (k.hom z)) = d.homologyIso.hom ≫ (d.ι ≫ c) := rfl
    have hValue : e.hom.hom (π.hom z) = d.homologyIso.hom ≫ (d.ι ≫ c) :=
      (AddCommGrpCat.comp_apply π e.hom z).symm.trans
        ((ConcreteCategory.congr_hom hπ z).trans
          ((AddCommGrpCat.comp_apply (k ≫ q) a z).trans
            ((congrArg a.hom (AddCommGrpCat.comp_apply k q z)).trans hq)))
    have hEπ : S.homologyπ ≫ e.hom.hom (π.hom z) = S.iCycles ≫ j.hom z :=
      (congrArg (fun w : S.homology ⟶ M => S.homologyπ ≫ w) hValue).trans
        ((congrArg (fun w : S.homology ⟶ M => S.homologyπ ≫ w)
          (Category.assoc d.homologyIso.hom d.ι c).symm).trans
          ((Category.assoc S.homologyπ (d.homologyIso.hom ≫ d.ι) c).symm.trans
            ((congrArg (fun w : S.cycles ⟶ d.Q => w ≫ c) hR).trans
              ((Category.assoc S.iCycles d.p c).trans
                (congrArg (fun w : S.X₂ ⟶ M => S.iCycles ≫ w) hc)))))
    have hΓValue : Γ.hom (π.hom z) = r.hom z :=
      (AddCommGrpCat.comp_apply π Γ z).symm.trans
        (ConcreteCategory.congr_hom hΓ z)
    have hΓπ : S.homologyπ ≫ Γ.hom (π.hom z) = S.iCycles ≫ j.hom z :=
      (congrArg (fun w : S.homology ⟶ M => S.homologyπ ≫ w) hΓValue).trans
        (homFixedCoefficientCycleRestriction_π P M n z)
    have hz : e.hom.hom (π.hom z) = Γ.hom (π.hom z) := by
      apply (cancel_epi S.homologyπ).1
      exact hEπ.trans hΓπ.symm
    change (π ≫ e.hom).hom z = (π ≫ Γ).hom z
    exact (AddCommGrpCat.comp_apply π e.hom z).trans
      (hz.trans (AddCommGrpCat.comp_apply π Γ z).symm)
  change IsIso Γ
  rw [← heΓ]
  infer_instance

/-- Let C be an abelian category. For integer chain complexes P,P′, injective objects M,M′, f : P′ →
P and b : M → M′, the inverse restrictions commute with Hⁿ Hom(f,b) and the homology-Hom action
t ↦ b ∘ t ∘ Hₙ(f), for every integer n. -/
lemma homFixedCoefficientRestriction_inv_naturality
    {P P' : ChainComplex C ℤ} {M M' : C} [Injective M] [Injective M']
    (f : P' ⟶ P) (b : M ⟶ M') (n : ℤ) :
    (asIso (homFixedCoefficientRestriction P M n)).inv ≫
        homologyMap (homFixedCoefficientMap f b) n =
      ((preadditiveYoneda.obj M).map (homologyMap f n).op ≫
        (preadditiveYoneda.map b).app (op (P'.homology n))) ≫
          (asIso (homFixedCoefficientRestriction P' M' n)).inv := by
  let K := homFixedCoefficient P M
  let K' := homFixedCoefficient P' M'
  let e := asIso (homFixedCoefficientRestriction P M n)
  let e' := asIso (homFixedCoefficientRestriction P' M' n)
  let m : K.homology n ⟶ K'.homology n := homologyMap (homFixedCoefficientMap f b) n
  let t : AddCommGrpCat.of (P.homology n ⟶ M) ⟶
      AddCommGrpCat.of (P'.homology n ⟶ M') :=
    (preadditiveYoneda.obj M).map (homologyMap f n).op ≫
      (preadditiveYoneda.map b).app (op (P'.homology n))
  have h : m ≫ e'.hom = e.hom ≫ t := homFixedCoefficientRestriction_naturality f b n
  have h' := congrArg
    (fun w : K.homology n ⟶ AddCommGrpCat.of (P'.homology n ⟶ M') =>
      e.inv ≫ w ≫ e'.inv) h
  change e.inv ≫ m = t ≫ e'.inv
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using h'

/-- Let C be an abelian category. Let f : P′ → P be a quasi-isomorphism of arbitrary integer chain
complexes and M an injective object. The contravariant cochain map Hom(f,id_M) : Hom(P,M) →
Hom(P′,M) is a quasi-isomorphism. -/
lemma homFixedCoefficientMap_quasiIso
    {P P' : ChainComplex C ℤ} (f : P' ⟶ P) [QuasiIso f]
    (M : C) [Injective M] :
    QuasiIso (homFixedCoefficientMap f (𝟙 M)) := by
  let F : Cᵒᵖ ⥤ AddCommGrpCat.{v} := preadditiveYoneda.obj M
  letI : F.PreservesHomology := homFixedCoefficient_injective_preservesHomology M
  let o : P.op ⟶ P'.op := (HomologicalComplex.opFunctor C (ComplexShape.down ℤ)).map f.op
  letI : QuasiIso o := by
    dsimp only [o]
    infer_instance
  let ψ : homFixedCoefficient P M ⟶ homFixedCoefficient P' M :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map o
  letI : QuasiIso ψ := by
    dsimp only [ψ]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology o F
  have hMap : homFixedCoefficientMap f (𝟙 M) = ψ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply AddCommGrpCat.ext
    intro z
    let z₀ : P.X n ⟶ M := z
    have h₀ : ((homFixedCoefficientMap f (𝟙 M)).f n).hom z₀ = f.f n ≫ z₀ :=
      (homFixedCoefficientMap_f_apply f (𝟙 M) n z₀).trans
        (congrArg (fun w : P.X n ⟶ M => f.f n ≫ w) (Category.comp_id z₀))
    have h₁ : (ψ.f n).hom z₀ = f.f n ≫ z₀ := rfl
    change ((homFixedCoefficientMap f (𝟙 M)).f n).hom z₀ = (ψ.f n).hom z₀
    exact h₀.trans h₁.symm
  rw [hMap]
  infer_instance

end ChainComplex
