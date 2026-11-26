/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerivedBifunctor
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison

/-!
# Naturality of degree-zero left derivation

For additive functors between abelian categories, augmentation of a
projective resolution induces the degree-zero derived comparison.
This comparison is natural in transformations of the functor; for
right-exact functors it is an isomorphism. A right-exact partial
bifunctor is likewise recovered in derived degree zero in both variables.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory

section Resolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- For abelian `C`, `D`, a projective resolution `P` of `X`,
and additive `F,G : C → D` with `α : F → G`, the induced
map on degree-zero opcycles of `F(P) → G(P)` commutes with
the two augmentation maps to `F(X)`, `G(X)` and `α_X`. -/
@[reassoc]
theorem ProjectiveResolution.fromLeftDerivedZero'_naturality_functor
    {X : C} (P : ProjectiveResolution X) (α : F ⟶ G) :
    HomologicalComplex.opcyclesMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
      P.fromLeftDerivedZero' G = P.fromLeftDerivedZero' F ≫ α.app X := by
  rw [← cancel_epi (HomologicalComplex.pOpcycles
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) 0)]
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  change α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
    F.map (P.π.f 0) ≫ α.app X
  exact (α.naturality (P.π.f 0)).symm

end Resolution

section Functors

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
and let `F,G : C → D` be additive. For `α : F → G`, the
native degree-zero augmentation transformations satisfy
`L₀(α) ≫ G.fromLeftDerivedZero = F.fromLeftDerivedZero ≫ α`. -/
@[reassoc]
theorem NatTrans.fromLeftDerivedZero_naturality_functor (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.fromLeftDerivedZero =
      F.fromLeftDerivedZero ≫ α := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  simp only [NatTrans.comp_app]
  have hι :
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyι 0 ≫
        P.fromLeftDerivedZero' G =
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyι 0 ≫
        P.fromLeftDerivedZero' F ≫ α.app X := by
    rw [HomologicalComplex.homologyι_naturality_assoc,
      P.fromLeftDerivedZero'_naturality_functor α]
  have hnat :
      ((NatTrans.leftDerived α 0).app X ≫ (P.isoLeftDerivedObj G 0).hom) ≫
        (ChainComplex.isoHomologyι₀
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom ≫
        P.fromLeftDerivedZero' G =
      (P.isoLeftDerivedObj F 0).hom ≫
        ((ChainComplex.isoHomologyι₀
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom ≫
          P.fromLeftDerivedZero' F) ≫ α.app X := by
    have hc := congrArg
      (fun f => f ≫
        (ChainComplex.isoHomologyι₀
          ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom ≫
          P.fromLeftDerivedZero' G)
      (P.isoLeftDerivedObj_hom_naturality_functor α 0)
    refine hc.trans ?_
    convert congrArg (fun f => (P.isoLeftDerivedObj F 0).hom ≫ f) hι using 1 <;>
      simp only [ChainComplex.isoHomologyι₀, HomologicalComplex.isoHomologyι_hom]
    · exact Category.assoc (obj := D) _ _ _
    · exact congrArg (fun f => (P.isoLeftDerivedObj F 0).hom ≫ f)
        (Category.assoc (obj := D)
          (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyι 0)
          (P.fromLeftDerivedZero' F) (α.app X))
  rw [P.fromLeftDerivedZero_eq F, P.fromLeftDerivedZero_eq G]
  convert hnat using 1 <;> simp only [Category.assoc]

variable [PreservesFiniteColimits F] [PreservesFiniteColimits G]

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
and let `F,G : C → D` be additive. If both functors preserve
finite colimits, their degree-zero isomorphisms to `F` and `G`
satisfy `L₀(α) ≫ e_G = e_F ≫ α` for every `α : F → G`. -/
@[reassoc]
theorem NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.leftDerivedZeroIsoSelf.hom =
      F.leftDerivedZeroIsoSelf.hom ≫ α :=
  NatTrans.fromLeftDerivedZero_naturality_functor α

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
and let `F,G : C → D` be additive. If both functors preserve
finite colimits, the inverse degree-zero comparisons satisfy
`α ≫ e_G⁻¹ = e_F⁻¹ ≫ L₀(α)`. -/
@[reassoc]
theorem NatTrans.leftDerivedZeroIsoSelf_inv_naturality_functor (α : F ⟶ G) :
    α ≫ G.leftDerivedZeroIsoSelf.inv =
      F.leftDerivedZeroIsoSelf.inv ≫ NatTrans.leftDerived α 0 := by
  calc
    α ≫ G.leftDerivedZeroIsoSelf.inv =
        F.leftDerivedZeroIsoSelf.inv ≫
          (F.leftDerivedZeroIsoSelf.hom ≫ α) ≫ G.leftDerivedZeroIsoSelf.inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = F.leftDerivedZeroIsoSelf.inv ≫
          (NatTrans.leftDerived α 0 ≫ G.leftDerivedZeroIsoSelf.hom) ≫
          G.leftDerivedZeroIsoSelf.inv := by
      rw [NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor α]
    _ = F.leftDerivedZeroIsoSelf.inv ≫ NatTrans.leftDerived α 0 := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Functors

section Bifunctor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  [HasProjectiveResolutions C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [∀ Y : C₂, (F.flip.obj Y).Additive]
  [∀ Y : C₂, PreservesFiniteColimits (F.flip.obj Y)]

/- Proof implementation note.
A right-exact bifunctor is recovered in derived degree zero, naturally
in both original variables. The parameter category need not be additive.
-/

/-- Let `C₁`, `D` be abelian, with projective resolutions in `C₁`,
and `C₂` a category. If each partial functor `F(-,Y) : C₁ → D`
is additive and preserves finite colimits, derivation in the
first variable gives a natural bifunctor isomorphism `L₀F ≅ F`. -/
def Functor.leftDerivedBifunctorZeroIsoSelf : F.leftDerivedBifunctor 0 ≅ F :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun Y => (F.flip.obj Y).leftDerivedZeroIsoSelf.app X)
      (by
        intro Y Y' g
        exact congrArg (fun α => α.app X)
          (NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor (F.flip.map g))))
    (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      exact (F.flip.obj Y).leftDerivedZeroIsoSelf.hom.naturality f)

/-- For the bifunctor `F : C₁ → C₂ → D` with additive right-exact
partials `F(-,Y)`, `C₁`, `D` abelian and `C₁` admitting
projective resolutions, the degree-zero comparison at `(X,Y)`
is the forward comparison `L₀(F(-,Y))(X) → F(X,Y)`. -/
@[simp]
theorem Functor.leftDerivedBifunctorZeroIsoSelf_hom_app (X : C₁) (Y : C₂) :
    ((F.leftDerivedBifunctorZeroIsoSelf).hom.app X).app Y =
      ((F.flip.obj Y).leftDerivedZeroIsoSelf.app X).hom := rfl

/-- For the bifunctor `F : C₁ → C₂ → D` with additive right-exact
partials `F(-,Y)`, `C₁`, `D` abelian and `C₁` admitting
projective resolutions, the inverse degree-zero comparison at
`(X,Y)` is `F(X,Y) → L₀(F(-,Y))(X)`. -/
@[simp]
theorem Functor.leftDerivedBifunctorZeroIsoSelf_inv_app (X : C₁) (Y : C₂) :
    ((F.leftDerivedBifunctorZeroIsoSelf).inv.app X).app Y =
      ((F.flip.obj Y).leftDerivedZeroIsoSelf.app X).inv := rfl

end Bifunctor

end CategoryTheory

end
