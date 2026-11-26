/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DerivedDeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.RightDerived.CompositionNaturality
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Right derivation of additive-functor diagrams

Let `C,E` be abelian, with injective resolutions in `C`, and let `J`
be a category. Right derivation in degree `n` sends a diagram of
additive functors `Φ : J → (C → E)` to the diagram of `R^nΦ_j`.
Deriving its flipped functor `C → (J → E)` gives a naturally isomorphic
flipped derived diagram. Evaluation at each `j` gives the component
comparison, which commutes with every index map and diagram map.
All object and morphism universes of `C,E,J` are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uE vE uJ vJ

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  [HasInjectiveResolutions C]

/-- Let `C,D,E` be abelian, with injective resolutions in `C`,
`F,G : C → D` additive, and `U : D → E` additive and preserving
homology. For `α : F → G`, the forward comparisons
`R^nF ⋙ U ≅ R^n(F ⋙ U)` commute with `R^nα ⋙ U` and `R^n(α ⋙ U)`. -/
theorem rightDerivedCompIsoOfPreservesHomology_hom_naturality_source
    (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
    (U : D ⥤ E) [U.Additive] [U.PreservesHomology] (n : ℕ) :
    whiskerRight (NatTrans.rightDerived α n) U ≫
        (G.rightDerivedCompIsoOfPreservesHomology U n).hom =
      (F.rightDerivedCompIsoOfPreservesHomology U n).hom ≫
        NatTrans.rightDerived (whiskerRight α U) n := by
  apply NatTrans.ext
  funext X
  let R := injectiveResolution X
  let K_F := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let K_G := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let H := HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n
  let H' := HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n
  let φ := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex
  let I_F := R.isoRightDerivedObj F n
  let I_G := R.isoRightDerivedObj G n
  let B_F := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).app K_F
  let B_G := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).app K_G
  let J_F := R.isoRightDerivedObj (F ⋙ U) n
  let J_G := R.isoRightDerivedObj (G ⋙ U) n
  let a := (NatTrans.rightDerived α n).app X
  let b := (NatTrans.rightDerived (whiskerRight α U) n).app X
  have hφ : (NatTrans.mapHomologicalComplex (whiskerRight α U) (ComplexShape.up ℕ)).app
      R.cocomplex = (U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hi : a ≫ I_G.hom = I_F.hom ≫ H.map φ :=
    R.isoRightDerivedObj_hom_naturality_functor α n
  have ha : U.map a ≫ U.map I_G.hom = U.map I_F.hom ≫ U.map (H.map φ) :=
    (U.map_comp a I_G.hom).symm.trans
      ((congrArg U.map hi).trans (U.map_comp I_F.hom (H.map φ)))
  have hb : U.map (H.map φ) ≫ B_G.inv =
      B_F.inv ≫ H'.map ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) :=
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n U).inv.naturality φ
  have hc : H'.map ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) ≫ J_G.inv =
      J_F.inv ≫ b := by
    have h := R.isoRightDerivedObj_inv_naturality_functor (whiskerRight α U) n
    rw [hφ] at h
    exact h
  have sa : CommSq (U.map I_F.hom) (U.map a) (U.map (H.map φ)) (U.map I_G.hom) :=
    ⟨ha.symm⟩
  have sb : CommSq B_F.inv (U.map (H.map φ))
      (H'.map ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) B_G.inv := ⟨hb.symm⟩
  have sc : CommSq J_F.inv
      (H'.map ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) b J_G.inv := ⟨hc.symm⟩
  simp only [NatTrans.comp_app]
  rw [rightDerivedCompIsoOfPreservesHomology_hom_app F U n X,
    rightDerivedCompIsoOfPreservesHomology_hom_app G U n X]
  change U.map a ≫ (U.map I_G.hom ≫ B_G.inv ≫ J_G.inv) =
    (U.map I_F.hom ≫ B_F.inv ≫ J_F.inv) ≫ b
  exact (sa.horiz_comp (sb.horiz_comp sc)).w.symm

end CategoryTheory.Functor

namespace CategoryTheory.RightDerivedDiagram

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {J : Type uJ} [Category.{vJ} J]
  [HasInjectiveResolutions C]

/-- For an abelian category `E` and a category `J`, the diagram
category `J → E` is preadditive, with sums of natural transformations
and bilinear composition defined at every `j`. -/
@[implicit_reducible]
local instance functorDiagramPreadditive : Preadditive (J ⥤ E) :=
  (inferInstance : Abelian (J ⥤ E)).toPreadditive

/-- Let `C,E` be abelian, with injective resolutions in `C`. Right derivation in a fixed degree `n` defines a functor
from additive functors `C → E` to ordinary functors `C → E`, with
maps given by right-derived natural transformations. -/
@[implicit_reducible]
def degreeFamily (n : ℕ) : (C ⥤+ E) ⥤ (C ⥤ E) :=
  rightDerivedDeltaFunctorFamily C E ⋙ CohomologicalDeltaFunctor.evaluation C E n

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. Its degree-`n` derived diagram sends `j` to `R^nΦ_j` and each
index arrow to the derived coefficient transformation. -/
@[implicit_reducible]
def diagram (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) : J ⥤ (C ⥤ E) :=
  Φ ⋙ degreeFamily n

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. At `j`, the object of its degree-`n` derived diagram is the
right-derived functor `R^nΦ_j`. -/
theorem diagram_obj (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) (j : J) :
    (diagram Φ n).obj j = (Φ.obj j).obj.rightDerived n := rfl

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. For `g : j → k`, the map of its degree-`n` derived diagram
is the natural transformation `R^n(Φ(g)) : R^nΦ_j → R^nΦ_k`. -/
theorem diagram_map (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) {j k : J} (f : j ⟶ k) :
    (diagram Φ n).map f = NatTrans.rightDerived (Φ.map f).hom n := rfl

/-- For abelian `C,E`, a category `J`, and a diagram `Φ` of additive
functors `C → E`, the flipped functor sends `X` to the diagram
`j ↦ Φ_j(X)` and sends each source map to its evaluated diagram map. -/
abbrev flipped (Φ : J ⥤ (C ⥤+ E)) : C ⥤ (J ⥤ E) :=
  (Φ ⋙ AdditiveFunctor.forget C E).flip

/-- For abelian `C,E`, a category `J`, and a diagram `Φ` of additive
functors `C → E`, the flipped functor `C → (J → E)` is additive:
it preserves sums of source maps at every index `j`. -/
instance flipped_additive (Φ : J ⥤ (C ⥤+ E)) : (flipped Φ).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext j
    change (Φ.obj j).obj.map (f + g) = (Φ.obj j).obj.map f + (Φ.obj j).obj.map g
    exact (Φ.obj j).obj.map_add (f := f) (g := g)

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. Evaluation at `j` gives the canonical natural isomorphism
`R^n(flip Φ) ⋙ ev_j ≅ R^nΦ_j`, from deriving the diagram-valued
functor to deriving its `j`-th component. -/
def evaluationIso (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) (j : J) :
    (flipped Φ).rightDerived n ⋙ (evaluation J E).obj j ≅ (diagram Φ n).obj j := by
  letI : ((evaluation J E).obj j).PreservesHomology := {}
  rw [diagram_obj Φ n j]
  simpa only [flipped, CategoryTheory.flip_comp_evaluation,
    Functor.comp_obj, AdditiveFunctor.forget_obj] using
      (flipped Φ).rightDerivedCompIsoOfPreservesHomology ((evaluation J E).obj j) n

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. For `g : j → k`, the evaluation comparisons commute with
`ev(g)` on the derived diagram-valued functor and the derived index
map `R^n(Φ(g))`. -/
theorem evaluationIso_hom_naturality_index (Φ : J ⥤ (C ⥤+ E)) (n : ℕ)
    {j k : J} (f : j ⟶ k) :
    Functor.whiskerLeft ((flipped Φ).rightDerived n) ((evaluation J E).map f) ≫
        (evaluationIso Φ n k).hom =
      (evaluationIso Φ n j).hom ≫ (diagram Φ n).map f := by
  let : ((evaluation J E).obj j).PreservesHomology := {}
  let : ((evaluation J E).obj k).PreservesHomology := {}
  have h := Functor.rightDerivedCompIsoOfPreservesHomology_hom_naturality_target
    (flipped Φ) ((evaluation J E).obj j) ((evaluation J E).obj k)
      ((evaluation J E).map f) n
  have hmap : Functor.whiskerLeft (flipped Φ) ((evaluation J E).map f) =
      (Φ.map f).hom := by
    apply NatTrans.ext
    funext X
    rfl
  rw [hmap] at h
  exact h

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. The comparisons at all indices give a natural isomorphism
`R^n(flip Φ) ≅ flip(R^nΦ)` of diagram-valued functors on `C`. -/
def flippedIso (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) :
    (flipped Φ).rightDerived n ≅ (diagram Φ n).flip :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun j => (evaluationIso Φ n j).app X)
      (fun {j k} f => congrArg (fun η => η.app X)
        (evaluationIso_hom_naturality_index Φ n f)))
    (fun {X Y} f => by
      apply NatTrans.ext
      funext j
      exact (evaluationIso Φ n j).hom.naturality f)

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. The forward component of the flipped comparison at `X,j`
is the forward evaluation comparison
`R^n(flip Φ)(X)_j → R^nΦ_j(X)`. -/
theorem flippedIso_hom_app_app (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) (X : C) (j : J) :
    ((flippedIso Φ n).hom.app X).app j = (evaluationIso Φ n j).hom.app X := rfl

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`J` a category. Let `Φ : J → (C → E)` be a diagram of additive functors. The inverse component of the flipped comparison at `X,j`
is the inverse evaluation comparison
`R^nΦ_j(X) → R^n(flip Φ)(X)_j`. -/
theorem flippedIso_inv_app_app (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) (X : C) (j : J) :
    ((flippedIso Φ n).inv.app X).app j = (evaluationIso Φ n j).inv.app X := rfl

local instance (Φ : J ⥤ (C ⥤+ E)) :
    ((CategoryTheory.flipFunctor J C E).obj (Φ ⋙ AdditiveFunctor.forget C E)).Additive := by
  change (flipped Φ).Additive
  exact flipped_additive Φ

/-- Let `C,E` be abelian, with injective resolutions in `C`, and
`Φ,Ψ : J → (C → E)` be diagrams of additive functors. A map
`α : Φ → Ψ` commutes with the forward comparisons
`R^n(flip Φ) ≅ flip(R^nΦ)` and `R^n(flip Ψ) ≅ flip(R^nΨ)`. -/
theorem flippedIso_naturality_diagramMap {Φ Ψ : J ⥤ (C ⥤+ E)} (α : Φ ⟶ Ψ) (n : ℕ) :
    NatTrans.rightDerived
        ((CategoryTheory.flipFunctor J C E).map
          (Functor.whiskerRight α (AdditiveFunctor.forget C E))) n ≫ (flippedIso Ψ n).hom =
      (flippedIso Φ n).hom ≫
        (CategoryTheory.flipFunctor J C E).map (Functor.whiskerRight α (degreeFamily n)) := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext j
  let : ((evaluation J E).obj j).PreservesHomology := {}
  let a : flipped Φ ⟶ flipped Ψ := (CategoryTheory.flipFunctor J C E).map
    (Functor.whiskerRight α (AdditiveFunctor.forget C E))
  have h := Functor.rightDerivedCompIsoOfPreservesHomology_hom_naturality_source
    (flipped Φ) (flipped Ψ) a ((evaluation J E).obj j) n
  have hmap : Functor.whiskerRight a ((evaluation J E).obj j) = (α.app j).hom := by
    apply NatTrans.ext
    funext Y
    rfl
  rw [hmap] at h
  have hX := congrArg (fun η => η.app X) h
  exact hX

end CategoryTheory.RightDerivedDiagram
