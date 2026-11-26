/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.FunctorDiagram
public import MathlibExt.CategoryTheory.Abelian.RightDerived.NatIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Right derivation commutes with exact diagram colimits

Let `C,E` be abelian, with injective resolutions in `C`, and let `J` be
a category. Suppose `E` has colimits of shape `J` and its colimit functor
preserves finite limits. For a diagram `Φ : J → (C → E)` of additive
functors, there is a natural comparison
`R^n(colim_j Φ_j) ≅ colim_j R^nΦ_j`.
It sends each derived diagram injection to the corresponding injection
and commutes with maps of additive-functor diagrams.

The diagram shape and all category object and morphism universes are
independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uE vE uJ vJ

namespace CategoryTheory.RightDerivedColimit

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {J : Type uJ} [Category.{vJ} J]
  [HasInjectiveResolutions C]
  [HasColimitsOfShape J E] [HasExactColimitsOfShape J E]

/-- For an abelian category `E` and a category `J`, the category of
`J`-diagrams in `E` is preadditive: morphisms add at each diagram object,
and composition is bilinear. -/
@[implicit_reducible]
local instance functorColimitPreadditive : Preadditive (J ⥤ E) :=
  (inferInstance : Abelian (J ⥤ E)).toPreadditive

omit [HasExactColimitsOfShape J E] in
/-- The colimit left adjoint is additive without an exact-colimit premise. -/
private theorem colim_additive : (colim : (J ⥤ E) ⥤ E).Additive :=
  rightExactFunctor_le_additiveFunctor (J ⥤ E) E
    (colim : (J ⥤ E) ⥤ E) (by
      change PreservesFiniteColimits (colim : (J ⥤ E) ⥤ E)
      infer_instance)

local instance : (colim : (J ⥤ E) ⥤ E).Additive := colim_additive

/-- Finite-limit and finite-colimit capabilities earn the homology preservation. -/
private theorem colim_preservesHomology : (colim : (J ⥤ E) ⥤ E).PreservesHomology := {}

local instance : (colim : (J ⥤ E) ⥤ E).PreservesHomology := colim_preservesHomology

/-- For abelian `C,E` and a category `J`, a diagram of additive functors
`Φ : J → (C → E)` has an underlying diagram of ordinary functors,
with the same objects and natural transformations. -/
abbrev underlying (Φ : J ⥤ (C ⥤+ E)) : J ⥤ (C ⥤ E) := Φ ⋙ AdditiveFunctor.forget C E

omit [HasExactColimitsOfShape J E] in
/-- For abelian `C,E` and a category `J`, suppose `E` has `J`-colimits.
The pointwise colimit of a diagram of additive functors `C → E` is
again additive. -/
instance underlying_colimit_additive (Φ : J ⥤ (C ⥤+ E)) : (colimit (underlying Φ)).Additive := by
  let e : colimit (underlying Φ) ≅
      RightDerivedDiagram.flipped Φ ⋙ (colim : (J ⥤ E) ⥤ E) :=
    colimitIsoFlipCompColim (underlying Φ)
  exact Functor.additive_of_iso e.symm

/-- For abelian `E` with colimits of shape `J` and `j : J`, the diagram
injections give a natural transformation from evaluation at `j` to the
colimit functor `J → E → E`. At a diagram `K`, its map is
`K_j → colim K`. -/
def targetCoprojection (j : J) : (evaluation J E).obj j ⟶ (colim : (J ⥤ E) ⥤ E) :=
  Functor.whiskerRight (colimConstAdj (J := J) (C := E)).unit ((evaluation J E).obj j)

omit [Abelian E] [HasExactColimitsOfShape J E] in
theorem targetCoprojection_app (j : J) (D : J ⥤ E) :
    (targetCoprojection (E := E) j).app D = colimit.ι D j := rfl

omit [Abelian C] [Abelian E] [HasInjectiveResolutions C] [HasExactColimitsOfShape J E] in
/-- Let `C,E` be abelian, `E` have `J`-colimits, and `P : J → (C → E)`.
The injection `P_j → colim P`, followed by the pointwise-colimit
comparison, equals the natural family of injections
`P_j(X) → colim_k P_k(X)`. -/
theorem pointwiseColimit_ι (P : J ⥤ (C ⥤ E)) (j : J) :
    colimit.ι P j ≫ (colimitIsoFlipCompColim P).hom =
      Functor.whiskerLeft P.flip (targetCoprojection (E := E) j) := by
  apply NatTrans.ext
  funext X
  simp [colimitIsoFlipCompColim, targetCoprojection, colimConstAdj]

/-- Let `C,E` be abelian, with injective resolutions in `C`, and suppose
`E` has exact colimits of shape `J`. For a diagram `Φ` of additive
functors `C → E`, right derivation has the natural comparison
`R^n(colim_j Φ_j) ≅ colim_j R^nΦ_j`. -/
def comparison (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) :
    (colimit (underlying Φ)).rightDerived n ≅ colimit (RightDerivedDiagram.diagram Φ n) := by
  let σ : colimit (underlying Φ) ≅
      RightDerivedDiagram.flipped Φ ⋙ (colim : (J ⥤ E) ⥤ E) :=
    colimitIsoFlipCompColim (underlying Φ)
  exact NatIso.rightDerived σ n ≪≫
    ((RightDerivedDiagram.flipped Φ).rightDerivedCompIsoOfPreservesHomology
      (colim : (J ⥤ E) ⥤ E) n).symm ≪≫
    Functor.isoWhiskerRight (RightDerivedDiagram.flippedIso Φ n) (colim : (J ⥤ E) ⥤ E) ≪≫
    (colimitIsoFlipCompColim (RightDerivedDiagram.diagram Φ n)).symm

/-- Let `C,E` be abelian, with injective resolutions in `C`, and suppose
`E` has exact `J`-colimits. For an additive-functor diagram `Φ`, the
forward derived-colimit comparison first identifies its pointwise colimit,
then commutes right derivation with the exact colimit functor, identifies
the derived diagram objectwise, and returns to its pointwise colimit. -/
theorem comparison_hom (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) :
    let σ : colimit (underlying Φ) ≅
        RightDerivedDiagram.flipped Φ ⋙ (colim : (J ⥤ E) ⥤ E) :=
      colimitIsoFlipCompColim (underlying Φ)
    (comparison Φ n).hom =
      (NatIso.rightDerived σ n).hom ≫
        ((RightDerivedDiagram.flipped Φ).rightDerivedCompIsoOfPreservesHomology
          (colim : (J ⥤ E) ⥤ E) n).inv ≫
        (Functor.isoWhiskerRight (RightDerivedDiagram.flippedIso Φ n) (colim : (J ⥤ E) ⥤ E)).hom ≫
        (colimitIsoFlipCompColim (RightDerivedDiagram.diagram Φ n)).inv := rfl

local instance (Φ : J ⥤ (C ⥤+ E)) (j : J) : ((underlying Φ).obj j).Additive := by
  change (Φ.obj j).obj.Additive
  infer_instance

local instance (Φ : J ⥤ (C ⥤+ E)) :
    (colim.obj (Φ ⋙ AdditiveFunctor.forget C E)).Additive := by
  change (colimit (underlying Φ)).Additive
  infer_instance

/-- Let `C,E` be abelian, with injective resolutions in `C`, and suppose
`E` has exact `J`-colimits. For an additive-functor diagram `Φ` and
`j : J`, deriving the injection `Φ_j → colim Φ` and following the
forward comparison gives the injection `R^nΦ_j → colim_k R^nΦ_k`. -/
theorem rightDerived_ι_comparison_hom (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) (j : J) :
    NatTrans.rightDerived (colimit.ι (underlying Φ) j) n ≫ (comparison Φ n).hom =
      colimit.ι (RightDerivedDiagram.diagram Φ n) j := by
  let F := RightDerivedDiagram.flipped Φ
  let U : (J ⥤ E) ⥤ E := colim
  let Q := RightDerivedDiagram.diagram Φ n
  let σ : colimit (underlying Φ) ≅ F ⋙ U := colimitIsoFlipCompColim (underlying Φ)
  let σQ := colimitIsoFlipCompColim Q
  let a := NatIso.rightDerived σ n
  let c := F.rightDerivedCompIsoOfPreservesHomology U n
  let e := RightDerivedDiagram.flippedIso Φ n
  let w := Functor.isoWhiskerRight e U
  let κ := targetCoprojection (E := E) j
  let ν := Functor.whiskerLeft F κ
  let ι := colimit.ι (underlying Φ) j
  let ρ := colimit.ι Q j
  let v := RightDerivedDiagram.evaluationIso Φ n j
  let : ((evaluation J E).obj j).PreservesHomology := {}
  have hι : ι ≫ σ.hom = ν := pointwiseColimit_ι (underlying Φ) j
  have h1 : NatTrans.rightDerived ι n ≫ a.hom = NatTrans.rightDerived ν n :=
    (NatTrans.rightDerived_comp ι σ.hom n).symm.trans
      (congrArg (fun η => NatTrans.rightDerived η n) hι)
  have h2 : NatTrans.rightDerived ν n ≫ c.inv =
      v.inv ≫ Functor.whiskerLeft (F.rightDerived n) κ :=
    Functor.rightDerivedCompIsoOfPreservesHomology_inv_naturality_target
      F ((evaluation J E).obj j) U κ n
  have h3 : Functor.whiskerLeft (F.rightDerived n) κ ≫ w.hom =
      v.hom ≫ Functor.whiskerLeft Q.flip κ := by
    apply NatTrans.ext
    funext X
    have h := (κ.naturality (e.hom.app X)).symm
    change κ.app ((F.rightDerived n).obj X) ≫ U.map (e.hom.app X) =
      (e.hom.app X).app j ≫ κ.app (Q.flip.obj X) at h
    rw [RightDerivedDiagram.flippedIso_hom_app_app] at h
    exact h
  have hρ : ρ ≫ σQ.hom = Functor.whiskerLeft Q.flip κ := pointwiseColimit_ι Q j
  have h4 : Functor.whiskerLeft Q.flip κ ≫ σQ.inv = ρ := by
    calc
      _ = (ρ ≫ σQ.hom) ≫ σQ.inv := congrArg (fun η => η ≫ σQ.inv) hρ.symm
      _ = ρ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [comparison_hom]
  have hstep1 :
      NatTrans.rightDerived ι n ≫ a.hom ≫ c.inv ≫ w.hom ≫ σQ.inv =
        NatTrans.rightDerived ν n ≫ c.inv ≫ w.hom ≫ σQ.inv := by
    simpa only [Category.assoc] using
      congrArg (fun η => η ≫ c.inv ≫ w.hom ≫ σQ.inv) h1
  have hstep2 :
      NatTrans.rightDerived ν n ≫ c.inv ≫ w.hom ≫ σQ.inv =
        v.inv ≫ (Functor.whiskerLeft (F.rightDerived n) κ ≫ w.hom) ≫ σQ.inv := by
    exact (Category.assoc (NatTrans.rightDerived ν n) c.inv (w.hom ≫ σQ.inv)).symm.trans
      ((congrArg (fun η => η ≫ w.hom ≫ σQ.inv) h2).trans
        ((Category.assoc v.inv (Functor.whiskerLeft (F.rightDerived n) κ)
          (w.hom ≫ σQ.inv)).trans
          (congrArg (fun η => v.inv ≫ η)
            (Category.assoc (Functor.whiskerLeft (F.rightDerived n) κ)
              w.hom σQ.inv).symm)))
  have hstep3 :
      v.inv ≫ (Functor.whiskerLeft (F.rightDerived n) κ ≫ w.hom) ≫ σQ.inv =
        v.inv ≫ v.hom ≫ (Functor.whiskerLeft Q.flip κ ≫ σQ.inv) := by
    simpa only [Category.assoc] using
      congrArg (fun η => v.inv ≫ η ≫ σQ.inv) h3
  have hstep4 :
      v.inv ≫ v.hom ≫ (Functor.whiskerLeft Q.flip κ ≫ σQ.inv) = ρ := by
    rw [Iso.inv_hom_id_assoc]
    exact h4
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-- Let `C,E` be abelian, with injective resolutions in `C`, and suppose
`E` has exact `J`-colimits. For an additive-functor diagram `Φ`, the
injection `R^nΦ_j → colim_k R^nΦ_k` followed by the inverse comparison
is the derived map of `Φ_j → colim Φ`. -/
theorem ι_comparison_inv (Φ : J ⥤ (C ⥤+ E)) (n : ℕ) (j : J) :
    colimit.ι (RightDerivedDiagram.diagram Φ n) j ≫ (comparison Φ n).inv =
      NatTrans.rightDerived (colimit.ι (underlying Φ) j) n := by
  exact (Iso.comp_inv_eq (comparison Φ n)).2
    (rightDerived_ι_comparison_hom Φ n j).symm

/-- Let `C,E` be abelian, with injective resolutions in `C`, and suppose
`E` has exact `J`-colimits. A map `α : Φ → Ψ` of additive-functor
diagrams commutes with the inverse comparisons from the colimits of
the degree-`n` derived diagrams to the derived colimit functors. -/
theorem comparison_inv_naturality_diagramMap {Φ Ψ : J ⥤ (C ⥤+ E)} (α : Φ ⟶ Ψ) (n : ℕ) :
    colim.map (Functor.whiskerRight α (RightDerivedDiagram.degreeFamily n)) ≫
        (comparison Ψ n).inv =
      (comparison Φ n).inv ≫
        NatTrans.rightDerived (colim.map (Functor.whiskerRight α (AdditiveFunctor.forget C E))) n := by
  let f : colimit (underlying Φ) ⟶ colimit (underlying Ψ) :=
    colim.map (Functor.whiskerRight α (AdditiveFunctor.forget C E))
  let g : colimit (RightDerivedDiagram.diagram Φ n) ⟶
      colimit (RightDerivedDiagram.diagram Ψ n) :=
    colim.map (Functor.whiskerRight α (RightDerivedDiagram.degreeFamily n))
  apply colimit.hom_ext
  intro j
  let ιΦ := colimit.ι (underlying Φ) j
  let ιΨ := colimit.ι (underlying Ψ) j
  let ρΦ := colimit.ι (RightDerivedDiagram.diagram Φ n) j
  let ρΨ := colimit.ι (RightDerivedDiagram.diagram Ψ n) j
  have hBase : (α.app j).hom ≫ ιΨ = ιΦ ≫ f :=
    (ι_colimMap (Functor.whiskerRight α (AdditiveFunctor.forget C E)) j).symm
  have hT : ρΦ ≫ g = (RightDerivedDiagram.degreeFamily n).map (α.app j) ≫ ρΨ :=
    ι_colimMap (Functor.whiskerRight α (RightDerivedDiagram.degreeFamily n)) j
  have hDegree : (RightDerivedDiagram.degreeFamily n).map (α.app j) =
      NatTrans.rightDerived (α.app j).hom n := rfl
  have hΦ : ρΦ ≫ (comparison Φ n).inv = NatTrans.rightDerived ιΦ n :=
    ι_comparison_inv Φ n j
  have hΨ : ρΨ ≫ (comparison Ψ n).inv = NatTrans.rightDerived ιΨ n :=
    ι_comparison_inv Ψ n j
  have hNative :
      NatTrans.rightDerived (α.app j).hom n ≫ NatTrans.rightDerived ιΨ n =
        NatTrans.rightDerived ιΦ n ≫ NatTrans.rightDerived f n := by
    have hmap := congrArg (fun η => NatTrans.rightDerived η n) hBase
    exact (NatTrans.rightDerived_comp (α.app j).hom ιΨ n).symm.trans
      (hmap.trans (NatTrans.rightDerived_comp ιΦ f n))
  have hIndex :
      ρΦ ≫ g = NatTrans.rightDerived (α.app j).hom n ≫ ρΨ := by
    exact hT.trans (congrArg
      (fun (η : (RightDerivedDiagram.diagram Φ n).obj j ⟶
        (RightDerivedDiagram.diagram Ψ n).obj j) => η ≫ ρΨ) hDegree)
  have hstep1 :
      ρΦ ≫ (g ≫ (comparison Ψ n).inv) =
        NatTrans.rightDerived (α.app j).hom n ≫ (ρΨ ≫ (comparison Ψ n).inv) := by
    exact (Category.assoc ρΦ g (comparison Ψ n).inv).symm.trans
      ((congrArg (fun η => η ≫ (comparison Ψ n).inv) hIndex).trans
        (Category.assoc (NatTrans.rightDerived (α.app j).hom n)
          ρΨ (comparison Ψ n).inv))
  have hstep2 :
      NatTrans.rightDerived (α.app j).hom n ≫ (ρΨ ≫ (comparison Ψ n).inv) =
        NatTrans.rightDerived (α.app j).hom n ≫ NatTrans.rightDerived ιΨ n :=
    congrArg (fun η => NatTrans.rightDerived (α.app j).hom n ≫ η) hΨ
  have hstep3 :
      NatTrans.rightDerived ιΦ n ≫ NatTrans.rightDerived f n =
        ρΦ ≫ ((comparison Φ n).inv ≫ NatTrans.rightDerived f n) := by
    exact (congrArg (fun η => η ≫ NatTrans.rightDerived f n) hΦ.symm).trans
      (Category.assoc ρΦ (comparison Φ n).inv (NatTrans.rightDerived f n))
  exact hstep1.trans (hstep2.trans (hNative.trans hstep3))

/-- Let `C,E` be abelian, with injective resolutions in `C`, and suppose
`E` has exact `J`-colimits. A map `α : Φ → Ψ` of additive-functor
diagrams commutes with the forward comparisons from the derived colimit
functors to the colimits of their degree-`n` derived diagrams. -/
theorem comparison_hom_naturality_diagramMap {Φ Ψ : J ⥤ (C ⥤+ E)} (α : Φ ⟶ Ψ) (n : ℕ) :
    NatTrans.rightDerived (colim.map (Functor.whiskerRight α (AdditiveFunctor.forget C E))) n ≫
        (comparison Ψ n).hom =
      (comparison Φ n).hom ≫
        colim.map (Functor.whiskerRight α (RightDerivedDiagram.degreeFamily n)) := by
  let f := NatTrans.rightDerived (colim.map (Functor.whiskerRight α (AdditiveFunctor.forget C E))) n
  let g : colimit (RightDerivedDiagram.diagram Φ n) ⟶
      colimit (RightDerivedDiagram.diagram Ψ n) :=
    colim.map (Functor.whiskerRight α (RightDerivedDiagram.degreeFamily n))
  let eΦ := comparison Φ n
  let eΨ := comparison Ψ n
  have h : g ≫ eΨ.inv = eΦ.inv ≫ f := comparison_inv_naturality_diagramMap α n
  apply (cancel_epi eΦ.inv).1
  calc
    eΦ.inv ≫ (f ≫ eΨ.hom) = (eΦ.inv ≫ f) ≫ eΨ.hom := (Category.assoc _ _ _).symm
    _ = ((g ≫ eΨ.inv) ≫ eΨ.hom : colimit (RightDerivedDiagram.diagram Φ n) ⟶
        colimit (RightDerivedDiagram.diagram Ψ n)) := congrArg (fun η => η ≫ eΨ.hom) h.symm
    _ = g := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = eΦ.inv ≫ (eΦ.hom ≫ g) := by simp only [Iso.inv_hom_id_assoc]

end CategoryTheory.RightDerivedColimit
