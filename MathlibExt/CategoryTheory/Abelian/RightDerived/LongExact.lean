/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua, Avocado

Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse

-/
module

public import MathlibExt.CategoryTheory.Iso
public import MathlibExt.Algebra.Homology.ShortComplex.Exact
public import MathlibExt.CategoryTheory.Abelian.Injective.Horseshoe
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Additive
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeData
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Long exact sequences for right-derived functors

An additive functor between abelian categories sends a degreewise-split injective horseshoe
to a short exact sequence of cochain complexes. Its homology connecting morphism, transported
through injective-resolution comparisons, gives the right-derived long exact sequence.
Functor-parameter naturality also compares the connecting maps obtained by applying a short
complex of additive functors to a fixed injective resolution.
-/

@[expose] public section

namespace CategoryTheory
open Category Limits
open scoped ZeroObject

universe v₁ u₁ v₂ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace NatTrans

/-- A commuting square of natural transformations remains commuting on every complex. -/
lemma mapHomologicalComplex_app_comp_eq
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    {ι : Type*} (c : ComplexShape ι) {F G H L : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [L.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ L) (δ : L ⟶ H)
    (h : α ≫ β = γ ≫ δ) (K : HomologicalComplex A c) :
    (NatTrans.mapHomologicalComplex α c).app K ≫
        (NatTrans.mapHomologicalComplex β c).app K =
      (NatTrans.mapHomologicalComplex γ c).app K ≫
        (NatTrans.mapHomologicalComplex δ c).app K := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, h]

/-- A zero composite of natural transformations remains zero on every complex. -/
lemma mapHomologicalComplex_app_comp_eq_zero
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    {ι : Type*} (c : ComplexShape ι) {F G H : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) (h : α ≫ β = 0) (K : HomologicalComplex A c) :
    (NatTrans.mapHomologicalComplex α c).app K ≫
        (NatTrans.mapHomologicalComplex β c).app K = 0 := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, h]
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

end NatTrans

namespace InjectiveResolution

set_option backward.isDefEq.respectTransparency false in
/-- A naturality square between mapped homology objects transports to right-derived objects. -/
lemma conjugateHomology_naturality
    {F₁ F₂ G₁ G₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    {X : C} (R : InjectiveResolution X) (α : F₂ ⟶ F₁) (β : G₂ ⟶ G₁) (n m : ℕ)
    (d₁ : ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology n ⟶
      ((G₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology m)
    (d₂ : ((F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology n ⟶
      ((G₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology m)
    (h : d₂ ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app R.cocomplex) m =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex) n ≫ d₁) :
    ((R.isoRightDerivedObj F₂ n).hom ≫ d₂ ≫ (R.isoRightDerivedObj G₂ m).inv) ≫
        (NatTrans.rightDerived β m).app X =
      (NatTrans.rightDerived α n).app X ≫
        ((R.isoRightDerivedObj F₁ n).hom ≫ d₁ ≫ (R.isoRightDerivedObj G₁ m).inv) := by
  exact Iso.conjugate_naturality
    (R.isoRightDerivedObj F₁ n) (R.isoRightDerivedObj F₂ n)
    (R.isoRightDerivedObj G₁ m) (R.isoRightDerivedObj G₂ m) d₁ d₂
    ((NatTrans.rightDerived α n).app X) ((NatTrans.rightDerived β m).app X)
    (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex) n)
    (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app R.cocomplex) m)
    (R.isoRightDerivedObj_hom_naturality_functor α n)
    (R.isoRightDerivedObj_inv_naturality_functor β m) h

end InjectiveResolution

namespace RightDerivedDelta

/-- The injective-horseshoe SES of cocomplexes after applying `F`, using
the shared arbitrary-resolution diagram. -/
noncomputable def RDhorseshoeF (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) : ShortComplex (CochainComplex D ℕ)  :=
  (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).mapped F

omit [HasInjectiveResolutions C] in
/-- Short exactness of the mapped endpoint horseshoe follows from the shared
degreewise splitting, transported from the standard biproduct splitting. -/
theorem RDhorseshoeF_shortExact (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    (RDhorseshoeF F S hS I₁ I₃).ShortExact  :=
  (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).mapped_shortExact F

/-- The shared connecting morphism for the prescribed endpoint resolutions. -/
noncomputable def RDdelta (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁  :=
  (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).delta F n (n + 1) rfl

/-- Unfolded form of `RDdelta` (proof irrelevance for the SES proof). -/
theorem RDdelta_eq (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃)
    (hHF : (RDhorseshoeF F S hS I₁ I₃).ShortExact) :
    RDdelta F n S hS I₁ I₃ =
      (I₃.isoRightDerivedObj F n).hom ≫
        hHF.δ n (n + 1) (ComplexShape.up_mk _ _ rfl) ≫
        (I₁.isoRightDerivedObj F (n + 1)).inv := rfl

omit [HasInjectiveResolutions C] in
/-- The endpoint interface uses the same mapped diagram as the shared core. -/
lemma RDhorseshoeF_eq_mapped (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    RDhorseshoeF F S hS I₁ I₃ =
      (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).mapped F := rfl

/-- The endpoint connecting morphism is the shared connecting morphism, with
no intervening comparison or choice. -/
lemma RDdelta_eq_ofEndpoints (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    RDdelta F n S hS I₁ I₃ =
      (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).delta
        F n (n + 1) rfl := rfl

/-- The shared sequence has exactly the endpoint maps and connecting morphism. -/
lemma RDlongSequence_eq (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence
        F n (n + 1) rfl =
      ComposableArrows.mk₅ ((F.rightDerived n).map S.f) ((F.rightDerived n).map S.g)
        (RDdelta F n S hS I₁ I₃) ((F.rightDerived (n + 1)).map S.f)
        ((F.rightDerived (n + 1)).map S.g) := rfl

omit [HasInjectiveResolutions C] in
/-- LES middle composite vanishes (via the horseshoe relation). -/
theorem RDles_middle_zero (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex _).map
          (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁)
            (I₃ := I₃)).i) n ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex _).map
          (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁)
            (I₃ := I₃)).p) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp,
    ← (F.mapHomologicalComplex _).map_comp,
    (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁)
      (I₃ := I₃)).zero]
  simp

/-- Exactness at `R^{n+1}(X₁)` in the shared long exact sequence. -/
theorem RDexact_A (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ w : RDdelta F n S hS I₁ I₃ ≫ (F.rightDerived (n + 1)).map S.f = 0,
      (ShortComplex.mk _ _ w).Exact  := by
  have h := (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence_exact
    F n (n + 1) rfl
  exact ⟨h.toIsComplex.zero 2, h.exact 2⟩

/-- Exactness at `R^n(X₂)` in the shared long exact sequence. -/
theorem RDexact_B (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ w : (F.rightDerived n).map S.f ≫ (F.rightDerived n).map S.g = 0,
      (ShortComplex.mk _ _ w).Exact  := by
  have h := (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence_exact
    F n (n + 1) rfl
  exact ⟨h.toIsComplex.zero 0, h.exact 0⟩

/-- Exactness at `R^n(X₃)` in the shared long exact sequence. -/
theorem RDexact_C (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ w : (F.rightDerived n).map S.g ≫ RDdelta F n S hS I₁ I₃ = 0,
      (ShortComplex.mk _ _ w).Exact  := by
  have h := (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence_exact
    F n (n + 1) rfl
  exact ⟨h.toIsComplex.zero 1, h.exact 1⟩

end RightDerivedDelta

end CategoryTheory
