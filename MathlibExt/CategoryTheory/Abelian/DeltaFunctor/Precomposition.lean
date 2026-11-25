/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Universal

/-!
# Exact precomposition of δ-functors

Precomposition with an additive exact functor retains the connecting maps
and exactness conditions. Universality of the source extends a specified
degree-zero transformation uniquely and gives its normalized comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CategoryTheory.CohomologicalDeltaFunctor

open CategoryTheory CategoryTheory.Limits

universe vA vB vD uA uB uD

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- Precompose by an additive functor whose short exact sequences
remain short exact. No injective preservation is required. -/
def precompose (R : A ⥤ B) [R.Additive]
    (hR : ∀ (S : ShortComplex A), S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) : CohomologicalDeltaFunctor A D where
  T n := R ⋙ T.T n
  additive _n := inferInstance
  connecting n :=
    { app S := (T.connecting n).app ⟨S.obj.map R, hR S.obj S.property⟩
      naturality {_S _S'} f := (T.connecting n).naturality
        ((ShortComplex.mapFunctor R hR).map f) }
  exactLeft n S := T.exactLeft n ⟨S.obj.map R, hR S.obj S.property⟩
  exactMiddle n S := T.exactMiddle n ⟨S.obj.map R, hR S.obj S.property⟩
  exactRight n S := T.exactRight n ⟨S.obj.map R, hR S.obj S.property⟩
  monoZero S := T.monoZero ⟨S.obj.map R, hR S.obj S.property⟩

/-- Precomposition of every degree and connector square. -/
def precomposeFunctor (R : A ⥤ B) [R.Additive]
    (hR : ∀ (S : ShortComplex A), S.ShortExact → (S.map R).ShortExact) :
    CohomologicalDeltaFunctor B D ⥤ CohomologicalDeltaFunctor A D where
  obj T := precompose R hR T
  map {S T} f := homMk A D (fun n => Functor.whiskerLeft R (Hom.app f n)) (fun n Z =>
    DeltaFunctor.System.comm f.hom n ⟨Z.obj.map R, hR Z.obj Z.property⟩)
  map_id T := by
    apply hom_ext
    intro n
    ext M
    rfl
  map_comp f g := by
    apply hom_ext
    intro n
    ext M
    rfl

end CategoryTheory.CohomologicalDeltaFunctor



namespace CategoryTheory.CohomologicalDeltaFunctor

universe vC vD uC uD
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- Extend the fixed degree-zero map by universality of the source. -/
def normalizedExtension (T S : CohomologicalDeltaFunctor C D)
    (hT : IsUniversal C D T) {F G : C ⥤ D}
    (eT : T.T 0 ≅ F) (eS : S.T 0 ≅ G) (f : F ⟶ G) : T ⟶ S :=
  (hT S (eT.hom ≫ f ≫ eS.inv)).choose

theorem normalizedExtension_app_zero (T S : CohomologicalDeltaFunctor C D)
    (hT : IsUniversal C D T) {F G : C ⥤ D}
    (eT : T.T 0 ≅ F) (eS : S.T 0 ≅ G) (f : F ⟶ G) :
    Hom.app (normalizedExtension T S hT eT eS f) 0 = eT.hom ≫ f ≫ eS.inv :=
  (hT S (eT.hom ≫ f ≫ eS.inv)).choose_spec.1

theorem normalizedExtension_normalization (T S : CohomologicalDeltaFunctor C D)
    (hT : IsUniversal C D T) {F G : C ⥤ D}
    (eT : T.T 0 ≅ F) (eS : S.T 0 ≅ G) (f : F ⟶ G) :
    Hom.app (normalizedExtension T S hT eT eS f) 0 ≫ eS.hom = eT.hom ≫ f := by
  exact (congrArg (· ≫ eS.hom) (normalizedExtension_app_zero T S hT eT eS f)).trans
    (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Two maps out of an universal source agreeing at zero agree in all degrees. -/
theorem hom_eq_of_app_zero (T : CohomologicalDeltaFunctor C D)
    (hT : IsUniversal C D T) (S : CohomologicalDeltaFunctor C D)
    (f g : T ⟶ S) (h₀ : Hom.app f 0 = Hom.app g 0) : f = g := by
  obtain ⟨a, ha, hu⟩ := hT S (Hom.app g 0)
  exact (hu f h₀).trans (hu g rfl).symm

/-- An independently extended derived map commutes with the normalized comparison.
Only universality of the two source functors is needed; targets may be arbitrary
precompositions by exact coefficient restriction. -/
theorem normalizedExtension_comparison
    (T S T' S' : CohomologicalDeltaFunctor C D)
    (hT : IsUniversal C D T) (hS : IsUniversal C D S)
    {F G : C ⥤ D} (eT : T.T 0 ≅ F) (eS : S.T 0 ≅ F)
    (eT' : T'.T 0 ≅ G) (eS' : S'.T 0 ≅ G) (f : F ⟶ G)
    (c : T ⟶ S) (d : T' ⟶ S') (m : T ⟶ T')
    (hc : Hom.app c 0 ≫ eS.hom = eT.hom)
    (hd : Hom.app d 0 ≫ eS'.hom = eT'.hom)
    (hm : Hom.app m 0 ≫ eT'.hom = eT.hom ≫ f) :
    m ≫ d = c ≫ normalizedExtension S S' hS eS eS' f := by
  apply hom_eq_of_app_zero T hT S'
  change Hom.app m 0 ≫ Hom.app d 0 =
    Hom.app c 0 ≫ Hom.app (normalizedExtension S S' hS eS eS' f) 0
  apply (cancel_mono eS'.hom).1
  calc
    (Hom.app m 0 ≫ Hom.app d 0) ≫ eS'.hom = Hom.app m 0 ≫ eT'.hom :=
      (Category.assoc _ _ _).trans (congrArg (Hom.app m 0 ≫ ·) hd)
    _ = eT.hom ≫ f := hm
    _ = Hom.app c 0 ≫ (eS.hom ≫ f) :=
      (congrArg (· ≫ f) hc.symm).trans (Category.assoc _ _ _)
    _ = (Hom.app c 0 ≫
          Hom.app (normalizedExtension S S' hS eS eS' f) 0) ≫ eS'.hom :=
      (congrArg (Hom.app c 0 ≫ ·)
        (normalizedExtension_normalization S S' hS eS eS' f).symm).trans
          (Category.assoc _ _ _).symm

/-- The same independent comparison square holds in every degree. -/
theorem normalizedExtension_comparison_app
    (T S T' S' : CohomologicalDeltaFunctor C D)
    (hT : IsUniversal C D T) (hS : IsUniversal C D S)
    {F G : C ⥤ D} (eT : T.T 0 ≅ F) (eS : S.T 0 ≅ F)
    (eT' : T'.T 0 ≅ G) (eS' : S'.T 0 ≅ G) (f : F ⟶ G)
    (c : T ⟶ S) (d : T' ⟶ S') (m : T ⟶ T')
    (hc : Hom.app c 0 ≫ eS.hom = eT.hom)
    (hd : Hom.app d 0 ≫ eS'.hom = eT'.hom)
    (hm : Hom.app m 0 ≫ eT'.hom = eT.hom ≫ f) (n : ℕ) :
    Hom.app m n ≫ Hom.app d n =
      Hom.app c n ≫ Hom.app (normalizedExtension S S' hS eS eS' f) n :=
  congrArg (fun z => Hom.app z n)
    (normalizedExtension_comparison T S T' S' hT hS eT eS eT' eS' f c d m hc hd hm)

end CategoryTheory.CohomologicalDeltaFunctor
