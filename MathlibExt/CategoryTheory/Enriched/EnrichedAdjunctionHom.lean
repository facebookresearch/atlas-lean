/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Generator.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC vC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedAdjunctionHom

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]

/-- Actual continuous full Hom maps of the original functors and their ordinary point laws.
No free/evaluation Hom isomorphism is supplied. -/
structure Data (L : V ⥤ C) (R : C ⥤ V) where
  /-- The internal Hom map induced by the left functor. -/
  leftMap : ∀ X Y : V, (ihom X).obj Y ⟶ (L.obj X ⟶[V] L.obj Y)
  /-- The internal Hom map induced by the right functor. -/
  rightMap : ∀ M N : C, (M ⟶[V] N) ⟶ (ihom (R.obj M)).obj (R.obj N)
  leftPoint : ∀ {X Y : V} (f : X ⟶ Y),
    eHomEquiv V f ≫ leftMap X Y = eHomEquiv V (L.map f)
  rightPoint : ∀ {M N : C} (f : M ⟶ N),
    eHomEquiv V f ≫ rightMap M N = eHomEquiv V (R.map f)

variable {L : V ⥤ C} {R : C ⥤ V} (d : Data L R) (adj : L ⊣ R)

/-- Evaluation is the actual right Hom map followed by the original unit precomposition. -/
@[no_expose]
def forward (M : C) : (L.obj (𝟙_ V) ⟶[V] M) ⟶ (ihom (𝟙_ V)).obj (R.obj M) :=
  d.rightMap (L.obj (𝟙_ V)) M ≫ eHomWhiskerRight V (adj.unit.app (𝟙_ V)) (R.obj M)

/-- Extension is the actual left Hom map followed by the original counit postcomposition. -/
@[no_expose]
def inverse (M : C) : (ihom (𝟙_ V)).obj (R.obj M) ⟶ (L.obj (𝟙_ V) ⟶[V] M) :=
  d.leftMap (𝟙_ V) (R.obj M) ≫ eHomWhiskerLeft V (L.obj (𝟙_ V)) (adj.counit.app M)

/-- Every actual original adjunct point is retained by the whole continuous evaluation map. -/
theorem forward_point (M : C) (f : L.obj (𝟙_ V) ⟶ M) :
    eHomEquiv V f ≫ forward d adj M = eHomEquiv V (adj.homEquiv (𝟙_ V) M f) := by
  change eHomEquiv V f ≫ d.rightMap (L.obj (𝟙_ V)) M ≫
    eHomWhiskerRight V (adj.unit.app (𝟙_ V)) (R.obj M) = _
  have h := congrArg (fun z => z ≫
    eHomWhiskerRight V (adj.unit.app (𝟙_ V)) (R.obj M)) (d.rightPoint f)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((eHomEquiv_comp_eHomWhiskerRight V V (adj.unit.app (𝟙_ V)) (R.map f)).trans
      (congrArg (eHomEquiv V) (adj.homEquiv_unit (𝟙_ V) M f).symm)))

/-- Every actual original inverse adjunct point is retained by the continuous extension map. -/
theorem inverse_point (M : C) (f : 𝟙_ V ⟶ R.obj M) :
    eHomEquiv V f ≫ inverse d adj M =
      eHomEquiv V ((adj.homEquiv (𝟙_ V) M).symm f) := by
  change eHomEquiv V f ≫ d.leftMap (𝟙_ V) (R.obj M) ≫
    eHomWhiskerLeft V (L.obj (𝟙_ V)) (adj.counit.app M) = _
  have h := congrArg (fun z => z ≫
    eHomWhiskerLeft V (L.obj (𝟙_ V)) (adj.counit.app M)) (d.leftPoint f)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((eHomEquiv_comp_eHomWhiskerLeft V C (L.map f) (adj.counit.app M)).trans
      (congrArg (eHomEquiv V) (adj.homEquiv_counit (𝟙_ V) M f).symm)))

/-- The original continuous mapping morphism is recovered using the actual tensor-unit separator. -/
theorem forward_inverse (hsep : IsSeparator (𝟙_ V)) (M : C) :
    forward d adj M ≫ inverse d adj M = 𝟙 _ := by
  apply hsep.def
  intro p
  let f : L.obj (𝟙_ V) ⟶ M := (eHomEquiv V).symm p
  have hp : eHomEquiv V f = p := (eHomEquiv V).apply_symm_apply p
  have hf := forward_point d adj M f
  have hg := inverse_point d adj M (adj.homEquiv (𝟙_ V) M f)
  have hinv : eHomEquiv V ((adj.homEquiv (𝟙_ V) M).symm
      (adj.homEquiv (𝟙_ V) M f)) = p :=
    (congrArg (eHomEquiv V) ((adj.homEquiv (𝟙_ V) M).symm_apply_apply f)).trans hp
  change p ≫ (forward d adj M ≫ inverse d adj M) = p ≫ 𝟙 _
  exact (Category.assoc p (forward d adj M) (inverse d adj M)).symm.trans
    ((congrArg (fun z => z ≫ inverse d adj M) ((congrArg
      (fun z => z ≫ forward d adj M) hp).symm.trans hf)).trans
        ((hg.trans hinv).trans (Category.comp_id p).symm))

/-- The original continuous evaluation morphism is recovered through the actual unit separator. -/
theorem inverse_forward (hsep : IsSeparator (𝟙_ V)) (M : C) :
    inverse d adj M ≫ forward d adj M = 𝟙 _ := by
  apply hsep.def
  intro p
  let f : 𝟙_ V ⟶ R.obj M :=
    (eHomEquiv V (X := 𝟙_ V) (Y := R.obj M)).symm p
  have hp : eHomEquiv V f = p :=
    (eHomEquiv V (X := 𝟙_ V) (Y := R.obj M)).apply_symm_apply p
  have hf := inverse_point d adj M f
  have hg := forward_point d adj M ((adj.homEquiv (𝟙_ V) M).symm f)
  have hinv : eHomEquiv V (adj.homEquiv (𝟙_ V) M
      ((adj.homEquiv (𝟙_ V) M).symm f)) = p :=
    (congrArg (eHomEquiv V) ((adj.homEquiv (𝟙_ V) M).apply_symm_apply f)).trans hp
  change p ≫ (inverse d adj M ≫ forward d adj M) = p ≫ 𝟙 _
  exact (Category.assoc p (inverse d adj M) (forward d adj M)).symm.trans
    ((congrArg (fun z => z ≫ forward d adj M) ((congrArg
      (fun z => z ≫ inverse d adj M) hp).symm.trans hf)).trans
        ((hg.trans hinv).trans (Category.comp_id p).symm))

/-- The entire original adjunction gives a genuine enriched mapping-object isomorphism. -/
@[no_expose]
def homIso (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (L.obj (𝟙_ V) ⟶[V] M) ≅ (ihom (𝟙_ V)).obj (R.obj M) where
  hom := forward d adj M
  inv := inverse d adj M
  hom_inv_id := forward_inverse d adj hsep M
  inv_hom_id := inverse_forward d adj hsep M

/-- The actual whole adjunction mapping object evaluates to the original actual value. -/
@[no_expose]
def valueIso (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (L.obj (𝟙_ V) ⟶[V] M) ≅ R.obj M :=
  homIso d adj hsep M ≪≫ MonoidalClosed.unitIsoSelf (X := R.obj M)

/-- Complete public object data of the evaluation map. -/
theorem forward_eq (M : C) : forward d adj M =
    d.rightMap (L.obj (𝟙_ V)) M ≫ eHomWhiskerRight V (adj.unit.app (𝟙_ V)) (R.obj M) :=
  by rfl

/-- Complete public object data of the extension map. -/
theorem inverse_eq (M : C) : inverse d adj M =
    d.leftMap (𝟙_ V) (R.obj M) ≫ eHomWhiskerLeft V (L.obj (𝟙_ V)) (adj.counit.app M) :=
  by rfl

/-- The whole adjunction Hom isomorphism retains the actual evaluation map. -/
theorem homIso_hom (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (homIso d adj hsep M).hom = forward d adj M := by rfl

/-- The whole adjunction Hom isomorphism retains the actual inverse extension map. -/
theorem homIso_inv (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (homIso d adj hsep M).inv = inverse d adj M := by rfl

end CategoryTheory.EnrichedAdjunctionHom
