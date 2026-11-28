/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Definitions/Def_SheafOfModules_Monoidal.lean`,
`Definitions/Def_SheafOfModules_MonoidalV2.lean`,
`Theorems/Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean`,
`P2M/Sol/S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# The monoidal structure on sheaves of modules

For a presheaf of commutative rings `𝒪` with a locally bijective morphism from its underlying
presheaf of rings to a sheaf of rings, the class of morphisms of presheaves of `𝒪`-modules that
become isomorphisms after sheafification is stable under tensoring
(`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`). For a sheaf of commutative rings `𝒪`
(the identity morphism), the monoidal structure on presheaves of modules therefore descends along
sheafification, and sheaves of modules over `𝒪` form a symmetric monoidal closed category whose
tensor product is the sheafified tensor product (`SheafOfModules.tensorIsoSheafify`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace PresheafOfModules.IsMonoidalW

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
  (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

private abbrev W : MorphismProperty (PresheafOfModulesOfCommRing.{u} 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

private abbrev shf : PresheafOfModulesOfCommRing.{u} 𝒪 ⥤ SheafOfModules.{u} R :=
  PresheafOfModules.sheafification α

private abbrev inc : SheafOfModules.{u} R ⥤ PresheafOfModulesOfCommRing.{u} 𝒪 :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

private abbrev adj : shf 𝒪 R α ⊣ inc 𝒪 R α := PresheafOfModules.sheafificationAdjunction α

private local instance : (inc 𝒪 R α).Faithful := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.faithful
private local instance : (inc 𝒪 R α).Full := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.full

private lemma W_eq : W (J := J) 𝒪 = (MorphismProperty.isomorphisms _).inverseImage (shf 𝒪 R α) :=
  PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α

private lemma isIso_unit_app_of_isSheaf (N : PresheafOfModulesOfCommRing.{u} 𝒪)
    (hN : Presheaf.IsSheaf J N.presheaf) :
    IsIso ((adj 𝒪 R α).unit.app N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((adj 𝒪 R α).unit.app N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J hN
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

private lemma isIso_shf_map_unit_whiskerRight (d d' : PresheafOfModulesOfCommRing.{u} 𝒪) :
    IsIso ((shf 𝒪 R α).map (((adj 𝒪 R α).unit.app d) ▷ d')) := by
  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 1 3
  refine (h.mp ?_) d d'
  intro c d
  apply isIso_unit_app_of_isSheaf
  exact PresheafOfModules.isSheaf_ihom _ _ c.isSheaf

include R α in
private lemma W_whiskerRight {d₁ d₂ : PresheafOfModulesOfCommRing.{u} 𝒪} (g : d₁ ⟶ d₂)
    (hg : W (J := J) 𝒪 g) (d' : PresheafOfModulesOfCommRing.{u} 𝒪) :
    W (J := J) 𝒪 (g ▷ d') := by
  have two3 : (W (J := J) 𝒪).HasTwoOutOfThreeProperty := by
    rw [W_eq 𝒪 R α]; infer_instance
  have hη : ∀ d : PresheafOfModulesOfCommRing.{u} 𝒪,
      W (J := J) 𝒪 ((adj 𝒪 R α).unit.app d ▷ d') := fun d => by
    rw [W_eq 𝒪 R α]
    exact isIso_shf_map_unit_whiskerRight 𝒪 R α d d'
  have hiso : W (J := J) 𝒪 ((inc 𝒪 R α).map ((shf 𝒪 R α).map g) ▷ d') := by
    rw [W_eq 𝒪 R α] at hg ⊢
    simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at hg ⊢
    have : IsIso ((inc 𝒪 R α).map ((shf 𝒪 R α).map g)) := Functor.map_isIso _ _
    infer_instance
  have e := (adj 𝒪 R α).unit_naturality g
  have hη₁ := hη d₁
  have hη₂ := hη d₂
  dsimp only [Functor.comp_obj, Functor.id_obj] at e hη₁ hη₂ hiso ⊢
  have h' := (W (J := J) 𝒪).comp_mem _ _ hη₁ hiso
  rw [← comp_whiskerRight, e, comp_whiskerRight] at h'
  exact (W (J := J) 𝒪).of_postcomp _ _ hη₂ h'

end PresheafOfModules.IsMonoidalW

open PresheafOfModules.IsMonoidalW in
/-- **Tensoring preserves morphisms inverted by sheafification.** Let `𝒪` be a presheaf of
commutative rings on a site `(C, J)` on which presheaves of abelian groups have sheafifications
and `J.W` consists of the locally bijective morphisms, and let `α` be a locally injective and
locally surjective morphism from the underlying presheaf of rings of `𝒪` to a sheaf of rings `R`.
Then the morphisms of presheaves of `𝒪`-modules whose underlying morphism of presheaves of
abelian groups becomes an isomorphism after sheafification (lies in `J.W`) are stable under
tensoring, on either side, with any presheaf of `𝒪`-modules. This generalizes the instance
`PresheafOfModules.isMonoidal_W_inverseImage_toPresheaf`, the case of a sheaf `𝒪` with `α = 𝟙`
stated in more general universes; for `C : Type u` with `Category.{u} C`, that instance follows
from this theorem. -/
theorem PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf {C : Type u} [Category.{u} C] {J :
  GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerRight g hg d' := W_whiskerRight 𝒪 R α g hg d'
  whiskerLeft d g₁ g₂ g hg :=
    ((W (J := J) 𝒪).arrow_mk_iso_iff (Arrow.isoMk' (g ▷ d) (d ◁ g) (β_ g₁ d) (β_ g₂ d)
      (BraidedCategory.braiding_naturality_left g d).symm)).1 (W_whiskerRight 𝒪 R α g hg d)

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **Underlying sheaf of rings.** For a presheaf of commutative rings `𝒪` whose underlying
presheaf of rings is a sheaf (`h𝒪`), that sheaf of rings. -/
abbrev ringSheaf : Sheaf J RingCat.{u} := ⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩

/-- **Morphisms inverted by sheafification.** The morphisms of presheaves of `𝒪`-modules whose
underlying morphism of presheaves of abelian groups lies in `J.W`, i.e. becomes an isomorphism
after sheafification. -/
abbrev presheafW (J : GrothendieckTopology C) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MorphismProperty (PresheafOfModulesOfCommRing.{u} 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

/-- **Sheafification of presheaves of modules.** For a presheaf of commutative rings `𝒪` whose
underlying presheaf of rings is a sheaf (`h𝒪`), sheafification of presheaves of `𝒪`-modules, with
values in sheaves of modules over that sheaf of rings. -/
abbrev sheafifyFunctor : PresheafOfModulesOfCommRing.{u} 𝒪 ⥤ SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) :=
  PresheafOfModules.sheafification (R := ringSheaf 𝒪 h𝒪) (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

/-- **Underlying presheaf of modules.** The underlying presheaf of modules of a sheaf of
modules. -/
abbrev toPMod : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪) ⥤ PresheafOfModulesOfCommRing.{u} 𝒪 :=
  SheafOfModules.forget (ringSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

/-- **Sheafification adjunction for modules.** Sheafification is left adjoint to the forgetful
functor. -/
abbrev sheafifyAdj : sheafifyFunctor 𝒪 h𝒪 ⊣ toPMod 𝒪 h𝒪 :=
  PresheafOfModules.sheafificationAdjunction (R := ringSheaf 𝒪 h𝒪)
    (𝟙 (𝒪 ⋙ forget₂ CommRingCat RingCat))

instance : (toPMod 𝒪 h𝒪).Faithful := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.faithful
instance : (toPMod 𝒪 h𝒪).Full := (sheafifyAdj 𝒪 h𝒪).fullyFaithfulROfIsIsoCounit.full

instance : (sheafifyFunctor 𝒪 h𝒪).IsLocalization (presheafW J 𝒪) := inferInstance

include h𝒪 in
theorem presheafW_isMonoidal : (presheafW J 𝒪).IsMonoidal :=
  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf 𝒪 (ringSheaf 𝒪 h𝒪) (𝟙 _)

/-- **Sheafifying a sheaf of modules.** A sheaf of modules is isomorphic to the sheafification
of its underlying presheaf. -/
def sheafifyCounitIso (M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj ((toPMod 𝒪 h𝒪).obj M) ≅ M :=
  (asIso (sheafifyAdj 𝒪 h𝒪).counit).app M

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

set_option backward.isDefEq.respectTransparency false in
/-- **Sheafification of the unit.** The sheafification of the unit presheaf of modules is the
unit sheaf. -/
def sheafifyUnitIso : (sheafifyFunctor 𝒪 h𝒪).obj (𝟙_ (PresheafOfModulesOfCommRing.{u} 𝒪)) ≅
    (unit (ringSheaf 𝒪 h𝒪) : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  sheafifyCounitIso 𝒪 h𝒪 (unit (ringSheaf 𝒪 h𝒪))

/-- The monoidal structure on sheaves of modules induced from presheaves. -/
instance monoidalCategory : MonoidalCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))

/-- Sheaves of modules form a symmetric monoidal category. -/
instance symmetricCategory : SymmetricCategory (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)))

/-- Sheafification is a monoidal functor. -/
instance sheafifyFunctor_monoidal : (sheafifyFunctor 𝒪 h𝒪).Monoidal :=
  letI := presheafW_isMonoidal 𝒪 h𝒪
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := sheafifyFunctor 𝒪 h𝒪) (W := presheafW J 𝒪) (sheafifyUnitIso 𝒪 h𝒪)).Monoidal

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[simp] theorem tensorUnit_eq : 𝟙_ (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) = unit _ := rfl

/-- Sheaves of modules form a monoidal closed category. -/
instance monoidalClosed : MonoidalClosed (SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :=
  Monoidal.Reflective.monoidalClosed (sheafifyAdj 𝒪 h𝒪)

/-- **Sheaf tensor product as sheafified tensor product.** The tensor product of sheaves of
modules is the sheafified presheaf tensor product. -/
def tensorIsoSheafify (L M : SheafOfModules.{u} (ringSheaf 𝒪 h𝒪)) :
    (sheafifyFunctor 𝒪 h𝒪).obj (L.val ⊗ M.val) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (sheafifyFunctor 𝒪 h𝒪) L.val M.val).symm ≪≫
    (sheafifyCounitIso 𝒪 h𝒪 L ⊗ᵢ sheafifyCounitIso 𝒪 h𝒪 M)

end SheafOfModules

end
