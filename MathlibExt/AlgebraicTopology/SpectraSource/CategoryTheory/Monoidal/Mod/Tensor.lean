/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Tensor.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Bimod
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Bimodule
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The balanced tensor product of modules over a commutative monoid

Let `A` be a commutative monoid object in a braided monoidal category `C` with coequalizers, such
that tensoring on either side preserves (universe-`0` small) colimits, in particular these
coequalizers. The balanced tensor product `M ⊗_A N` of two left
`A`-modules is the coequalizer of the two actions of `A` on `M ⊗ A ⊗ N`: the right action
`m ⊗ a ↦ a • m` of `A` on `M`, obtained through the braiding, and the left action on `N`. The
scalars act on `M ⊗_A N` through `M`. With unit the regular module `A`, this makes `Mod C A` a
monoidal category.

For the commutative sphere monoid in symmetric sequences this is the smash product `X ∧ Y` of
symmetric spectra, the coequalizer of `X ⊗ S ⊗ Y ⇉ X ⊗ Y`.

The construction reuses Mathlib's tensor product of bimodules `Bimod.tensorBimod`, with the
associator and unitors of Mathlib's bicategory `Bimod.monBicategory` of monoids and bimodules.
A module over a commutative monoid is a bimodule through `Mod.toBimod`. The bimodule tensor
product of two such bimodules is again of this form (`Bimod.tensorBimod_actRight_eq`), so the
monoidal structure `Bimod.monoidalCategory` of the endomorphism category `Bimod R R` is
transported to `Mod C A` along the fully faithful functor `Mod.toBimod` by Mathlib's
`Monoidal.induced`.

## Main definitions

* `Mod.monoidalCategory`: the monoidal category of modules over a commutative monoid object, under
  the balanced tensor product.
* `Mod.tensorπ M N : M.X ⊗ N.X ⟶ (M ⊗ N).X`: the quotient map onto the balanced tensor product, and
  `Mod.tensorDesc`, its universal property.

## Main statements

* `Mod.tensorπ_whiskerLeft_hom`, `Mod.tensorπ_whiskerRight_hom`, `Mod.tensorπ_associator_hom_hom`,
  `Mod.tensorπ_associator_inv_hom`, `Mod.tensorπ_leftUnitor_hom_hom` and
  `Mod.tensorπ_rightUnitor_hom_hom`: the monoidal structure on representatives in `M.X ⊗ N.X`.
* The instance `(Mod.toBimod (A := A)).Monoidal`: `Mod.toBimod` is a monoidal functor, with
  structure maps `Mod.toBimod_μ`, `Mod.toBimod_δ`, `Mod.toBimod_ε` and `Mod.toBimod_η`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonoidalLeftAction MonObj BraidedCategory Limits

namespace Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- The balanced tensor product `M ⊗_A N` of modules over a commutative monoid object: the
tensor product of the associated bimodules, with its left action. -/
noncomputable def tensorObj (M N : Mod C A) : Mod C A :=
  (Bimod.toLeftMod _ _).obj (toBimod.obj M ⊗ toBimod.obj N)

/-- The bimodule associated with `M ⊗_A N` is the tensor product of the bimodules associated with
`M` and `N`. The comparison is the identity on the common carrier. -/
noncomputable def toBimodTensorObjIso (M N : Mod C A) :
    toBimod.obj M ⊗ toBimod.obj N ≅ toBimod.obj (tensorObj M N) :=
  (Bimod.toLeftModToBimodIsoOfActRightEq _
    (Bimod.tensorBimod_actRight_eq (toBimod.obj M) (toBimod.obj N) rfl rfl)).symm

/-- The balanced tensor product, with the monoidal data of bimodules conjugated by
`toBimodTensorObjIso`. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct (Mod C A) where
  tensorObj := tensorObj
  whiskerLeft M _ _ g := fullyFaithfulToBimod.preimage
    ((toBimodTensorObjIso M _).inv ≫ (toBimod.obj M ◁ toBimod.map g) ≫
      (toBimodTensorObjIso M _).hom)
  whiskerRight f N := fullyFaithfulToBimod.preimage
    ((toBimodTensorObjIso _ N).inv ≫ (toBimod.map f ▷ toBimod.obj N) ≫
      (toBimodTensorObjIso _ N).hom)
  tensorHom f g := fullyFaithfulToBimod.preimage
    ((toBimodTensorObjIso _ _).inv ≫ (toBimod.map f ⊗ₘ toBimod.map g) ≫
      (toBimodTensorObjIso _ _).hom)
  tensorUnit := regular A
  associator M N P := fullyFaithfulToBimod.preimageIso
    (((toBimodTensorObjIso _ _).symm ≪≫ ((toBimodTensorObjIso _ _).symm ⊗ᵢ .refl _))
      ≪≫ α_ (toBimod.obj M) (toBimod.obj N) (toBimod.obj P)
      ≪≫ ((.refl _ ⊗ᵢ toBimodTensorObjIso _ _) ≪≫ toBimodTensorObjIso _ _))
  leftUnitor M := fullyFaithfulToBimod.preimageIso
    (((toBimodTensorObjIso _ _).symm ≪≫ (toBimodRegularIso ⊗ᵢ .refl _)) ≪≫
      λ_ (toBimod.obj M))
  rightUnitor M := fullyFaithfulToBimod.preimageIso
    (((toBimodTensorObjIso _ _).symm ≪≫ (.refl _ ⊗ᵢ toBimodRegularIso)) ≪≫
      ρ_ (toBimod.obj M))

/-- The data inducing the monoidal structure of `Mod C A` from that of bimodules along `toBimod`. -/
noncomputable def inducingFunctorData : Monoidal.InducingFunctorData (toBimod (A := A)) where
  μIso := toBimodTensorObjIso
  whiskerLeft_eq _ _ _ _ := fullyFaithfulToBimod.map_preimage _
  whiskerRight_eq _ _ := fullyFaithfulToBimod.map_preimage _
  tensorHom_eq _ _ := fullyFaithfulToBimod.map_preimage _
  εIso := toBimodRegularIso.symm
  associator_eq _ _ _ := fullyFaithfulToBimod.map_preimage _
  leftUnitor_eq _ := fullyFaithfulToBimod.map_preimage _
  rightUnitor_eq _ := fullyFaithfulToBimod.map_preimage _

/-- Modules over a commutative monoid object form a monoidal category under the balanced tensor
product, with unit the regular module. -/
noncomputable instance monoidalCategory : MonoidalCategory (Mod C A) :=
  Monoidal.induced toBimod inducingFunctorData

/-- Regarding modules over a commutative monoid object as bimodules is a monoidal functor. -/
noncomputable instance : (toBimod (A := A)).Monoidal :=
  Monoidal.fromInducedMonoidal toBimod inducingFunctorData

/-- The tensorator of the monoidal functor `toBimod` is the comparison `toBimodTensorObjIso`. -/
@[simp]
theorem toBimod_μ (M N : Mod C A) :
    Functor.LaxMonoidal.μ toBimod M N = (toBimodTensorObjIso M N).hom :=
  (rfl)

/-- The inverse tensorator of `toBimod` is the inverse of `toBimodTensorObjIso`. -/
@[simp]
theorem toBimod_δ (M N : Mod C A) :
    Functor.OplaxMonoidal.δ toBimod M N = (toBimodTensorObjIso M N).inv :=
  (rfl)

/-- The unit map of the monoidal functor `toBimod` is the inverse of `toBimodRegularIso`. -/
@[simp]
theorem toBimod_ε : Functor.LaxMonoidal.ε (toBimod (A := A)) = toBimodRegularIso.inv :=
  (rfl)

/-- The counit map of the monoidal functor `toBimod` is `toBimodRegularIso`. -/
@[simp]
theorem toBimod_η : Functor.OplaxMonoidal.η (toBimod (A := A)) = toBimodRegularIso.hom :=
  (rfl)

/-- The quotient map `M ⊗ N ⟶ M ⊗_A N` onto the balanced tensor product. -/
noncomputable def tensorπ (M N : Mod C A) : M.X ⊗ N.X ⟶ (M ⊗ N).X :=
  coequalizer.π _ _

/-- The quotient map onto `M ⊗_A N` identifies the action of `A` on `M` with that on `N`. -/
@[reassoc]
theorem tensorπ_condition (M N : Mod C A) :
    ((β_ A M.X).inv ≫ γ[A, M.X]) ▷ N.X ≫ tensorπ M N =
      (α_ M.X A N.X).hom ≫ M.X ◁ γ[A, N.X] ≫ tensorπ M N :=
  (coequalizer.condition _ _).trans (Category.assoc _ _ _)

/-- In `M ⊗_A N`, a scalar acting on `M` may be moved, through the braiding, to act on `N`. -/
@[reassoc]
theorem smul_whiskerRight_tensorπ (M N : Mod C A) :
    γ[A, M.X] ▷ N.X ≫ tensorπ M N =
      (β_ A M.X).hom ▷ N.X ≫ (α_ M.X A N.X).hom ≫ M.X ◁ γ[A, N.X] ≫ tensorπ M N := by
  rw [← tensorπ_condition, ← comp_whiskerRight_assoc, Iso.hom_inv_id_assoc]

instance (M N : Mod C A) : Epi (tensorπ M N) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- Tensoring on the right preserves the coequalizer defining `M ⊗_A N`, so the whiskered quotient
map is still an epimorphism. -/
instance (M N : Mod C A) (X : C) : Epi (tensorπ M N ▷ X) :=
  inferInstanceAs (Epi ((MonoidalCategory.tensorRight X).map (coequalizer.π _ _)))

/-- Tensoring on the left preserves the coequalizer defining `M ⊗_A N`, so the whiskered quotient
map is still an epimorphism. -/
instance (M N : Mod C A) (X : C) : Epi (X ◁ tensorπ M N) :=
  inferInstanceAs (Epi ((tensorLeft X).map (coequalizer.π _ _)))

/-- Morphisms out of `M ⊗_A N` are determined by their composites with the quotient map. -/
@[ext]
theorem tensor_hom_ext {M N : Mod C A} {Z : C} {f g : (M ⊗ N).X ⟶ Z}
    (h : tensorπ M N ≫ f = tensorπ M N ≫ g) : f = g :=
  (cancel_epi _).1 h

/-- A morphism out of `M ⊗ N` identifying the actions of `A` on `M` and on `N` factors through
the balanced tensor product. -/
noncomputable def tensorDesc {M N : Mod C A} {Z : C} (f : M.X ⊗ N.X ⟶ Z)
    (hf : ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ f = (α_ M.X A N.X).hom ≫ M.X ◁ γ[A,N.X] ≫ f) :
    (M ⊗ N).X ⟶ Z :=
  coequalizer.desc f (by simpa using hf)

/-- The factorization through the balanced tensor product restricts to the given morphism. -/
@[reassoc (attr := simp)]
theorem tensorπ_tensorDesc {M N : Mod C A} {Z : C} (f : M.X ⊗ N.X ⟶ Z)
    (hf : ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ f = (α_ M.X A N.X).hom ≫ M.X ◁ γ[A,N.X] ≫ f) :
    tensorπ M N ≫ tensorDesc f hf = f :=
  coequalizer.π_desc _ _

/-- The factorization through the balanced tensor product, whiskered on the left, restricts to the
whiskered morphism. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_tensorπ_tensorDesc {M N : Mod C A} {Z : C} (f : M.X ⊗ N.X ⟶ Z)
    (hf : ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ f = (α_ M.X A N.X).hom ≫ M.X ◁ γ[A,N.X] ≫ f)
    (X : C) : X ◁ tensorπ M N ≫ X ◁ tensorDesc f hf = X ◁ f := by
  rw [← whiskerLeft_comp, tensorπ_tensorDesc]

/-- The factorization through the balanced tensor product, whiskered on the right, restricts to
the whiskered morphism. -/
@[reassoc (attr := simp)]
theorem tensorπ_tensorDesc_whiskerRight {M N : Mod C A} {Z : C} (f : M.X ⊗ N.X ⟶ Z)
    (hf : ((β_ A M.X).inv ≫ γ[A,M.X]) ▷ N.X ≫ f = (α_ M.X A N.X).hom ≫ M.X ◁ γ[A,N.X] ≫ f)
    (X : C) : tensorπ M N ▷ X ≫ tensorDesc f hf ▷ X = f ▷ X := by
  rw [← comp_whiskerRight, tensorπ_tensorDesc]

/-- The scalars act on `M ⊗_A N` through `M`. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_tensorπ_smul (M N : Mod C A) :
    A ◁ tensorπ M N ≫ γ[A, (M ⊗ N).X] = (α_ A M.X N.X).inv ≫ γ[A, M.X] ▷ N.X ≫ tensorπ M N :=
  Bimod.TensorBimod.whiskerLeft_π_actLeft (toBimod.obj M) (toBimod.obj N)

/-- The comparison `toBimodTensorObjIso` carries the quotient map onto `M ⊗_A N` to the quotient
map onto the tensor product of bimodules. -/
theorem tensorπ_toBimodTensorObjIso_inv_hom (M N : Mod C A) :
    tensorπ M N ≫ (toBimodTensorObjIso M N).inv.hom =
      coequalizer.π ((toBimod.obj M).actRight ▷ (toBimod.obj N).X)
        ((α_ (toBimod.obj M).X (Mon.mk A).X (toBimod.obj N).X).hom ≫
          (toBimod.obj M).X ◁ (toBimod.obj N).actLeft) := by
  -- The comparison is the identity on the common carrier.
  simp only [toBimodTensorObjIso, Iso.symm_inv, Bimod.toLeftModToBimodIsoOfActRightEq_hom_hom]
  exact Category.comp_id _

/-- The comparison `toBimodTensorObjIso` carries the quotient map onto the tensor product of
bimodules to the quotient map onto `M ⊗_A N`. -/
theorem π_toBimodTensorObjIso_hom_hom (M N : Mod C A) :
    coequalizer.π ((toBimod.obj M).actRight ▷ (toBimod.obj N).X)
        ((α_ (toBimod.obj M).X (Mon.mk A).X (toBimod.obj N).X).hom ≫
          (toBimod.obj M).X ◁ (toBimod.obj N).actLeft) ≫ (toBimodTensorObjIso M N).hom.hom =
      tensorπ M N := by
  -- The comparison is the identity on the common carrier.
  simp only [toBimodTensorObjIso, Iso.symm_hom, Bimod.toLeftModToBimodIsoOfActRightEq_inv_hom]
  exact Category.comp_id _

/-- Whiskering `g : N ⟶ N'` on the left by `M` acts on representatives as `M.X ◁ g.hom`. -/
@[reassoc (attr := simp)]
theorem tensorπ_whiskerLeft_hom (M : Mod C A) {N N' : Mod C A} (g : N ⟶ N') :
    tensorπ M N ≫ (M ◁ g).hom = M.X ◁ g.hom ≫ tensorπ M N' := by
  have h : (M ◁ g).hom = (toBimodTensorObjIso M N).inv.hom ≫
      (toBimod.obj M ◁ toBimod.map g).hom ≫ (toBimodTensorObjIso M N').hom.hom :=
    congrArg Bimod.Hom.hom (inducingFunctorData.whiskerLeft_eq M g)
  rw [h, ← Category.assoc, tensorπ_toBimodTensorObjIso_inv_hom, Bimod.π_whiskerLeft_hom_assoc,
    π_toBimodTensorObjIso_hom_hom, toBimod_map_hom]

/-- Whiskering `f : M ⟶ M'` on the right by `N` acts on representatives as `f.hom ▷ N.X`. -/
@[reassoc (attr := simp)]
theorem tensorπ_whiskerRight_hom {M M' : Mod C A} (f : M ⟶ M') (N : Mod C A) :
    tensorπ M N ≫ (f ▷ N).hom = f.hom ▷ N.X ≫ tensorπ M' N := by
  have h : (f ▷ N).hom = (toBimodTensorObjIso M N).inv.hom ≫
      (toBimod.map f ▷ toBimod.obj N).hom ≫ (toBimodTensorObjIso M' N).hom.hom :=
    congrArg Bimod.Hom.hom (inducingFunctorData.whiskerRight_eq f N)
  rw [h, ← Category.assoc, tensorπ_toBimodTensorObjIso_inv_hom, Bimod.π_whiskerRight_hom_assoc,
    π_toBimodTensorObjIso_hom_hom, toBimod_map_hom]

/-- The tensor product of `f : M ⟶ M'` and `g : N ⟶ N'` acts on representatives as
`f.hom ⊗ₘ g.hom`. -/
@[reassoc (attr := simp)]
theorem tensorπ_tensorHom_hom {M M' N N' : Mod C A} (f : M ⟶ M') (g : N ⟶ N') :
    tensorπ M N ≫ (f ⊗ₘ g).hom = (f.hom ⊗ₘ g.hom) ≫ tensorπ M' N' := by
  simp [MonoidalCategory.tensorHom_def]

/-- The associator of `M ⊗_A N ⊗_A P` acts on representatives in `M.X ⊗ N.X ⊗ P.X` as the
associator of the underlying objects. -/
@[reassoc]
theorem tensorπ_associator_hom_hom (M N P : Mod C A) :
    tensorπ M N ▷ P.X ≫ tensorπ (M ⊗ N) P ≫ (α_ M N P).hom.hom =
      (α_ M.X N.X P.X).hom ≫ M.X ◁ tensorπ N P ≫ tensorπ M (N ⊗ P) := by
  have h : toBimod.map (α_ M N P).hom = (toBimodTensorObjIso (M ⊗ N) P).inv ≫
      (toBimodTensorObjIso M N).inv ▷ toBimod.obj P ≫
        (α_ (toBimod.obj M) (toBimod.obj N) (toBimod.obj P)).hom ≫
          toBimod.obj M ◁ (toBimodTensorObjIso N P).hom ≫
            (toBimodTensorObjIso M (N ⊗ P)).hom := by
    rw [inducingFunctorData.associator_eq]
    simp [inducingFunctorData]
  replace h := congrArg Bimod.Hom.hom h
  rw [toBimod_map_hom, Bimod.comp_hom', Bimod.comp_hom', Bimod.comp_hom', Bimod.comp_hom'] at h
  rw [h, ← Category.assoc (tensorπ _ _), tensorπ_toBimodTensorObjIso_inv_hom,
    Bimod.π_whiskerRight_hom_assoc, ← comp_whiskerRight_assoc, tensorπ_toBimodTensorObjIso_inv_hom,
    Bimod.π_associator_hom_hom_assoc (toBimod.obj M) (toBimod.obj N) (toBimod.obj P),
    Bimod.π_whiskerLeft_hom_assoc, ← whiskerLeft_comp_assoc,
    π_toBimodTensorObjIso_hom_hom]
  -- The remaining quotient map is that of `M ⊗_A (N ⊗_A P)`, written through `tensorObj N P`
  -- rather than `N ⊗ P`, which `rw` does not unfold.
  exact congrArg (fun f ↦ (α_ M.X N.X P.X).hom ≫ M.X ◁ tensorπ N P ≫ f)
    (π_toBimodTensorObjIso_hom_hom M (N ⊗ P))

/-- The inverse associator of `M ⊗_A (N ⊗_A P)` acts on representatives in `M.X ⊗ N.X ⊗ P.X` as
the inverse associator of the underlying objects. -/
@[reassoc]
theorem tensorπ_associator_inv_hom (M N P : Mod C A) :
    M.X ◁ tensorπ N P ≫ tensorπ M (N ⊗ P) ≫ (α_ M N P).inv.hom =
      (α_ M.X N.X P.X).inv ≫ tensorπ M N ▷ P.X ≫ tensorπ (M ⊗ N) P := by
  rw [Iso.eq_inv_comp, ← tensorπ_associator_hom_hom_assoc, ← comp_hom', Iso.hom_inv_id, id_hom',
    Category.comp_id]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] in
/- The regular module has carrier `A`, so the comparison `toBimodRegularIso` is the identity. -/
private lemma toBimodRegularIso_hom_hom_eq_id : (toBimodRegularIso (A := A)).hom.hom = 𝟙 A :=
  toBimodRegularIso_hom_hom.trans (eqToHom_refl _ _)

/-- The left unitor of `𝟙_ ⊗_A M` is induced by the action `γ[A, M.X]` of `A` on `M`. -/
@[reassoc (attr := simp)]
theorem tensorπ_leftUnitor_hom_hom (M : Mod C A) :
    tensorπ (𝟙_ (Mod C A)) M ≫ (λ_ M).hom.hom = γ[A, M.X] := by
  have h : toBimod.map (λ_ M).hom = (toBimodTensorObjIso (𝟙_ (Mod C A)) M).inv ≫
      (toBimodRegularIso.hom ▷ toBimod.obj M) ≫ (λ_ (toBimod.obj M)).hom := by
    rw [inducingFunctorData.leftUnitor_eq]
    simp [inducingFunctorData]
  replace h := congrArg Bimod.Hom.hom h
  rw [toBimod_map_hom, Bimod.comp_hom', Bimod.comp_hom'] at h
  rw [h, ← Category.assoc, tensorπ_toBimodTensorObjIso_inv_hom, Bimod.π_whiskerRight_hom_assoc,
    Bimod.π_leftUnitor_hom_hom, toBimodRegularIso_hom_hom_eq_id]
  -- This identity of `A` is typed by the carriers of the unit module and of the regular bimodule,
  -- which are `A` only after unfolding, so `id_whiskerRight` is applied up to unfolding.
  exact (congrArg (· ≫ γ[A, M.X]) (id_whiskerRight A M.X)).trans (Category.id_comp _)

/-- The right unitor of `M ⊗_A 𝟙_` is induced by the action of `A` on `M` precomposed with the
inverse braiding. -/
@[reassoc (attr := simp)]
theorem tensorπ_rightUnitor_hom_hom (M : Mod C A) :
    tensorπ M (𝟙_ (Mod C A)) ≫ (ρ_ M).hom.hom = (β_ A M.X).inv ≫ γ[A, M.X] := by
  have h : toBimod.map (ρ_ M).hom = (toBimodTensorObjIso M (𝟙_ (Mod C A))).inv ≫
      (toBimod.obj M ◁ toBimodRegularIso.hom) ≫ (ρ_ (toBimod.obj M)).hom := by
    rw [inducingFunctorData.rightUnitor_eq]
    simp [inducingFunctorData]
  replace h := congrArg Bimod.Hom.hom h
  rw [toBimod_map_hom, Bimod.comp_hom', Bimod.comp_hom'] at h
  rw [h, ← Category.assoc, tensorπ_toBimodTensorObjIso_inv_hom, Bimod.π_whiskerLeft_hom_assoc,
    Bimod.π_rightUnitor_hom_hom, toBimodRegularIso_hom_hom_eq_id]
  -- As for the left unitor, `whiskerLeft_id` is applied up to unfolding the carriers.
  exact (congrArg (· ≫ (β_ A M.X).inv ≫ γ[A, M.X]) (whiskerLeft_id M.X A)).trans
    (Category.id_comp _)

end Mod

end CategoryTheory
