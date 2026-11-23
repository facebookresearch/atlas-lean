/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Algebra.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Symmetric
public import MathlibExt.CategoryTheory.Monoidal.Mon

/-!
# Commutative monoids under a commutative monoid as monoids of modules

Let `A` be a commutative monoid object of a braided monoidal category `C`, and `f : A ⟶ B` a
morphism of monoids into a commutative monoid `B`. Restricting the regular `B`-module along `f`
makes `B` an `A`-module (`Mod.comapRegular f`), acting by `f ▷ B ≫ μ`. Its multiplication
`μ : B ⊗ B ⟶ B` identifies the two actions of `A` on `B ⊗ B`, so it descends to the balanced
tensor product `B ⊗_A B`. With unit `f : A ⟶ B` this makes `B` a monoid object of `Mod C A`
(`Mod.monObjComapRegular`), which is commutative when `C` is symmetric
(`Mod.isCommMonObjComapRegular`).

On representatives the multiplication is that of `B` (`Mod.tensorπ_comapRegular_mul_hom`), and
the unit is `f` (`Mod.comapRegular_one_hom`). For symmetric spectra, `A` is the sphere and this
makes a commutative monoid of symmetric sequences under the sphere a commutative ring spectrum.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.2.
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonObj BraidedCategory Limits

namespace Mod

section comapRegular

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A B : C} [MonObj A] [MonObj B]
  (f : A ⟶ B) [IsMonHom f]

/-- The monoid `B` as an `A`-module through `f : A ⟶ B`: the restriction along `f` of the regular
`B`-module. -/
-- Written as a structure with an explicit underlying object, exposed and implicitly reducible, so
-- that its underlying object is `B` and morphisms of `B` may be used as morphisms of this module.
@[expose, implicit_reducible]
def comapRegular : Mod C A :=
  letI := ModObj.regular B
  letI := scalarRestriction f B
  ⟨B⟩

/-- `comapRegular f` is the restriction along `f` of the regular `B`-module. -/
lemma comapRegular_eq : comapRegular f = (comap f).obj (regular B) :=
  (rfl)

@[simp]
lemma comapRegular_X : (comapRegular f).X = B :=
  (rfl)

/-- `A` acts on `B` through `f`, followed by the multiplication of `B`. -/
lemma comapRegular_smul : γ[A, (comapRegular f).X] = f ▷ B ≫ μ :=
  (rfl)

end comapRegular

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A] {B : C} [MonObj B] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [IsCommMonObj A] in
/- The multiplication of `B` identifies the two actions of `A` on `B ⊗ B`. -/
private lemma mul_tensorπ_condition :
    ((β_ A (comapRegular f).X).inv ≫ γ[A, (comapRegular f).X]) ▷ (comapRegular f).X ≫
        (μ : B ⊗ B ⟶ B) =
      (α_ (comapRegular f).X A (comapRegular f).X).hom ≫
        (comapRegular f).X ◁ γ[A, (comapRegular f).X] ≫ (μ : B ⊗ B ⟶ B) := by
  -- The action on `comapRegular f` is `f ▷ B ≫ μ` only after unfolding, so the statement is
  -- restated in `C` before rewriting.
  change ((β_ A B).inv ≫ f ▷ B ≫ μ) ▷ B ≫ μ = (α_ B A B).hom ≫ B ◁ (f ▷ B ≫ μ) ≫ μ
  rw [braiding_inv_whiskerRight_mul, whiskerLeft_comp_assoc, mul_assoc_flip,
    associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc, comp_whiskerRight_assoc]

/-- The multiplication of `B`, descended to the balanced tensor product `B ⊗_A B`. -/
noncomputable def comapRegularMul : comapRegular f ⊗ comapRegular f ⟶ comapRegular f :=
  Hom.mk' (tensorDesc (μ : B ⊗ B ⟶ B) (mul_tensorπ_condition f)) (by
    rw [← cancel_epi (A ◁ tensorπ _ _), whiskerLeft_tensorπ_smul_assoc, tensorπ_tensorDesc,
      selfLeftAction_actionHomRight, whiskerLeft_tensorπ_tensorDesc_assoc]
    -- Rewriting with `comapRegular_smul` leaves `(comapRegular f).X` in the associators and
    -- whiskerings, where the naturality lemmas need `B` syntactically, and `comapRegular_X`
    -- cannot be rewritten there (the motive is not type correct). So the goal is restated in `C`.
    change (α_ A B B).inv ≫ (f ▷ B ≫ μ) ▷ B ≫ μ = A ◁ μ ≫ f ▷ B ≫ μ
    rw [comp_whiskerRight_assoc, MonObj.mul_assoc, ← associator_inv_naturality_left_assoc,
      Iso.inv_hom_id_assoc, whisker_exchange_assoc])

/-- A commutative monoid `B` under a commutative monoid `A` is a monoid object of `A`-modules, with
multiplication that of `B` on representatives and unit `f : A ⟶ B`. -/
noncomputable instance monObjComapRegular : MonObj (comapRegular f) where
  one := Hom.mk' (M := 𝟙_ (Mod C A)) f (by
    rw [comapRegular_smul]
    exact (IsMonHom.mul_hom f).trans (by rw [tensorHom_def', Category.assoc]; rfl))
  mul := comapRegularMul f
  one_mul := by
    ext
    simp only [comapRegularMul, comp_hom', tensorπ_whiskerRight_hom_assoc, Hom.mk'_hom,
      tensorπ_tensorDesc, tensorπ_leftUnitor_hom_hom]
    rfl
  mul_one := by
    ext
    simp only [comapRegularMul, comp_hom', tensorπ_whiskerLeft_hom_assoc, Hom.mk'_hom,
      tensorπ_tensorDesc, tensorπ_rightUnitor_hom_hom]
    exact (braiding_inv_whiskerRight_mul f).symm
  mul_assoc := by
    apply hom_ext
    rw [← cancel_epi (tensorπ _ _ ▷ _ ≫ tensorπ _ _)]
    simp [comapRegularMul, tensorπ_associator_hom_hom_assoc, MonObj.mul_assoc]

/-- On representatives, the multiplication `B ⊗_A B ⟶ B` is the multiplication of `B`. -/
@[reassoc (attr := simp)]
lemma tensorπ_comapRegular_mul_hom :
    tensorπ _ _ ≫ (μ : comapRegular f ⊗ comapRegular f ⟶ _).hom = (μ : B ⊗ B ⟶ B) :=
  tensorπ_tensorDesc _ _

/-- The unit of `B` as a monoid of `A`-modules is `f : A ⟶ B`. -/
@[simp]
lemma comapRegular_one_hom : (η : 𝟙_ (Mod C A) ⟶ comapRegular f).hom = f :=
  (rfl)

end Braided

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A] {B : C} [MonObj B] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f]

/-- A commutative monoid `B` under a commutative monoid `A` is a commutative monoid object of
`A`-modules. -/
instance isCommMonObjComapRegular : IsCommMonObj (comapRegular f) where
  mul_comm := by
    ext
    simp only [comp_hom', tensorπ_braiding_hom_hom_assoc, tensorπ_comapRegular_mul_hom]
    exact IsCommMonObj.mul_comm B

end Symmetric

end Mod

end CategoryTheory
