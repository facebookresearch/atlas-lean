/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.Grp.ModQuotient
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The quotient-by-multiples adjunction

The functor `A ↦ A / ell A` from additive commutative groups to
`ZMod ell`-modules is left adjoint to the additive-group forgetful functor.
Indeed, every additive map from `A` to a `ZMod ell`-module kills
`ell`-multiples and therefore descends uniquely through the quotient.

Consequently the mod-`ell` quotient functor preserves all colimits, in
particular cokernels.  This packages the right exactness needed by
coefficient-reduction arguments in homology.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AddCommGrpCat

universe u

/-- Every additive map into a `ZMod ell`-module kills `ell`-multiples. -/
theorem multiples_le_ker_of_zmod (ell : ℕ) {A : AddCommGrpCat.{u}}
    {M : ModuleCat.{u} (ZMod ell)}
    (g : A ⟶ (forget₂ (ModuleCat (ZMod ell)) AddCommGrpCat).obj M) :
    multiples A ell ≤ g.hom.ker := by
  intro x hx
  rw [multiples] at hx
  rcases AddMonoidHom.mem_range.mp hx with ⟨y, rfl⟩
  rw [AddMonoidHom.mem_ker]
  change g ((ell : ℤ) • y) = 0
  rw [map_zsmul]
  simpa using ZModModule.char_nsmul_eq_zero ell (show M from g y)

/-- Descent of an additive homomorphism into a `ZMod ell`-module through
the quotient by `ell`-multiples. -/
noncomputable def modQuotientDesc (ell : ℕ) {A : AddCommGrpCat.{u}}
    {M : ModuleCat.{u} (ZMod ell)}
    (g : A ⟶ (forget₂ (ModuleCat (ZMod ell)) AddCommGrpCat).obj M) :
    modQuotientObj A ell ⟶ M := by
  letI : Module (ZMod ell) (ModQuotientCarrier A ell) :=
    QuotientAddGroup.zmodModule (H := multiples A ell) (by
      intro x
      exact AddMonoidHom.mem_range.mpr ⟨x, natCast_zsmul x ell⟩)
  let g' : A →+ M := g.hom
  let h : ModQuotientCarrier A ell →+ M :=
    QuotientAddGroup.lift (multiples A ell) g'
      (multiples_le_ker_of_zmod ell g)
  let hlin : ModQuotientCarrier A ell →ₗ[ZMod ell] M :=
    h.toZModLinearMap ell
  exact ModuleCat.ofHom hlin

@[simp]
theorem modQuotientDesc_mk (ell : ℕ) {A : AddCommGrpCat.{u}}
    {M : ModuleCat.{u} (ZMod ell)}
    (g : A ⟶ (forget₂ (ModuleCat (ZMod ell)) AddCommGrpCat).obj M)
    (x : A) :
    (modQuotientDesc ell g).hom (modQuotientMk A ell x) = g x := by
  unfold modQuotientDesc
  dsimp only
  change (QuotientAddGroup.lift (multiples A ell) g.hom
      (multiples_le_ker_of_zmod ell g))
      (QuotientAddGroup.mk' (multiples A ell) x) = g x
  exact QuotientAddGroup.lift_mk' _ _ x

/-- The hom-set equivalence underlying the quotient-by-`ell` adjunction. -/
noncomputable def modQuotientHomEquiv (ell : ℕ)
    (A : AddCommGrpCat.{u}) (M : ModuleCat.{u} (ZMod ell)) :
    ((modQuotientFunctor ell).obj A ⟶ M) ≃
      (A ⟶ (forget₂ (ModuleCat (ZMod ell)) AddCommGrpCat).obj M) where
  toFun f := AddCommGrpCat.ofHom
    (f.hom.toAddMonoidHom.comp (modQuotientMk A ell))
  invFun g := modQuotientDesc ell g
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
        change (modQuotientDesc ell
          (AddCommGrpCat.ofHom
            (f.hom.toAddMonoidHom.comp (modQuotientMk A ell)))).hom
              (modQuotientMk A ell x) = f (modQuotientMk A ell x)
        rw [modQuotientDesc_mk]
        rfl
  right_inv g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change (modQuotientDesc ell g).hom
      (modQuotientMk A ell x) = g x
    exact modQuotientDesc_mk ell g x

/-- Quotient by `ell`-multiples is left adjoint to forgetting the
`ZMod ell`-module structure. -/
noncomputable def modQuotientAdjunction (ell : ℕ) :
    modQuotientFunctor ell ⊣
      forget₂ (ModuleCat (ZMod ell)) AddCommGrpCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := modQuotientHomEquiv ell
      homEquiv_naturality_left_symm := by
        intro A' A M f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro q
        induction q using QuotientAddGroup.induction_on with
        | H x =>
            change (modQuotientDesc ell (f ≫ g)).hom
                (modQuotientMk A' ell x) =
              (modQuotientDesc ell g).hom
                (modQuotientMap f ell (modQuotientMk A' ell x))
            rw [modQuotientDesc_mk, modQuotientMap_mk,
              modQuotientDesc_mk]
            rfl
      homEquiv_naturality_right := by
        intro A M M' f g
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        rfl }

/-- The quotient-by-`ell` functor preserves all colimits. -/
noncomputable instance modQuotientFunctor_preservesColimits (ell : ℕ) :
    PreservesColimitsOfSize (modQuotientFunctor ell) :=
  (modQuotientAdjunction ell).leftAdjoint_preservesColimits

end AddCommGrpCat
