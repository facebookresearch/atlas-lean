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
# Quotient by multiples is left adjoint to scalar forgetting

For a natural ℓ, let Q_ℓ(A)=A/ℓA with its canonical ZMod(ℓ)-module structure. Every additive map
g:A→U(M) to a ZMod(ℓ)-module kills ℓA and descends uniquely to a linear map Q_ℓ(A)→M. This gives
a natural bijection Hom_{ZMod(ℓ)}(Q_ℓ(A),M)≃Hom_Ab(A,U(M)).

Thus Q_ℓ is left adjoint to the underlying abelian-group functor. It preserves colimits,
including cokernels, giving the right-exact coefficient reduction functor in the same carrier
universe.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AddCommGrpCat

universe u

/-- Let ℓ∈ℕ, A be an abelian group in universe u, and M a ZMod(ℓ)-module with carrier in u. Write
Q_ℓ(A)=A/ℓA and U for the abelian-group forgetful functor. For an additive map g:A→U(M), the
subgroup ℓA is contained in ker(g). Indeed g(ℓa)=ℓg(a)=0 because M is a ZMod(ℓ)-module. -/
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

/-- Let ℓ∈ℕ, A be an abelian group in universe u, and M a ZMod(ℓ)-module with carrier in u. Write
Q_ℓ(A)=A/ℓA and U for the abelian-group forgetful functor. For g:A→U(M), the descended map
ḡ:Q_ℓ(A)→M is ZMod(ℓ)-linear and satisfies ḡ([a])=g(a) for every a∈A. An additive map into M
kills ℓA, so this quotient descent is well defined and unique. -/
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

/-- Let ℓ∈ℕ, A be an abelian group in universe u, and M a ZMod(ℓ)-module with carrier in u. Write
Q_ℓ(A)=A/ℓA and U for the abelian-group forgetful functor. The hom-set equivalence
Hom_{ZMod(ℓ)}(Q_ℓ(A),M)≃Hom_Ab(A,U(M)) sends f to f∘q_A. Its inverse sends g to its quotient
descent ḡ, characterized by ḡ(q_A(a))=g(a). -/
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

/-- For any natural ℓ, Q_ℓ:Ab_u→ModuleCat_u(ZMod(ℓ)), A↦A/ℓA, is left adjoint to the abelian-group
forgetful functor U. The adjunction bijection sends f:Q_ℓ(A)→M to f∘q_A:A→U(M), and sends an
additive g to its unique linear quotient descent. -/
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

/-- For ℓ∈ℕ, the functor Q_ℓ from abelian groups to ZMod(ℓ)-modules preserves colimits. If c is a
colimit cocone of an abelian-group diagram D, then its image Q_ℓ(c) is a colimit cocone of
Q_ℓ∘D. This follows from the quotient-by-multiples adjunction. -/
noncomputable instance modQuotientFunctor_preservesColimits (ell : ℕ) :
    PreservesColimitsOfSize (modQuotientFunctor ell) :=
  (modQuotientAdjunction ell).leftAdjoint_preservesColimits

end AddCommGrpCat
