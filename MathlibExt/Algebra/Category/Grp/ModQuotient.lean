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

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Additive groups modulo natural-number multiples

For a natural number `ell`, quotient an additive commutative group by the
subgroup of `ell`-multiples and give the quotient its canonical
`ZMod ell`-module structure.  Additive homomorphisms preserve multiples, so
this construction is an additive functor from additive commutative groups to
`ZMod ell`-modules.

The construction treats `ell = 0` honestly: the quotient is by zero
multiples and `ZMod 0 = ℤ`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace AddCommGrpCat

/-- Subgroup of `ell`-multiples in an additive commutative group. -/
def multiples (A : AddCommGrpCat) (ell : ℕ) : AddSubgroup A :=
  (zsmulAddGroupHom (α := A) (ell : ℤ)).range

/-- The underlying quotient group modulo `ell`-multiples. -/
abbrev ModQuotientCarrier (A : AddCommGrpCat) (ell : ℕ) :=
  A ⧸ multiples A ell

/-- The quotient by `ell`-multiples as a `ZMod ell`-module object. -/
noncomputable def modQuotientObj (A : AddCommGrpCat) (ell : ℕ) :
    ModuleCat (ZMod ell) := by
  letI : Module (ZMod ell) (ModQuotientCarrier A ell) :=
    QuotientAddGroup.zmodModule (H := multiples A ell) (by
      intro x
      exact AddMonoidHom.mem_range.mpr ⟨x, natCast_zsmul x ell⟩)
  exact ModuleCat.of (ZMod ell) (ModQuotientCarrier A ell)

/-- Quotient projection onto the mod-`ell` object. -/
noncomputable def modQuotientMk (A : AddCommGrpCat) (ell : ℕ) :
    A →+ modQuotientObj A ell :=
  QuotientAddGroup.mk' (multiples A ell)

/-- Multiplication by `ell` as an additive endomorphism. -/
def multipleHom (A : AddCommGrpCat) (ell : ℕ) : A →+ A :=
  zsmulAddGroupHom (α := A) (ell : ℤ)

/-- Multiplication by `ell` followed by the quotient projection is exact. -/
theorem multipleHom_modQuotientMk_exact (A : AddCommGrpCat) (ell : ℕ) :
    Function.Exact (multipleHom A ell) (modQuotientMk A ell) := by
  unfold multipleHom modQuotientMk modQuotientObj
  intro y
  constructor
  · intro hy
    exact (QuotientAddGroup.eq_zero_iff (x := y)).mp hy
  · intro hy
    exact (QuotientAddGroup.eq_zero_iff (x := y)).mpr hy

/-- The quotient projection modulo `ell` is surjective. -/
theorem modQuotientMk_surjective (A : AddCommGrpCat) (ell : ℕ) :
    Function.Surjective (modQuotientMk A ell) :=
  QuotientAddGroup.mk'_surjective _

/-- Additive homomorphisms preserve subgroups of `ell`-multiples. -/
theorem multiples_map_le {A B : AddCommGrpCat} (f : A ⟶ B) (ell : ℕ) :
    multiples A ell ≤ AddSubgroup.comap f.hom (multiples B ell) := by
  intro x hx
  rw [multiples] at hx ⊢
  rcases AddMonoidHom.mem_range.mp hx with ⟨y, rfl⟩
  rw [AddSubgroup.mem_comap]
  apply AddMonoidHom.mem_range.mpr
  refine ⟨f y, ?_⟩
  exact (map_zsmul f.hom (ell : ℤ) y).symm

/-- Map on mod-`ell` quotient objects induced by an additive homomorphism. -/
noncomputable def modQuotientMap {A B : AddCommGrpCat}
    (f : A ⟶ B) (ell : ℕ) : modQuotientObj A ell ⟶ modQuotientObj B ell := by
  letI : Module (ZMod ell) (ModQuotientCarrier A ell) :=
    QuotientAddGroup.zmodModule (H := multiples A ell) (by
      intro x
      exact AddMonoidHom.mem_range.mpr ⟨x, natCast_zsmul x ell⟩)
  letI : Module (ZMod ell) (ModQuotientCarrier B ell) :=
    QuotientAddGroup.zmodModule (H := multiples B ell) (by
      intro x
      exact AddMonoidHom.mem_range.mpr ⟨x, natCast_zsmul x ell⟩)
  exact ModuleCat.ofHom
    ((QuotientAddGroup.map (multiples A ell) (multiples B ell)
      f.hom (multiples_map_le f ell)).toZModLinearMap ell)

/-- The induced quotient map computes on representatives. -/
@[simp]
theorem modQuotientMap_mk {A B : AddCommGrpCat}
    (f : A ⟶ B) (ell : ℕ) (x : A) :
    modQuotientMap f ell (modQuotientMk A ell x) =
      modQuotientMk B ell (f x) :=
  by
    unfold modQuotientMap modQuotientMk
    rfl

/-- Quotient by `ell`-multiples as a functor into `ZMod ell`-modules. -/
noncomputable def modQuotientFunctor (ell : ℕ) :
    AddCommGrpCat ⥤ ModuleCat (ZMod ell) where
  obj A := modQuotientObj A ell
  map f := modQuotientMap f ell
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
        change modQuotientMap (𝟙 A) ell (modQuotientMk A ell x) =
          modQuotientMk A ell x
        rw [modQuotientMap_mk]
        rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
        change modQuotientMap (f ≫ g) ell (modQuotientMk X ell x) =
          modQuotientMap g ell
            (modQuotientMap f ell (modQuotientMk X ell x))
        rw [modQuotientMap_mk, modQuotientMap_mk, modQuotientMap_mk]
        rfl

/-- The mod-`ell` quotient functor preserves addition of morphisms. -/
noncomputable instance modQuotientFunctor_additive (ell : ℕ) :
    (modQuotientFunctor ell).Additive where
  map_add := by
    intro A B f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
        change modQuotientMap (f + g) ell (modQuotientMk A ell x) =
          modQuotientMap f ell (modQuotientMk A ell x) +
            modQuotientMap g ell (modQuotientMk A ell x)
        rw [modQuotientMap_mk, modQuotientMap_mk, modQuotientMap_mk]
        rfl

/-- Natural multiplication-by-`ell` endomorphism of additive commutative
groups. -/
def multipleNatTrans (ell : ℕ) :
    𝟭 AddCommGrpCat ⟶ 𝟭 AddCommGrpCat where
  app A := AddCommGrpCat.ofHom (multipleHom A ell)
  naturality {A B} f := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact (map_zsmul f.hom (ell : ℤ) x).symm

/-- Natural quotient map from an additive commutative group to its
underlying mod-`ell` quotient group. -/
noncomputable def modQuotientNatTrans (ell : ℕ) :
    𝟭 AddCommGrpCat ⟶
      modQuotientFunctor ell ⋙
        forget₂ (ModuleCat (ZMod ell)) AddCommGrpCat where
  app A := AddCommGrpCat.ofHom (modQuotientMk A ell)
  naturality {A B} f := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact modQuotientMap_mk f ell x

end AddCommGrpCat
