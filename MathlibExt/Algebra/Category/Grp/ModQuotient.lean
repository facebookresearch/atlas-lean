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
# Abelian groups modulo natural-number multiples

For a natural number ℓ and an abelian group A, the subgroup ℓA is the image of multiplication by
ℓ. The quotient A/ℓA has its canonical ZMod(ℓ)-module structure, and its projection q_A is
surjective with kernel ℓA. Thus A --ℓ→ A --q_A→ A/ℓA→0 is exact at the second A and at the
quotient.

An additive map f:A→B sends ℓA into ℓB and induces the linear quotient map [a]↦[f(a)]. These
maps define an additive functor to ZMod(ℓ)-modules, and multiplication by ℓ and quotient
projection are natural. The construction includes ℓ=0, when ℓA=0 and the scalar ring ZMod(0) is
the integers.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace AddCommGrpCat

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
The subgroup ℓA is the range of the additive endomorphism a↦(ℓ:ℤ)•a. It includes precisely the
elements that are ℓ times another coefficient. -/
def multiples (A : AddCommGrpCat) (ell : ℕ) : AddSubgroup A :=
  (zsmulAddGroupHom (α := A) (ell : ℤ)).range

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
The carrier of the mod-ℓ quotient is the additive quotient group A/ℓA. It retains the
coefficient universe of A and identifies two representatives exactly when their difference
belongs to ℓA. -/
abbrev ModQuotientCarrier (A : AddCommGrpCat) (ell : ℕ) :=
  A ⧸ multiples A ell

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
The object A/ℓA has a canonical ZMod(ℓ)-module structure because ℓ[a]=0 for every quotient
class. It is a module object in the same carrier universe as A, including ℓ=0 with integer
coefficients. -/
noncomputable def modQuotientObj (A : AddCommGrpCat) (ell : ℕ) :
    ModuleCat (ZMod ell) := by
  letI : Module (ZMod ell) (ModQuotientCarrier A ell) :=
    QuotientAddGroup.zmodModule (H := multiples A ell) (by
      intro x
      exact AddMonoidHom.mem_range.mpr ⟨x, natCast_zsmul x ell⟩)
  exact ModuleCat.of (ZMod ell) (ModQuotientCarrier A ell)

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
The additive quotient projection q_A:A→A/ℓA is a↦[a]. Its target is the underlying abelian group
of the canonical ZMod(ℓ)-module object. -/
noncomputable def modQuotientMk (A : AddCommGrpCat) (ell : ℕ) :
    A →+ modQuotientObj A ell :=
  QuotientAddGroup.mk' (multiples A ell)

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
The endomorphism m_ℓ:A→A sends a to ℓa, equivalently (ℓ:ℤ)•a. Its range is the subgroup ℓA and
it is zero when ℓ=0. -/
def multipleHom (A : AddCommGrpCat) (ell : ℕ) : A →+ A :=
  zsmulAddGroupHom (α := A) (ell : ℤ)

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
For m_ℓ(a)=ℓa and q_A(a)=[a], im(m_ℓ)=ker(q_A). Equivalently q_A(b)=0 if and only if b=ℓa for
some a∈A. This is exactness of A --m_ℓ→ A --q_A→ A/ℓA at the middle A. -/
theorem multipleHom_modQuotientMk_exact (A : AddCommGrpCat) (ell : ℕ) :
    Function.Exact (multipleHom A ell) (modQuotientMk A ell) := by
  unfold multipleHom modQuotientMk modQuotientObj
  intro y
  constructor
  · intro hy
    exact (QuotientAddGroup.eq_zero_iff (x := y)).mp hy
  · intro hy
    exact (QuotientAddGroup.eq_zero_iff (x := y)).mpr hy

/-- Let A be an abelian group in its coefficient universe and ℓ a natural number. Put ℓA={ℓa | a∈A}.
The projection q_A:A→A/ℓA is surjective: for every quotient coefficient x there exists a∈A with
q_A(a)=x. -/
theorem modQuotientMk_surjective (A : AddCommGrpCat) (ell : ℕ) :
    Function.Surjective (modQuotientMk A ell) :=
  QuotientAddGroup.mk'_surjective _

/-- For abelian groups A,B, an additive morphism f:A→B, and ℓ∈ℕ, one has ℓA⊆f⁻¹(ℓB). Indeed
f(ℓa)=ℓf(a), so every ℓ-multiple has an ℓ-multiple image. -/
theorem multiples_map_le {A B : AddCommGrpCat} (f : A ⟶ B) (ell : ℕ) :
    multiples A ell ≤ AddSubgroup.comap f.hom (multiples B ell) := by
  intro x hx
  rw [multiples] at hx ⊢
  rcases AddMonoidHom.mem_range.mp hx with ⟨y, rfl⟩
  rw [AddSubgroup.mem_comap]
  apply AddMonoidHom.mem_range.mpr
  refine ⟨f y, ?_⟩
  exact (map_zsmul f.hom (ell : ℤ) y).symm

/-- For abelian groups A,B, an additive morphism f:A→B, and ℓ∈ℕ, the induced map Q_ℓ(f):A/ℓA→B/ℓB is
ZMod(ℓ)-linear. It is obtained by quotient descent using f(ℓA)⊆ℓB. -/
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

/-- For f:A→B additive, ℓ∈ℕ, and a∈A, the induced quotient map satisfies Q_ℓ(f)(q_A(a))=q_B(f(a)).
Thus [a] is sent to [f(a)] in B/ℓB. -/
@[simp]
theorem modQuotientMap_mk {A B : AddCommGrpCat}
    (f : A ⟶ B) (ell : ℕ) (x : A) :
    modQuotientMap f ell (modQuotientMk A ell x) =
      modQuotientMk B ell (f x) :=
  by
    unfold modQuotientMap modQuotientMk
    rfl

/-- For ℓ∈ℕ, the functor Q_ℓ sends an abelian group A to its canonical ZMod(ℓ)-module A/ℓA and an
additive morphism f to [a]↦[f(a)]. These quotient maps preserve identities and composition, with
the coefficient carrier universe retained. -/
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

/-- For ℓ∈ℕ and parallel additive maps f,g:A→B, Q_ℓ(f+g)=Q_ℓ(f)+Q_ℓ(g) as ZMod(ℓ)-linear quotient
maps. On a class [a], both sides are [f(a)+g(a)]. -/
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

/-- For ℓ∈ℕ, the maps m_ℓ^A:A→A form a natural endomorphism of the identity functor on abelian
groups. For every additive f:A→B, m_ℓ^A≫f=f≫m_ℓ^B, since f(ℓa)=ℓf(a). -/
def multipleNatTrans (ell : ℕ) :
    𝟭 AddCommGrpCat ⟶ 𝟭 AddCommGrpCat where
  app A := AddCommGrpCat.ofHom (multipleHom A ell)
  naturality {A B} f := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact (map_zsmul f.hom (ell : ℤ) x).symm

/-- For ℓ∈ℕ, let Q_ℓ:A↦A/ℓA and U forget ZMod(ℓ)-scalar multiplication. The additive projections
q_A:A→U(Q_ℓA) form a natural transformation Id→U∘Q_ℓ. Its square is f≫q_B=q_A≫U(Q_ℓf) for every
additive f:A→B. -/
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
