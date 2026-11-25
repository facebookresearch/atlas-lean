/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import Mathlib.Algebra.Exact.Basic

/-!
# Concrete extensions of C-star algebras

A concrete extension of `A` by `B` is normalized by an actual middle
nonunital C-star algebra, a closed two-sided star ideal identified with `B`,
and an explicit equivalence from the canonical ideal quotient to `A`.

The inclusion, quotient map, and their exactness are derived from this data;
they are not stored as theorem fields.  Quotient C-star structures are
activated only locally.  Morphisms and equivalences retain independent
universes for both endpoints and both middle algebras.
-/

@[expose] public section

open Set
open scoped CStarAlgebra

universe uA uB uE uA' uB' uE' uA'' uB'' uE''

/-- **Normalized C*-algebra extension.** For nonunital complex C*-algebras `A,B`, a normalized extension
of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and quotient
identified with `A`, giving `0 → B → E → A → 0`. The endpoint identifications are complex
star-algebra equivalences. -/
structure CStarExtension
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  /-- The middle C-star algebra. -/
  Middle : Type uE
  /-- The C-star structure on the middle algebra. -/
  [middleCStar : NonUnitalCStarAlgebra Middle]
  /-- The distinguished closed two-sided ideal in the middle algebra. -/
  ideal : ClosedStarIdeal Middle
  /-- Identification of the ideal coefficient with the distinguished ideal. -/
  idealEquiv : B ≃⋆ₐ[ℂ] ideal.carrier
  /-- Identification of the canonical ideal quotient with the quotient coefficient. -/
  quotientEquiv :
    let _ : NonUnitalCStarAlgebra ideal.Quotient := ideal.quotientCStarAlgebra
    ideal.Quotient ≃⋆ₐ[ℂ] A

namespace CStarExtension

attribute [instance] CStarExtension.middleCStar

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Ideal inclusion in a C*-extension.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. Its ideal identification gives the
nonunital complex star homomorphism `B → E`. -/
noncomputable def inclusion (X : CStarExtension A B) :
    B →⋆ₙₐ[ℂ] X.Middle :=
  (NonUnitalStarSubalgebraClass.subtype X.ideal.carrier).comp
    X.idealEquiv.toNonUnitalStarAlgHom

@[simp]
theorem inclusion_apply (X : CStarExtension A B) (b : B) :
    X.inclusion b = (X.idealEquiv b : X.Middle) :=
  rfl

/-- **Quotient projection in a C*-extension.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. Its quotient identification gives the
nonunital complex star homomorphism `E → A`. -/
noncomputable def quotient (X : CStarExtension A B) :
    X.Middle →⋆ₙₐ[ℂ] A := by
  let _ : X.ideal.carrier.IsTwoSided := X.ideal.isTwoSided
  let _ : NonUnitalCStarAlgebra X.ideal.Quotient :=
    X.ideal.quotientCStarAlgebra
  exact X.quotientEquiv.toNonUnitalStarAlgHom.comp X.ideal.quotientMap

@[simp]
theorem quotient_apply (X : CStarExtension A B) (e : X.Middle) :
    X.quotient e = X.quotientEquiv (X.ideal.quotientMap e) :=
  rfl

theorem inclusion_injective (X : CStarExtension A B) :
    Function.Injective X.inclusion := by
  intro b c hbc
  apply X.idealEquiv.injective
  apply Subtype.ext
  exact hbc

theorem quotient_surjective (X : CStarExtension A B) :
    Function.Surjective X.quotient := by
  let _ : X.ideal.carrier.IsTwoSided := X.ideal.isTwoSided
  let _ : NonUnitalCStarAlgebra X.ideal.Quotient :=
    X.ideal.quotientCStarAlgebra
  intro a
  obtain ⟨x, rfl⟩ := X.quotientEquiv.surjective a
  obtain ⟨e, rfl⟩ := X.ideal.quotientMap_surjective x
  exact ⟨e, rfl⟩

@[simp]
theorem quotient_eq_zero_iff (X : CStarExtension A B) (e : X.Middle) :
    X.quotient e = 0 ↔ e ∈ X.ideal := by
  let _ : X.ideal.carrier.IsTwoSided := X.ideal.isTwoSided
  let _ : NonUnitalCStarAlgebra X.ideal.Quotient :=
    X.ideal.quotientCStarAlgebra
  constructor
  · intro he
    change X.quotientEquiv (X.ideal.quotientMap e) = 0 at he
    apply (X.ideal.quotientMap_eq_zero_iff e).mp
    have hx := congrArg (fun a ↦ X.quotientEquiv.symm a) he
    simpa using hx
  · intro he
    change X.quotientEquiv (X.ideal.quotientMap e) = 0
    rw [(X.ideal.quotientMap_eq_zero_iff e).mpr he, map_zero]

/-- **Exactness of the normalized extension maps.** For nonunital complex C*-algebras `A,B`, a
normalized extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified
with `B` and quotient identified with `A`, giving `0 → B → E → A → 0`. The image of `B → E` equals
the kernel of `E → A`. -/
theorem exact (X : CStarExtension A B) :
    Function.Exact X.inclusion X.quotient := by
  intro e
  rw [X.quotient_eq_zero_iff]
  constructor
  · intro he
    obtain ⟨b, hb⟩ := X.idealEquiv.surjective ⟨e, he⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, rfl⟩
    exact (X.idealEquiv b).property

@[simp]
theorem quotient_comp_inclusion (X : CStarExtension A B) :
    X.quotient.comp X.inclusion = 0 := by
  apply NonUnitalStarAlgHom.ext
  intro b
  exact X.exact.apply_apply_eq_zero b

theorem range_inclusion (X : CStarExtension A B) :
    Set.range X.inclusion = {e : X.Middle | X.quotient e = 0} := by
  ext e
  exact (X.exact e).symm

/-! ## Morphisms of normalized extensions -/

variable {A' : Type uA'} {B' : Type uB'}
variable [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B']

/-- **Morphism of normalized C*-extensions.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. A morphism to another such extension
consists of nonunital star homomorphisms on both endpoints and on the middle algebra, making both
squares commute. -/
structure Hom (X : CStarExtension A B) (Y : CStarExtension A' B') where
  idealMap : B →⋆ₙₐ[ℂ] B'
  middleMap : X.Middle →⋆ₙₐ[ℂ] Y.Middle
  quotientMap : A →⋆ₙₐ[ℂ] A'
  inclusion_commutes :
    middleMap.comp X.inclusion = Y.inclusion.comp idealMap
  quotient_commutes :
    Y.quotient.comp middleMap = quotientMap.comp X.quotient

namespace Hom

variable {X : CStarExtension A B} {Y : CStarExtension A' B'}

@[simp]
theorem inclusion_commutes_apply (f : CStarExtension.Hom X Y) (b : B) :
    f.middleMap (X.inclusion b) = Y.inclusion (f.idealMap b) :=
  DFunLike.congr_fun f.inclusion_commutes b

@[simp]
theorem quotient_commutes_apply (f : CStarExtension.Hom X Y) (e : X.Middle) :
    Y.quotient (f.middleMap e) = f.quotientMap (X.quotient e) :=
  DFunLike.congr_fun f.quotient_commutes e

@[ext (iff := false)]
theorem ext {f g : CStarExtension.Hom X Y}
    (hideal : f.idealMap = g.idealMap)
    (hmiddle : f.middleMap = g.middleMap)
    (hquotient : f.quotientMap = g.quotientMap) : f = g := by
  cases f
  cases g
  cases hideal
  cases hmiddle
  cases hquotient
  rfl

/-- **Identity morphism of a C*-extension.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. The identity maps on the endpoints and
middle algebra form its identity extension morphism. -/
def id (X : CStarExtension A B) : CStarExtension.Hom X X where
  idealMap := NonUnitalStarAlgHom.id ℂ B
  middleMap := NonUnitalStarAlgHom.id ℂ X.Middle
  quotientMap := NonUnitalStarAlgHom.id ℂ A
  inclusion_commutes := by ext; rfl
  quotient_commutes := by ext; rfl

variable {A'' : Type uA''} {B'' : Type uB''}
variable [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B'']
variable {Z : CStarExtension A'' B''}

/-- **Composition of C*-extension morphisms.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. Compatible extension morphisms compose by
composing their endpoint and middle star homomorphisms. -/
def comp (g : CStarExtension.Hom Y Z) (f : CStarExtension.Hom X Y) :
    CStarExtension.Hom X Z where
  idealMap := g.idealMap.comp f.idealMap
  middleMap := g.middleMap.comp f.middleMap
  quotientMap := g.quotientMap.comp f.quotientMap
  inclusion_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro b
    simp only [NonUnitalStarAlgHom.comp_apply]
    rw [f.inclusion_commutes_apply, g.inclusion_commutes_apply]
  quotient_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro e
    simp only [NonUnitalStarAlgHom.comp_apply]
    rw [g.quotient_commutes_apply, f.quotient_commutes_apply]

@[simp]
theorem comp_idealMap_apply (g : CStarExtension.Hom Y Z)
    (f : CStarExtension.Hom X Y) (b : B) :
    (comp g f).idealMap b = g.idealMap (f.idealMap b) :=
  rfl

@[simp]
theorem comp_middleMap_apply (g : CStarExtension.Hom Y Z)
    (f : CStarExtension.Hom X Y) (e : X.Middle) :
    (comp g f).middleMap e = g.middleMap (f.middleMap e) :=
  rfl

@[simp]
theorem comp_quotientMap_apply (g : CStarExtension.Hom Y Z)
    (f : CStarExtension.Hom X Y) (a : A) :
    (comp g f).quotientMap a = g.quotientMap (f.quotientMap a) :=
  rfl

@[simp]
theorem id_comp (f : CStarExtension.Hom X Y) : comp (id Y) f = f := by
  apply CStarExtension.Hom.ext <;> apply NonUnitalStarAlgHom.ext <;> intro <;> rfl

@[simp]
theorem comp_id (f : CStarExtension.Hom X Y) : comp f (id X) = f := by
  apply CStarExtension.Hom.ext <;> apply NonUnitalStarAlgHom.ext <;> intro <;> rfl

variable {A''' : Type*} {B''' : Type*}
variable [NonUnitalCStarAlgebra A'''] [NonUnitalCStarAlgebra B''']
variable {W : CStarExtension A''' B'''}

theorem comp_assoc (h : CStarExtension.Hom Z W)
    (g : CStarExtension.Hom Y Z) (f : CStarExtension.Hom X Y) :
    comp h (comp g f) = comp (comp h g) f := by
  apply CStarExtension.Hom.ext <;> apply NonUnitalStarAlgHom.ext <;> intro <;> rfl

end Hom

/-! ## Equivalences of normalized extensions -/

/-- **Equivalence of normalized C*-extensions.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. An equivalence consists of star-algebra
equivalences on the endpoints and middle algebra, compatible with the inclusion and quotient maps. -/
structure Equiv (X : CStarExtension A B) (Y : CStarExtension A' B') where
  idealEquiv : B ≃⋆ₐ[ℂ] B'
  middleEquiv : X.Middle ≃⋆ₐ[ℂ] Y.Middle
  quotientEquiv : A ≃⋆ₐ[ℂ] A'
  inclusion_commutes :
    middleEquiv.toNonUnitalStarAlgHom.comp X.inclusion =
      Y.inclusion.comp idealEquiv.toNonUnitalStarAlgHom
  quotient_commutes :
    Y.quotient.comp middleEquiv.toNonUnitalStarAlgHom =
      quotientEquiv.toNonUnitalStarAlgHom.comp X.quotient

namespace Equiv

variable {X : CStarExtension A B} {Y : CStarExtension A' B'}

@[simp]
theorem inclusion_commutes_apply (f : CStarExtension.Equiv X Y) (b : B) :
    f.middleEquiv (X.inclusion b) = Y.inclusion (f.idealEquiv b) :=
  DFunLike.congr_fun f.inclusion_commutes b

@[simp]
theorem quotient_commutes_apply (f : CStarExtension.Equiv X Y) (e : X.Middle) :
    Y.quotient (f.middleEquiv e) = f.quotientEquiv (X.quotient e) :=
  DFunLike.congr_fun f.quotient_commutes e

@[ext (iff := false)]
theorem ext {f g : CStarExtension.Equiv X Y}
    (hideal : f.idealEquiv = g.idealEquiv)
    (hmiddle : f.middleEquiv = g.middleEquiv)
    (hquotient : f.quotientEquiv = g.quotientEquiv) : f = g := by
  cases f
  cases g
  cases hideal
  cases hmiddle
  cases hquotient
  rfl

/-- **Morphisms underlying extension equivalences.** For nonunital complex C*-algebras `A,B`, a
normalized extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified
with `B` and quotient identified with `A`, giving `0 → B → E → A → 0`. An equivalence of normalized
extensions gives a morphism by taking the nonunital star homomorphisms underlying its three
equivalences. -/
def toHom (f : CStarExtension.Equiv X Y) : CStarExtension.Hom X Y where
  idealMap := f.idealEquiv.toNonUnitalStarAlgHom
  middleMap := f.middleEquiv.toNonUnitalStarAlgHom
  quotientMap := f.quotientEquiv.toNonUnitalStarAlgHom
  inclusion_commutes := f.inclusion_commutes
  quotient_commutes := f.quotient_commutes

/-- **Reflexive equivalence of a C*-extension.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. The identity star-algebra equivalences on
its three algebras give its reflexive extension equivalence. -/
def refl (X : CStarExtension A B) : CStarExtension.Equiv X X where
  idealEquiv := StarAlgEquiv.refl ℂ B
  middleEquiv := StarAlgEquiv.refl ℂ X.Middle
  quotientEquiv := StarAlgEquiv.refl ℂ A
  inclusion_commutes := by ext; rfl
  quotient_commutes := by ext; rfl

/-- **Inverse of a C*-extension equivalence.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. Inverting the three star-algebra
equivalences gives an equivalence in the opposite direction. -/
def symm (f : CStarExtension.Equiv X Y) : CStarExtension.Equiv Y X where
  idealEquiv := f.idealEquiv.symm
  middleEquiv := f.middleEquiv.symm
  quotientEquiv := f.quotientEquiv.symm
  inclusion_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro b
    simp only [NonUnitalStarAlgHom.comp_apply]
    apply f.middleEquiv.injective
    change f.middleEquiv (f.middleEquiv.symm (Y.inclusion b)) =
      f.middleEquiv (X.inclusion (f.idealEquiv.symm b))
    rw [f.middleEquiv.apply_symm_apply, f.inclusion_commutes_apply,
      f.idealEquiv.apply_symm_apply]
  quotient_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro e
    simp only [NonUnitalStarAlgHom.comp_apply]
    apply f.quotientEquiv.injective
    change f.quotientEquiv (X.quotient (f.middleEquiv.symm e)) =
      f.quotientEquiv (f.quotientEquiv.symm (Y.quotient e))
    rw [f.quotientEquiv.apply_symm_apply]
    simpa using (f.quotient_commutes_apply (f.middleEquiv.symm e)).symm

variable {A'' : Type uA''} {B'' : Type uB''}
variable [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B'']
variable {Z : CStarExtension A'' B''}

/-- **Composition of C*-extension equivalences.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. Two consecutive extension equivalences
compose by composing their endpoint and middle equivalences. -/
def trans (f : CStarExtension.Equiv X Y) (g : CStarExtension.Equiv Y Z) :
    CStarExtension.Equiv X Z where
  idealEquiv := f.idealEquiv.trans g.idealEquiv
  middleEquiv := f.middleEquiv.trans g.middleEquiv
  quotientEquiv := f.quotientEquiv.trans g.quotientEquiv
  inclusion_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro b
    simp only [StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.trans_apply]
    rw [f.inclusion_commutes_apply, g.inclusion_commutes_apply]
  quotient_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro e
    simp only [StarAlgEquiv.toNonUnitalStarAlgHom_apply,
      NonUnitalStarAlgHom.comp_apply, StarAlgEquiv.trans_apply]
    rw [g.quotient_commutes_apply, f.quotient_commutes_apply]

@[simp]
theorem toHom_refl (X : CStarExtension A B) : (refl X).toHom = Hom.id X :=
  rfl

@[simp]
theorem toHom_trans (f : Equiv X Y) (g : Equiv Y Z) :
    (trans f g).toHom = Hom.comp g.toHom f.toHom :=
  rfl

@[simp]
theorem symm_symm (f : CStarExtension.Equiv X Y) : symm (symm f) = f := by
  apply CStarExtension.Equiv.ext
  · exact StarAlgEquiv.symm_symm f.idealEquiv
  · exact StarAlgEquiv.symm_symm f.middleEquiv
  · exact StarAlgEquiv.symm_symm f.quotientEquiv

@[simp]
theorem refl_trans (f : CStarExtension.Equiv X Y) : trans (refl X) f = f := by
  apply CStarExtension.Equiv.ext <;> apply StarAlgEquiv.ext <;> intro <;> rfl

@[simp]
theorem trans_refl (f : CStarExtension.Equiv X Y) : trans f (refl Y) = f := by
  apply CStarExtension.Equiv.ext <;> apply StarAlgEquiv.ext <;> intro <;> rfl

variable {A''' : Type*} {B''' : Type*}
variable [NonUnitalCStarAlgebra A'''] [NonUnitalCStarAlgebra B''']
variable {W : CStarExtension A''' B'''}

theorem trans_assoc (f : CStarExtension.Equiv X Y)
    (g : CStarExtension.Equiv Y Z) (h : CStarExtension.Equiv Z W) :
    trans (trans f g) h = trans f (trans g h) := by
  apply CStarExtension.Equiv.ext <;> apply StarAlgEquiv.ext <;> intro <;> rfl

end Equiv

/-- **Strong equivalence of C*-extensions.** For nonunital complex C*-algebras `A,B`, a normalized
extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and
quotient identified with `A`, giving `0 → B → E → A → 0`. An equivalence between two extensions with
the same endpoints is strong when both endpoint equivalences are identities. -/
def Equiv.IsStrong {X Y : CStarExtension A B} (f : Equiv X Y) : Prop :=
  f.idealEquiv = StarAlgEquiv.refl ℂ B ∧
    f.quotientEquiv = StarAlgEquiv.refl ℂ A

/-! ## Construction from an exact pair -/

variable {E : Type uE} [NonUnitalCStarAlgebra E]

/-- **Normalizing an exact pair of C*-homomorphisms.** Let `A,B,E` be nonunital complex C*-algebras, and
let `j : B → E`, `q : E → A` be nonunital complex star homomorphisms. If `j` is injective, `q` is
surjective, and `range(j) = ker(q)`, they determine a normalized extension of `A` by `B`, with
middle algebra `E`. -/
noncomputable def ofExact
    (j : B →⋆ₙₐ[ℂ] E) (q : E →⋆ₙₐ[ℂ] A)
    (hj : Function.Injective j) (hq : Function.Surjective q)
    (hexact : Function.Exact j q) : CStarExtension.{uA, uB, uE} A B := by
  let jKer : B →⋆ₙₐ[ℂ] (ClosedStarIdeal.ker q).carrier :=
    NonUnitalStarAlgHom.codRestrict j (ClosedStarIdeal.ker q).carrier fun b ↦
      (ClosedStarIdeal.mem_ker q (j b)).2 ((hexact (j b)).2 ⟨b, rfl⟩)
  have hjKer : Function.Injective jKer := fun b c hbc ↦
    hj (congrArg Subtype.val hbc)
  have hjKer_surjective : Function.Surjective jKer := by
    intro x
    have hx0 : q x = 0 := (ClosedStarIdeal.mem_ker q x).1 x.property
    obtain ⟨b, hb⟩ := (hexact x).1 hx0
    exact ⟨b, Subtype.ext hb⟩
  exact
    { Middle := E
      middleCStar := inferInstance
      ideal := ClosedStarIdeal.ker q
      idealEquiv := StarAlgEquiv.ofBijective jKer ⟨hjKer, hjKer_surjective⟩
      quotientEquiv := NonUnitalStarAlgHom.quotientKerEquivOfSurjective q hq }

@[simp]
theorem ofExact_inclusion_apply
    (j : B →⋆ₙₐ[ℂ] E) (q : E →⋆ₙₐ[ℂ] A)
    (hj : Function.Injective j) (hq : Function.Surjective q)
    (hexact : Function.Exact j q) (b : B) :
    (ofExact j q hj hq hexact).inclusion b = j b :=
  rfl

@[simp]
theorem ofExact_quotient_apply
    (j : B →⋆ₙₐ[ℂ] E) (q : E →⋆ₙₐ[ℂ] A)
    (hj : Function.Injective j) (hq : Function.Surjective q)
    (hexact : Function.Exact j q) (e : E) :
    (ofExact j q hj hq hexact).quotient e = q e := by
  change NonUnitalStarAlgHom.quotientKerEquivOfSurjective q hq
      ((ClosedStarIdeal.ker q).quotientMap e) = q e
  exact NonUnitalStarAlgHom.quotientKerEquivOfSurjective_quotientMap q hq e

theorem ofExact_inclusion
    (j : B →⋆ₙₐ[ℂ] E) (q : E →⋆ₙₐ[ℂ] A)
    (hj : Function.Injective j) (hq : Function.Surjective q)
    (hexact : Function.Exact j q) :
    (ofExact j q hj hq hexact).inclusion = j := by
  ext b
  exact ofExact_inclusion_apply j q hj hq hexact b

theorem ofExact_quotient
    (j : B →⋆ₙₐ[ℂ] E) (q : E →⋆ₙₐ[ℂ] A)
    (hj : Function.Injective j) (hq : Function.Surjective q)
    (hexact : Function.Exact j q) :
    (ofExact j q hj hq hexact).quotient = q := by
  ext e
  exact ofExact_quotient_apply j q hj hq hexact e

/-- **Equivalence with the normalization of an extension.** For nonunital complex C*-algebras `A,B`, a
normalized extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified
with `B` and quotient identified with `A`, giving `0 → B → E → A → 0`. Normalizing its own inclusion
and quotient maps gives a strongly equivalent extension, with the identity on the middle algebra. -/
noncomputable def normalizationEquiv
    (X : CStarExtension.{uA, uB, uE} A B) :
    Equiv X (ofExact X.inclusion X.quotient X.inclusion_injective
      X.quotient_surjective X.exact) where
  idealEquiv := StarAlgEquiv.refl ℂ B
  middleEquiv := by
    change X.Middle ≃⋆ₐ[ℂ] X.Middle
    exact StarAlgEquiv.refl ℂ X.Middle
  quotientEquiv := StarAlgEquiv.refl ℂ A
  inclusion_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro b
    change X.inclusion b =
      (ofExact X.inclusion X.quotient X.inclusion_injective
        X.quotient_surjective X.exact).inclusion b
    rw [ofExact_inclusion_apply]
  quotient_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro e
    change (ofExact X.inclusion X.quotient X.inclusion_injective
      X.quotient_surjective X.exact).quotient e = X.quotient e
    rw [ofExact_quotient_apply]

theorem normalizationEquiv_isStrong
    (X : CStarExtension.{uA, uB, uE} A B) :
    (normalizationEquiv X).IsStrong :=
  ⟨rfl, rfl⟩

/-- **Uniqueness of the normalization equivalence.** For nonunital complex C*-algebras `A,B`, a
normalized extension of `A` by `B` is a middle C*-algebra `E` with a closed star ideal identified
with `B` and quotient identified with `A`, giving `0 → B → E → A → 0`. Among equivalences to the
normalization, the normalization equivalence is the unique strong equivalence whose middle map is
the identity. -/
theorem normalizationEquiv_unique
    (X : CStarExtension.{uA, uB, uE} A B)
    (f : Equiv X (ofExact X.inclusion X.quotient X.inclusion_injective
      X.quotient_surjective X.exact))
    (hstrong : f.IsStrong) (hmiddle : ∀ e, f.middleEquiv e = e) :
    f = normalizationEquiv X := by
  apply CStarExtension.Equiv.ext
  · exact hstrong.1
  · apply StarAlgEquiv.ext
    intro e
    exact hmiddle e
  · exact hstrong.2

/-! ## The product extension -/

/-- **Product C*-extension.** For nonunital complex C*-algebras `A,B`, a normalized extension of `A` by
`B` is a middle C*-algebra `E` with a closed star ideal identified with `B` and quotient identified
with `A`, giving `0 → B → E → A → 0`. The direct product gives the normalized extension `0 → B → A ×
B → A → 0`, with inclusion `b ↦ (0,b)` and projection `(a,b) ↦ a`. -/
noncomputable def product (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    CStarExtension A B :=
  ofExact (NonUnitalStarAlgHom.inl ℂ B A)
    (NonUnitalStarAlgHom.snd ℂ B A)
    (fun _ _ h ↦ congrArg Prod.fst h)
    (fun a ↦ ⟨(0, a), rfl⟩)
    (by
      rintro ⟨b, a⟩
      constructor
      · intro ha
        exact ⟨b, Prod.ext rfl ha.symm⟩
      · rintro ⟨c, hc⟩
        exact (congrArg Prod.snd hc).symm)

@[simp]
theorem product_inclusion_apply (b : B) :
    (product A B).inclusion b = (b, 0) :=
  rfl

@[simp]
theorem product_quotient_apply (a : A) (b : B) :
    (product A B).quotient (b, a) = a := by
  apply ofExact_quotient_apply

end CStarExtension
