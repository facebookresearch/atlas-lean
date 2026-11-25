/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Classes of short exact extensions

Extension objects have specified endpoints in the category of short exact
sequences. Endpoint-fixing isomorphisms define equivalence, and `extClass`
descends to the quotient of extension objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e v u

namespace CategoryTheory.ShortExactSequence

variable {C : Type u} [Category.{v} C]

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- The short exact sequences with first endpoint Y and last endpoint X. -/
def endpointsProperty (X Y : C) : ObjectProperty (ShortExactSequence C) :=
  fun S ↦ S.obj.X₁ = Y ∧ S.obj.X₃ = X

/-- The fibre of short exact sequence objects with specified literal endpoints. -/
abbrev WithEndpoints (X Y : C) := (endpointsProperty X Y).FullSubcategory

namespace WithEndpoints

variable {X Y : C}

/-- The same sequence, with identity transport making both
endpoint objects literal. -/
abbrev complex (S : WithEndpoints X Y) : ShortComplex C where
  X₁ := Y
  X₂ := S.obj.obj.X₂
  X₃ := X
  f := eqToHom S.property.1.symm ≫ S.obj.obj.f
  g := S.obj.obj.g ≫ eqToHom S.property.2
  zero := by
    calc
      (eqToHom S.property.1.symm ≫ S.obj.obj.f) ≫
          (S.obj.obj.g ≫ eqToHom S.property.2) =
        eqToHom S.property.1.symm ≫
          (S.obj.obj.f ≫ S.obj.obj.g) ≫ eqToHom S.property.2 := by
            simp only [Category.assoc]
      _ = 0 := by rw [S.obj.obj.zero, zero_comp, comp_zero]

/-- Endpoint transport; its middle component is the identity. -/
def complexIso (S : WithEndpoints X Y) : S.complex ≅ S.obj.obj :=
  ShortComplex.isoMk
    (eqToIso S.property.1.symm) (Iso.refl _) (eqToIso S.property.2.symm)
    (by simp [complex])
    (by simp [complex])

/-- Endpoint transport preserves the short exact property. -/
theorem complex_shortExact (S : WithEndpoints X Y) : S.complex.ShortExact :=
  ShortComplex.shortExact_of_iso S.complexIso.symm S.obj.property

/-- A literal short exact pair is an object of the endpoint fibre. -/
def mk {E : C} (f : Y ⟶ E) (g : E ⟶ X) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) : WithEndpoints X Y :=
  ⟨⟨ShortComplex.mk f g w, h⟩, ⟨rfl, rfl⟩⟩

@[simp]
theorem complex_mk_f {E : C} (f : Y ⟶ E) (g : E ⟶ X) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    (mk f g w h).complex.f = f := by
  exact Category.id_comp f

@[simp]
theorem complex_mk_g {E : C} (f : Y ⟶ E) (g : E ⟶ X) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).ShortExact) :
    (mk f g w h).complex.g = g := by
  exact Category.comp_id g

/-- Extension equivalence is a short-complex isomorphism
whose endpoint components are identities. -/
def Rel (S T : WithEndpoints X Y) : Prop :=
  ∃ h : S.complex ≅ T.complex, h.hom.τ₁ = 𝟙 Y ∧ h.hom.τ₃ = 𝟙 X

theorem rel_refl (S : WithEndpoints X Y) : Rel S S :=
  ⟨Iso.refl _, rfl, rfl⟩

theorem rel_symm {S T : WithEndpoints X Y} (h : Rel S T) : Rel T S := by
  rcases h with ⟨h, h₁, h₃⟩
  have hi₁ := congrArg (fun f : S.complex ⟶ S.complex ↦ f.τ₁) h.hom_inv_id
  have hi₃ := congrArg (fun f : S.complex ⟶ S.complex ↦ f.τ₃) h.hom_inv_id
  change h.hom.τ₁ ≫ h.inv.τ₁ = 𝟙 Y at hi₁
  change h.hom.τ₃ ≫ h.inv.τ₃ = 𝟙 X at hi₃
  rw [h₁, Category.id_comp] at hi₁
  rw [h₃, Category.id_comp] at hi₃
  exact ⟨h.symm, hi₁, hi₃⟩

theorem rel_trans {S T U : WithEndpoints X Y} (h : Rel S T) (h' : Rel T U) :
    Rel S U := by
  rcases h with ⟨h, h₁, h₃⟩
  rcases h' with ⟨h', h'₁, h'₃⟩
  refine ⟨h ≪≫ h', ?_, ?_⟩
  · change h.hom.τ₁ ≫ h'.hom.τ₁ = 𝟙 Y
    rw [h₁, h'₁, Category.id_comp]
  · change h.hom.τ₃ ≫ h'.hom.τ₃ = 𝟙 X
    rw [h₃, h'₃, Category.id_comp]

/-- The endpoint-fixing isomorphism relation is an equivalence relation. -/
def setoid (X Y : C) : Setoid (WithEndpoints X Y) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- Equivalence classes of short exact extension objects. -/
def Classes (X Y : C) := _root_.Quotient (setoid X Y)

/-- The class of an extension. -/
def classOf (S : WithEndpoints X Y) : Classes X Y :=
  _root_.Quotient.mk _ S

theorem classOf_eq_of_rel {S T : WithEndpoints X Y} (h : Rel S T) :
    classOf S = classOf T :=
  _root_.Quotient.sound h

theorem rel_of_classOf_eq {S T : WithEndpoints X Y} (h : classOf S = classOf T) :
    Rel S T :=
  _root_.Quotient.exact h

end WithEndpoints

end ZeroMorphisms

section Abelian

variable [Abelian C] [HasExt.{e} C]
variable {X Y : C}

namespace WithEndpoints

/-- The Ext class of a sequence, with both literal endpoints. -/
def extClass (S : WithEndpoints X Y) : Abelian.Ext.{e} X Y 1 :=
  S.complex_shortExact.extClass

/-- The Ext class is invariant under endpoint-fixing equivalence. -/
theorem extClass_eq_of_rel {S T : WithEndpoints X Y} (h : Rel S T) :
    extClass S = extClass T := by
  rcases h with ⟨h, h₁, h₃⟩
  have hn := ShortComplex.ShortExact.extClass_naturality
    S.complex_shortExact T.complex_shortExact h.hom
  change (extClass S).comp (Abelian.Ext.mk₀ h.hom.τ₁) (add_zero 1) =
    (Abelian.Ext.mk₀ h.hom.τ₃).comp (extClass T) (zero_add 1) at hn
  rw [h₁, h₃, Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_id_comp] at hn
  exact hn

/-- The Ext class map on the quotient of extension objects. -/
def classifyingMap : Classes X Y → Abelian.Ext.{e} X Y 1 :=
  _root_.Quotient.lift extClass (fun _ _ h ↦ extClass_eq_of_rel h)

@[simp]
theorem classifyingMap_classOf (S : WithEndpoints X Y) :
    classifyingMap (classOf S) = extClass S :=
  rfl

end WithEndpoints

end Abelian

end CategoryTheory.ShortExactSequence

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]
  {S : ShortComplex C}

/-- A section kills the extension class. -/
theorem extClass_eq_zero_of_section (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂)
    (hs : s ≫ S.g = 𝟙 S.X₃) : hS.extClass = 0 := by
  calc
    hS.extClass = (Abelian.Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) :=
      (Abelian.Ext.mk₀_id_comp hS.extClass).symm
    _ = (Abelian.Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) := by rw [hs]
    _ = (Abelian.Ext.mk₀ s).comp
        ((Abelian.Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) :=
      (Abelian.Ext.mk₀_comp_mk₀_assoc s S.g hS.extClass).symm
    _ = 0 := by rw [hS.comp_extClass, Abelian.Ext.comp_zero]

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ShortExactSequence.WithEndpoints

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The literal split extension0→Y→Y⊞X→X→0. -/
def split (X Y : C) : WithEndpoints X Y := by
  let S : ShortComplex C :=
    ShortComplex.mk (biprod.inl : Y ⟶ Y ⊞ X) (biprod.snd : Y ⊞ X ⟶ X) (by simp)
  let h : S.Splitting :=
    { r := biprod.fst
      s := biprod.inr
      f_r := by simp [S]
      s_g := by simp [S]
      id := by apply biprod.hom_ext <;> simp [S] }
  exact mk S.f S.g S.zero h.shortExact

@[simp]
theorem extClass_split [HasExt.{e} C] (X Y : C) :
    extClass (split X Y) = (0 : Abelian.Ext.{e} X Y 1) := by
  exact (complex_shortExact (split X Y)).extClass_eq_zero_of_section
    (biprod.inr : X ⟶ Y ⊞ X) (by simp [split, complex, mk])

end CategoryTheory.ShortExactSequence.WithEndpoints
