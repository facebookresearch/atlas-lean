/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
AI-assisted original formalization: Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.Collection
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Finite colored profiles

A colored profile has an unordered finite type of inputs, a color for every input, and an output
color. Morphisms are bijections of the input types preserving all colors. Thus colored profiles
form a groupoid without choosing an ordering of the inputs.

This is the indexing layer for colored symmetric collections and colored operads. It deliberately
depends only on the strict finite-set operad foundation, not on simplicial sets or model-category
APIs.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe u v

/-- A finite colored profile with unordered inputs.

The bundled finite type `inputs` is the arity, `inputColor` labels each input, and `outputColor`
labels the output. -/
structure ColoredProfile (Color : Type u) where
  /-- The finite type indexing the inputs. -/
  inputs : FintypeCat.{0}
  /-- The color of each input. -/
  inputColor : inputs → Color
  /-- The output color. -/
  outputColor : Color

namespace ColoredProfile

variable {Color : Type u} {Color' : Type v}

/-- A profile whose input type is `Fin n`. -/
def ofFin {n : ℕ} (inputColor : Fin n → Color) (outputColor : Color) :
    ColoredProfile Color where
  inputs := FintypeCat.of (Fin n)
  inputColor := inputColor
  outputColor := outputColor

/-- The nullary profile with the specified output color. -/
def nullary (outputColor : Color) : ColoredProfile Color :=
  ofFin Fin.elim0 outputColor

/-- The unary profile from `inputColor` to `outputColor`. -/
def unary (inputColor outputColor : Color) : ColoredProfile Color :=
  { inputs := FintypeCat.of PUnit
    inputColor := fun _ => inputColor
    outputColor := outputColor }

/-- A profile with constant input color. -/
def constant (inputs : FintypeCat.{0}) (inputColor outputColor : Color) :
    ColoredProfile Color where
  inputs := inputs
  inputColor := fun _ => inputColor
  outputColor := outputColor

/-- Apply a function to every color in a profile. -/
def mapColors (f : Color → Color') (P : ColoredProfile Color) : ColoredProfile Color' where
  inputs := P.inputs
  inputColor := f ∘ P.inputColor
  outputColor := f P.outputColor

/-- Reindex the inputs of a profile along an equivalence, without changing its colors or output. -/
def reindex (P : ColoredProfile Color) (J : FintypeCat.{0}) (e : J ≃ P.inputs) :
    ColoredProfile Color where
  inputs := J
  inputColor := P.inputColor ∘ e
  outputColor := P.outputColor

@[simp]
theorem mapColors_inputs (f : Color → Color') (P : ColoredProfile Color) :
    (P.mapColors f).inputs = P.inputs :=
  rfl

@[simp]
theorem mapColors_inputColor (f : Color → Color') (P : ColoredProfile Color)
    (i : P.inputs) :
    (P.mapColors f).inputColor i = f (P.inputColor i) :=
  rfl

@[simp]
theorem mapColors_outputColor (f : Color → Color') (P : ColoredProfile Color) :
    (P.mapColors f).outputColor = f P.outputColor :=
  rfl

@[simp]
theorem reindex_inputs (P : ColoredProfile Color) (J : FintypeCat.{0}) (e : J ≃ P.inputs) :
    (P.reindex J e).inputs = J :=
  rfl

@[simp]
theorem reindex_inputColor (P : ColoredProfile Color) (J : FintypeCat.{0})
    (e : J ≃ P.inputs) (j : J) :
    (P.reindex J e).inputColor j = P.inputColor (e j) :=
  rfl

@[simp]
theorem reindex_outputColor (P : ColoredProfile Color) (J : FintypeCat.{0})
    (e : J ≃ P.inputs) :
    (P.reindex J e).outputColor = P.outputColor :=
  rfl

@[simp]
theorem reindex_refl (P : ColoredProfile Color) :
    P.reindex P.inputs (Equiv.refl _) = P :=
  rfl

@[simp]
theorem reindex_trans (P : ColoredProfile Color) (J K : FintypeCat.{0})
    (e : J ≃ P.inputs) (f : K ≃ J) :
    (P.reindex J e).reindex K f = P.reindex K (f.trans e) :=
  rfl

@[simp]
theorem mapColors_id (P : ColoredProfile Color) : P.mapColors id = P := by
  cases P
  rfl

@[simp]
theorem mapColors_comp {Color'' : Type*} (f : Color → Color') (g : Color' → Color'')
    (P : ColoredProfile Color) :
    (P.mapColors f).mapColors g = P.mapColors (g ∘ f) :=
  rfl

/-- A color-preserving equivalence of finite colored profiles. -/
@[ext]
structure Hom (P Q : ColoredProfile Color) where
  /-- The bijection of input types. -/
  inputEquiv : P.inputs ≃ Q.inputs
  /-- The input bijection preserves colors. -/
  inputColor_eq : ∀ i, P.inputColor i = Q.inputColor (inputEquiv i)
  /-- The output colors agree. -/
  outputColor_eq : P.outputColor = Q.outputColor

namespace Hom

variable {P Q R S : ColoredProfile Color}

/-- The identity profile equivalence. -/
def refl (P : ColoredProfile Color) : Hom P P where
  inputEquiv := Equiv.refl _
  inputColor_eq := fun _ => rfl
  outputColor_eq := rfl

/-- Composition of profile equivalences. -/
def trans (f : Hom P Q) (g : Hom Q R) : Hom P R where
  inputEquiv := f.inputEquiv.trans g.inputEquiv
  inputColor_eq := fun i => (f.inputColor_eq i).trans (g.inputColor_eq (f.inputEquiv i))
  outputColor_eq := f.outputColor_eq.trans g.outputColor_eq

/-- The inverse profile equivalence. -/
def symm (f : Hom P Q) : Hom Q P where
  inputEquiv := f.inputEquiv.symm
  inputColor_eq := fun j => by
    simpa using (f.inputColor_eq (f.inputEquiv.symm j)).symm
  outputColor_eq := f.outputColor_eq.symm

/-- Apply a function to the colors in a profile equivalence. -/
def mapColors (g : Color → Color') (f : Hom P Q) : Hom (P.mapColors g) (Q.mapColors g) where
  inputEquiv := f.inputEquiv
  inputColor_eq := fun i => congrArg g (f.inputColor_eq i)
  outputColor_eq := congrArg g f.outputColor_eq

@[simp]
theorem refl_inputEquiv (P : ColoredProfile Color) : (refl P).inputEquiv = Equiv.refl _ :=
  rfl

@[simp]
theorem trans_inputEquiv (f : Hom P Q) (g : Hom Q R) :
    (f.trans g).inputEquiv = f.inputEquiv.trans g.inputEquiv :=
  rfl

@[simp]
theorem symm_inputEquiv (f : Hom P Q) : f.symm.inputEquiv = f.inputEquiv.symm :=
  rfl

@[simp]
theorem mapColors_inputEquiv (g : Color → Color') (f : Hom P Q) :
    (f.mapColors g).inputEquiv = f.inputEquiv :=
  rfl

end Hom

/-- Colored profiles and color-preserving input bijections form a groupoid. -/
instance instGroupoid : Groupoid (ColoredProfile Color) where
  Hom := Hom
  id := Hom.refl
  comp := Hom.trans
  inv := Hom.symm
  id_comp := by
    intro P Q f
    ext i
    rfl
  comp_id := by
    intro P Q f
    ext i
    rfl
  assoc := by
    intro P Q R S f g h
    ext i
    rfl
  inv_comp := by
    intro P Q f
    ext i
    simp
  comp_inv := by
    intro P Q f
    ext i
    simp

namespace Hom

/-- The identity profile equivalence is the categorical identity. -/
theorem refl_eq_id (P : ColoredProfile Color) :
    Hom.refl P = 𝟙 P := by
  ext i
  rfl

/-- Left cancellation of a heterogeneously-identity prefix under
composition, with endpoint equations. -/
theorem trans_heq_cancel {A B C P : ColoredProfile Color}
    {a : A ⟶ B} {b : B ⟶ C}
    (h : HEq a (Hom.refl P)) (hA : A = P) (hB : B = P) :
    HEq (Hom.trans a b) b := by
  subst hB
  subst hA
  rw [eq_of_heq h]
  have hid : Hom.trans (Hom.refl A) b = b := by
    ext i
    rfl
  exact heq_of_eq hid

end Hom

@[simp]
theorem id_inputEquiv (P : ColoredProfile Color) :
    (𝟙 P : P ⟶ P).inputEquiv = Equiv.refl _ :=
  rfl

@[simp]
theorem comp_inputEquiv {P Q R : ColoredProfile Color} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).inputEquiv = f.inputEquiv.trans g.inputEquiv :=
  rfl

@[simp]
theorem inv_inputEquiv {P Q : ColoredProfile Color} (f : P ⟶ Q) :
    (Groupoid.inv f).inputEquiv = f.inputEquiv.symm :=
  rfl

/-- The canonical map from a reindexed profile to the original profile. -/
def reindexHom (P : ColoredProfile Color) (J : FintypeCat.{0}) (e : J ≃ P.inputs) :
    P.reindex J e ⟶ P where
  inputEquiv := e
  inputColor_eq := fun _ => rfl
  outputColor_eq := rfl

/-- The canonical isomorphism from a reindexed profile to the original profile. -/
noncomputable def reindexIso (P : ColoredProfile Color) (J : FintypeCat.{0})
    (e : J ≃ P.inputs) : P.reindex J e ≅ P :=
  asIso (P.reindexHom J e)

@[simp]
theorem reindexHom_inputEquiv (P : ColoredProfile Color) (J : FintypeCat.{0})
    (e : J ≃ P.inputs) :
    (P.reindexHom J e).inputEquiv = e :=
  rfl

theorem reindexHom_trans (P : ColoredProfile Color) (J K : FintypeCat.{0})
    (e : J ≃ P.inputs) (f : K ≃ J) :
    (P.reindex J e).reindexHom K f ≫ P.reindexHom J e =
      P.reindexHom K (f.trans e) := by
  apply Hom.ext
  rfl

/-- Applying a function to all colors defines a functor on profile groupoids. -/
def mapColorsFunctor (f : Color → Color') : ColoredProfile Color ⥤ ColoredProfile Color' where
  obj P := P.mapColors f
  map g := g.mapColors f
  map_id P := by
    apply Hom.ext
    rfl
  map_comp g h := by
    apply Hom.ext
    rfl

@[simp]
theorem mapColorsFunctor_obj (f : Color → Color') (P : ColoredProfile Color) :
    (mapColorsFunctor f).obj P = P.mapColors f :=
  rfl

@[simp]
theorem mapColorsFunctor_map_inputEquiv (f : Color → Color') {P Q : ColoredProfile Color}
    (g : P ⟶ Q) :
    ((mapColorsFunctor f).map g).inputEquiv = g.inputEquiv :=
  rfl

@[simp]
theorem mapColorsFunctor_id : mapColorsFunctor (id : Color → Color) = 𝟭 _ :=
  rfl

@[simp]
theorem mapColorsFunctor_comp {Color'' : Type*} (f : Color → Color') (g : Color' → Color'') :
    mapColorsFunctor f ⋙ mapColorsFunctor g = mapColorsFunctor (g ∘ f) :=
  rfl

/-- Forget all profile colors, retaining only the finite input arity. -/
abbrev arityFunctor (Color : Type u) : ColoredProfile Color ⥤ FinBijGroupoid where
  obj P := ⟨P.inputs⟩
  map f := FinBijGroupoid.homOfEquiv f.inputEquiv
  map_id P := by
    apply Core.hom_ext
    apply FintypeCat.hom_ext
    intro i
    rfl
  map_comp f g := by
    apply Core.hom_ext
    apply FintypeCat.hom_ext
    intro i
    rfl

@[simp]
theorem arityFunctor_obj (Color : Type u) (P : ColoredProfile Color) :
    (arityFunctor Color).obj P = ⟨P.inputs⟩ :=
  rfl

@[simp]
theorem arityFunctor_map {P Q : ColoredProfile Color} (f : P ⟶ Q) :
    (arityFunctor Color).map f = FinBijGroupoid.homOfEquiv f.inputEquiv :=
  rfl

/-- `eqToHom` acts on input equivs as transport. -/
theorem eqToHom_inputEquiv_cast {P Q : ColoredProfile Color} (e : P = Q) :
    (eqToHom e).inputEquiv =
      Equiv.cast (congrArg (fun Q : ColoredProfile Color => ↥Q.inputs) e) := by
  cases e
  rfl

end ColoredProfile

/-- Colored profiles seen as a sigma type over input arities. -/
private def profileEquivSigma {Color : Type u} :
    ColoredProfile Color ≃ Σ I : FintypeCat.{0}, (↥I → Color) × Color where
  toFun P := ⟨P.inputs, P.inputColor, P.outputColor⟩
  invFun S := ⟨S.1, S.2.1, S.2.2⟩
  left_inv P := by cases P; rfl
  right_inv S := by obtain ⟨I, f, c⟩ := S; rfl

/-- Colored profiles over `Type u` colors are `u + 1`-small. -/
theorem smallColoredProfile {Color : Type u} :
    Small.{u + 1} (ColoredProfile Color) := by
  have hFin : Small.{u + 1} FintypeCat.{0} :=
    Small.mk' (S := ULift.{u + 1, 1} FintypeCat.{0}) Equiv.ulift.symm
  exact small_map profileEquivSigma

/-- Colored profiles form a `u + 1`-locally small category. -/
theorem locallySmallColoredProfile {Color : Type u} :
    LocallySmall.{u + 1} (ColoredProfile Color) where
  hom_small P Q := by
    change Small.{u + 1} (ColoredProfile.Hom P Q)
    exact small_zero _

end CategoryTheory.Operad
