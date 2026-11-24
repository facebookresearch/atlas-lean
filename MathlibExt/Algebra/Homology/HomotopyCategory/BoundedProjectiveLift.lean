/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Literal lifts from bounded projective cochain complexes

An original bounded-above complex of projective objects is K-projective. The stock localization
bijection therefore lifts an original map through an quasi-isomorphism. A representative in the
homotopy category gives a literal cochain map, and the quotient equality gives a full homotopy
between its composite and the original map.

For an additive full faithful image functor, projectivity and the cutoff of the original terms
earn K-projectivity of the image complex. Fullness then returns a literal morphism in the original
source category.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uA vA uP vP

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {K L T : CochainComplex A ℤ}

private theorem exists_liftThroughQuasiIso_of_isKProjective [K.IsKProjective]
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) :
    ∃ g : K ⟶ L, Nonempty (Homotopy (g ≫ q) f) := by
  let _ := HasDerivedCategory.standard A
  let U := HomotopyCategory.quotient A (.up ℤ)
  let V := DerivedCategory.Qh (C := A)
  let _ : IsIso (V.map (U.map q)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) q).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso A q).2 hq)
  obtain ⟨g, hg⟩ := (IsKProjective.Qh_map_bijective K (U.obj L)).surjective
    (V.map (U.map f) ≫ inv (V.map (U.map q)))
  have hgq : g ≫ U.map q = U.map f := by
    apply (IsKProjective.Qh_map_bijective K (U.obj T)).injective
    change V.map (g ≫ U.map q) = V.map (U.map f)
    rw [V.map_comp, hg, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨g₀, rfl⟩ := U.map_surjective g
  refine ⟨g₀, ⟨HomotopyCategory.homotopyOfEq (g₀ ≫ q) f ?_⟩⟩
  exact (U.map_comp g₀ q).trans hgq

/--
The original cutoff and projective terms earn a literal lift through the quasi-isomorphism,
together with its original-map homotopy.
-/
theorem exists_boundedProjectiveLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (K.X j))
    (hproj : ∀ j : ℤ, Projective (K.X j))
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) :
    ∃ g : K ⟶ L, Nonempty (Homotopy (g ≫ q) f) := by
  let _ : K.IsStrictlyLE d := (isStrictlyLE_iff K d).2 hzero
  let _ : ∀ j : ℤ, Projective (K.X j) := hproj
  let _ : K.IsKProjective := isKProjective_of_projective K d
  exact exists_liftThroughQuasiIso_of_isKProjective q hq f

/--
Choose the cochain lift whose existence follows from the original cutoff, projective terms, and
quasi-isomorphism.
-/
@[no_expose]
def boundedProjectiveLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (K.X j))
    (hproj : ∀ j : ℤ, Projective (K.X j))
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) : K ⟶ L :=
  Classical.choose (exists_boundedProjectiveLift d hzero hproj q hq f)

/-- The full homotopy between the chosen lift followed by `q` and the original map `f`. -/
@[no_expose]
def boundedProjectiveLiftHomotopy (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (K.X j))
    (hproj : ∀ j : ℤ, Projective (K.X j))
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) :
    Homotopy (boundedProjectiveLift d hzero hproj q hq f ≫ q) f :=
  (Classical.choose_spec (exists_boundedProjectiveLift d hzero hproj q hq f)).some

section Images

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable (i : P ⥤ A) [i.Additive] [i.Full] [i.Faithful]
variable {F G : CochainComplex P ℤ}

/--
The original image-term projectivity and cutoff earn a literal source-category lift through an
image quasi-isomorphism.
-/
theorem exists_boundedProjectiveImageLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (F.X j))
    (hproj : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (q : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T) (hq : QuasiIso q)
    (f : (i.mapHomologicalComplex (.up ℤ)).obj F ⟶ T) :
    ∃ g : F ⟶ G, Nonempty (Homotopy ((i.mapHomologicalComplex (.up ℤ)).map g ≫ q) f) := by
  have hzero' : ∀ j : ℤ, d < j →
      IsZero (((i.mapHomologicalComplex (.up ℤ)).obj F).X j) :=
    fun j hj => i.map_isZero (hzero j hj)
  obtain ⟨g', hg'⟩ := exists_boundedProjectiveLift d hzero' hproj q hq f
  obtain ⟨g, rfl⟩ := (i.mapHomologicalComplex (.up ℤ)).map_surjective g'
  exact ⟨g, hg'⟩

/--
The lift is a literal morphism of the original source complexes, obtained through the original
additive full faithful image.
-/
@[no_expose]
def boundedProjectiveImageLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (F.X j))
    (hproj : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (q : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T) (hq : QuasiIso q)
    (f : (i.mapHomologicalComplex (.up ℤ)).obj F ⟶ T) : F ⟶ G :=
  Classical.choose (exists_boundedProjectiveImageLift i d hzero hproj q hq f)

/--
The full homotopy of the original image of the chosen source-category lift followed by `q` to the
original map `f`.
-/
@[no_expose]
def boundedProjectiveImageLiftHomotopy (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (F.X j))
    (hproj : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (q : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T) (hq : QuasiIso q)
    (f : (i.mapHomologicalComplex (.up ℤ)).obj F ⟶ T) :
    Homotopy ((i.mapHomologicalComplex (.up ℤ)).map
      (boundedProjectiveImageLift i d hzero hproj q hq f) ≫ q) f :=
  (Classical.choose_spec (exists_boundedProjectiveImageLift i d hzero hproj q hq f)).some

end Images

end CochainComplex

end
