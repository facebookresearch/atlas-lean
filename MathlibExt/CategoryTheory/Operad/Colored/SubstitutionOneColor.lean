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

public import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionData

/-!
# One-colored substitution data

Ordinary finite-set substitution data are equivalent to colored substitution data with color type
`PUnit`. The normalized finite-family representation makes the object-level comparison
definitionally transparent.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

namespace ColoredSubstitutionData

universe c

/-- Regard ordinary substitution data as one-colored substitution data. -/
def oneColorFunctor : SubstitutionData ⥤ ColoredSubstitutionData PUnit where
  obj d :=
    { outputColor := PUnit.unit
      inner := (FiniteFamily.map ColoredProfile.oneColorFunctor).obj d }
  map f :=
    { outputColor_eq := rfl
      innerHom := (FiniteFamily.map ColoredProfile.oneColorFunctor).map f }
  map_id d := by
    apply Hom.ext
    exact (FiniteFamily.map ColoredProfile.oneColorFunctor).map_id d
  map_comp f g := by
    apply Hom.ext
    exact (FiniteFamily.map ColoredProfile.oneColorFunctor).map_comp f g

/-- Forget all colors from one-colored substitution data. -/
def forgetOneColorFunctor : ColoredSubstitutionData PUnit ⥤ SubstitutionData where
  obj d := (FiniteFamily.map ColoredProfile.forgetOneColorFunctor).obj d.inner
  map f := (FiniteFamily.map ColoredProfile.forgetOneColorFunctor).map f.innerHom
  map_id d := (FiniteFamily.map ColoredProfile.forgetOneColorFunctor).map_id d.inner
  map_comp f g :=
    (FiniteFamily.map ColoredProfile.forgetOneColorFunctor).map_comp f.innerHom g.innerHom

@[simp]
theorem oneColorFunctor_obj_inner_index (d : SubstitutionData) :
    (oneColorFunctor.obj d).inner.index = d.index :=
  rfl

@[simp]
theorem oneColorFunctor_obj_inner_obj (d : SubstitutionData) (i : d.index) :
    (oneColorFunctor.obj d).inner.obj i = ColoredProfile.oneColorFunctor.obj (d.obj i) :=
  rfl

@[simp]
theorem oneColorFunctor_obj_outerProfile (d : SubstitutionData) :
    (oneColorFunctor.obj d).outerProfile = ColoredProfile.oneColorFunctor.obj ⟨d.index⟩ :=
  rfl

@[simp]
theorem oneColorFunctor_obj_totalProfile (d : SubstitutionData) :
    (oneColorFunctor.obj d).totalProfile =
      ColoredProfile.oneColorFunctor.obj ⟨substitutionTotalObj d⟩ :=
  rfl

/-- Unit of the equivalence between ordinary and one-colored substitution data. -/
def oneColorUnitIso : 𝟭 SubstitutionData ≅ oneColorFunctor ⋙ forgetOneColorFunctor :=
  NatIso.ofComponents (fun d => Iso.refl d) (by
    intro d e f
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact heq_of_eq (FinBijGroupoid.homOfEquiv_equivOfHom (f.hom i)).symm)

/-- The forward component of the normalization unit is the identity. -/
@[simp]
theorem oneColorUnitIso_hom_app (d : SubstitutionData) :
    oneColorUnitIso.hom.app d = 𝟙 d :=
  rfl

/-- The inverse component of the normalization unit is the identity. -/
@[simp]
theorem oneColorUnitIso_inv_app (d : SubstitutionData) :
    oneColorUnitIso.inv.app d = 𝟙 d :=
  rfl

/-- Canonical map from the normalized one-colored substitution datum back to the original. -/
def oneColorCounitHom (d : ColoredSubstitutionData PUnit) :
    (forgetOneColorFunctor ⋙ oneColorFunctor).obj d ⟶ d where
  outputColor_eq := Subsingleton.elim _ _
  innerHom :=
    { equiv := Equiv.refl _
      hom := fun i => ColoredProfile.oneColorCounitHom (d.inner.obj i) }

/-- Inverse of `oneColorCounitHom`. -/
def oneColorCounitInv (d : ColoredSubstitutionData PUnit) :
    d ⟶ (forgetOneColorFunctor ⋙ oneColorFunctor).obj d where
  outputColor_eq := Subsingleton.elim _ _
  innerHom :=
    { equiv := Equiv.refl _
      hom := fun i => Groupoid.inv (ColoredProfile.oneColorCounitHom (d.inner.obj i)) }

/-- Counit component for the equivalence between ordinary and one-colored substitution data. -/
def oneColorCounitIsoApp (d : ColoredSubstitutionData PUnit) :
    (forgetOneColorFunctor ⋙ oneColorFunctor).obj d ≅ d where
  hom := oneColorCounitHom d
  inv := oneColorCounitInv d
  hom_inv_id := by
    apply Hom.ext
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact heq_of_eq (by
        apply ColoredProfile.Hom.ext
        rfl)
  inv_hom_id := by
    apply Hom.ext
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact heq_of_eq (by
        apply ColoredProfile.Hom.ext
        rfl)

/-- Counit of the equivalence between ordinary and one-colored substitution data. -/
def oneColorCounitIso : forgetOneColorFunctor ⋙ oneColorFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents oneColorCounitIsoApp (by
    intro d e f
    apply Hom.ext
    apply FiniteFamily.Hom_ext
    · rfl
    · intro i
      exact heq_of_eq (by
        apply ColoredProfile.Hom.ext
        rfl))

/-- The chosen unit and counit satisfy the triangle identity. -/
theorem oneColor_triangle (d : SubstitutionData) :
    oneColorFunctor.{c}.map (oneColorUnitIso.{c}.hom.app d) ≫
        oneColorCounitIso.{c}.hom.app (oneColorFunctor.{c}.obj d) = 𝟙 _ := by
  rw [oneColorUnitIso_hom_app]
  with_unfolding_all
    change 𝟙 _ ≫ oneColorCounitHom (oneColorFunctor.obj d) = 𝟙 _
  rw [Category.id_comp]
  apply Hom.ext
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    exact heq_of_eq (by
      apply ColoredProfile.Hom.ext
      rfl)

/-- Ordinary substitution data and one-colored substitution data are equivalent categories. -/
def oneColorEquivalence : SubstitutionData ≌ ColoredSubstitutionData PUnit :=
  CategoryTheory.Equivalence.mk' oneColorFunctor forgetOneColorFunctor
    oneColorUnitIso oneColorCounitIso oneColor_triangle

@[simp]
theorem oneColorEquivalence_functor : oneColorEquivalence.functor = oneColorFunctor :=
  rfl

@[simp]
theorem oneColorEquivalence_inverse : oneColorEquivalence.inverse = forgetOneColorFunctor :=
  rfl

/-- The unit of the one-color substitution-data equivalence is the chosen normalization
isomorphism. -/
@[simp]
theorem oneColorEquivalence_unitIso : oneColorEquivalence.unitIso = oneColorUnitIso :=
  rfl

/-- The counit of the one-color substitution-data equivalence is the chosen denormalization
isomorphism. -/
@[simp]
theorem oneColorEquivalence_counitIso : oneColorEquivalence.counitIso = oneColorCounitIso :=
  rfl

end ColoredSubstitutionData

end CategoryTheory.Operad
