/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.ScalarExtension

/-!
# Nonunital coefficient maps on finite idempotent projectives

An actual nonunital ring homomorphism maps finite idempotent matrices and
their complete rectangular corner morphisms. The identity of an idempotent
object is its idempotent, so this construction does not require preservation
of the ambient ring unit. Unital maps retain the existing scalar-extension
object, morphism and complete natural-isomorphism programs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace FGProjectiveCat.IdempotentModel.NonunitalMap

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]


/-- The same original finite rank and its actual entrywise image idempotent. -/
@[reducible]
def obj (f : R →ₙ+* S) (P : IdempotentModel R) : IdempotentModel S where
  X := P.X
  p := (rowHomEquiv S P.X P.X).symm ((rowHomEquiv R P.X P.X P.p).map f)
  idem := by
    apply (rowHomEquiv S P.X P.X).injective
    rw [(equivalence_characteristic S).2.2.1]
    simp only [AddEquiv.apply_symm_apply]
    rw [← Matrix.map_mul, (equivalence_characteristic R).2.2.2.1 P]

@[simp]
theorem obj_rank (f : R →ₙ+* S) (P : IdempotentModel R) : (obj f P).X = P.X :=
  rfl

/-- The original full idempotent matrix is mapped without changing rank or coordinates. -/
theorem obj_matrix (f : R →ₙ+* S) (P : IdempotentModel R) :
    rowHomEquiv S P.X P.X (obj f P).p = (rowHomEquiv R P.X P.X P.p).map f :=
  AddEquiv.apply_symm_apply _ _

private theorem corner_matrix {P Q : IdempotentModel R} (g : P ⟶ Q) :
    rowHomEquiv R P.X P.X P.p * rowHomEquiv R P.X Q.X g.f *
      rowHomEquiv R Q.X Q.X Q.p = rowHomEquiv R P.X Q.X g.f := by
  have h := (equivalence_characteristic R).2.2.2.2.2.2.2.1 P Q g
  rw [h.1, h.2]

private theorem mapped_corner (f : R →ₙ+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    rowHomEquiv S P.X P.X (obj f P).p * (rowHomEquiv R P.X Q.X g.f).map f *
      rowHomEquiv S Q.X Q.X (obj f Q).p = (rowHomEquiv R P.X Q.X g.f).map f := by
  rw [obj_matrix, obj_matrix, ← Matrix.map_mul, ← Matrix.map_mul, corner_matrix g]

/-- The actual image of every complete rectangular corner morphism. -/
def hom (f : R →ₙ+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) : obj f P ⟶ obj f Q :=
  homOfMatrix S ((rowHomEquiv R P.X Q.X g.f).map f) (by exact mapped_corner f g)

/-- The full image morphism has the actual entrywise coefficient matrix. -/
@[simp]
theorem hom_matrix (f : R →ₙ+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    rowHomEquiv S P.X Q.X (hom f g).f = (rowHomEquiv R P.X Q.X g.f).map f :=
  homOfMatrix_matrix S (P := obj f P) (Q := obj f Q)
    ((rowHomEquiv R P.X Q.X g.f).map f) (mapped_corner f g)

/-- Nonunital coefficients give a genuine functor on the original Karoubi categories. -/
@[reducible]
def functor (f : R →ₙ+* S) : IdempotentModel R ⥤ IdempotentModel S where
  obj := obj f
  map := hom f
  map_id P := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X P.X).injective
    change rowHomEquiv S P.X P.X (hom f (𝟙 P)).f =
      rowHomEquiv S P.X P.X (obj f P).p
    rw [hom_matrix, obj_matrix]
    rfl
  map_comp {P Q U} g h := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X U.X).injective
    change rowHomEquiv S P.X U.X (hom f (g ≫ h)).f =
      rowHomEquiv S P.X U.X ((hom f g).f ≫ (hom f h).f)
    rw [(equivalence_characteristic S).2.2.1]
    change rowHomEquiv S P.X U.X (hom f (g ≫ h)).f =
      rowHomEquiv S P.X Q.X (hom f g).f * rowHomEquiv S Q.X U.X (hom f h).f
    rw [hom_matrix, hom_matrix, hom_matrix]
    change (rowHomEquiv R P.X U.X (g.f ≫ h.f)).map f = _
    rw [(equivalence_characteristic R).2.2.1, Matrix.map_mul]

instance functorAdditive (f : R →ₙ+* S) : (functor f).Additive where
  map_add {P Q} g h := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv S P.X Q.X).injective
    change rowHomEquiv S P.X Q.X (hom f (g + h)).f =
      rowHomEquiv S P.X Q.X ((hom f g).f + (hom f h).f)
    rw [(rowHomEquiv S P.X Q.X).map_add, hom_matrix, hom_matrix, hom_matrix]
    change (rowHomEquiv R P.X Q.X (g.f + h.f)).map f = _
    rw [(rowHomEquiv R P.X Q.X).map_add]
    ext i j
    exact map_add f _ _

/-- The same additive map preserves the original split exact structures. -/
instance functorIsExact (f : R →ₙ+* S) : (functor f).IsExact :=
  ExactCategory.isExact_splitSource (functor f)

/-- Identity coefficients recover the entire original idempotent object. -/
@[simp]
theorem obj_id (P : IdempotentModel R) : obj (NonUnitalRingHom.id R) P = P := by
  apply Idempotents.Karoubi.ext (P := obj (NonUnitalRingHom.id R) P) (Q := P) rfl
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change (rowHomEquiv R P.X P.X).symm (rowHomEquiv R P.X P.X P.p) = P.p
  exact AddEquiv.symm_apply_apply _ _

/-- Both original coefficient maps compose on the complete original idempotent. -/
theorem obj_comp (f : R →ₙ+* S) (g : S →ₙ+* T) (P : IdempotentModel R) :
    obj (g.comp f) P = obj g (obj f P) := by
  apply Idempotents.Karoubi.ext (P := obj (g.comp f) P) (Q := obj g (obj f P)) rfl
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply (rowHomEquiv T P.X P.X).injective
  calc
    _ = (rowHomEquiv R P.X P.X P.p).map (g.comp f) := obj_matrix (g.comp f) P
    _ = ((rowHomEquiv R P.X P.X P.p).map f).map g := rfl
    _ = (rowHomEquiv S P.X P.X (obj f P).p).map g :=
      congrArg (fun b : Matrix (Fin P.X) (Fin P.X) S => b.map g) (obj_matrix f P).symm
    _ = _ := (obj_matrix g (obj f P)).symm

/-- The zero coefficient map yields a true zero object, at the same finite rank. -/
theorem obj_zero_isZero (P : IdempotentModel R) :
    IsZero (obj (0 : R →ₙ+* S) P) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply Idempotents.Karoubi.hom_ext
  apply (rowHomEquiv S P.X P.X).injective
  change rowHomEquiv S P.X P.X (obj (0 : R →ₙ+* S) P).p =
    rowHomEquiv S P.X P.X 0
  rw [obj_matrix, map_zero]
  ext i j
  rfl

/-- A unital map has exactly the existing scalar-extension idempotent object. -/
@[simp]
theorem obj_toNonUnitalRingHom (f : R →+* S) (P : IdempotentModel R) :
    obj f.toNonUnitalRingHom P = mapObject f P :=
  rfl

/-- A unital map retains the entire existing scalar-extension rectangular morphism. -/
@[simp]
theorem hom_toNonUnitalRingHom (f : R →+* S) {P Q : IdempotentModel R} (g : P ⟶ Q) :
    hom f.toNonUnitalRingHom g = mapHom f g := by
  apply Idempotents.Karoubi.hom_ext
  apply (rowHomEquiv S P.X Q.X).injective
  rw [hom_matrix, mapHom_matrix]
  rfl

/-- On unital coefficients this is the actual original scalar-extension functor,
through the same original row-range equivalences, including every morphism. -/
def scalarExtensionNatIso (f : R →+* S) :
    (equivalence R).functor ⋙ FGProjectiveCat.ringScalarExtension f ≅
      functor f.toNonUnitalRingHom ⋙ (equivalence S).functor :=
  NatIso.ofComponents (scalarExtensionIso f) (by
    intro P Q g
    change (FGProjectiveCat.ringScalarExtension f).map ((equivalence R).functor.map g) ≫
        (scalarExtensionIso f Q).hom =
      (scalarExtensionIso f P).hom ≫ (equivalence S).functor.map (hom f.toNonUnitalRingHom g)
    rw [hom_toNonUnitalRingHom]
    exact scalarExtensionIso_naturality f g)

end FGProjectiveCat.IdempotentModel.NonunitalMap
