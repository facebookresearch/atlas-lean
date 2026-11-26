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

public import MathlibExt.CategoryTheory.Operad.OperadObj.Basic

/-!
# Morphisms of enriched operad objects and their category

Morphisms of `OperadObj V` relative to `FiniteTensor V` as morphisms of
underlying symmetric collections preserving unit and substitution.
Equivariance follows from naturality. Empty arities remain allowed via the
underlying `SubstitutionData`.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe v u

namespace OperadObj

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

/-! Forced-public helpers for operad morphisms.

These are forced public in Lean 4.33 because the public `Hom` structure
and its category laws depend on file-private constants otherwise.
All names are contained in `HomData`. -/
namespace HomData

/-- Factor-family morphism induced by `α : O ⟶ P` at `X : SubstitutionData`.

Index `none` corresponds to the outer arity `X.index`; `some i` corresponds
to the inner arity `X.obj i`. -/
def factorHom {O P : SymmetricCollection V} (α : O ⟶ P) (X : SubstitutionData) :
    (substitutionFactors O).obj X ⟶ (substitutionFactors P).obj X where
  equiv := Equiv.refl _
  hom := fun o =>
    match o with
    | none => α.app ⟨X.index⟩
    | some i => α.app (X.obj i)

/-- Tensor image of `factorHom`. This is the source part of the substitution
compatibility law: `tensor (factors O X) ⟶ tensor (factors P X)`. -/
def sourceHom {O P : SymmetricCollection V} (α : O ⟶ P) (X : SubstitutionData) :
    (FiniteTensor.tensor (V := V)).obj ((substitutionFactors O).obj X) ⟶
      (FiniteTensor.tensor (V := V)).obj ((substitutionFactors P).obj X) :=
  (FiniteTensor.tensor (V := V)).map (factorHom (V := V) α X)

omit [FiniteTensor V] in
theorem factorHom_id (O : SymmetricCollection V) (X : SubstitutionData) :
    factorHom (V := V) (𝟙 O) X = 𝟙 ((substitutionFactors O).obj X) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none => exact heq_of_eq rfl
    | some _ => exact heq_of_eq rfl

theorem sourceHom_id (O : SymmetricCollection V) (X : SubstitutionData) :
    sourceHom (V := V) (𝟙 O) X = 𝟙 _ := by
  unfold sourceHom
  rw [factorHom_id]
  exact (FiniteTensor.tensor (V := V)).map_id ((substitutionFactors O).obj X)

omit [FiniteTensor V] in
theorem factorHom_comp {O P Q : SymmetricCollection V}
    (α : O ⟶ P) (β : P ⟶ Q) (X : SubstitutionData) :
    factorHom (V := V) (α ≫ β) X =
      (factorHom (V := V) α X).comp (factorHom (V := V) β X) := by
  apply FiniteFamily.Hom_ext
  · exact (Equiv.refl_trans (Equiv.refl _)).symm
  · intro o
    cases o with
    | none => exact heq_of_eq rfl
    | some _ => exact heq_of_eq rfl

theorem sourceHom_comp {O P Q : SymmetricCollection V}
    (α : O ⟶ P) (β : P ⟶ Q) (X : SubstitutionData) :
    sourceHom (V := V) (α ≫ β) X =
      sourceHom (V := V) α X ≫ sourceHom (V := V) β X := by
  unfold sourceHom
  rw [factorHom_comp]
  exact (FiniteTensor.tensor (V := V)).map_comp
    (factorHom (V := V) α X) (factorHom (V := V) β X)

end HomData

/-- Morphism of enriched operad objects.

A morphism is a morphism of underlying symmetric collections preserving the
enriched unit and substitution. Equivariance is encoded in naturality of
`toCollectionHom`. Empty outer/inner arities are allowed. -/
structure Hom (O P : OperadObj V) where
  /-- Underlying morphism of symmetric collections. -/
  toCollectionHom : O.toCollection ⟶ P.toCollection
  /-- Preservation of the enriched unit. -/
  map_unit : O.unit ≫ toCollectionHom.app ⟨arityOne⟩ = P.unit
  /-- Preservation of substitution. -/
  map_subst : ∀ (X : SubstitutionData),
    O.subst.app X ≫ toCollectionHom.app ⟨substitutionTotalObj X⟩ =
      HomData.sourceHom toCollectionHom X ≫ P.subst.app X

namespace Hom

@[ext]
theorem ext {O P : OperadObj V} {F G : Hom O P}
    (h : F.toCollectionHom = G.toCollectionHom) : F = G := by
  cases F with
  | mk homF unitF substF =>
    cases G with
    | mk homG unitG substG =>
      subst h
      rfl

/-- Identity morphism of `OperadObj`. -/
def id (O : OperadObj V) : Hom O O :=
  ⟨𝟙 O.toCollection,
    by
      have h_app :
          NatTrans.app (𝟙 O.toCollection : O.toCollection ⟶ _) ⟨arityOne⟩ =
            𝟙 (O.toCollection.obj ⟨arityOne⟩) := rfl
      have h1 :
          O.unit ≫ NatTrans.app (𝟙 O.toCollection) ⟨arityOne⟩ =
            O.unit ≫ 𝟙 (O.toCollection.obj ⟨arityOne⟩) :=
        congrArg (fun t => O.unit ≫ t) h_app
      exact h1.trans (Category.comp_id _),
    by
      intro X
      have h_app :
          NatTrans.app (𝟙 O.toCollection : O.toCollection ⟶ _) ⟨substitutionTotalObj X⟩ =
            𝟙 ((substitutionTarget O.toCollection).obj X) := rfl
      have h_src :
          HomData.sourceHom (𝟙 O.toCollection : O.toCollection ⟶ _) X =
            𝟙 _ := HomData.sourceHom_id O.toCollection X
      have h1 :
          O.subst.app X ≫ NatTrans.app (𝟙 O.toCollection) ⟨substitutionTotalObj X⟩ =
            O.subst.app X ≫ 𝟙 ((substitutionTarget O.toCollection).obj X) :=
        congrArg (fun t => O.subst.app X ≫ t) h_app
      have h2 : O.subst.app X ≫ 𝟙 ((substitutionTarget O.toCollection).obj X) = O.subst.app X :=
        Category.comp_id _
      have h3 : O.subst.app X = 𝟙 _ ≫ O.subst.app X := (Category.id_comp _).symm
      have h4 :
          𝟙 _ ≫ O.subst.app X =
            HomData.sourceHom (𝟙 O.toCollection) X ≫ O.subst.app X :=
        congrArg (fun t => t ≫ O.subst.app X) h_src.symm
      exact (h1.trans h2).trans (h3.trans h4)⟩

/-- Composition of morphisms of `OperadObj`. -/
def comp {O P Q : OperadObj V} (F : Hom O P) (G : Hom P Q) : Hom O Q :=
  ⟨F.toCollectionHom ≫ G.toCollectionHom,
    by
      have h_app :
          NatTrans.app (F.toCollectionHom ≫ G.toCollectionHom) ⟨arityOne⟩ =
            F.toCollectionHom.app ⟨arityOne⟩ ≫ G.toCollectionHom.app ⟨arityOne⟩ := rfl
      have h1 :
          O.unit ≫ NatTrans.app (F.toCollectionHom ≫ G.toCollectionHom) ⟨arityOne⟩ =
            O.unit ≫ (F.toCollectionHom.app ⟨arityOne⟩ ≫ G.toCollectionHom.app ⟨arityOne⟩) :=
        congrArg (fun t => O.unit ≫ t) h_app
      have h2 :
          O.unit ≫ (F.toCollectionHom.app ⟨arityOne⟩ ≫ G.toCollectionHom.app ⟨arityOne⟩) =
            (O.unit ≫ F.toCollectionHom.app ⟨arityOne⟩) ≫ G.toCollectionHom.app ⟨arityOne⟩ :=
        (Category.assoc _ _ _).symm
      have h3 :
          (O.unit ≫ F.toCollectionHom.app ⟨arityOne⟩) ≫ G.toCollectionHom.app ⟨arityOne⟩ =
            P.unit ≫ G.toCollectionHom.app ⟨arityOne⟩ :=
        congrArg (fun t => t ≫ G.toCollectionHom.app ⟨arityOne⟩) F.map_unit
      have h4 : P.unit ≫ G.toCollectionHom.app ⟨arityOne⟩ = Q.unit := G.map_unit
      exact ((h1.trans h2).trans h3).trans h4,
    by
      intro X
      have h_app :
          NatTrans.app (F.toCollectionHom ≫ G.toCollectionHom) ⟨substitutionTotalObj X⟩ =
            F.toCollectionHom.app ⟨substitutionTotalObj X⟩ ≫
              G.toCollectionHom.app ⟨substitutionTotalObj X⟩ := rfl
      have h1 :
          O.subst.app X ≫
              NatTrans.app (F.toCollectionHom ≫ G.toCollectionHom) ⟨substitutionTotalObj X⟩ =
            O.subst.app X ≫
              (F.toCollectionHom.app ⟨substitutionTotalObj X⟩ ≫
                G.toCollectionHom.app ⟨substitutionTotalObj X⟩) :=
        congrArg (fun t => O.subst.app X ≫ t) h_app
      have h2 :
          O.subst.app X ≫
              (F.toCollectionHom.app ⟨substitutionTotalObj X⟩ ≫
                G.toCollectionHom.app ⟨substitutionTotalObj X⟩) =
            (O.subst.app X ≫ F.toCollectionHom.app ⟨substitutionTotalObj X⟩) ≫
              G.toCollectionHom.app ⟨substitutionTotalObj X⟩ :=
        (Category.assoc _ _ _).symm
      have h3 :
          (O.subst.app X ≫ F.toCollectionHom.app ⟨substitutionTotalObj X⟩) ≫
              G.toCollectionHom.app ⟨substitutionTotalObj X⟩ =
            (HomData.sourceHom F.toCollectionHom X ≫ P.subst.app X) ≫
              G.toCollectionHom.app ⟨substitutionTotalObj X⟩ :=
        congrArg (fun t => t ≫ G.toCollectionHom.app ⟨substitutionTotalObj X⟩) (F.map_subst X)
      have h4 :
          (HomData.sourceHom F.toCollectionHom X ≫ P.subst.app X) ≫
              G.toCollectionHom.app ⟨substitutionTotalObj X⟩ =
            HomData.sourceHom F.toCollectionHom X ≫
              (P.subst.app X ≫ G.toCollectionHom.app ⟨substitutionTotalObj X⟩) :=
        Category.assoc _ _ _
      have h5_eq :
          P.subst.app X ≫ G.toCollectionHom.app ⟨substitutionTotalObj X⟩ =
            HomData.sourceHom G.toCollectionHom X ≫ Q.subst.app X :=
        G.map_subst X
      have h5 :
          HomData.sourceHom F.toCollectionHom X ≫
              (P.subst.app X ≫ G.toCollectionHom.app ⟨substitutionTotalObj X⟩) =
            HomData.sourceHom F.toCollectionHom X ≫
              (HomData.sourceHom G.toCollectionHom X ≫ Q.subst.app X) :=
        congrArg (fun t => HomData.sourceHom F.toCollectionHom X ≫ t) h5_eq
      have h6 :
          HomData.sourceHom F.toCollectionHom X ≫
              (HomData.sourceHom G.toCollectionHom X ≫ Q.subst.app X) =
            (HomData.sourceHom F.toCollectionHom X ≫ HomData.sourceHom G.toCollectionHom X) ≫
              Q.subst.app X :=
        (Category.assoc _ _ _).symm
      have h7 :
          (HomData.sourceHom F.toCollectionHom X ≫ HomData.sourceHom G.toCollectionHom X) ≫
              Q.subst.app X =
            HomData.sourceHom (F.toCollectionHom ≫ G.toCollectionHom) X ≫ Q.subst.app X := by
        have h_comp :
            HomData.sourceHom F.toCollectionHom X ≫ HomData.sourceHom G.toCollectionHom X =
              HomData.sourceHom (F.toCollectionHom ≫ G.toCollectionHom) X := by
          rw [← HomData.sourceHom_comp]
        exact congrArg (fun t => t ≫ Q.subst.app X) h_comp
      exact (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7⟩

@[simp]
theorem id_toCollectionHom (O : OperadObj V) :
    (Hom.id (V := V) O).toCollectionHom = (𝟙 O.toCollection : O.toCollection ⟶ O.toCollection) :=
  rfl

@[simp]
theorem comp_toCollectionHom {O P Q : OperadObj V} (F : Hom O P) (G : Hom P Q) :
    (F.comp G).toCollectionHom =
      (F.toCollectionHom ≫ G.toCollectionHom : O.toCollection ⟶ Q.toCollection) :=
  rfl

end Hom

/-- Category structure on `OperadObj V`. The universe is inferred by elaboration. -/
instance : Category (OperadObj V) where
  Hom O P := Hom O P
  id O := Hom.id O
  comp F G := F.comp G
  id_comp := by
    intro O P F
    apply Hom.ext
    simp
  comp_id := by
    intro O P F
    apply Hom.ext
    simp
  assoc := by
    intro W X Y Z F G H
    apply Hom.ext
    simp [Category.assoc]

/-- Forgetful functor from enriched operad objects to symmetric collections. -/
def forget : OperadObj V ⥤ SymmetricCollection V where
  obj O := O.toCollection
  map F := F.toCollectionHom
  map_id O := Hom.id_toCollectionHom O
  map_comp F G := Hom.comp_toCollectionHom F G

instance : (forget (V := V)).Faithful where
  map_injective h := Hom.ext h

/-- A collection isomorphism that preserves the unit and substitution in the forward direction
defines a morphism of operads. -/
def homOfCollectionIso {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) : O ⟶ P where
  toCollectionHom := e.hom
  map_unit := mapUnit
  map_subst := mapSubst

/-- The inverse collection isomorphism automatically preserves the unit and substitution once the
forward direction does. -/
def invHomOfCollectionIso {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) : P ⟶ O where
  toCollectionHom := e.inv
  map_unit := by
    rw [← mapUnit, Category.assoc, e.hom_inv_id_app, Category.comp_id]
  map_subst X := by
    let sourceO := (substitutionSource O.toCollection).obj X
    let sourceP := (substitutionSource P.toCollection).obj X
    let targetO := O.toCollection.obj ⟨substitutionTotalObj X⟩
    let targetP := P.toCollection.obj ⟨substitutionTotalObj X⟩
    let substO : sourceO ⟶ targetO := by
      with_unfolding_all exact O.subst.app X
    let substP : sourceP ⟶ targetP := by
      with_unfolding_all exact P.subst.app X
    let homTarget : targetO ⟶ targetP := e.hom.app ⟨substitutionTotalObj X⟩
    let invTarget : targetP ⟶ targetO := e.inv.app ⟨substitutionTotalObj X⟩
    let sourceHom : sourceO ⟶ sourceP := HomData.sourceHom e.hom X
    let sourceInv : sourceP ⟶ sourceO := HomData.sourceHom e.inv X
    have hForward : substO ≫ homTarget = sourceHom ≫ substP := by
      with_unfolding_all exact mapSubst X
    have hSource : sourceInv ≫ sourceHom = 𝟙 sourceP := by
      have hComp : sourceInv ≫ sourceHom =
          HomData.sourceHom (e.inv ≫ e.hom) X :=
        (HomData.sourceHom_comp e.inv e.hom X).symm
      have hIso : HomData.sourceHom (e.inv ≫ e.hom) X =
          HomData.sourceHom (𝟙 P.toCollection) X :=
        congrArg (fun α => HomData.sourceHom α X) e.inv_hom_id
      have hId : HomData.sourceHom (𝟙 P.toCollection) X = 𝟙 sourceP :=
        HomData.sourceHom_id P.toCollection X
      exact hComp.trans (hIso.trans hId)
    with_unfolding_all
      change substP ≫ invTarget = sourceInv ≫ substO
    apply (cancel_mono homTarget).1
    calc
      (substP ≫ invTarget) ≫ homTarget = substP ≫ (invTarget ≫ homTarget) :=
        Category.assoc _ _ _
      _ = substP ≫ 𝟙 targetP :=
        congrArg (substP ≫ ·) (e.inv_hom_id_app ⟨substitutionTotalObj X⟩)
      _ = substP := Category.comp_id _
      _ = 𝟙 sourceP ≫ substP := (Category.id_comp _).symm
      _ = (sourceInv ≫ sourceHom) ≫ substP :=
        congrArg (· ≫ substP) hSource.symm
      _ = sourceInv ≫ (sourceHom ≫ substP) := Category.assoc _ _ _
      _ = sourceInv ≫ (substO ≫ homTarget) :=
        congrArg (sourceInv ≫ ·) hForward.symm
      _ = (sourceInv ≫ substO) ≫ homTarget := (Category.assoc _ _ _).symm

/-- Lift a collection isomorphism to an operad isomorphism. It suffices to prove unit and
substitution compatibility for the forward collection map. -/
def isoOfCollectionIso {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) : O ≅ P where
  hom := homOfCollectionIso e mapUnit mapSubst
  inv := invHomOfCollectionIso e mapUnit mapSubst
  hom_inv_id := by
    apply Hom.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    exact e.inv_hom_id

@[simp]
theorem homOfCollectionIso_toCollectionHom {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (homOfCollectionIso e mapUnit mapSubst).toCollectionHom = e.hom :=
  rfl

@[simp]
theorem invHomOfCollectionIso_toCollectionHom {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (invHomOfCollectionIso e mapUnit mapSubst).toCollectionHom = e.inv :=
  rfl

@[simp]
theorem isoOfCollectionIso_hom_toCollectionHom {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (isoOfCollectionIso e mapUnit mapSubst).hom.toCollectionHom = e.hom :=
  rfl

@[simp]
theorem isoOfCollectionIso_inv_toCollectionHom {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (isoOfCollectionIso e mapUnit mapSubst).inv.toCollectionHom = e.inv :=
  rfl

end OperadObj

end CategoryTheory.Operad
