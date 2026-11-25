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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Basic

/-!
# Morphisms of fixed-color enriched operads

Morphisms are natural transformations of the underlying colored symmetric collections preserving
the color-indexed units and simultaneous substitution. The resulting category has a faithful
forgetful functor to colored symmetric collections.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

namespace HomData

/-- The morphism of substitution-factor families induced by a natural transformation of colored
symmetric collections. -/
def factorHom {O P : ColoredSymmetricCollection Color V} (α : O ⟶ P)
    (d : ColoredSubstitutionData Color) :
    (substitutionFactors O).obj d ⟶ (substitutionFactors P).obj d :=
  (FiniteFamily.mapNatTrans α).app d.factorFamily

/-- Tensor the factor-family morphism induced by a collection morphism. -/
def sourceHom {O P : ColoredSymmetricCollection Color V} (α : O ⟶ P)
    (d : ColoredSubstitutionData Color) :
    (substitutionSource O).obj d ⟶ (substitutionSource P).obj d :=
  (FiniteTensor.tensor (V := V)).map (factorHom α d)

omit [FiniteTensor V] in
theorem factorHom_id (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    factorHom (𝟙 O) d = 𝟙 ((substitutionFactors O).obj d) := by
  change
    ((FiniteFamily.mapFunctor (C₁ := ColoredProfile Color) (D := V)).map (𝟙 O)).app
        d.factorFamily = 𝟙 _
  exact congrArg (fun τ => τ.app d.factorFamily)
    ((FiniteFamily.mapFunctor (C₁ := ColoredProfile Color) (D := V)).map_id O)

theorem sourceHom_id (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    sourceHom (𝟙 O) d = 𝟙 _ := by
  unfold sourceHom
  rw [factorHom_id]
  exact (FiniteTensor.tensor (V := V)).map_id _

omit [FiniteTensor V] in
theorem factorHom_comp {O P Q : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) (β : P ⟶ Q) (d : ColoredSubstitutionData Color) :
    factorHom (α ≫ β) d = (factorHom α d).comp (factorHom β d) := by
  change
    ((FiniteFamily.mapFunctor (C₁ := ColoredProfile Color) (D := V)).map (α ≫ β)).app
        d.factorFamily =
      (((FiniteFamily.mapFunctor (C₁ := ColoredProfile Color) (D := V)).map α).app
        d.factorFamily).comp
        (((FiniteFamily.mapFunctor (C₁ := ColoredProfile Color) (D := V)).map β).app
          d.factorFamily)
  exact congrArg (fun τ => τ.app d.factorFamily)
    ((FiniteFamily.mapFunctor (C₁ := ColoredProfile Color) (D := V)).map_comp α β)

theorem sourceHom_comp {O P Q : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) (β : P ⟶ Q) (d : ColoredSubstitutionData Color) :
    sourceHom (α ≫ β) d = sourceHom α d ≫ sourceHom β d := by
  unfold sourceHom
  rw [factorHom_comp]
  exact (FiniteTensor.tensor (V := V)).map_comp (factorHom α d) (factorHom β d)

end HomData

/-- A morphism of enriched colored operads with the color type fixed. -/
structure Hom (O P : ColoredOperadObj Color V) where
  /-- The underlying morphism of colored symmetric collections. -/
  toCollectionHom : O.toCollection ⟶ P.toCollection
  /-- Preservation of each color-indexed unit. -/
  map_unit : ∀ c,
    O.unit c ≫ toCollectionHom.app (ColoredSubstitutionData.unitProfile c) = P.unit c
  /-- Preservation of simultaneous color-matching substitution. -/
  map_subst : ∀ d,
    O.subst.app d ≫ toCollectionHom.app d.totalProfile =
      HomData.sourceHom toCollectionHom d ≫ P.subst.app d

namespace Hom

@[ext]
theorem ext {O P : ColoredOperadObj Color V} {F G : Hom O P}
    (h : F.toCollectionHom = G.toCollectionHom) : F = G := by
  cases F
  cases G
  subst h
  rfl

/-- Identity morphism of a fixed-color enriched operad. -/
def id (O : ColoredOperadObj Color V) : Hom O O where
  toCollectionHom := 𝟙 O.toCollection
  map_unit c := by
    simp
  map_subst d := by
    rw [HomData.sourceHom_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Composition of fixed-color enriched-operad morphisms. -/
def comp {O P Q : ColoredOperadObj Color V} (F : Hom O P) (G : Hom P Q) : Hom O Q where
  toCollectionHom := F.toCollectionHom ≫ G.toCollectionHom
  map_unit c := by
    calc
      O.unit c ≫ (F.toCollectionHom ≫ G.toCollectionHom).app
          (ColoredSubstitutionData.unitProfile c) =
          (O.unit c ≫ F.toCollectionHom.app (ColoredSubstitutionData.unitProfile c)) ≫
            G.toCollectionHom.app (ColoredSubstitutionData.unitProfile c) := by
              simp only [NatTrans.comp_app, Category.assoc]
      _ = P.unit c ≫ G.toCollectionHom.app (ColoredSubstitutionData.unitProfile c) := by
        rw [F.map_unit c]
      _ = Q.unit c := G.map_unit c
  map_subst d := by
    have h_app :
        NatTrans.app (F.toCollectionHom ≫ G.toCollectionHom) d.totalProfile =
          F.toCollectionHom.app d.totalProfile ≫
            G.toCollectionHom.app d.totalProfile := rfl
    have h1 :
        O.subst.app d ≫
            NatTrans.app (F.toCollectionHom ≫ G.toCollectionHom) d.totalProfile =
          O.subst.app d ≫
            (F.toCollectionHom.app d.totalProfile ≫
              G.toCollectionHom.app d.totalProfile) :=
      congrArg (fun t => O.subst.app d ≫ t) h_app
    have h2 :
        O.subst.app d ≫
            (F.toCollectionHom.app d.totalProfile ≫
              G.toCollectionHom.app d.totalProfile) =
          (O.subst.app d ≫ F.toCollectionHom.app d.totalProfile) ≫
            G.toCollectionHom.app d.totalProfile :=
      (Category.assoc _ _ _).symm
    have h3 :
        (O.subst.app d ≫ F.toCollectionHom.app d.totalProfile) ≫
            G.toCollectionHom.app d.totalProfile =
          (HomData.sourceHom F.toCollectionHom d ≫ P.subst.app d) ≫
            G.toCollectionHom.app d.totalProfile :=
      congrArg (fun t => t ≫ G.toCollectionHom.app d.totalProfile) (F.map_subst d)
    have h4 :
        (HomData.sourceHom F.toCollectionHom d ≫ P.subst.app d) ≫
            G.toCollectionHom.app d.totalProfile =
          HomData.sourceHom F.toCollectionHom d ≫
            (P.subst.app d ≫ G.toCollectionHom.app d.totalProfile) :=
      Category.assoc _ _ _
    have h5 :
        HomData.sourceHom F.toCollectionHom d ≫
            (P.subst.app d ≫ G.toCollectionHom.app d.totalProfile) =
          HomData.sourceHom F.toCollectionHom d ≫
            (HomData.sourceHom G.toCollectionHom d ≫ Q.subst.app d) :=
      congrArg (fun t => HomData.sourceHom F.toCollectionHom d ≫ t) (G.map_subst d)
    have h6 :
        HomData.sourceHom F.toCollectionHom d ≫
            (HomData.sourceHom G.toCollectionHom d ≫ Q.subst.app d) =
          (HomData.sourceHom F.toCollectionHom d ≫
            HomData.sourceHom G.toCollectionHom d) ≫ Q.subst.app d :=
      (Category.assoc _ _ _).symm
    have h7 :
        (HomData.sourceHom F.toCollectionHom d ≫
            HomData.sourceHom G.toCollectionHom d) ≫ Q.subst.app d =
          HomData.sourceHom (F.toCollectionHom ≫ G.toCollectionHom) d ≫
            Q.subst.app d := by
      rw [HomData.sourceHom_comp]
    exact (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7

@[simp]
theorem id_toCollectionHom (O : ColoredOperadObj Color V) :
    (id O).toCollectionHom = 𝟙 O.toCollection :=
  rfl

@[simp]
theorem comp_toCollectionHom {O P Q : ColoredOperadObj Color V} (F : Hom O P) (G : Hom P Q) :
    (comp F G).toCollectionHom = F.toCollectionHom ≫ G.toCollectionHom :=
  rfl

end Hom

instance instCategory : Category (ColoredOperadObj Color V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
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

/-- Forgetful functor to colored symmetric collections. -/
def forget : ColoredOperadObj Color V ⥤ ColoredSymmetricCollection Color V where
  obj O := O.toCollection
  map F := F.toCollectionHom
  map_id O := Hom.id_toCollectionHom O
  map_comp F G := Hom.comp_toCollectionHom F G

instance forget_faithful : (forget (Color := Color) (V := V)).Faithful where
  map_injective h := Hom.ext h

/-- A collection isomorphism that preserves units and substitution in the forward direction
defines a morphism of colored operads. -/
def homOfCollectionIso {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) : O ⟶ P where
  toCollectionHom := e.hom
  map_unit := mapUnit
  map_subst := mapSubst

/-- The inverse collection isomorphism automatically preserves units and substitution once the
forward direction does. -/
def invHomOfCollectionIso {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) : P ⟶ O where
  toCollectionHom := e.inv
  map_unit c := by
    rw [← mapUnit c, Category.assoc, e.hom_inv_id_app, Category.comp_id]
  map_subst d := by
    let sourceO := (substitutionSource O.toCollection).obj d
    let sourceP := (substitutionSource P.toCollection).obj d
    let targetO := O.toCollection.obj d.totalProfile
    let targetP := P.toCollection.obj d.totalProfile
    let substO : sourceO ⟶ targetO := by
      with_unfolding_all exact O.subst.app d
    let substP : sourceP ⟶ targetP := by
      with_unfolding_all exact P.subst.app d
    let homTarget : targetO ⟶ targetP := e.hom.app d.totalProfile
    let invTarget : targetP ⟶ targetO := e.inv.app d.totalProfile
    let sourceHom : sourceO ⟶ sourceP := HomData.sourceHom e.hom d
    let sourceInv : sourceP ⟶ sourceO := HomData.sourceHom e.inv d
    have hForward : substO ≫ homTarget = sourceHom ≫ substP := by
      with_unfolding_all exact mapSubst d
    have hSource : sourceInv ≫ sourceHom = 𝟙 sourceP := by
      calc
        sourceInv ≫ sourceHom = HomData.sourceHom (e.inv ≫ e.hom) d :=
          (HomData.sourceHom_comp e.inv e.hom d).symm
        _ = HomData.sourceHom (𝟙 P.toCollection) d := by rw [e.inv_hom_id]
        _ = 𝟙 sourceP := HomData.sourceHom_id P.toCollection d
    with_unfolding_all
      change substP ≫ invTarget = sourceInv ≫ substO
    apply (cancel_mono homTarget).1
    calc
      (substP ≫ invTarget) ≫ homTarget = substP ≫ (invTarget ≫ homTarget) :=
        Category.assoc _ _ _
      _ = substP ≫ 𝟙 targetP :=
        congrArg (substP ≫ ·) (e.inv_hom_id_app d.totalProfile)
      _ = substP := Category.comp_id _
      _ = 𝟙 sourceP ≫ substP := (Category.id_comp _).symm
      _ = (sourceInv ≫ sourceHom) ≫ substP :=
        congrArg (· ≫ substP) hSource.symm
      _ = sourceInv ≫ (sourceHom ≫ substP) := Category.assoc _ _ _
      _ = sourceInv ≫ (substO ≫ homTarget) :=
        congrArg (sourceInv ≫ ·) hForward.symm
      _ = (sourceInv ≫ substO) ≫ homTarget := (Category.assoc _ _ _).symm

/-- Lift a collection isomorphism to a colored-operad isomorphism. It suffices to prove unit and
substitution compatibility for the forward collection map; compatibility of the inverse follows
categorically. -/
def isoOfCollectionIso {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) : O ≅ P where
  hom := homOfCollectionIso e mapUnit mapSubst
  inv := invHomOfCollectionIso e mapUnit mapSubst
  hom_inv_id := by
    apply Hom.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    exact e.inv_hom_id

@[simp]
theorem homOfCollectionIso_toCollectionHom {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) :
    (homOfCollectionIso e mapUnit mapSubst).toCollectionHom = e.hom :=
  rfl

@[simp]
theorem invHomOfCollectionIso_toCollectionHom {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) :
    (invHomOfCollectionIso e mapUnit mapSubst).toCollectionHom = e.inv :=
  rfl

@[simp]
theorem isoOfCollectionIso_hom_toCollectionHom {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) :
    (isoOfCollectionIso e mapUnit mapSubst).hom.toCollectionHom = e.hom :=
  rfl

@[simp]
theorem isoOfCollectionIso_inv_toCollectionHom {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) = P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        HomData.sourceHom e.hom d ≫ P.subst.app d) :
    (isoOfCollectionIso e mapUnit mapSubst).inv.toCollectionHom = e.inv :=
  rfl

end ColoredOperadObj

end CategoryTheory.Operad
