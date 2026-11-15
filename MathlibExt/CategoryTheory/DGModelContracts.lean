/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGSource.DGYoneda
public import MathlibExt.CategoryTheory.DGSource.DGTensorProduct
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Actual DG-category models, replacements and localized tensor

The objects are cochain-enriched categories, arrows are actual enriched
functors, and weak equivalences are the source-defined Hom
quasi-isomorphisms and H0 essential surjectivity. The ordinary localization
is Mathlib's formal localization of this category. Replacements are
actual DG categories with quasi-equivalent augmentation and the standard
lifting property. They do not contain an internal-Hom, degeneration or
Calabi--Yau conclusion.

The completed DG primitives are ports of TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9, retained under Apache 2.0 in
DGSource. References: Toën, arXiv:math/0408337v7, §§2--6; Keller,
*Deriving DG categories*, §§1--2. Source construction and theorem
providers are requested separately with these fixed native endpoints.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGModelContracts

open _root_.CategoryTheory MonoidalCategory
open MathlibExt.DGSource

universe u

variable (k : Type u) [CommRing k]

/-- The native coefficient cochain category. -/
abbrev Cochains := CochainComplex (ModuleCat.{u} k) ℤ

/-- A bundled actual cochain-enriched DG category. The carrier is its
object set, with the complete source-defined Hom/identity/composition
structure, rather than a Type named by a theory. -/
structure DGCat where
  carrier : Type u
  [dg : DGCategory k carrier]

attribute [instance] DGCat.dg

instance : CoeSort (DGCat k) (Type u) := ⟨DGCat.carrier⟩

/-- Bundle an actual source DG enrichment. -/
def DGCat.of (C : Type u) [DGCategory k C] : DGCat k := ⟨C⟩

instance : _root_.CategoryTheory.Category (DGCat k) where
  Hom C D := EnrichedFunctor (Cochains k) C D
  id C := EnrichedFunctor.id (Cochains k) C
  comp f g := f.comp (Cochains k) g
  id_comp f := by
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp, EnrichedFunctor.id]
  comp_id f := by
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp, EnrichedFunctor.id]
  assoc f g h := by
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp, Category.assoc]

/-- The actual quasi-equivalence predicate on DG functors. -/
def quasiEquivalences : MorphismProperty (DGCat k) :=
  fun _ _ f => EnrichedFunctor.IsQuasiEquivalence f

/-- Ho(dgCat), with actual formal inversion of the above functors. -/
abbrev HoDG := (quasiEquivalences k).Localization

/-- The native localization map. -/
abbrev toHo : DGCat k ⥤ HoDG k := (quasiEquivalences k).Q

variable {k}

/-- Actual H0 isomorphisms lift, with their specified images. -/
def IsIsofibration {C D : Type*} [Category C] [Category D] (F : C ⥤ D) : Prop :=
  ∀ (x : C) (y : D) (e : F.obj x ≅ y),
    ∃ (x' : C) (e' : x ≅ x') (h : F.obj x' = y), F.mapIso e' ≪≫ eqToIso h = e

/-- Tabuada's DG fibration conditions, stated on the actual Hom
complexes and the actual H0 functor. -/
def IsFibration {C D : DGCat k} (f : C ⟶ D) : Prop :=
  (∀ (X Y : C) (n : ℤ), Function.Surjective ((f.map X Y).f n)) ∧
    IsIsofibration f.mapDGHomotopyCategory

/-- An actual DG trivial fibration. -/
def IsTrivialFibration {C D : DGCat k} (f : C ⟶ D) : Prop :=
  IsFibration f ∧ EnrichedFunctor.IsQuasiEquivalence f

/-- The initial-object lifting formulation of DG cofibrancy. -/
def IsCofibrant (C : DGCat k) : Prop :=
  ∀ (D E : DGCat k) (p : D ⟶ E), IsTrivialFibration p →
    ∀ f : C ⟶ E, ∃ g : C ⟶ D, g ≫ p = f

/-- An actual augmented DG replacement. -/
structure CofibrantReplacement (C : DGCat k) where
  category : DGCat k
  augmentation : category ⟶ C
  cofibrant : IsCofibrant category
  trivialFibration : IsTrivialFibration augmentation

/-- Functorial replacement with its actual augmentation. No tensor
adjunction or mapping-space theorem is part of this input. -/
structure ReplacementFunctor (k : Type u) [CommRing k] where
  functor : DGCat k ⥤ DGCat k
  augmentation : functor ⟶ 𝟭 (DGCat k)
  cofibrant : ∀ C, IsCofibrant (functor.obj C)
  trivialFibration : ∀ C, IsTrivialFibration (augmentation.app C)

/-- The source ordinary DG tensor category. -/
def tensor (C D : DGCat k) : DGCat k := DGCat.of k (C × D)

/-- A DG tensor map is constrained on its actual object pairs and every
cochain Hom map. These conditions fix the product functor. -/
structure TensorMapModel {A B C D : DGCat k} (f : A ⟶ B) (g : C ⟶ D) where
  functor : tensor A C ⟶ tensor B D
  object_eq : ∀ x : A × C, functor.obj x = (f.obj x.1, g.obj x.2)
  map_eq : ∀ x y : A × C,
    functor.map x y ≫ eqToHom (by rw [object_eq x, object_eq y]; rfl) =
      f.map x.1 y.1 ⊗ₘ g.map x.2 y.2

/-- Localized tensor, normalized on actual objects and all localization
generators. It is a construction output, not a closedness assumption. -/
structure LocalizedTensorModel (Q : ReplacementFunctor k) (C : DGCat k) where
  functor : HoDG k ⥤ HoDG k
  object_eq : ∀ A : DGCat k,
    functor.obj ((toHo k).obj A) =
      (toHo k).obj (tensor (Q.functor.obj A) (Q.functor.obj C))
  map_eq : ∀ {A B : DGCat k} (f : A ⟶ B),
    ∃ m : TensorMapModel (Q.functor.map f) (𝟙 (Q.functor.obj C)),
      eqToHom (object_eq A).symm ≫ functor.map ((toHo k).map f) ≫
        eqToHom (object_eq B) = (toHo k).map m.functor

end MathlibExt.CategoryTheory.DGModelContracts
