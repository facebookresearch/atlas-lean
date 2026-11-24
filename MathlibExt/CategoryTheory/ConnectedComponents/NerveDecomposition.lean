/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The actual nerve of a disjoint union of categories

The inclusion cofan is a coproduct after taking nerves. Each composable chain
lies in the component of its first object. The proof uses the stock coproduct
criterion for types and pointwise colimits, and keeps the original inclusion
maps. The stock connected-component decomposition is also a strict category
isomorphism because its map on objects is bijective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v uA vA

public section

namespace CategoryTheory

private theorem postcompose_injective_of_injective_obj
    {A : Type uA} [Category.{vA} A] {B D : Type u} [Category.{max u v} B]
    [Category.{max u v} D] (H : B ⥤ D) [H.Faithful]
    (hH : Function.Injective H.obj) {F G : A ⥤ B} (h : F ⋙ H = G ⋙ H) : F = G := by
  let hObj : ∀ X, F.obj X = G.obj X := fun X => hH (Functor.congr_obj h X)
  refine Functor.ext hObj ?_
  intro X Y f
  apply H.map_injective
  have hMap := Functor.congr_hom h f
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using hMap

namespace NerveDecomposition

variable {I : Type u} {C : I → Type u} [∀ i, Category.{max u v} (C i)]

private def tagProperty (i : I) : ObjectProperty (Σ j, C j) := fun X => X.1 = i

private abbrev Tagged (i : I) := (tagProperty (C := C) i).FullSubcategory

private def taggedInclusion (i : I) : C i ⥤ Tagged (C := C) i :=
  ObjectProperty.lift (tagProperty (C := C) i) (CategoryTheory.Sigma.incl i)
    (fun _ => rfl)

private theorem taggedInclusion_bijective (i : I) :
    Function.Bijective (taggedInclusion (C := C) i).obj := by
  constructor
  · intro X Y h
    exact sigma_mk_injective (congrArg ObjectProperty.FullSubcategory.obj h)
  · rintro ⟨⟨j, X⟩, h⟩
    change j = i at h
    subst j
    exact ⟨X, rfl⟩

private instance taggedInclusion_full (i : I) :
    (taggedInclusion (C := C) i).Full where
  map_surjective := by
    intro X Y f
    cases f with
    | mk f =>
      cases f with
      | mk f => exact ⟨f, rfl⟩

private instance taggedInclusion_faithful (i : I) :
    (taggedInclusion (C := C) i).Faithful where
  map_injective := by
    intro X Y f g h
    have h' := congrArg InducedCategory.Hom.hom h
    exact CategoryTheory.Sigma.SigmaHom.mk.inj h'

private def taggedIso (i : I) : IsoCat (C i) (Tagged (C := C) i) := by
  letI : (taggedInclusion (C := C) i).IsIso :=
    { bijective_obj := taggedInclusion_bijective i }
  exact (taggedInclusion (C := C) i).asIsomorphism

private theorem tag_eq_of_hom {X Y : Σ i, C i} (f : X ⟶ Y) : X.1 = Y.1 := by
  cases f
  rfl

private theorem nerve_inclusion_jointly_surjective (n : SimplexCategoryᵒᵖ)
    (F : (nerve (Σ i, C i)).obj n) :
    ∃ (i : I) (X : (nerve (C i)).obj n),
      (nerveMap (CategoryTheory.Sigma.incl i)).app n X = F := by
  let i : I := (F.obj (0 : Fin (n.unop.len + 1))).1
  have hTag : ∀ j, tagProperty (C := C) i (F.obj j) := by
    intro j
    exact (tag_eq_of_hom (F.map (homOfLE (Fin.zero_le j)))).symm
  let L := ObjectProperty.lift (tagProperty (C := C) i) F hTag
  let e := taggedIso (C := C) i
  let X : (nerve (C i)).obj n := L ⋙ e.inverse
  refine ⟨i, X, ?_⟩
  change (L ⋙ e.inverse) ⋙ CategoryTheory.Sigma.incl i = F
  have hIncl : e.functor ⋙ (tagProperty (C := C) i).ι =
      CategoryTheory.Sigma.incl i := rfl
  rw [← hIncl, Functor.assoc, ← Functor.assoc e.inverse e.functor,
    e.counit_eq, Functor.id_comp]
  rfl

private theorem nerve_inclusion_injective (i : I) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((nerveMap (CategoryTheory.Sigma.incl (C := C) i)).app n) := by
  intro X Y h
  let H : C i ⥤ (Σ j, C j) := CategoryTheory.Sigma.incl i
  exact postcompose_injective_of_injective_obj H sigma_mk_injective h

private theorem nerve_inclusion_eq_index (n : SimplexCategoryᵒᵖ)
    {i j : I} (X : (nerve (C i)).obj n) (Y : (nerve (C j)).obj n)
    (h : (nerveMap (CategoryTheory.Sigma.incl i)).app n X =
      (nerveMap (CategoryTheory.Sigma.incl j)).app n Y) : i = j := by
  exact congrArg (fun F => (F.obj (0 : Fin (n.unop.len + 1))).1) h

/-- The cofan consists of the actual nerves of the original categorical inclusions. -/
def nerveSigmaCofan (C : I → Type u) [∀ i, Category.{max u v} (C i)] :
    Cofan (fun i => nerve (C i)) :=
  Cofan.mk (nerve (Σ i, C i)) (fun i => nerveMap (CategoryTheory.Sigma.incl i))

/-- Every simplex belongs to one original summand, so this is the entire coproduct cofan. -/
def nerveSigmaCofanIsColimit : IsColimit (nerveSigmaCofan C) := by
  apply evaluationJointlyReflectsColimits
  intro n
  let c : Cofan (fun i => (nerve (C i)).obj n) :=
    Cofan.mk ((nerve (Σ i, C i)).obj n)
      (fun i => (nerveMap (CategoryTheory.Sigma.incl i)).app n)
  have h : c.cofanTypes.IsColimit := CofanTypes.isColimit_mk _
    (nerve_inclusion_jointly_surjective n)
    (fun i => nerve_inclusion_injective i n)
    (fun i j X Y h => nerve_inclusion_eq_index n X Y h)
  exact (isColimitMapCoconeCofanMkEquiv
    ((evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj n)
    (fun i => nerve (C i)) (fun i => nerveMap (CategoryTheory.Sigma.incl i))).symm
      (Classical.choice ((Cofan.isColimit_cofanTypes_iff c).mp h))

/-- The whole nerve of the disjoint union, with the original coproduct inclusions. -/
def nerveSigmaIso : (∐ fun i => nerve (C i)) ≅ nerve (Σ i, C i) :=
  colimit.isoColimitCocone ⟨nerveSigmaCofan C, nerveSigmaCofanIsColimit⟩

/-- The forward comparison retains each entire original simplex inclusion. -/
theorem nerveSigmaIso_ι (i : I) :
    Limits.Sigma.ι (fun i => nerve (C i)) i ≫ (nerveSigmaIso (C := C)).hom =
      nerveMap (CategoryTheory.Sigma.incl i) :=
  colimit.isoColimitCocone_ι_hom
    ⟨nerveSigmaCofan C, nerveSigmaCofanIsColimit⟩ ⟨i⟩

/-- The inverse comparison returns the same original summand and simplex. -/
theorem nerveSigmaIso_inv_ι (i : I) :
    nerveMap (CategoryTheory.Sigma.incl i) ≫ (nerveSigmaIso (C := C)).inv =
      Limits.Sigma.ι (fun i => nerve (C i)) i := by
  rw [← nerveSigmaIso_ι]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Limits.Sigma.ι (fun i => nerve (C i)) i ≫ k)
      (nerveSigmaIso (C := C)).hom_inv_id).trans (Category.comp_id _))

end NerveDecomposition

variable (J : Type u) [Category.{max u v} J]

/-- The stock decomposition is bijective on actual objects, including the original unit. -/
theorem decomposedTo_bijective_obj : Function.Bijective (decomposedTo J).obj := by
  constructor
  · rintro ⟨_, X, rfl⟩ ⟨_, Y, rfl⟩ h
    change X = Y at h
    subst Y
    rfl
  · intro X
    exact ⟨⟨ConnectedComponents.mk X, ⟨X, rfl⟩⟩, rfl⟩

/-- The stock whole component decomposition as a strict category isomorphism. -/
def decomposedIsoCat : IsoCat (Decomposed J) J := by
  letI : (decomposedTo J).IsIso := { bijective_obj := decomposedTo_bijective_obj J }
  exact (decomposedTo J).asIsomorphism

private theorem decomposedIsoCat_functor_computation :
    (decomposedIsoCat J).functor = decomposedTo J := rfl

/-- The strict isomorphism retains the actual stock forward decomposition functor. -/
theorem decomposedIsoCat_functor :
    (decomposedIsoCat J).functor = decomposedTo J :=
  decomposedIsoCat_functor_computation J

/-- The actual whole nerve comparison of the stock decomposition. -/
def decomposedNerveIso : nerve (Decomposed J) ≅ nerve J where
  hom := nerveMap (decomposedTo J)
  inv := nerveMap (decomposedIsoCat J).inverse
  hom_inv_id := by
    change nerveMap (decomposedIsoCat J).functor ≫
      nerveMap (decomposedIsoCat J).inverse = _
    rw [nerveMap_comp, ← (decomposedIsoCat J).unit_eq, nerveMap_id]
  inv_hom_id := by
    change nerveMap (decomposedIsoCat J).inverse ≫
      nerveMap (decomposedIsoCat J).functor = _
    rw [nerveMap_comp, (decomposedIsoCat J).counit_eq, nerveMap_id]

private theorem decomposedNerveIso_hom_computation :
    (decomposedNerveIso J).hom = nerveMap (decomposedTo J) := rfl

/-- The whole nerve comparison is the original stock forget-the-component map. -/
theorem decomposedNerveIso_hom :
    (decomposedNerveIso J).hom = nerveMap (decomposedTo J) :=
  decomposedNerveIso_hom_computation J

/-- The specified original object is retained by the actual forward comparison. -/
theorem decomposedNerveIso_hom_unit (X : J) :
    (decomposedNerveIso J).hom.app (op ⦋0⦌)
      (ComposableArrows.mk₀ ⟨ConnectedComponents.mk X, ⟨X, rfl⟩⟩) =
        ComposableArrows.mk₀ X :=
  nerveMap_app_mk₀ (decomposedTo J) _

end CategoryTheory
