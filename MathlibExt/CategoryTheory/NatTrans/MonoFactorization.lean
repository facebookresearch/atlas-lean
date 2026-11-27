/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Elements
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Factoring natural transformations through monomorphisms

A monomorphism between Type-valued functors is injective on its total category
of elements.  If the range of another natural transformation lies in the
range of that monomorphism, the native subfunctor range factorization gives
the unique whole natural transformation through it.

The construction retains every original indexing object and value.  It does
not assemble a natural transformation from unrelated pointwise choices: those
choices are used only to prove the range inclusion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A monomorphism of Type-valued functors is injective on total elements. -/
theorem NatTrans.mapElements_obj_injective {F G : C ⥤ Type w}
    (f : F ⟶ G) [Mono f] : Function.Injective f.mapElements.obj := by
  intro x y h
  cases x with
  | @mk X x =>
    cases y with
    | @mk Y y =>
      have hobj : X = Y := congrArg (fun z : G.Elements => z.obj) h
      cases hobj
      have hval : f.app X x = f.app X y :=
        eq_of_heq (Functor.Elements.mk.inj h).2
      have hf : Mono (f.app X) :=
        (NatTrans.mono_iff_mono_app f).mp inferInstance X
      have hxy : x = y := (mono_iff_injective (f.app X)).mp hf hval
      cases hxy
      rfl

/-- An epimorphism of Type-valued functors is surjective on total elements. -/
theorem NatTrans.mapElements_obj_surjective {F G : C ⥤ Type w}
    (f : F ⟶ G) [Epi f] : Function.Surjective f.mapElements.obj := by
  intro y
  have hf : Epi (f.app y.obj) :=
    (NatTrans.epi_iff_epi_app f).mp inferInstance y.obj
  obtain ⟨x, hx⟩ := (epi_iff_surjective (f.app y.obj)).mp hf y.val
  refine ⟨Functor.elementsMk F y.obj x, ?_⟩
  apply Functor.Elements.ext
    (f.mapElements.obj (Functor.elementsMk F y.obj x)) y rfl
  simpa only [eqToHom_refl, Functor.map_id, types_id_apply,
    NatTrans.mapElements] using hx

/-- Total elements do not increase under a monomorphism of Type-valued functors. -/
theorem Functor.mk_elements_le_of_mono {F G : C ⥤ Type w}
    (f : F ⟶ G) [Mono f] : Cardinal.mk F.Elements ≤ Cardinal.mk G.Elements :=
  Cardinal.mk_le_of_injective f.mapElements_obj_injective

/-- Total elements of the target of an epimorphism are bounded by those of its
source. -/
theorem Functor.mk_elements_le_of_epi {F G : C ⥤ Type w}
    (f : F ⟶ G) [Epi f] : Cardinal.mk G.Elements ≤ Cardinal.mk F.Elements :=
  Cardinal.mk_le_of_surjective f.mapElements_obj_surjective

/-- Taking the native range of a natural transformation does not increase its
total category of elements. -/
theorem Subfunctor.mk_elements_range_le {F G : C ⥤ Type w} (f : F ⟶ G) :
    Cardinal.mk (Subfunctor.range f).toFunctor.Elements ≤ Cardinal.mk F.Elements :=
  Functor.mk_elements_le_of_epi (Subfunctor.toRange f)

/-- Same-object pointwise preimages imply inclusion of native subfunctor ranges. -/
theorem Subfunctor.range_le_range_of_app {A B D : C ⥤ Type w}
    (f : A ⟶ D) (m : B ⟶ D)
    (h : ∀ (X : C) (x : A.obj X), ∃ y : B.obj X,
      m.app X y = f.app X x) :
    Subfunctor.range f ≤ Subfunctor.range m := by
  intro X _ hz
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, hy⟩ := h X x
  exact ⟨y, hy⟩

/-- The canonical whole natural transformation through a monomorphism whose
range contains the supplied map. -/
noncomputable def NatTrans.factorThruMono {A B D : C ⥤ Type w}
    (f : A ⟶ D) (m : B ⟶ D) [Mono m]
    (h : Subfunctor.range f ≤ Subfunctor.range m) : A ⟶ B :=
  Subfunctor.lift f h ≫ inv (Subfunctor.toRange m)

@[reassoc (attr := simp)]
theorem NatTrans.factorThruMono_comp {A B D : C ⥤ Type w}
    (f : A ⟶ D) (m : B ⟶ D) [Mono m]
    (h : Subfunctor.range f ≤ Subfunctor.range m) :
    factorThruMono f m h ≫ m = f := by
  let t := Subfunctor.toRange m
  have ht : inv t ≫ m = (Subfunctor.range m).ι := by
    calc
      inv t ≫ m = inv t ≫ (t ≫ (Subfunctor.range m).ι) :=
        congrArg (fun k => inv t ≫ k) (Subfunctor.toRange_ι m).symm
      _ = (Subfunctor.range m).ι := by simp [t]
  change (Subfunctor.lift f h ≫ inv t) ≫ m = f
  rw [Category.assoc, ht, Subfunctor.lift_ι]

/-- The canonical factor through a monomorphism is the unique such factor. -/
theorem NatTrans.factorThruMono_unique {A B D : C ⥤ Type w}
    (f : A ⟶ D) (m : B ⟶ D) [Mono m]
    (h : Subfunctor.range f ≤ Subfunctor.range m)
    (l : A ⟶ B) (hl : l ≫ m = f) :
    l = factorThruMono f m h := by
  apply (cancel_mono m).mp
  rw [hl, factorThruMono_comp]

end CategoryTheory
