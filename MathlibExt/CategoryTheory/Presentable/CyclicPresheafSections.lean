/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.NatTrans.MonoFactorization
public import Mathlib.CategoryTheory.Subfunctor.OfSection
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Original cyclic presheaf pieces and their site-sized bound

Representable elements inject into the literal arrow type of the site. The
native range quotient gives the original map onto a cyclic piece, including
quotient orbits, and both endpoints of its intersection inclusion are bounded
by the same explicit site cardinal.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory.Subfunctor

variable {E : Type u} [SmallCategory E]

/-- A representable element is its original arrow, with its original domain. -/
def yonedaElementsArrow (a : E) : (yoneda.obj a).Elements → Arrow E :=
  fun s => Arrow.mk s.val

/-- The literal arrow retains enough data to recover the original element. -/
theorem yonedaElementsArrow_injective (a : E) :
    Function.Injective (yonedaElementsArrow a) := by
  intro s t h
  cases s with
  | @mk S s =>
    cases t with
    | @mk T t =>
      have hobj : S = T := congrArg (fun f : Arrow E => op f.left) h
      cases hobj
      have hval : s = t := (Arrow.mk_injective S.unop a) h
      cases hval
      rfl

/-- All original representable points are bounded by the literal site arrow type. -/
theorem mk_yoneda_elements_le_arrow (a : E) :
    Cardinal.mk (yoneda.obj a).Elements ≤ Cardinal.mk (Arrow E) :=
  Cardinal.mk_le_of_injective (yonedaElementsArrow_injective a)

variable {F : Eᵒᵖ ⥤ Type u} {a : E}

private theorem eqToIso_hom_ι {S T : Subfunctor F} (h : S = T) :
    (eqToIso (congrArg (fun A : Subfunctor F => A.toFunctor) h)).hom ≫ T.ι = S.ι := by
  cases h
  simp

/-- The original Yoneda natural map factors through its literal cyclic image. -/
def yonedaToOfSection (x : F.obj (op a)) : yoneda.obj a ⟶ (ofSection x).toFunctor :=
  toRange (yonedaEquiv.symm x) ≫
    (eqToIso (congrArg (fun A : Subfunctor F => A.toFunctor)
      (ofSection_eq_range x).symm)).hom

/-- The cyclic quotient retains the original ambient Yoneda natural map. -/
@[reassoc]
theorem yonedaToOfSection_comp_ι (x : F.obj (op a)) :
    yonedaToOfSection x ≫ (ofSection x).ι = yonedaEquiv.symm x := by
  rw [yonedaToOfSection, Category.assoc,
    eqToIso_hom_ι (ofSection_eq_range x).symm, toRange_ι]

/-- The native range epi remains epi after the actual range-to-cyclic equality. -/
instance epi_yonedaToOfSection (x : F.obj (op a)) : Epi (yonedaToOfSection x) := by
  dsimp only [yonedaToOfSection]
  infer_instance

/-- Each original site operator acts on the supplied original section. -/
theorem yonedaToOfSection_app_val (x : F.obj (op a)) (b : Eᵒᵖ) (f : b.unop ⟶ a) :
    ((yonedaToOfSection x).app b f).val = F.map f.op x := by
  have h := congrArg (fun k : yoneda.obj a ⟶ F => k.app b f)
    (yonedaToOfSection_comp_ι x)
  change ((yonedaToOfSection x).app b f).val = F.map f.op x at h
  exact h

/-- The actual cyclic quotient is surjective on total elements and preserves
each original site object and operator image. -/
theorem yonedaToOfSection_elements (x : F.obj (op a)) :
    Function.Surjective (yonedaToOfSection x).mapElements.obj ∧
      ∀ s : (yoneda.obj a).Elements,
        ((yonedaToOfSection x).mapElements.obj s).obj = s.obj ∧
          HEq (((yonedaToOfSection x).mapElements.obj s).val.val) (F.map s.val.op x) := by
  refine ⟨NatTrans.mapElements_obj_surjective (yonedaToOfSection x), ?_⟩
  intro s
  refine ⟨rfl, ?_⟩
  exact heq_of_eq (yonedaToOfSection_app_val x s.obj s.val)

/-- A cyclic image is bounded by the original site arrows, even when it is a quotient orbit. -/
theorem mk_elements_ofSection_le_arrow (x : F.obj (op a)) :
    Cardinal.mk (ofSection x).toFunctor.Elements ≤ Cardinal.mk (Arrow E) := by
  rw [ofSection_eq_range]
  exact (Subfunctor.mk_elements_range_le (yonedaEquiv.symm x)).trans
    (mk_yoneda_elements_le_arrow a)

/-- Both endpoints of the original intersection inclusion have the same
explicit infinite site-sized bound. No bound on the original U is assumed. -/
theorem cyclicSectionArrow_bounds (x : F.obj (op a)) (U : Subfunctor F) :
    let i := Arrow.mk (homOfLe (show U ⊓ ofSection x ≤ ofSection x from inf_le_right))
    Cardinal.mk i.left.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (Arrow E)) ∧
      Cardinal.mk i.right.Elements ≤ max Cardinal.aleph0 (Cardinal.mk (Arrow E)) := by
  change Cardinal.mk (U ⊓ ofSection x).toFunctor.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow E)) ∧
    Cardinal.mk (ofSection x).toFunctor.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow E))
  have h : Cardinal.mk (ofSection x).toFunctor.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow E)) :=
    (mk_elements_ofSection_le_arrow x).trans
      (le_max_right Cardinal.aleph0 (Cardinal.mk (Arrow E)))
  exact ⟨(Functor.mk_elements_le_of_mono
    (homOfLe (show U ⊓ ofSection x ≤ ofSection x from inf_le_right))).trans h, h⟩

end CategoryTheory.Subfunctor
