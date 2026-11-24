/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison

/-!
# Coefficient naturality of the elements comparison

For `C : Type u` with `Category.{v} C` and `α : L ⟶ L'`, the degreewise
elements comparison `replElementsEquiv` is natural in the coefficient functor:
comparing and then pushing forward along the nerve of
`α.mapElements` agrees with pushing coefficients forward along `α`
via `replCoeffMap` and then comparing. This promotes to naturality of the
simplicial comparison `replNerveSimplicialIso` against `replMap α`.

Nonclaims: no Data-level map/square, no helper, no base-change functor, and no
comma/Grothendieck/opposite/reversal comparison.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uL

namespace CategoryTheory

namespace CategoryBar

variable {C : Type u} [Category.{v} C]

/-- The degreewise elements comparison is natural in the coefficient functor. -/
theorem replElements_naturality {L L' : C ⥤ Type uL} (α : L ⟶ L') {n : ℕ}
    (x : replObj C L n) :
    (nerveMap α.mapElements).app
        (op (SimplexCategory.mk n))
        (replElementsEquiv C L n x) =
      replElementsEquiv C L' n (replCoeffMap α x) := by
  obtain ⟨F, l, _⟩ := x
  refine Functor.ext (fun i : Fin (n + 1) => ?_)
    (fun (i j : Fin (n + 1)) (f : i ⟶ j) => ?_)
  · refine Functor.Elements.ext _ _ rfl ?_
    have h := α.naturality_apply (F.map' 0 i.val) l
    change L'.map (eqToHom rfl) (α.app (F.obj i) (L.map (F.map' 0 i.val) l)) =
      L'.map (F.map' 0 i.val) (α.app F.left l)
    rw [eqToHom_refl, L'.map_id]
    exact h
  · apply Functor.Elements.hom_ext
    have hEq : ∀ {x y : L'.Elements} (h : x = y),
        (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
      intro x y h
      cases h
      rfl
    rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom, hEq, hEq]
    change F.map f = 𝟙 _ ≫ F.map f ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- The simplicial elements comparison is natural in the coefficient functor. -/
theorem replNerve_naturality {L L' : C ⥤ Type uL} (α : L ⟶ L') :
    replMap α ≫ (replNerveSimplicialIso L').hom =
      (replNerveSimplicialIso L).hom ≫
        nerveMap α.mapElements := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  change replElementsEquiv C L' n (replCoeffMap α x) =
    (nerveMap α.mapElements).app (op (SimplexCategory.mk n))
      (replElementsEquiv C L n x)
  exact (replElements_naturality α x).symm

end CategoryBar

end CategoryTheory
