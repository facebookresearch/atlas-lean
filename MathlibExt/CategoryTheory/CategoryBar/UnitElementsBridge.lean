/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.NerveComparison

/-!
# Unit-coefficient category-of-elements bridge

At unit coefficients (`ULift PUnit`), the category of elements of `unitCoeffL C`
is equivalent to the base category `C`: the projection forgets a subsingleton
coefficient and the section reattaches the canonical point. This promotes
degreewise to an equivalence between `ComposableArrows` of the elements and of
the base, and further to a simplicial-set isomorphism between the nerves.

Nonclaims: no comparison triangle, no right-coefficient isomorphism, no
comma/Grothendieck comparison, no opposite/reversal comparison, no contraction,
no homotopy, and no KQ statement.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CategoryTheory

namespace CategoryBar

/-- Section of the elements projection at unit coefficients. -/
noncomputable def unitElementsSection (C : Type u) [Category.{v} C] :
    C ⥤ (unitCoeffL C).Elements where
  obj X := (unitCoeffL C).elementsMk X (ULift.up (PUnit.unit : PUnit))
  map {X Y} f :=
    Functor.Elements.homMk f (by
      have hSub : Subsingleton ((unitCoeffL C).obj Y) := by
        change Subsingleton (ULift.{0} PUnit)
        infer_instance
      exact @Subsingleton.elim _ hSub _ _)
  map_id X := by
    apply Functor.Elements.hom_ext
    rfl
  map_comp f g := by
    apply Functor.Elements.hom_ext
    rfl

/-- The category of elements at unit coefficients is equivalent to the base. -/
noncomputable def unitElementsEquiv (C : Type u) [Category.{v} C] :
    (unitCoeffL C).Elements ≌ C where
  functor := Functor.Elements.π (unitCoeffL C)
  inverse := unitElementsSection C
  unitIso :=
    NatIso.ofComponents
      (fun X =>
        Functor.Elements.isoMk (Iso.refl _) (by
          have hSub : Subsingleton ((unitCoeffL C).obj X.obj) := by
            change Subsingleton (ULift.{0} PUnit)
            infer_instance
          exact @Subsingleton.elim _ hSub _ _))
      (by
        intro X Y f
        apply Functor.Elements.hom_ext
        simp only [Functor.Elements.comp_hom]
        change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
        simp)
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.comp_id _

@[simp] theorem unitElementsEquiv_functor (C : Type u) [Category.{v} C] :
    (unitElementsEquiv C).functor = Functor.Elements.π (unitCoeffL C) :=
  rfl

@[simp] theorem unitElementsEquiv_inverse (C : Type u) [Category.{v} C] :
    (unitElementsEquiv C).inverse = unitElementsSection C :=
  rfl

/-- Degreewise nerve equivalence through the elements projection. -/
noncomputable def unitElementsNerveEquiv (C : Type u) [Category.{v} C] (n : ℕ) :
    ComposableArrows (unitCoeffL C).Elements n ≃ ComposableArrows C n where
  toFun G := ((Functor.Elements.π (unitCoeffL C)).mapComposableArrows n).obj G
  invFun F := ((unitElementsSection C).mapComposableArrows n).obj F
  left_inv G := by
    refine Functor.ext (fun i => ?_) (fun i j f => ?_)
    · exact Functor.Elements.ext _ _ rfl (by
        have hSub : Subsingleton ((unitCoeffL C).obj (G.obj i).obj) := by
          change Subsingleton (ULift.{0} PUnit)
          infer_instance
        exact @Subsingleton.elim _ hSub _ _)
    · apply Functor.Elements.hom_ext
      have hEq : ∀ {x y : (unitCoeffL C).Elements} (h : x = y),
          (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
        intro x y h
        cases h
        rfl
      rw [Functor.Elements.comp_hom, Functor.Elements.comp_hom, hEq, hEq]
      change (G.map f).hom = _
      change (G.map f).hom = 𝟙 _ ≫ (G.map f).hom ≫ 𝟙 _
      simp
  right_inv F := by
    refine Functor.ext (fun i => rfl) (fun i j f => ?_)
    change F.map f = _
    change F.map f = 𝟙 _ ≫ F.map f ≫ 𝟙 _
    simp

/-- Nerve-level isomorphism induced by the unit-elements equivalence. -/
noncomputable def unitElementsNerveIso (C : Type u) [Category.{v} C] :
    nerve (unitCoeffL C).Elements ≅ nerve C :=
  NatIso.ofComponents (fun Δ => (unitElementsNerveEquiv C (Δ.unop.len)).toIso) (by
    intro Δ₁ Δ₂ f
    ext X
    rfl)

@[simp] theorem unitElementsNerveIso_hom (C : Type u) [Category.{v} C] :
    (unitElementsNerveIso C).hom =
      nerveMap (Functor.Elements.π (unitCoeffL C)) :=
  rfl

@[simp] theorem unitElementsNerveIso_inv (C : Type u) [Category.{v} C] :
    (unitElementsNerveIso C).inv = nerveMap (unitElementsSection C) :=
  rfl

end CategoryBar

end CategoryTheory
