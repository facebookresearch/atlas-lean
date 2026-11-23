/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.Basic
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedPushforward

/-!
# Homology coefficient functor of a cofibered category

For a cofibered functor `p : X ⥤ S`, chosen pushforwards between its strict
fibers induce a genuine functor from `S` to category homology.  Its functor
laws follow from homotopy invariance and the coherent unit and compositor of
the fiber pseudofunctor.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory
namespace Functor.IsCofibered

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]
  {p : CategoryTheory.Functor X S} [p.IsCofibered]
  (A : Type u₃) [Category.{v₃} A] [Preadditive A]
  [HasCoproducts.{max u₂ v₂} A] [CategoryWithHomology A]

/-- The degree-`n` homology of the strict fibers of a cofibered functor,
with transport induced by chosen cocartesian pushforwards. -/
noncomputable def fiberHomologyFunctor (R : A) (n : ℕ) :
    CategoryTheory.Functor S A where
  obj s := (categoryHomologyFunctor A R n).obj (Cat.of (p.Fiber s))
  map {s t} f :=
    (categoryHomologyFunctor A R n).map
      (fiberPushforwardFunctor (p := p) f).toCatHom
  map_id s := by
    let H : CategoryTheory.Functor Cat.{v₂, u₂} A :=
      categoryHomologyFunctor A R n
    calc
      H.map (fiberPushforwardFunctor (p := p) (𝟙 s)).toCatHom =
          H.map (𝟭 (p.Fiber s)).toCatHom :=
        categoryHomologyMap_eq_of_natTrans A
          (fiberPushforwardIdIso (p := p)).hom R n
      _ = 𝟙 _ := by
        change H.map (𝟙 (Cat.of (p.Fiber s))) = 𝟙 _
        exact H.map_id (Cat.of (p.Fiber s))
  map_comp {s t u} f g := by
    let H : CategoryTheory.Functor Cat.{v₂, u₂} A :=
      categoryHomologyFunctor A R n
    calc
      H.map (fiberPushforwardFunctor (p := p) (f ≫ g)).toCatHom =
          H.map (fiberPushforwardFunctor (p := p) f ⋙
            fiberPushforwardFunctor g).toCatHom :=
        (categoryHomologyMap_eq_of_natTrans A
          (fiberPushforwardCompIso (p := p) f g).hom R n).symm
      _ = H.map (fiberPushforwardFunctor (p := p) f).toCatHom ≫
          H.map (fiberPushforwardFunctor (p := p) g).toCatHom := by
        change H.map ((fiberPushforwardFunctor (p := p) f).toCatHom ≫
            (fiberPushforwardFunctor (p := p) g).toCatHom) = _
        exact H.map_comp
          (fiberPushforwardFunctor (p := p) f).toCatHom
          (fiberPushforwardFunctor (p := p) g).toCatHom

@[simp]
theorem fiberHomologyFunctor_obj (R : A) (n : ℕ) (s : S) :
    (fiberHomologyFunctor (p := p) A R n).obj s =
      (nerve (p.Fiber s)).homology R n := rfl

@[simp]
theorem fiberHomologyFunctor_map (R : A) (n : ℕ)
    {s t : S} (f : s ⟶ t) :
    (fiberHomologyFunctor (p := p) A R n).map f =
      SSet.homologyMap
        (nerveMap (fiberPushforwardFunctor (p := p) f)) R n := rfl

end Functor.IsCofibered
end CategoryTheory

end
