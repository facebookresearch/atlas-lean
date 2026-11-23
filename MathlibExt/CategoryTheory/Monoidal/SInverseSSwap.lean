/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion

/-!
# Coordinate swap on additive S⁻¹S

Swapping the two coordinates of a pair, and the two coordinate
isomorphisms of every stabilized arrow, defines an involutive equivalence of
the additive `S⁻¹S` category.

This is the categorical inversion leaf used by the later component-splitting
argument.  No H-space, realization, or plus-construction claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C]

section Basic

variable [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Swap the two coordinates of a pair. -/
abbrev swapObj (X : Pair C) : Pair C := ⟨X.snd, X.fst⟩

namespace RawHom

/-- Swap the two coordinate isomorphisms of a raw stabilized arrow. -/
def swap {X Y : Pair C} (f : RawHom X Y) :
    RawHom (swapObj X) (swapObj Y) where
  stabilizer := f.stabilizer
  hom₁ := f.hom₂
  hom₂ := f.hom₁

omit [HasZeroObject C] in
/-- Raw coordinate swap respects change of stabilizer. -/
theorem swap_rel {X Y : Pair C} {f g : RawHom X Y}
    (h : f.Rel g) : f.swap.Rel g.swap := by
  obtain ⟨e, h₁, h₂⟩ := h
  exact ⟨e, h₂, h₁⟩

omit [HasZeroObject C] in
@[simp]
theorem swap_swap {X Y : Pair C} (f : RawHom X Y) : f.swap.swap = f :=
  rfl

@[simp]
theorem swap_id (X : Pair C) : (RawHom.id X).swap = RawHom.id (swapObj X) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem swap_comp {X Y Z : Pair C} (f : RawHom X Y) (g : RawHom Y Z) :
    (f.comp g).swap = f.swap.comp g.swap :=
  rfl

end RawHom

/-- Swap the coordinates of a quotient stabilized arrow. -/
def Hom.swap {X Y : Pair C} : Hom X Y → Hom (swapObj X) (swapObj Y) :=
  Quotient.map RawHom.swap (fun _ _ h ↦ RawHom.swap_rel h)

omit [HasZeroObject C] in
@[simp]
theorem Hom.swap_swap {X Y : Pair C} (f : Hom X Y) : f.swap.swap = f := by
  induction f using Quotient.inductionOn
  rfl

/-- Coordinate swap as an endofunctor of additive `S⁻¹S`. -/
def swapFunctor : Pair C ⥤ Pair C where
  obj := swapObj
  map := Hom.swap
  map_id X := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl

/-- Applying coordinate swap twice is naturally isomorphic to the identity. -/
noncomputable def swapInvolutionIso :
    swapFunctor (C := C) ⋙ swapFunctor ≅ 𝟭 (Pair C) :=
  NatIso.ofComponents (fun X ↦ Iso.refl X) (fun f ↦ by
    change f.swap.swap ≫ 𝟙 _ = 𝟙 _ ≫ f
    simp)

/-- Coordinate swap is an involutive equivalence of categories. -/
noncomputable def swapEquivalence : Pair C ≌ Pair C :=
  Equivalence.mk swapFunctor swapFunctor
    swapInvolutionIso.symm swapInvolutionIso

end Basic

section Difference

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- Coordinate swap negates the Grothendieck difference. -/
@[simp]
theorem Pair.difference_swapObj (X : Pair C) :
    (swapObj X).difference = -X.difference := by
  unfold Pair.difference swapObj
  abel

/-- On connected components, coordinate swap acts by negation under the
Grothendieck-group classification. -/
theorem connectedComponentsToGrothendieck_mapConnectedComponents_swap
    (x : ConnectedComponents (Pair C)) :
    connectedComponentsToGrothendieck
        ((swapFunctor (C := C)).mapConnectedComponents x) =
      -connectedComponentsToGrothendieck x := by
  induction x using Quotient.inductionOn with
  | _ X => exact Pair.difference_swapObj X

end Difference

end SInverseS
end CategoryTheory

end
