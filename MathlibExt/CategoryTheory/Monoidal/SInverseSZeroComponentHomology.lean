/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.ConnectedComponents
public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The zero component of the additive S⁻¹S nerve

The nerve of the categorical zero component of additive `S⁻¹S` is
canonically isomorphic to the connected-component subcomplex of the full
nerve selected by `(0,0)`.  Under the homology decomposition by simplicial
connected components, its inclusion is therefore the corresponding
coproduct inclusion and is a split monomorphism.

This is a statement about the categorical nerve and simplicial homology.  It
does not identify a realized topological subspace and makes no telescope,
Bousfield--Kan, localization, plus-construction, or Quillen comparison claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory

private noncomputable def nervePiZeroFunctor
    {D : Type u} [Category.{v} D] :
    D ⥤ Discrete (SSet.π₀ (nerve D)) where
  obj X := Discrete.mk
    (SSet.π₀.mk (X := nerve D) (nerveEquiv.symm X))
  map f := Discrete.eqToHom' (SSet.π₀.sound (nerve.edgeMk f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private theorem nerve_piZero_eq_of_zigzag
    {D : Type u} [Category.{v} D] {X Y : D} (h : Zigzag X Y) :
    SSet.π₀.mk (X := nerve D) (nerveEquiv.symm X) =
      SSet.π₀.mk (X := nerve D) (nerveEquiv.symm Y) := by
  have h' := zigzag_obj_of_zigzag (nervePiZeroFunctor (D := D)) h
  exact CategoryTheory.eq_of_zigzag _ h'

namespace SInverseS

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The connected-component index in `nerve (Pair C)` selected by the
categorical zero-component base object. -/
noncomputable abbrev zeroComponentNerveIndex :
    SSet.π₀ (nerve (Pair C)) :=
  SSet.π₀.mk
    (nerveEquiv.symm (zeroComponentBaseObject (C := C)).obj)

/-- The connected-component subcomplex of `nerve (Pair C)` selected by
the categorical zero-component base object. -/
noncomputable abbrev zeroComponentNerveComponent :
    (nerve (Pair C)).Subcomplex :=
  SSet.π₀.component (zeroComponentNerveIndex C)

private theorem zeroComponentNerveMap_mem
    {D : SimplexCategoryᵒᵖ}
    (z : (nerve (ZeroComponent (C := C))).obj D) :
    (nerveMap (zeroComponentProperty (C := C)).ι).app D z ∈
      (zeroComponentNerveComponent C).obj D := by
  obtain ⟨⟨n⟩⟩ := D
  change SSet.π₀.mk
      ((nerve (Pair C)).map (⦋0⦌.const ⦋n⦌ 0).op
        ((nerveMap (zeroComponentProperty (C := C)).ι).app
          (op ⦋n⦌) z)) =
    zeroComponentNerveIndex C
  have hvertex :
      (nerve (Pair C)).map (⦋0⦌.const ⦋n⦌ 0).op
          ((nerveMap (zeroComponentProperty (C := C)).ι).app
            (op ⦋n⦌) z) =
        nerveEquiv.symm (z.obj ⟨0, by omega⟩).obj := by
    apply ComposableArrows.ext₀
    rfl
  rw [hvertex]
  apply nerve_piZero_eq_of_zigzag
  apply Pair.zigzag_of_difference_eq
  rw [(z.obj ⟨0, by omega⟩).property,
    (zeroComponentBaseObject (C := C)).property]

/-- The nerve map induced by the categorical zero-component inclusion has
range in the selected simplicial connected component. -/
theorem zeroComponentNerveMap_range :
    SSet.Subcomplex.range
        (nerveMap (zeroComponentProperty (C := C)).ι) ≤
      zeroComponentNerveComponent C := by
  intro D y hy
  obtain ⟨z, rfl⟩ := hy
  exact zeroComponentNerveMap_mem C z

/-- The nerve map induced by the categorical inclusion, with codomain
restricted to the selected simplicial connected component. -/
noncomputable def zeroComponentNerveToComponent :
    nerve (ZeroComponent (C := C)) ⟶
      (zeroComponentNerveComponent C : SSet) :=
  SSet.Subcomplex.lift
    (nerveMap (zeroComponentProperty (C := C)).ι)
    (zeroComponentNerveMap_range C)

private noncomputable def nerveDifference :
    SSet.π₀ (nerve (Pair C)) →
      Algebra.GrothendieckAddGroup (Skeleton C) :=
  SSet.π₀.lift (fun x => (nerveEquiv x).difference)
    (fun _ _ e => Hom.difference_eq (nerve.homEquiv e))

/-- Every object of a simplex in the selected nerve component has zero
Grothendieck difference. -/
theorem componentSimplex_obj_difference_zero
    (n : ℕ) (z : (zeroComponentNerveComponent C).obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    (z.1.obj i).difference = 0 := by
  have hcomponent := z.2
  change SSet.π₀.mk
      ((nerve (Pair C)).map (⦋0⦌.const ⦋n⦌ 0).op z.1) =
    zeroComponentNerveIndex C at hcomponent
  have hvertex :
      (nerve (Pair C)).map (⦋0⦌.const ⦋n⦌ 0).op z.1 =
        nerveEquiv.symm (z.1.obj ⟨0, by omega⟩) := by
    apply ComposableArrows.ext₀
    rfl
  rw [hvertex] at hcomponent
  have hzero := congrArg (nerveDifference C) hcomponent
  change (z.1.obj ⟨0, by omega⟩).difference =
    (zeroComponentBaseObject (C := C)).obj.difference at hzero
  rw [(zeroComponentBaseObject (C := C)).property] at hzero
  have hmap := Hom.difference_eq
    (z.1.map (homOfLE (Fin.zero_le i)))
  exact hmap.symm.trans hzero

/-- A simplex in the selected connected component, lifted objectwise to the
categorical zero component. -/
noncomputable def componentSimplexToZero
    (n : ℕ) (z : (zeroComponentNerveComponent C).obj (op ⦋n⦌)) :
    ComposableArrows (ZeroComponent (C := C)) n where
  obj i := ⟨z.1.obj i, componentSimplex_obj_difference_zero C n z i⟩
  map f := ObjectProperty.homMk (z.1.map f)
  map_id i := by
    apply ObjectProperty.hom_ext
    exact z.1.map_id i
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact z.1.map_comp f g

private theorem zeroComposableArrows_ext {n : ℕ}
    {F G : ComposableArrows (ZeroComponent (C := C)) n}
    (h :
      (((zeroComponentProperty (C := C)).ι.mapComposableArrows n).obj F) =
        (((zeroComponentProperty (C := C)).ι.mapComposableArrows n).obj G)) :
    F = G := by
  refine Functor.ext
    (fun i => ObjectProperty.FullSubcategory.ext
      (Functor.congr_obj h i)) ?_
  intro i j f
  apply ObjectProperty.hom_ext
  simpa using Functor.congr_hom h f

/-- Lift every simplex of the selected simplicial connected component to a
simplex in the categorical zero-component nerve. -/
noncomputable def zeroComponentNerveComponentToNerve :
    (zeroComponentNerveComponent C : SSet) ⟶
      nerve (ZeroComponent (C := C)) where
  app D := ↾fun z => componentSimplexToZero C D.unop.len z
  naturality := by
    intro D E f
    ext z
    apply zeroComposableArrows_ext C
    rfl

/-- The nerve of the categorical zero component is the connected-component
subcomplex of the full additive `S⁻¹S` nerve selected by `(0,0)`. -/
noncomputable def zeroComponentNerveIso :
    nerve (ZeroComponent (C := C)) ≅
      (zeroComponentNerveComponent C : SSet) where
  hom := zeroComponentNerveToComponent C
  inv := zeroComponentNerveComponentToNerve C
  hom_inv_id := by
    ext D z
    apply zeroComposableArrows_ext C
    rfl
  inv_hom_id := by
    ext D z
    apply Subtype.ext
    rfl

/-- The forward nerve comparison retains the underlying `Pair C` simplex. -/
@[simp]
theorem zeroComponentNerveIso_hom_app_val
    {D : SimplexCategoryᵒᵖ}
    (z : (nerve (ZeroComponent (C := C))).obj D) :
    ((zeroComponentNerveIso C).hom.app D z).1 =
      (nerveMap (zeroComponentProperty (C := C)).ι).app D z :=
  rfl

/-- The inverse nerve comparison retains every underlying `Pair C` object. -/
@[simp]
theorem zeroComponentNerveIso_inv_app_obj
    (n : ℕ) (z : (zeroComponentNerveComponent C).obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    (((zeroComponentNerveIso C).inv.app (op ⦋n⦌) z).obj i).obj =
      z.1.obj i :=
  rfl

/-- The inverse nerve comparison retains every underlying `Pair C` map. -/
@[simp]
theorem zeroComponentNerveIso_inv_app_map_hom
    (n : ℕ) (z : (zeroComponentNerveComponent C).obj (op ⦋n⦌))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    (((zeroComponentNerveIso C).inv.app (op ⦋n⦌) z).map f).hom =
      z.1.map f :=
  rfl

/-- The zero-component nerve isomorphism followed by the component
inclusion is the nerve map induced by the categorical inclusion. -/
@[reassoc]
theorem zeroComponentNerveIso_hom_comp_ι :
    (zeroComponentNerveIso C).hom ≫
        (zeroComponentNerveComponent C).ι =
      nerveMap (zeroComponentProperty (C := C)).ι := by
  exact SSet.Subcomplex.lift_ι
    (nerveMap (zeroComponentProperty (C := C)).ι)
    (zeroComponentNerveMap_range C)

/-- Homology of the categorical zero-component nerve is homology of the
selected connected-component subcomplex. -/
noncomputable def zeroComponentNerveHomologyIso
    (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    (nerve (ZeroComponent (C := C))).homology R n ≅
      (zeroComponentNerveComponent C : SSet).homology R n :=
  (SSet.homologyFunctor R n).mapIso (zeroComponentNerveIso C)

set_option backward.isDefEq.respectTransparency false in
/-- Under the homology decomposition of the full additive `S⁻¹S` nerve,
the categorical zero-component homology map is the selected coproduct
inclusion. -/
@[reassoc]
theorem zeroComponentHomologyMap_comp_homologyComponentsIso_hom
    (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    SSet.homologyMap
          (nerveMap (zeroComponentProperty (C := C)).ι) R n ≫
        (SSet.homologyComponentsIso (nerve (Pair C)) R n).hom =
      (zeroComponentNerveHomologyIso C R n).hom ≫
        Sigma.ι
          (fun d : SSet.π₀ (nerve (Pair C)) =>
            (SSet.π₀.component d : SSet.{max u v}).homology R n)
          (zeroComponentNerveIndex C) := by
  have h := congrArg (fun f => SSet.homologyMap f R n)
    (zeroComponentNerveIso_hom_comp_ι C)
  rw [SSet.homologyMap_comp] at h
  rw [← h, Category.assoc,
    SSet.homologyMap_component_ι_comp_homologyComponentsIso_hom]
  rfl

/-- The canonical splitting of the categorical zero-component homology map. -/
noncomputable def zeroComponentHomologyMapSplitMono
    (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    SplitMono (SSet.homologyMap
      (nerveMap (zeroComponentProperty (C := C)).ι) R n) where
  retraction :=
    (SSet.homologyComponentsIso (nerve (Pair C)) R n).hom ≫
      retraction (Sigma.ι
        (fun d : SSet.π₀ (nerve (Pair C)) =>
          (SSet.π₀.component d : SSet.{max u v}).homology R n)
        (zeroComponentNerveIndex C)) ≫
      (zeroComponentNerveHomologyIso C R n).inv
  id := by
    rw [← Category.assoc,
      zeroComponentHomologyMap_comp_homologyComponentsIso_hom]
    simp

/-- The categorical zero-component inclusion induces a split monomorphism
on simplicial homology. -/
noncomputable instance zeroComponentHomologyMap_isSplitMono
    (R : AddCommGrpCat.{max u v}) (n : ℕ) :
    IsSplitMono (SSet.homologyMap
      (nerveMap (zeroComponentProperty (C := C)).ι) R n) :=
  IsSplitMono.mk' (zeroComponentHomologyMapSplitMono C R n)

end SInverseS
end CategoryTheory

end
