/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Nerve contractibility via initial and terminal objects

A natural transformation from a constant functor to the identity, or from the identity to a
constant functor, gives the corresponding simplicial contraction of the nerve.
After realization, either contraction makes the terminal map a realization weak equivalence.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace NerveContractible

/-- The constant endomorphism of `nerve C` at `X`. -/
noncomputable abbrev constNerveMap (X : C) :
    (nerve C : SSet.{max u v}) ⟶ (nerve C : SSet.{max u v}) :=
  nerveMap ((Functor.const C).obj X)

/-- The contraction from the constant map at an initial object to the identity. -/
noncomputable def homotopyOfIsInitial {X : C} (hX : IsInitial X) :
    SimplicialObject.Homotopy
      (constNerveMap (C := C) X)
      (𝟙 (nerve C : SSet.{max u v})) := by
  let η : (Functor.const C).obj X ⟶ 𝟭 C :=
    { app := fun Y => hX.to Y
      naturality := by
        intro Y Z f
        dsimp
        exact IsInitial.hom_ext hX _ _ }
  simpa only [constNerveMap, CategoryTheory.nerveMap_id] using
    (NatTrans.nerveHomotopy η).toSimplicialObjectHomotopy

/-- The contraction from the identity to the constant map at a terminal object. -/
noncomputable def homotopyOfIsTerminal {Y : C} (hY : IsTerminal Y) :
    SimplicialObject.Homotopy
      (𝟙 (nerve C : SSet.{max u v}))
      (constNerveMap (C := C) Y) := by
  let η : 𝟭 C ⟶ (Functor.const C).obj Y :=
    { app := fun X => hY.from X
      naturality := by
        intro X Z f
        dsimp
        exact IsTerminal.hom_ext hY _ _ }
  simpa only [constNerveMap, CategoryTheory.nerveMap_id] using
    (NatTrans.nerveHomotopy η).toSimplicialObjectHomotopy

/-- The nerve of a category with an initial object contracts to that object. -/
theorem nerve_homotopy_const_of_isInitial {X : C} (hX : IsInitial X) :
    Nonempty
      (SimplicialObject.Homotopy
        (constNerveMap (C := C) X)
        (𝟙 (nerve C : SSet.{max u v}))) :=
  ⟨homotopyOfIsInitial hX⟩

/-- The nerve of a category with a terminal object contracts to that object. -/
theorem nerve_homotopy_of_isTerminal {Y : C} (hY : IsTerminal Y) :
    Nonempty
      (SimplicialObject.Homotopy
        (𝟙 (nerve C : SSet.{max u v}))
        (constNerveMap (C := C) Y)) :=
  ⟨homotopyOfIsTerminal hY⟩

/-- A category with an initial object has a contractible nerve. -/
theorem nerve_homotopy_of_hasInitial [HasInitial C] :
    Nonempty
      (SimplicialObject.Homotopy
        (constNerveMap (C := C) (⊥_ C))
        (𝟙 (nerve C : SSet.{max u v}))) :=
  nerve_homotopy_const_of_isInitial initialIsInitial

/-- A category with a terminal object has a contractible nerve. -/
theorem nerve_homotopy_of_hasTerminal [HasTerminal C] :
    Nonempty
      (SimplicialObject.Homotopy
        (𝟙 (nerve C : SSet.{max u v}))
        (constNerveMap (C := C) (⊤_ C))) :=
  nerve_homotopy_of_isTerminal terminalIsTerminal

private noncomputable def terminalSection (X : C) :
    (⊤_ SSet.{max u v}) ⟶ (nerve C : SSet.{max u v}) :=
  SSet.const (nerveEquiv.symm X)

private theorem terminal_comp_terminalSection (X : C) :
    terminal.from (nerve C : SSet.{max u v}) ≫ terminalSection X =
      constNerveMap X := by
  ext n x
  rfl

private noncomputable def actualHomotopyOfIsInitial {X : C} (hX : IsInitial X) :
    SSet.Homotopy (constNerveMap X) (𝟙 (nerve C : SSet.{max u v})) := by
  let η : (Functor.const C).obj X ⟶ 𝟭 C :=
    { app := fun Y => hX.to Y
      naturality := by
        intro Y Z f
        dsimp
        exact IsInitial.hom_ext hX _ _ }
  simpa only [constNerveMap, CategoryTheory.nerveMap_id] using
    NatTrans.nerveHomotopy η

private noncomputable def actualHomotopyOfIsTerminal {Y : C} (hY : IsTerminal Y) :
    SSet.Homotopy (𝟙 (nerve C : SSet.{max u v})) (constNerveMap Y) := by
  let η : 𝟭 C ⟶ (Functor.const C).obj Y :=
    { app := fun X => hY.from X
      naturality := by
        intro X Z f
        dsimp
        exact IsTerminal.hom_ext hY _ _ }
  simpa only [constNerveMap, CategoryTheory.nerveMap_id] using
    NatTrans.nerveHomotopy η

/-- The terminal map from the nerve of a category with a chosen initial object
is a realization weak equivalence. -/
theorem nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial
    {X : C} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) := by
  let f := terminal.from (nerve C : SSet.{max u v})
  let g := terminalSection X
  have hfg : SSet.Homotopy (f ≫ g) (𝟙 (nerve C : SSet.{max u v})) := by
    simpa only [f, g, terminal_comp_terminalSection] using
      actualHomotopyOfIsInitial hX
  have hgf : SSet.Homotopy (g ≫ f) (𝟙 (⊤_ SSet.{max u v})) := by
    have heq : g ≫ f = 𝟙 (⊤_ SSet.{max u v}) := Subsingleton.elim _ _
    rw [heq]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    exact SSet.RelativeMorphism.Homotopy.refl _
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (terminal.from (nerve C : SSet.{max u v})))
  exact TopCat.mem_of_eq_toFun
    (SSet.realizedHomotopyEquiv _ _ f g hfg hgf) rfl

/-- The terminal map from the nerve of a category with a chosen terminal
object is a realization weak equivalence. -/
theorem nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
    {Y : C} (hY : IsTerminal Y) :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) := by
  let f := terminalSection Y
  let g := terminal.from (nerve C : SSet.{max u v})
  have hfg : SSet.Homotopy (f ≫ g) (𝟙 (⊤_ SSet.{max u v})) := by
    have heq : f ≫ g = 𝟙 (⊤_ SSet.{max u v}) := Subsingleton.elim _ _
    rw [heq]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    exact SSet.RelativeMorphism.Homotopy.refl _
  have hid_comp : g ≫ f = constNerveMap Y :=
    terminal_comp_terminalSection Y
  have hgfReverse : SSet.Homotopy
      (𝟙 (nerve C : SSet.{max u v})) (g ≫ f) := by
    simpa only [hid_comp] using actualHomotopyOfIsTerminal hY
  let e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (⊤_ SSet.{max u v}))
      (SSet.toTop.obj (nerve C : SSet.{max u v})) :=
    { toFun := (SSet.toTop.map f).hom
      invFun := (SSet.toTop.map g).hom
      left_inv := by
        have h := SSet.realizeHomotopy _ _ (f ≫ g) (𝟙 _) hfg
        have h' : ContinuousMap.Homotopy
            ((SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom)
            (ContinuousMap.id _) := by
          simpa [Functor.map_comp, TopCat.hom_comp,
            Functor.map_id, TopCat.hom_id] using h
        exact ⟨h'⟩
      right_inv := by
        have h := SSet.realizeHomotopy _ _ (𝟙 _) (g ≫ f) hgfReverse
        have h' : ContinuousMap.Homotopy
            ((SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom)
            (ContinuousMap.id _) := by
          simpa [Functor.map_comp, TopCat.hom_comp,
            Functor.map_id, TopCat.hom_id] using h.symm
        exact ⟨h'⟩ }
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (terminal.from (nerve C : SSet.{max u v})))
  exact TopCat.mem_of_eq_invFun e rfl

/-- The terminal map from the nerve of a category with an initial object is a
realization weak equivalence. -/
theorem nerve_to_terminal_mem_realizationWeakEquivalences_of_hasInitial
    [HasInitial C] :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial
    initialIsInitial

/-- The terminal map from the nerve of a category with a terminal object is a
realization weak equivalence. -/
theorem nerve_to_terminal_mem_realizationWeakEquivalences_of_hasTerminal
    [HasTerminal C] :
    SSet.realizationWeakEquivalences
      (terminal.from (nerve C : SSet.{max u v})) :=
  nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal
    terminalIsTerminal

end NerveContractible

end
