/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
public import Mathlib.CategoryTheory.Equivalence
public import MathlibExt.CategoryTheory.NerveCommonHom

/-!
# Weak equivalences from categorical nerve contractions

An equivalence of categories induces a realization weak equivalence on
nerves.  The proof realizes the simplicial homotopies supplied by the inverse
unit and counit of the categorical equivalence.

The terminal map from the nerve of a category with an initial object is also
a realization weak equivalence.  This uses an explicit section through
`Δ[0]`, the initial-object nerve contraction, and the canonical isomorphism
from `Δ[0]` to the chosen terminal simplicial set.

No claim is made that either simplicial map is an isomorphism, or that
categorical connectedness alone contracts a nerve.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

universe v u

namespace CategoryTheory

/-- The nerve map of an equivalence of categories is a realization weak
equivalence. -/
theorem nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
    {A B : Type u} [Category.{v} A] [Category.{v} B]
    (F : A ⥤ B) [F.IsEquivalence] :
    SSet.realizationWeakEquivalences (nerveMap F) := by
  let E : A ≌ B := F.asEquivalence
  let G : B ⥤ A := E.inverse
  have hleft : SSet.Homotopy
      (nerveMap E.functor ≫ nerveMap G)
      (𝟙 (nerve A : SSet.{max u v})) := by
    simpa only [nerveMap_comp, nerveMap_id] using
      (NatTrans.nerveHomotopy E.unitInv)
  have hright : SSet.Homotopy
      (nerveMap G ≫ nerveMap E.functor)
      (𝟙 (nerve B : SSet.{max u v})) := by
    simpa only [nerveMap_comp, nerveMap_id] using
      (NatTrans.nerveHomotopy E.counit)
  let e := SSet.realizedHomotopyEquiv
    (nerve A : SSet.{max u v}) (nerve B : SSet.{max u v})
    (nerveMap E.functor) (nerveMap G) hleft hright
  have hE : SSet.realizationWeakEquivalences
      (nerveMap E.functor) := by
    change TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (nerveMap E.functor))
    exact TopCat.mem_of_eq_toFun e rfl
  simpa only [E, Functor.asEquivalence_functor] using hE

end CategoryTheory

namespace NerveContractible

/-- If a category has an initial object, the canonical map from its nerve to
the chosen terminal simplicial set is a realization weak equivalence. -/
theorem terminal_from_mem_realizationWeakEquivalences_of_isInitial
    {C : Type u} [Category.{v} C] {X : C} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (terminal.from (CategoryTheory.nerve C)) := by
  let N : SSet.{max u v} := CategoryTheory.nerve C
  let q₀ : N ⟶ (Δ[0] : SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.from N
  let s : (Δ[0] : SSet.{max u v}) ⟶ N :=
    SSet.const (ComposableArrows.mk₀ X)
  have hqs : q₀ ≫ s = constNerveMap (C := C) X := by
    ext Δ Z
    rfl
  let η : (Functor.const C).obj X ⟶ 𝟭 C :=
    { app := fun Y => hX.to Y
      naturality := by
        intro Y Z f
        exact hX.hom_ext _ _ }
  have hconst : SSet.Homotopy
      (constNerveMap (C := C) X)
      (𝟙 (CategoryTheory.nerve C : SSet.{max u v})) := by
    simpa only [constNerveMap, CategoryTheory.nerveMap_id] using
      (CategoryTheory.NatTrans.nerveHomotopy η)
  have hleft : SSet.Homotopy (q₀ ≫ s) (𝟙 N) := by
    rw [hqs]
    exact hconst
  have hsq : s ≫ q₀ = 𝟙 (Δ[0] : SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hright : SSet.Homotopy (s ≫ q₀)
      (𝟙 (Δ[0] : SSet.{max u v})) := by
    rw [hsq]
    change SSet.RelativeMorphism.Homotopy
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
      (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))
    exact SSet.RelativeMorphism.Homotopy.refl _
  let e := SSet.realizedHomotopyEquiv
    N (Δ[0] : SSet.{max u v}) q₀ s hleft hright
  have hq₀ : SSet.realizationWeakEquivalences q₀ := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map q₀)
    exact TopCat.mem_of_eq_toFun e rfl
  let e₀ : (Δ[0] : SSet.{max u v}) ≅ (⊤_ SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal
  have htriangle : q₀ ≫ e₀.hom = terminal.from N :=
    terminal.hom_ext _ _
  have hPost := RespectsIso.postcomp
    SSet.realizationWeakEquivalences e₀.hom q₀ hq₀
  rw [htriangle] at hPost
  exact hPost

end NerveContractible

end

section CommonHomUp

universe uObj vObj wHom

namespace CategoryTheory

/-- An equivalence induces a weak native up map across object levels with common Hom levels. -/
theorem nerveMapCommonHomUp_mem_realizationWeakEquivalences_of_isEquivalence
    {A : Type uObj} [Category.{max vObj wHom} A]
    {B : Type (max uObj vObj)} [Category.{max vObj wHom} B]
    (F : A ⥤ B) [F.IsEquivalence] :
    SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{uObj, vObj, wHom} F) := by
  let E : A ≌ B := F.asEquivalence
  let G : B ⥤ A := E.inverse
  have hLeft : SSet.Homotopy
      (nerveMapCommonHomUp.{uObj, vObj, wHom} E.functor ≫ nerveMapCommonHom.{uObj, vObj, wHom} G)
      (𝟙 (nerve A : SSet.{max uObj vObj wHom})) := by
    rw [nerveMapCommonHomUp_comp, ← nerveMap_id]
    exact NatTrans.nerveHomotopy E.unitInv
  have hRight : SSet.Homotopy
      (nerveMapCommonHom.{uObj, vObj, wHom} G ≫ nerveMapCommonHomUp.{uObj, vObj, wHom} E.functor)
      (𝟙 (nerve B : SSet.{max uObj vObj wHom})) := by
    rw [nerveMapCommonHom_comp_up, ← nerveMap_id]
    exact NatTrans.nerveHomotopy E.counit
  let e := SSet.realizedHomotopyEquiv
    (nerve A : SSet.{max uObj vObj wHom}) (nerve B : SSet.{max uObj vObj wHom})
    (nerveMapCommonHomUp.{uObj, vObj, wHom} E.functor) (nerveMapCommonHom.{uObj, vObj, wHom} G)
      hLeft hRight
  have hE : SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{uObj, vObj, wHom} E.functor) :=
    by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map (nerveMapCommonHomUp.{uObj, vObj, wHom}
      E.functor))
    exact TopCat.mem_of_eq_toFun e rfl
  simpa only [E, Functor.asEquivalence_functor] using hE

end CategoryTheory

end CommonHomUp
