/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMonomorphisms

/-!
# Terminal lifting and complete Segal locality

The full original auxiliary family lifts against the actual terminal map
exactly for the genuine complete Segal predicate. All raw horn/localizing
indices and every scalar boundary, including zero and the full E/x₀ branch,
are retained. Native terminal pullback-Hom and full lifting transposition
preserve both prescribed diagonal equations; no whole-Leibniz or auxiliary
weakness premise or global arbitrary-arrow localized fibration identity occurs.

Source: Rezk, A model for the homotopy theory of homotopy theory,
§9.1 and Proposition 6.4(3); the literal-family proof is the project bridge.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner Simplicial
namespace SimplicialSpace.LocalGenerators

private theorem boundary_terminal_iff (i : SSet.Rezk.LocalizingIndex)
    (n : ℕ) (Z : SimplicialSpace.{u}) :
    HasLiftingProperty (boundaryPushout.{u} i n).ι (terminal.from Z) ↔
      HasLiftingProperty (SSet.boundary.{u} n).ι
        ((innerHomFunctor.{u}.map (localizingArrow.{u} i).hom.op).app Z) := by
  let s := (localizingArrow.{u} i).hom
  let _ : (innerHomFunctor.{u}.obj (op (localizingArrow.{u} i).left)).IsRightAdjoint :=
    (innerTensorHomAdjunction₂.adj (localizingArrow.{u} i).left).isRightAdjoint
  let _ : (innerHomFunctor.{u}.obj (op (localizingArrow.{u} i).right)).IsRightAdjoint :=
    (innerTensorHomAdjunction₂.adj (localizingArrow.{u} i).right).isRightAdjoint
  let q := Functor.PullbackObjObj.ofIsTerminal innerHomFunctor.{u}
    s (terminal.from Z) terminalIsTerminal
  exact innerTensorHomAdjunction₂.hasLiftingProperty_iff
    (boundaryPushout.{u} i n) q

/-- Terminal RLP for the full literal auxiliary family is exactly complete Segal locality. -/
theorem terminal_rlp_iff_completeSegalSpaces (Z : SimplicialSpace.{u}) :
    J.{u}.rlp (terminal.from Z) ↔ completeSegalSpaces Z := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  constructor
  · intro h
    have hHorn : ReedyGeneratingFamilies.J.{u}.rlp (terminal.from Z) := by
      intro A B f hf
      rcases hf with ⟨horn⟩
      exact h _ (horn_mem horn)
    have hFib : IsFibrant Z := by
      rw [ReedyGeneratingFamilies.J_rlp_eq_fibrations.{u}] at hHorn
      exact (HomotopicalAlgebra.fibration_iff _).2 hHorn
    refine ⟨hFib, ?_⟩
    intro i
    let g := (innerHomFunctor.{u}.map (localizingArrow.{u} i).hom.op).app Z
    have hBound : SSet.modelCategoryQuillen.I.{u}.rlp g := by
      intro A B f hf
      rcases hf with ⟨n⟩
      exact (boundary_terminal_iff i n Z).1 (h _ (boundary_mem i n))
    have hTF : trivialFibrations SSet.{u} g := by
      rw [← SSet.rlp_monomorphisms] at hBound
      change (cofibrations SSet.{u}).rlp g at hBound
      rw [cofibrations_rlp SSet.{u}] at hBound
      exact hBound
    exact hTF.2
  · intro hZ
    have hHorn : ReedyGeneratingFamilies.J.{u}.rlp (terminal.from Z) := by
      rw [ReedyGeneratingFamilies.J_rlp_eq_fibrations.{u}]
      exact (HomotopicalAlgebra.fibration_iff _).1 hZ.1
    have hBound (i : SSet.Rezk.LocalizingIndex) (n : ℕ) :
        HasLiftingProperty (boundaryPushout.{u} i n).ι (terminal.from Z) := by
      let s := (localizingArrow.{u} i).hom
      have hsMono : Mono s := SimplicialSpace.localizingMap_mono i
      have hsCof : cofibrations SimplicialSpace.{u} s :=
        (HomotopicalAlgebra.cofibration_iff s).1 ((ReedyModel.cofibration_iff s).2 hsMono)
      let g := (innerHomFunctor.{u}.map s.op).app Z
      have hTF : trivialFibrations SSet.{u} g :=
        ⟨ReedyModel.inner_precomp_fibration s Z hsCof hZ.1, hZ.2 i⟩
      have hRLP : SSet.modelCategoryQuillen.I.{u}.rlp g := by
        rw [← SSet.rlp_monomorphisms]
        change (cofibrations SSet.{u}).rlp g
        rw [cofibrations_rlp SSet.{u}]
        exact hTF
      exact (boundary_terminal_iff i n Z).2
        (hRLP _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n))
    intro A B f hf
    rcases hf with ⟨index⟩
    cases index with
    | inl horn =>
      simpa only [family] using hHorn _
        (MorphismProperty.ofHoms.mk (f := fun h : ReedyGeneratingFamilies.HornIndex =>
          (ReedyGeneratingFamilies.hornFamily.{u} h).hom) horn)
    | inr b =>
      rcases b with ⟨i, n⟩
      simpa only [family, boundaryFamily, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
        using hBound i n

end SimplicialSpace.LocalGenerators
