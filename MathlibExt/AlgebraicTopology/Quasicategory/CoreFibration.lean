/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLiftingTarget
public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHorn
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Strict equivalence lifting gives Kan fibrations on cores

The core map of an inner fibration with quasicategory target and strict
source equivalence lifting has right lifting against all positive-dimensional
Kan horns. Dimension one uses source and target strict lifting. Higher horns
use the inner fibration or the relative special outer-horn theorem, then the
existing unconditional horn-lifting property of the core inclusion.

This is the forward implication of Joyal Proposition 4.27
(*The Theory of Quasi-Categories and its Applications*, February 2008,
p. 268). The source quasicategory follows from innerness and the target.
It is the core fibration input of Joyal–Tierney Proposition 1.16 used in
the vertically Reedy fibrant part of Proposition 4.10.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

private lemma core_map_one_zero_lifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [HasStrictEquivalenceLifting p] :
    HasLiftingProperty Λ[1, (0 : Fin 2)].ι (core.map p) where
  sq_hasLift {a b} sq := by
    let α : (Λ[1, 0] : SSet.{u}) ⟶ X := a ≫ (core X).ι
    let β : (Δ[1] : SSet.{u}) ⟶ Y := b ≫ (core Y).ι
    have hsq : α ≫ p = Λ[1, 0].ι ≫ β := by
      dsimp only [α, β]
      rw [Category.assoc, ← core.map_ι, ← Category.assoc, sq.w, Category.assoc]
    let v : (Δ[0] : SSet.{u}) ⟶ X :=
      horn.ι (0 : Fin 2) (1 : Fin 2) (by decide) ≫ α
    let x₀ : X _⦋0⦌ := yonedaEquiv v
    let g₀ : Edge (Y.δ 1 (yonedaEquiv β)) (Y.δ 0 (yonedaEquiv β)) :=
      Edge.mk' (yonedaEquiv β)
    have hvbase : v ≫ p = stdSimplex.δ (1 : Fin 2) ≫ β := by
      dsimp only [v]
      rw [Category.assoc, hsq, ← Category.assoc, horn.ι_ι]
    have hx : p.app _ x₀ = Y.δ 1 (yonedaEquiv β) := by
      dsimp only [x₀]
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← yonedaEquiv_comp, hvbase]
    let g := g₀.ofEq hx.symm rfl
    have hg₀ : g₀.IsEquivalence := by
      dsimp only [g₀, β]
      rw [yonedaEquiv_comp]
      exact mem_core_obj_one_iff.mp (yonedaEquiv b).2
    have hg : g.IsEquivalence := hg₀.of_edge_eq rfl
    obtain ⟨x₁, hx₁, f, hf, hfmap⟩ :=
      HasStrictEquivalenceLifting.exists_lift g hg
    have hfcore : f.edge ∈ (core X).obj (op ⦋1⦌) :=
      mem_core_obj_one_iff.mpr (hf.of_edge_eq rfl)
    let σ : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm f.edge
    let σc : (Δ[1] : SSet.{u}) ⟶ (core X : SSet.{u}) :=
      yonedaEquiv.symm ⟨f.edge, hfcore⟩
    have hσc : σc ≫ (core X).ι = σ := by
      dsimp only [σc, σ]
      rw [yonedaEquiv_symm_comp]
      rfl
    have hσhorn : Λ[1, 0].ι ≫ σ = α := by
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · rw [← Category.assoc, horn.ι_ι]
        dsimp only [σ]
        simp only [Fin.isValue, Fin.reduceFinMk]
        rw [stdSimplex.δ_comp_yonedaEquiv_symm, f.src_eq]
        exact Equiv.symm_apply_apply yonedaEquiv v
    have hσbase : σ ≫ p = β := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      dsimp only [σ]
      rw [Equiv.apply_symm_apply, ← Edge.map_edge, hfmap]
      rfl
    refine CommSq.HasLift.mk' ⟨σc, ?_, ?_⟩
    · apply (cancel_mono (core X).ι).mp
      rw [Category.assoc, hσc]
      exact hσhorn
    · apply (cancel_mono (core Y).ι).mp
      rw [Category.assoc, core.map_ι, ← Category.assoc, hσc]
      exact hσbase

private lemma core_map_one_one_lifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] :
    HasLiftingProperty Λ[1, (1 : Fin 2)].ι (core.map p) where
  sq_hasLift {a b} sq := by
    let α : (Λ[1, 1] : SSet.{u}) ⟶ X := a ≫ (core X).ι
    let β : (Δ[1] : SSet.{u}) ⟶ Y := b ≫ (core Y).ι
    have hsq : α ≫ p = Λ[1, 1].ι ≫ β := by
      dsimp only [α, β]
      rw [Category.assoc, ← core.map_ι, ← Category.assoc, sq.w, Category.assoc]
    let v : (Δ[0] : SSet.{u}) ⟶ X :=
      horn.ι (1 : Fin 2) (0 : Fin 2) (by decide) ≫ α
    let x₁ : X _⦋0⦌ := yonedaEquiv v
    let g₀ : Edge (Y.δ 1 (yonedaEquiv β)) (Y.δ 0 (yonedaEquiv β)) :=
      Edge.mk' (yonedaEquiv β)
    have hvbase : v ≫ p = stdSimplex.δ (0 : Fin 2) ≫ β := by
      dsimp only [v]
      rw [Category.assoc, hsq, ← Category.assoc, horn.ι_ι]
    have hx : p.app _ x₁ = Y.δ 0 (yonedaEquiv β) := by
      dsimp only [x₁]
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← yonedaEquiv_comp, hvbase]
    let g := g₀.ofEq rfl hx.symm
    have hg₀ : g₀.IsEquivalence := by
      dsimp only [g₀, β]
      rw [yonedaEquiv_comp]
      exact mem_core_obj_one_iff.mp (yonedaEquiv b).2
    have hg : g.IsEquivalence := hg₀.of_edge_eq rfl
    obtain ⟨x₀, hx₀, f, hf, hfmap⟩ :=
      HasStrictEquivalenceLifting.exists_lift_target g hg
    have hfcore : f.edge ∈ (core X).obj (op ⦋1⦌) :=
      mem_core_obj_one_iff.mpr (hf.of_edge_eq rfl)
    let σ : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm f.edge
    let σc : (Δ[1] : SSet.{u}) ⟶ (core X : SSet.{u}) :=
      yonedaEquiv.symm ⟨f.edge, hfcore⟩
    have hσc : σc ≫ (core X).ι = σ := by
      dsimp only [σc, σ]
      rw [yonedaEquiv_symm_comp]
      rfl
    have hσhorn : Λ[1, 1].ι ≫ σ = α := by
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · rw [← Category.assoc, horn.ι_ι]
        dsimp only [σ]
        simp only [Fin.isValue, Fin.reduceFinMk]
        rw [stdSimplex.δ_comp_yonedaEquiv_symm, f.tgt_eq]
        exact Equiv.symm_apply_apply yonedaEquiv v
      · exact (hj rfl).elim
    have hσbase : σ ≫ p = β := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      dsimp only [σ]
      rw [Equiv.apply_symm_apply, ← Edge.map_edge, hfmap]
      rfl
    refine CommSq.HasLift.mk' ⟨σc, ?_, ?_⟩
    · apply (cancel_mono (core X).ι).mp
      rw [Category.assoc, hσc]
      exact hσhorn
    · apply (cancel_mono (core Y).ι).mp
      rw [Category.assoc, core.map_ι, ← Category.assoc, hσc]
      exact hσbase

private lemma core_map_higher_horn_lifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    {n : ℕ} (i : Fin (n + 3)) :
    HasLiftingProperty Λ[n + 2, i].ι (core.map p) where
  sq_hasLift {a b} sq := by
    let α : (Λ[n + 2, i] : SSet.{u}) ⟶ X := a ≫ (core X).ι
    let β : (Δ[n + 2] : SSet.{u}) ⟶ Y := b ≫ (core Y).ι
    have hsq : α ≫ p = Λ[n + 2, i].ι ≫ β := by
      dsimp only [α, β]
      rw [Category.assoc, ← core.map_ι, ← Category.assoc, sq.w, Category.assoc]
    obtain ⟨σ, hσhorn, hσbase⟩ : ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X,
        Λ[n + 2, i].ι ≫ σ = α ∧ σ ≫ p = β := by
      by_cases h0 : i = 0
      · subst i
        exact exists_fill_relativeSpecialOuterHorn_of_isEquivalence
          SpecialOuterHornEndpoint.zero α β hsq
          (leftHornEdge_isEquivalence_of_factor_core a)
      · by_cases hn : i = Fin.last (n + 2)
        · subst i
          exact exists_fill_relativeSpecialOuterHorn_of_isEquivalence
            SpecialOuterHornEndpoint.last α β hsq
            (rightHornEdge_isEquivalence_of_factor_core a)
        · have h0' : 0 < i := Fin.pos_iff_ne_zero.mpr h0
          have hn' : i < Fin.last (n + 2) := lt_of_le_of_ne (Fin.le_last i) hn
          obtain ⟨σ, hσhorn, hσbase⟩ :=
            (InnerFibration.mem _ (innerHornInclusions.intro i h0' hn')).sq_hasLift
              (CommSq.mk hsq)
          exact ⟨σ, hσhorn, hσbase⟩
    obtain ⟨σc, hσchorn, hσc⟩ :=
      (hasLiftingProperty_horn_core_ι i).sq_hasLift (CommSq.mk hσhorn.symm)
    refine CommSq.HasLift.mk' ⟨σc, hσchorn, ?_⟩
    apply (cancel_mono (core Y).ι).mp
    rw [Category.assoc, core.map_ι, ← Category.assoc, hσc]
    exact hσbase

/-- The literal core map of an inner fibration with quasicategory target
and strict source equivalence lifting has RLP against the Kan generating horns.
The source quasicategory is inferred from innerness and the target. -/
private lemma core_map_mem_rlp_kanHorns
    {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] : modelCategoryQuillen.J.rlp (core.map p) := by
  intro A B i hi
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨j⟩⟩ := hi
  cases n with
  | zero =>
    fin_cases j
    · exact core_map_one_zero_lifting p
    · exact core_map_one_one_lifting p
  | succ n => exact core_map_higher_horn_lifting p j

open modelCategoryQuillen in
/-- An inner fibration with quasicategory target and strict source equivalence
lifting induces a Kan fibration on the literal equivalence-edge cores. -/
theorem fibration_core_map_of_hasStrictEquivalenceLifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] : HomotopicalAlgebra.Fibration (core.map p) :=
  (modelCategoryQuillen.fibration_iff _).2 (core_map_mem_rlp_kanHorns p)

end SSet
