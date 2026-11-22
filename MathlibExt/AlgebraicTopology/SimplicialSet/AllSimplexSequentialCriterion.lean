/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FixedSimplexTailWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpSimplexCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredColimitStageData
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Sharp maps between sequential colimits from finite-tail comparisons

Every standard-simplex operator is a weak equivalence. For a map of simplicial-set sequences with monic source transitions, sharp components, and weak incoming comparisons on every finite tail, the induced map between actual colimits satisfies all standard-simplex comparison conditions and is sharp.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen Simplicial

namespace SSet.RezkAllSimplexSequential
open SharpComparisonDraft RezkFixedSimplexTail

/-- Actual terminal comparison of every original simplex, derived from the
public realized product projection and the actual terminal-object Iso. -/
theorem simplex_terminal_weak (n : ℕ) : WeakEquivalence
    (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) := by
  let e : (Δ[n] : SSet.{u}) ⨯ (Δ[0] : SSet.{u}) ≅ (Δ[n] : SSet.{u}) :=
    { hom := prod.fst
      inv := prod.lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _)
      hom_inv_id := by
        apply prod.hom_ext
        · simp
        · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      inv_hom_id := by simp }
  let : IsIso e.inv := e.isIso_inv
  have hp : realizationWeakEquivalences
      (prod.snd : (Δ[n] : SSet.{u}) ⨯ (Δ[0] : SSet.{u}) ⟶ Δ[0]) :=
    stdSimplexProdSnd_mem_weakHomotopyEquivalences n (Δ[0] : SSet.{u})
  have hv := realizationWeakEquivalences.comp_mem e.inv _
    (realizationWeakEquivalences.of_isIso e.inv) hp
  have he : e.inv ≫ prod.snd = SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he] at hv
  exact (HomotopicalAlgebra.weakEquivalence_iff _).2 hv

/-- EVERY original simplex operator is weak; no degree bound or outcome input. -/
theorem simplex_operator_weak {m a : ℕ} (delta : ⦋m⦌ ⟶ ⦋a⦌) :
    WeakEquivalence (SSet.stdSimplex.map delta : (Δ[m] : SSet.{u}) ⟶ Δ[a]) := by
  let : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{u})) :=
    simplex_terminal_weak a
  have comp : WeakEquivalence
      (SSet.stdSimplex.map delta ≫ SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{u})) := by
    rw [SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.stdSimplex.map delta ≫ SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{u}))
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[m] : SSet.{u}))]
    exact simplex_terminal_weak m
  let := comp
  exact weakEquivalence_of_postcomp (SSet.stdSimplex.map delta)
    (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{u}))

/-- All original simplex tests follow from actual finite-stage lifts and
finite Sharp/HC. The final q is not assumed sharp at any basechange step. -/
theorem all_simplex_and_sharp_of_actual_finite_tail
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ n, cX.ι.app n ≫ q = p.app n ≫ cY.ι.app n)
    (hX : IsColimit cX) (hY : IsColimit cY)
    (hmX : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (X.map f))
    (hsharp : ∀ n, Sharp (p.app n))
    (hincoming : ∀ (n k : ℕ), WeakEquivalence
      (pullback.lift (X.map (homOfLE (Nat.le_add_right n k))) (p.app n)
        (p.naturality (homOfLE (Nat.le_add_right n k))) ≫
        comparison (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))))) :
    SharpSaturation.allSimplexComparisons q ∧ Sharp q := by
  have hall : SharpSaturation.allSimplexComparisons q := by
    intro a m b delta
    obtain ⟨n, b', hb, allOperatorsAtSameStage⟩ :=
      FilteredColimitStage.exists_simplex_stage_with_all_operators cY hY a b
    have hweak := total_operator_weak p n (SSet.stdSimplex.map delta) b'
      cX cY q hq hX hY hmX (fun k => hsharp (n + k)) (hincoming n)
      (simplex_operator_weak delta)
    have path : (SSet.stdSimplex.map delta ≫ b') ≫ cY.ι.app n =
        SSet.stdSimplex.map delta ≫ b := allOperatorsAtSameStage m delta
    let e := pullback.congrHom (f₁ := q) (f₂ := q) rfl path
    let target := pullback.congrHom (f₁ := q) (f₂ := q) rfl hb
    have fac : e.inv ≫
        pullback.map q ((SSet.stdSimplex.map delta ≫ b') ≫ cY.ι.app n) q (b' ≫ cY.ι.app n)
          (𝟙 _) (SSet.stdSimplex.map delta) (𝟙 _) (by simp) (by simp [Category.assoc]) ≫
              target.hom =
        pullback.map q (SSet.stdSimplex.map delta ≫ b) q b
          (𝟙 _) (SSet.stdSimplex.map delta) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [e, target, pullback.map, Category.assoc]
    have h : WeakEquivalence
        (pullback.map q (SSet.stdSimplex.map delta ≫ b) q b
          (𝟙 _) (SSet.stdSimplex.map delta) (𝟙 _) (by simp) (by simp)) := by
      rw [← fac]
      let := hweak
      infer_instance
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1 h
  exact ⟨hall, (SharpSaturation.sharp_iff_allSimplexComparisons q).2 hall⟩

end SSet.RezkAllSimplexSequential
