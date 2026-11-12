/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Walls.gc10ghostfourpoint
import Code.Walls.gc8Z0pos

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









theorem gc15_sd0 {W : Type*} [DecidableEq W] (O X Y g : W) :
    (∅ : Finset W) ∆ (∅ : Finset W) ∆ {O, X, Y, g} = {O, X, Y, g} := by simp


theorem gc15_sd1 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    (∅ : Finset W) ∆ {O, g} ∆ {X, Y} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


theorem gc15_sd2 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    (∅ : Finset W) ∆ {O, X} ∆ {Y, g} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


theorem gc15_sd3 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    (∅ : Finset W) ∆ {O, Y} ∆ {X, g} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all



theorem gc15_sd4 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    ({O, g} : Finset W) ∆ {X, g} ∆ {Y, g} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all










variable (S : SimpleGraph V) [DecidableRel S.Adj]





noncomputable def gc15_tpsum (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) : ℝ :=
  ∑ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
    (if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0)
      * (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0)
      * weight S β J (ofEdgeFun S (fun e => m e - K.1.1 e - K.1.2 e))




noncomputable def gc15_tFiber (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (m : ↥S.edgeFinset → ℕ) : ℝ :=
  if sources S (ofEdgeFun S m) = A ∆ B ∆ C then gc15_tpsum S β J m A B else 0






theorem gc15_inner_fiber_triple (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B C : Finset V) :
    (∑ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
        ((if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0) *
          (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0)) *
          (if sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C
            then weight S β J (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) else 0))
      = gc15_tFiber S β J A B C m := by
  unfold gc15_tFiber gc15_tpsum
  by_cases hm : sources S (ofEdgeFun S m) = A ∆ B ∆ C
  · rw [if_pos hm]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    by_cases hA : sources S (ofEdgeFun S K.1.1) = A
    · by_cases hB : sources S (ofEdgeFun S K.1.2) = B
      · simp only [if_pos hA, if_pos hB]
        have hcompl : sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C := by
          have hadd := sources_ofEdgeFun_add₃ S m K.1.1 K.1.2 K.2
          rw [hA, hB, hm] at hadd
          exact (symmDiff_right_injective (A ∆ B) hadd).symm
        rw [if_pos hcompl]
      · simp only [if_neg hB, mul_zero, zero_mul]
    · simp only [if_neg hA, zero_mul, zero_mul]
  · rw [if_neg hm]
    refine Finset.sum_eq_zero (fun K _ => ?_)
    by_cases hA : sources S (ofEdgeFun S K.1.1) = A
    · by_cases hB : sources S (ofEdgeFun S K.1.2) = B
      · simp only [if_pos hA, if_pos hB]
        by_cases hcompl : sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C
        · exact absurd (by rw [sources_ofEdgeFun_add₃ S m K.1.1 K.1.2 K.2, hA, hB, hcompl]) hm
        · rw [if_neg hcompl, mul_zero]
      · simp only [if_neg hB, mul_zero, zero_mul]
    · simp only [if_neg hA, zero_mul, zero_mul]




theorem gc15_summable_tFiber (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    Summable (gc15_tFiber S β J A B C) := by
  set f : (↥S.edgeFinset → ℕ) → ℝ :=
    fun p => if sources S (ofEdgeFun S p) = A then weight S β J (ofEdgeFun S p) else 0 with hf
  set g : (↥S.edgeFinset → ℕ) → ℝ :=
    fun p => if sources S (ofEdgeFun S p) = B then weight S β J (ofEdgeFun S p) else 0 with hg
  set k : (↥S.edgeFinset → ℕ) → ℝ :=
    fun p => if sources S (ofEdgeFun S p) = C then weight S β J (ofEdgeFun S p) else 0 with hk
  set F : (Σ m : (↥S.edgeFinset → ℕ),
      {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) → ℝ :=
    fun s => f s.2.1.1 * g s.2.1.2 * k (fun e => s.1 e - s.2.1.1 e - s.2.1.2 e) with hF
  have hgknorm : Summable
      (fun w : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) => ‖g w.1 * k w.2‖) := by
    apply ((summable_norm_currentSum_summand S β J B).mul_of_nonneg
      (summable_norm_currentSum_summand S β J C)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro w; rw [norm_mul]
  have hABC := summable_mul_of_summable_norm (summable_norm_currentSum_summand S β J A) hgknorm
  have htriple : Summable
      (fun z : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2) := by
    have heq : (fun z : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2) = (fun z => f z.1 * (g z.2.1 * k z.2.2)) := by
      funext z; rw [mul_assoc]
    rw [heq]; exact hABC
  have hcomp : ∀ z : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ),
      f z.1 * g z.2.1 * k z.2.2 = F (tripleEquivSigma z) := by
    rintro ⟨p, q, r⟩
    simp only [hF, tripleEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => p e + q e + r e - p e - q e) = r := by ext e; omega
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (tripleEquivSigma (E := ↥S.edgeFinset)).summable_iff]
    exact htriple.congr (fun z => hcomp z)
  have hmarg : Summable (fun m : ↥S.edgeFinset → ℕ => ∑' K, F ⟨m, K⟩) := hsumF.sigma
  refine hmarg.congr (fun m => ?_)
  rw [tsum_fintype, ← gc15_inner_fiber_triple S β J m A B C]








theorem gc15_sourceTripleSum_eq_tFiber (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    sourceTripleSum S β J A B C = ∑' m, gc15_tFiber S β J A B C m := by
  rw [sourceTripleSum_eq_superposition]
  exact tsum_congr (fun m => gc15_inner_fiber_triple S β J m A B C)









noncomputable def gc15_Z0 (β h : ℝ) : ℝ :=
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅


theorem gc15_Z0_pos (β h : ℝ) : 0 < gc15_Z0 G β h := gc8_Z0_pos_ghost G β h










theorem gc15_u3_ghost_expectationJ (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y
      = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o} : Finset V).map someEmb))
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (({x, y} : Finset V).map someEmb)
        - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, x} : Finset V).map someEmb)
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))
        - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, y} : Finset V).map someEmb)
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
        + 2 * (expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({o} : Finset V).map someEmb))
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
  unfold eg_ursell3
  rw [← gc10_moment_oxyg G β h o x y hox hoy hxy,
      ← gc10_moment_ghostSingle G β h o, ← gc10_moment_pair G β h x y hxy,
      ← gc10_moment_pair G β h o x hox, ← gc10_moment_ghostSingle G β h y,
      ← gc10_moment_pair G β h o y hoy, ← gc10_moment_ghostSingle G β h x]
  ring











theorem gc15_u3_currentSum_poly (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = (gc15_Z0 G β h) ^ 2 * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o} : Finset V).map someEmb))
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (({x, y} : Finset V).map someEmb)
        - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, x} : Finset V).map someEmb)
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))
        - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, y} : Finset V).map someEmb)
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
        + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({o} : Finset V).map someEmb))
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
  rw [gc15_u3_ghost_expectationJ G β h o x y hox hoy hxy,
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o} : Finset V).map someEmb)),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({y} : Finset V).map someEmb)),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({x} : Finset V).map someEmb))]
  unfold gc15_Z0
  ring








theorem gc15_gsingle (a : V) :
    insert (none : Option V) (({a} : Finset V).map someEmb)
      = ({some a, none} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_singleton, someEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro (rfl | ⟨b, rfl, rfl⟩) <;> tauto
  · rintro (rfl | rfl) <;> tauto


theorem gc15_gpair (a b : V) :
    (({a, b} : Finset V).map someEmb) = ({some a, some b} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_map, Finset.mem_insert, Finset.mem_singleton, someEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hc, rfl⟩; rcases hc with rfl | rfl <;> tauto
  · rintro (rfl | rfl) <;> [exact ⟨a, by tauto, rfl⟩; exact ⟨b, by tauto, rfl⟩]


theorem gc15_gquad (o x y : V) :
    insert (none : Option V) (({o, x, y} : Finset V).map someEmb)
      = ({some o, some x, some y, none} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_singleton, someEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro (rfl | ⟨b, hb, rfl⟩) <;> [tauto; (rcases hb with rfl | rfl | rfl <;> tauto)]
  · rintro (rfl | rfl | rfl | rfl) <;>
      first | (left; rfl) | (right; exact ⟨_, by tauto, rfl⟩)


theorem gc15_marks_distinct {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V))
      ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V)) :=
  ⟨by simp [hox], by simp [hoy], by simp, by simp [hxy], by simp, by simp⟩



















noncomputable def gc15_threeGap (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : ℝ :=
  gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ∅
      ({some o, some x, some y, none} : Finset (Option V)) m
    - gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ {some o, none} {some x, some y} m
    - gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ {some o, some x} {some y, none} m
    - gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ {some o, some y} {some x, none} m
    + 2 * gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1))
        {some o, none} {some x, none} {some y, none} m













theorem gc15_u3_eq_tsum_threeGap (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = ∑' m, gc15_threeGap G β h o x y m := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  
  rw [gc15_u3_currentSum_poly G β h o x y hox hoy hxy]
  rw [gc15_gquad o x y, gc15_gsingle o, gc15_gpair x y, gc15_gpair o x, gc15_gsingle y,
      gc15_gpair o y, gc15_gsingle x]
  
  
  
  have m0 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ ∅
    ({some o, some x, some y, none} : Finset (Option V))
  have m1 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ {some o, none} {some x, some y}
  have m2 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ {some o, some x} {some y, none}
  have m3 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ {some o, some y} {some x, none}
  have m4 := sourceTripleSum_eq_mul (withGhost G) β J' {some o, none} {some x, none} {some y, none}
  have hZ0 : gc15_Z0 G β h = currentSum (withGhost G) β J' ∅ := by rw [hJ', gc15_Z0]
  
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ ∅
        ({some o, some x, some y, none} : Finset (Option V))] at m0
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y}] at m1
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none}] at m2
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none}] at m3
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none}] at m4
  
  rw [hZ0, pow_two]
  
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' ∅ *
        currentSum (withGhost G) β J' {some o, some x, some y, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ ∅
          ({some o, some x, some y, none} : Finset (Option V)) m from m0.symm]
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' {some o, none}
        * currentSum (withGhost G) β J' {some x, some y}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y} m from m1.symm]
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' {some o, some x}
        * currentSum (withGhost G) β J' {some y, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none} m from m2.symm]
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' {some o, some y}
        * currentSum (withGhost G) β J' {some x, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none} m from m3.symm]
  rw [show currentSum (withGhost G) β J' {some o, none} * currentSum (withGhost G) β J' {some x, none}
        * currentSum (withGhost G) β J' {some y, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none} m
      from m4.symm]
  
  have s0 := gc15_summable_tFiber (withGhost G) β J' ∅ ∅
    ({some o, some x, some y, none} : Finset (Option V))
  have s1 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y}
  have s2 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none}
  have s3 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none}
  have s4 := gc15_summable_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none}
  rw [← Summable.tsum_sub s0 s1, ← Summable.tsum_sub (s0.sub s1) s2,
      ← Summable.tsum_sub ((s0.sub s1).sub s2) s3,
      ← tsum_mul_left,
      ← Summable.tsum_add (((s0.sub s1).sub s2).sub s3) (s4.mul_left 2)]
  refine tsum_congr (fun m => ?_)
  simp only [gc15_threeGap, hJ']





















def gc15_PerConfigUrsellSign (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m ≤ 0










theorem gc15_ursell_nonpos_of_perConfig (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc15_PerConfigUrsellSign G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hsum_nonpos : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
    rw [gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]
    
    have hsummable : Summable (gc15_threeGap G β h o x y) := by
      set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ))
      have s0 := gc15_summable_tFiber (withGhost G) β J' ∅ ∅
        ({some o, some x, some y, none} : Finset (Option V))
      have s1 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y}
      have s2 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none}
      have s3 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none}
      have s4 := gc15_summable_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none}
      exact (((s0.sub s1).sub s2).sub s3).add (s4.mul_left 2)
    exact tsum_nonpos (fun m => hsign m)
  nlinarith [pow_pos hZ 3, hsum_nonpos]












theorem gc15_ghs_of_perConfig (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox
    
    exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy
      
      rw [ghc_ursell_swap]
      exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · 
      exact gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy (hsign x y hox hoy hxy)













theorem gc15_aizenman_barsky_of_perConfig (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc15_ghs_of_perConfig G β h hβ hh o hsign) hfactor













theorem gc15_distinct_ursell_nonpos (β h : ℝ) (o : V)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y)
    {x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy (hsign x y hox hoy hxy)














theorem gc15_threeGap_vanish (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        ≠ ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m = 0 := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  unfold gc15_threeGap gc15_tFiber
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  rw [if_neg hm, if_neg hm, if_neg hm, if_neg hm, if_neg hm]
  ring

end StatMech.Walls
