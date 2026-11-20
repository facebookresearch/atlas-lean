/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalSeries









namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decGraph_adj_of_portLineAdj
    (L : ℕ) (site : ZMod L × ZMod L) {a b : Fin 4}
    (h : ons_portLineAdj a b) :
    (ons_decGraph L).Adj (site, a) (site, b) :=
  Or.inr ⟨rfl, h⟩

theorem ons_decGraph_adj01 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 0) (site, 1) :=
  ons_decGraph_adj_of_portLineAdj L site (by left; norm_num)

theorem ons_decGraph_adj10 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 1) (site, 0) :=
  ons_decGraph_adj_of_portLineAdj L site (by right; norm_num)

theorem ons_decGraph_adj12 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 1) (site, 2) :=
  ons_decGraph_adj_of_portLineAdj L site (by left; norm_num)

theorem ons_decGraph_adj21 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 2) (site, 1) :=
  ons_decGraph_adj_of_portLineAdj L site (by right; norm_num)

theorem ons_decGraph_adj23 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 2) (site, 3) :=
  ons_decGraph_adj_of_portLineAdj L site (by left; norm_num)

theorem ons_decGraph_adj32 (L : ℕ) (site : ZMod L × ZMod L) :
    (ons_decGraph L).Adj (site, 3) (site, 2) :=
  ons_decGraph_adj_of_portLineAdj L site (by right; norm_num)

@[simp] theorem ons_decChainPathIndices_00 :
    ons_decChainPathIndices 0 0 = ∅ := by decide
@[simp] theorem ons_decChainPathIndices_01 :
    ons_decChainPathIndices 0 1 = {0} := by decide
@[simp] theorem ons_decChainPathIndices_02 :
    ons_decChainPathIndices 0 2 = {0, 1} := by decide
@[simp] theorem ons_decChainPathIndices_03 :
    ons_decChainPathIndices 0 3 = Finset.univ := by decide
@[simp] theorem ons_decChainPathIndices_10 :
    ons_decChainPathIndices 1 0 = {0} := by decide
@[simp] theorem ons_decChainPathIndices_11 :
    ons_decChainPathIndices 1 1 = ∅ := by decide
@[simp] theorem ons_decChainPathIndices_12 :
    ons_decChainPathIndices 1 2 = {1} := by decide
@[simp] theorem ons_decChainPathIndices_13 :
    ons_decChainPathIndices 1 3 = {1, 2} := by decide
@[simp] theorem ons_decChainPathIndices_20 :
    ons_decChainPathIndices 2 0 = {0, 1} := by decide
@[simp] theorem ons_decChainPathIndices_21 :
    ons_decChainPathIndices 2 1 = {1} := by decide
@[simp] theorem ons_decChainPathIndices_22 :
    ons_decChainPathIndices 2 2 = ∅ := by decide
@[simp] theorem ons_decChainPathIndices_23 :
    ons_decChainPathIndices 2 3 = {2} := by decide
@[simp] theorem ons_decChainPathIndices_30 :
    ons_decChainPathIndices 3 0 = Finset.univ := by decide
@[simp] theorem ons_decChainPathIndices_31 :
    ons_decChainPathIndices 3 1 = {1, 2} := by decide
@[simp] theorem ons_decChainPathIndices_32 :
    ons_decChainPathIndices 3 2 = {2} := by decide
@[simp] theorem ons_decChainPathIndices_33 :
    ons_decChainPathIndices 3 3 = ∅ := by decide


theorem ons_exists_decPortChainWalk
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    ∃ p : (ons_decGraph L).Walk (site, a) (site, b),
      p.edges.toFinset = ons_decChainPathEdges site a b := by
  fin_cases a <;> fin_cases b
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj01 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site)
        (.cons (ons_decGraph_adj23 L site) .nil)), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj10 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj12 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj12 L site)
      (.cons (ons_decGraph_adj23 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj21 L site)
      (.cons (ons_decGraph_adj10 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj21 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj23 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site)
        (.cons (ons_decGraph_adj10 L site) .nil)), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site) .nil), ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site) .nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]


noncomputable def ons_decPortChainWalk
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decGraph L).Walk (site, a) (site, b) :=
  Classical.choose (ons_exists_decPortChainWalk L site a b)

@[simp] theorem ons_decPortChainWalk_edges_toFinset
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decPortChainWalk L site a b).edges.toFinset =
      ons_decChainPathEdges site a b :=
  Classical.choose_spec (ons_exists_decPortChainWalk L site a b)


theorem ons_exists_decPortChainPath
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    ∃ p : (ons_decGraph L).Walk (site, a) (site, b),
      p.IsPath ∧ p.edges.toFinset = ons_decChainPathEdges site a b := by
  fin_cases a <;> fin_cases b
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj01 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj01 L site)
      (.cons (ons_decGraph_adj12 L site)
        (.cons (ons_decGraph_adj23 L site) .nil)), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj10 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj12 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj12 L site)
      (.cons (ons_decGraph_adj23 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj21 L site)
      (.cons (ons_decGraph_adj10 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj21 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]
  · refine ⟨.cons (ons_decGraph_adj23 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site)
        (.cons (ons_decGraph_adj10 L site) .nil)), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (1 : Fin 4)), (site, (0 : Fin 4))) =
      s((site, (0 : Fin 4)), (site, (1 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site)
      (.cons (ons_decGraph_adj21 L site) .nil), by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
    rw [show s((site, (3 : Fin 4)), (site, (2 : Fin 4))) =
      s((site, (2 : Fin 4)), (site, (3 : Fin 4))) from Sym2.eq_swap]
    rw [show s((site, (2 : Fin 4)), (site, (1 : Fin 4))) =
      s((site, (1 : Fin 4)), (site, (2 : Fin 4))) from Sym2.eq_swap]
    ext edge
    simp [ons_decChainEdge] <;> tauto
  · refine ⟨.cons (ons_decGraph_adj32 L site) .nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainEdge]
  · refine ⟨.nil, by simp, ?_⟩
    simp [ons_decChainPathEdges, ons_decChainPathIndices]

noncomputable def ons_decPortChainPath
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decGraph L).Walk (site, a) (site, b) :=
  Classical.choose (ons_exists_decPortChainPath L site a b)

theorem ons_decPortChainPath_isPath
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decPortChainPath L site a b).IsPath :=
  (Classical.choose_spec (ons_exists_decPortChainPath L site a b)).1

@[simp] theorem ons_decPortChainPath_edges_toFinset
    (L : ℕ) (site : ZMod L × ZMod L) (a b : Fin 4) :
    (ons_decPortChainPath L site a b).edges.toFinset =
      ons_decChainPathEdges site a b :=
  (Classical.choose_spec (ons_exists_decPortChainPath L site a b)).2

theorem ons_dartRev_fst_eq_step
    (L : ℕ) (d : ons_Dart L) :
    (ons_dartRev L d).1 = ons_dirStep L d.2 d.1 := by
  rfl


noncomputable def ons_decTransitionWalk
    (L : ℕ) (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decGraph L).Walk d₁ d₂ := by
  let ext : (ons_decGraph L).Walk d₁ (ons_dartRev L d₁) :=
    .cons (Or.inl rfl) .nil
  let chain₀ := ons_decPortChainPath L d₂.1 (d₁.2 + 2) d₂.2
  have hstart : (d₂.1, d₁.2 + 2) = ons_dartRev L d₁ := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L d₁).symm
    · simp [ons_dartRev]
  let chain : (ons_decGraph L).Walk (ons_dartRev L d₁) d₂ :=
    chain₀.copy hstart rfl
  exact ext.append chain

@[simp] theorem ons_decTransitionWalk_edges_toFinset
    (L : ℕ) (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decTransitionWalk L d₂ d₁ hstep).edges.toFinset =
      insert s(d₁, ons_dartRev L d₁)
        (ons_decChainPathEdges d₂.1 (d₁.2 + 2) d₂.2) := by
  have hstart : (d₂.1, d₁.2 + 2) = ons_dartRev L d₁ := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L d₁).symm
    · simp [ons_dartRev]
  simp [ons_decTransitionWalk]
  rw [hstart]

theorem ons_decChainEdge_injective
    {L : ℕ} (site : ZMod L × ZMod L) :
    Function.Injective (ons_decChainEdge site) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [ons_decChainEdge, Sym2.eq_iff, Fin.ext_iff] at hij ⊢

theorem ons_externalEdge_not_mem_chainPath
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (site : ZMod L × ZMod L) (a b : Fin 4) :
    s(d, ons_dartRev L d) ∉ ons_decChainPathEdges site a b := by
  intro hmem
  rw [ons_decChainPathEdges, Finset.mem_image] at hmem
  obtain ⟨i, hi, hedge⟩ := hmem
  apply ons_decChainEdge_not_external L site i
  exact ⟨d, hedge⟩

theorem ons_decTransitionWalk_isTrail
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decTransitionWalk L d₂ d₁ hstep).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  have hchain :=
    (ons_decPortChainPath_isPath L d₂.1 (d₁.2 + 2) d₂.2).isTrail
  rw [SimpleGraph.Walk.isTrail_def] at hchain
  simp [ons_decTransitionWalk, hchain]
  intro hedge
  apply ons_externalEdge_not_mem_chainPath
    L d₁ d₂.1 (d₁.2 + 2) d₂.2
  rw [← ons_decPortChainPath_edges_toFinset]
  apply List.mem_toFinset.mpr
  simpa [hstep, ons_dartRev] using hedge



theorem ons_decTransitionExponent_eq_walkEdges
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    ons_decTransitionExponent L d₂ d₁ =
      ons_finsetExponent
        (ons_decTransitionWalk L d₂ d₁ hstep).edges.toFinset := by
  rw [ons_decTransitionWalk_edges_toFinset]
  unfold ons_decTransitionExponent ons_decChainPathEdges
  rw [ons_finsetExponent_insert]
  · rw [ons_finsetExponent_image
      (ons_decChainPathIndices (d₁.2 + 2) d₂.2)
      (ons_decChainEdge d₂.1)
      (ons_decChainEdge_injective d₂.1).injOn]
  · exact ons_externalEdge_not_mem_chainPath L d₁ d₂.1
      (d₁.2 + 2) d₂.2

theorem ons_decTransitionExponent_prod
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decTransitionExponent L d₂ d₁).prod
        (fun edge n ↦ decWeight edge ^ n) =
      ons_decTransitionWeight L decWeight d₂ d₁ := by
  rw [ons_decTransitionExponent_eq_walkEdges L d₂ d₁ hstep,
    ons_finsetExponent_prod,
    ons_decTransitionWalk_edges_toFinset,
    Finset.prod_insert
      (ons_externalEdge_not_mem_chainPath L d₁ d₂.1
        (d₁.2 + 2) d₂.2)]
  unfold ons_decChainPathEdges ons_decTransitionWeight
  rw [Finset.prod_image (ons_decChainEdge_injective d₂.1).injOn]

theorem ons_KWmatDecorationWeightedPhase_entry_factor
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (omega u v : ℂ)
    (d₂ d₁ : ons_Dart L) :
    ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ d₁ =
      ons_decTransitionScalar L omega u v d₂ d₁ *
        (ons_decTransitionExponent L d₂ d₁).prod
          (fun edge n ↦ decWeight edge ^ n) := by
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [ons_decTransitionExponent_prod L decWeight d₂ d₁ hstep]
    simp [ons_KWmatDecorationWeightedPhase, ons_decTransitionScalar, hstep]
    ring
  · simp [ons_KWmatDecorationWeightedPhase,
      ons_decTransitionScalar, hstep]

theorem ons_finsuppProd_sum_pow
    {I E R : Type*} [Fintype I] [DecidableEq E] [CommMonoid R]
    (m : I → E →₀ ℕ) (weight : E → R) :
    (∑ i, m i).prod (fun edge n ↦ weight edge ^ n) =
      ∏ i, (m i).prod (fun edge n ↦ weight edge ^ n) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finsupp.prod_add_index]
      · rw [ih]
      · intro edge hedge
        simp
      · intro edge hedge n₁ n₂
        simp [pow_add]

theorem ons_loopWeight_KWmatDecorationWeightedPhase
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (decWeight : ons_DecEdge L → ℂ) (omega u v : ℂ)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d =
      ons_decLoopScalar L omega u v d *
        (ons_decLoopExponent L d).prod
          (fun edge k ↦ decWeight edge ^ k) := by
  unfold ons_loopWeight ons_decLoopScalar ons_decLoopExponent
  simp_rw [ons_KWmatDecorationWeightedPhase_entry_factor]
  rw [Finset.prod_mul_distrib, ons_finsuppProd_sum_pow]

end StatMech.Onsager
