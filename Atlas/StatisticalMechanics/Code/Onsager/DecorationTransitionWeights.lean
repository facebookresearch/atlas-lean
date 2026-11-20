/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationCoefficientAssembly











namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


def ons_decChainEdge {L : ℕ}
    (site : ZMod L × ZMod L) (i : Fin 3) : Sym2 (ons_Dart L) :=
  s((site, ⟨i.val, by omega⟩), (site, ⟨i.val + 1, by omega⟩))



def ons_decChainPathIndices (a b : Fin 4) : Finset (Fin 3) :=
  Finset.univ.filter fun i ↦ (i.val < a.val) ≠ (i.val < b.val)

def ons_decChainPathEdges {L : ℕ}
    (site : ZMod L × ZMod L) (a b : Fin 4) :
    Finset (Sym2 (ons_Dart L)) :=
  (ons_decChainPathIndices a b).image (ons_decChainEdge site)



def ons_decTransitionWeight
    (L : ℕ) (decWeight : Sym2 (ons_Dart L) → ℂ)
    (d₂ d₁ : ons_Dart L) : ℂ :=
  decWeight s(d₁, ons_dartRev L d₁) *
    ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
      decWeight (ons_decChainEdge d₂.1 i)



noncomputable def ons_KWmatDecorationWeightedPhase
    (L : ℕ) (decWeight : Sym2 (ons_Dart L) → ℂ)
    (omega u v : ℂ) : Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d₂ d₁ ↦
    if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
      ons_dirPhase u v d₁.2 *
        (ons_decTransitionWeight L decWeight d₂ d₁ *
          ons_turnW omega d₁.2 d₂.2)
    else 0

noncomputable def ons_decSpecializedWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ons_Dart L)) : ℂ := by
  classical
  exact if ons_decIsExternal edge then
      weight (ons_decEdgeProjection edge)
    else 1

noncomputable def ons_decInterpolatedWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ) (t : ℂ)
    (edge : Sym2 (ons_Dart L)) : ℂ := by
  classical
  exact if ons_decIsExternal edge then
      weight (ons_decEdgeProjection edge)
    else t

@[simp] theorem ons_decInterpolatedWeight_one
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ) :
    ons_decInterpolatedWeight weight 1 = ons_decSpecializedWeight weight := by
  funext edge
  classical
  simp only [ons_decInterpolatedWeight, ons_decSpecializedWeight]

@[simp] theorem ons_decSpecializedWeight_external
    (L : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (d : ons_Dart L) :
    ons_decSpecializedWeight weight s(d, ons_dartRev L d) =
      weight (ons_portEdge L d) := by
  classical
  unfold ons_decSpecializedWeight
  rw [if_pos ⟨d, rfl⟩, ons_decEdgeProjection_external]

@[simp] theorem ons_decInterpolatedWeight_external
    (L : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (t : ℂ) (d : ons_Dart L) :
    ons_decInterpolatedWeight weight t s(d, ons_dartRev L d) =
      weight (ons_portEdge L d) := by
  classical
  unfold ons_decInterpolatedWeight
  rw [if_pos ⟨d, rfl⟩, ons_decEdgeProjection_external]

theorem ons_decChainEdge_mem_decGraph
    (L : ℕ) [Fact (2 < L)]
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decChainEdge site i ∈ (ons_decGraph L).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  change s((site, ⟨i.val, by omega⟩),
      (site, ⟨i.val + 1, by omega⟩)) ∈ (ons_decGraph L).edgeSet
  rw [SimpleGraph.mem_edgeSet]
  change ons_decAdj L
    (site, ⟨i.val, by omega⟩) (site, ⟨i.val + 1, by omega⟩)
  exact Or.inr ⟨rfl, Or.inl rfl⟩

theorem ons_decChainEdge_not_external
    (L : ℕ) [Fact (2 < L)]
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ¬ ons_decIsExternal (ons_decChainEdge site i) := by
  intro hext
  rcases hext with ⟨d, hd⟩
  have hloop : ons_portEdge L d = s(site, site) := by
    calc
      ons_portEdge L d =
          ons_decEdgeProjection s(d, ons_dartRev L d) :=
        (ons_decEdgeProjection_external L d).symm
      _ = ons_decEdgeProjection (ons_decChainEdge site i) :=
        congrArg ons_decEdgeProjection hd.symm
      _ = s(site, site) := by
        rfl
  have hedge : s(site, site) ∈ (onsTorusGraph L).edgeFinset := by
    rw [← hloop]
    exact ons_portEdge_mem_edgeFinset L d
  simpa using hedge

@[simp] theorem ons_decSpecializedWeight_chainEdge
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decSpecializedWeight weight (ons_decChainEdge site i) = 1 := by
  simp [ons_decSpecializedWeight,
    ons_decChainEdge_not_external L site i]

@[simp] theorem ons_decInterpolatedWeight_chainEdge
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (t : ℂ)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decInterpolatedWeight weight t (ons_decChainEdge site i) = t := by
  simp [ons_decInterpolatedWeight,
    ons_decChainEdge_not_external L site i]

theorem norm_ons_decInterpolatedWeight_le_one
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (q : ℝ) (hq1 : q ≤ 1) (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (t : ℂ) (ht : ‖t‖ ≤ 1) (edge : Sym2 (ons_Dart L)) :
    ‖ons_decInterpolatedWeight weight t edge‖ ≤ 1 := by
  classical
  unfold ons_decInterpolatedWeight
  split
  · exact (hweight _).trans hq1
  · exact ht

theorem ons_decTransitionWeight_specialized
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (d₂ d₁ : ons_Dart L) :
    ons_decTransitionWeight L (ons_decSpecializedWeight weight) d₂ d₁ =
      weight (ons_portEdge L d₁) := by
  unfold ons_decTransitionWeight
  rw [ons_decSpecializedWeight_external]
  simp

theorem ons_KWmatDecorationWeightedPhase_specialized
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v : ℂ) :
    ons_KWmatDecorationWeightedPhase L
        (ons_decSpecializedWeight weight) omega u v =
      ons_KWmatWeightedPhase L weight omega u v := by
  ext d₂ d₁
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · simp [ons_KWmatDecorationWeightedPhase,
      ons_KWmatWeightedPhase, ons_KWmatWeighted, hstep,
      ons_decTransitionWeight_specialized]
  · simp [ons_KWmatDecorationWeightedPhase,
      ons_KWmatWeightedPhase, ons_KWmatWeighted, hstep]

theorem norm_ons_decTransitionWeight_le
    (L : ℕ) (decWeight : Sym2 (ons_Dart L) → ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (d₂ d₁ : ons_Dart L) :
    ‖ons_decTransitionWeight L decWeight d₂ d₁‖ ≤ q := by
  unfold ons_decTransitionWeight
  rw [norm_mul]
  have hprod :
      ‖∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
        decWeight (ons_decChainEdge d₂.1 i)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro i hi
      positivity
    · intro i hi
      exact hall _
  calc
    ‖decWeight s(d₁, ons_dartRev L d₁)‖ *
        ‖∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
          decWeight (ons_decChainEdge d₂.1 i)‖ ≤
        q * 1 := mul_le_mul (hext d₁) hprod (norm_nonneg _) hq
    _ = q := mul_one q

theorem norm_ons_KWmatDecorationWeightedPhase_entry_le
    (L : ℕ) (decWeight : Sym2 (ons_Dart L) → ℂ)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (d₂ d₁ : ons_Dart L) :
    ‖ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q := by
  unfold ons_KWmatDecorationWeightedPhase
  split
  · rw [norm_mul, norm_mul]
    have hphase :
        ‖ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d₁.2‖ = 1 := by
      generalize hdir : d₁.2 = direction
      fin_cases direction <;> simp [ons_dirPhase, norm_ons_spinPhase]
    rw [hphase, one_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (norm_ons_turnW_turnRoot_le_one d₁.2 d₂.2)).trans
        (norm_ons_decTransitionWeight_le L decWeight q hq hall hext d₂ d₁)
  · simpa using hq

theorem ons_KWmatDecorationWeightedPhase_detWalkRoot_sq
    (L : ℕ) [NeZero L]
    (decWeight : Sym2 (ons_Dart L) → ℂ) (a b : Fin 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
    (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
    (hsmall : q <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) ^ 2 =
      (1 - ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  let M := ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  have hentry : ∀ d₂ d₁, ‖M d₂ d₁‖ ≤ q :=
    norm_ons_KWmatDecorationWeightedPhase_entry_le
      L decWeight a b q hq hall hext
  have hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1 :=
    ons_card_mul_lt_one_of_Sherman_small q hsmall
  exact ons_detWalkRoot_sq M
    (ons_spectral_lt_one_of_entry M q hq hentry hcard)


noncomputable def ons_decoratedFullWeightedSpinSum
    (L : ℕ) [Fact (2 < L)]
    (decWeight : Sym2 (ons_Dart L) → ℂ) (a b : Fin 2) : ℂ :=
  ∑ D : ons_DecoratedEvenSubgraph L,
    (ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ) *
      ∏ edge ∈ D.1, decWeight edge

theorem ons_decoratedFullWeight_specialized
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (D : ons_DecoratedEvenSubgraph L) :
    (∏ edge ∈ D.1, ons_decSpecializedWeight weight edge) =
      ∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge := by
  classical
  rw [← ons_decoratedExternalEdges_image L D]
  rw [Finset.prod_image]
  · rw [← Finset.prod_filter_mul_prod_filter_not
      (s := D.1) (p := ons_decIsExternal)]
    simp only [ons_decoratedExternalEdges]
    have hnonext :
        (∏ edge ∈ D.1.filter (fun edge ↦ ¬ ons_decIsExternal edge),
          ons_decSpecializedWeight weight edge) = 1 := by
      apply Finset.prod_eq_one
      intro edge hedge
      have hnot := (Finset.mem_filter.mp hedge).2
      simp [ons_decSpecializedWeight, hnot]
    rw [hnonext, mul_one]
    apply Finset.prod_congr rfl
    intro edge hedge
    have hext := (Finset.mem_filter.mp hedge).2
    simp [ons_decSpecializedWeight, hext]
  · intro edge hedge edge' hedge' hproj
    exact ons_decEdgeProjection_injective_of_external L
      (Finset.mem_filter.mp hedge).2
      (Finset.mem_filter.mp hedge').2 hproj

theorem ons_decoratedFullWeightedSpinSum_specialized
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ons_decoratedFullWeightedSpinSum L
        (ons_decSpecializedWeight weight) a b =
      ons_weightedSpinCharacterSum L weight a b := by
  rw [ons_weightedSpinCharacterSum_eq_decorated]
  unfold ons_decoratedFullWeightedSpinSum
    ons_decoratedWeightedSpinWeight
  apply Finset.sum_congr rfl
  intro D hD
  rw [ons_decoratedFullWeight_specialized]

end StatMech.Onsager
