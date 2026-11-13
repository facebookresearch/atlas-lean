/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































































import Mathlib
import Code.Walls.gc8core
import Code.Walls.gc9Znormaliserpos
import Code.Walls.gc9assembledDnonneg
import Code.Walls.gc9deltadef
import Code.Walls.gc9Jnonneg
import Code.Walls.gc9betaderivcov3
import Code.Walls.gc9switching
import Code.Walls.gc9eq15insertion
import Code.Walls.gc6_ghostgraph
import Code.Sharpness.GhostCurrentRep
import Code.Ising.CurrentWeight

open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FieldGhostDict
open StatMech.Sharpness.GhostCurrentRep
open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum sourcePairDisconnSum_eq_edgecopy)
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (G : SimpleGraph V) [DecidableRel G.Adj]















noncomputable def gc9_assembledD_pair (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g x y : V) : ℝ :=
  J s(x, y) * gc9_pivotalMass ends F o g x y






theorem gc9_assembledD_pair_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g x y : V) (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc9_assembledD_pair ends F J o g x y :=
  mul_nonneg (hJ _) (gc9_concrete_delta_nonneg ends F hF o g x y)













theorem gc9_eq20_symmDiff (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        ∆ ({some o, none} : Finset (Option V))
      = (({x, y} : Finset V).map someEmb) := by
  ext z
  cases z with
  | none => simp [Finset.mem_symmDiff, someEmb]
  | some a =>
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_map, someEmb,
      Function.Embedding.coeFn_mk, Finset.mem_singleton, Option.some.injEq, reduceCtorEq,
      false_or, or_false]
    constructor
    · rintro (⟨⟨b, hb, hba⟩, hne⟩ | ⟨hcon, hneg⟩)
      · subst hba; rcases hb with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact ⟨b, by simp, rfl⟩
        · exact ⟨b, by simp, rfl⟩
      · exact absurd ⟨a, Or.inl hcon, rfl⟩ hneg
    · rintro ⟨b, hb, hba⟩; subst hba; rcases hb with rfl | rfl
      · exact Or.inl ⟨⟨b, by simp, rfl⟩, fun h => hox h.symm⟩
      · exact Or.inl ⟨⟨b, by simp, rfl⟩, fun h => hoy h.symm⟩




theorem gc9_eq20_uv (o : V) :
    ({some o, none} : Finset (Option V))
      = insert (none : Option V) (({o} : Finset V).map someEmb) := by
  ext z; cases z with
  | none => simp [someEmb]
  | some a => simp [someEmb]



theorem gc9_eq20_card_oxy (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Odd (({o, x, y} : Finset V).card) := by
  rw [Finset.card_insert_of_notMem (by simp [hox, hoy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]; decide


theorem gc9_eq20_card_xy (x y : V) (hxy : x ≠ y) :
    Even (({x, y} : Finset V).card) := by
  rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]; decide



theorem gc9_cov3_spinProd_form (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    cov3sym G β h o s(x, y)
      = isingExpectation G β h (spinProd ({o, x, y} : Finset V))
        - isingExpectation G β h (spinProd ({x, y} : Finset V))
          * isingExpectation G β h (spinProd ({o} : Finset V)) := by
  rw [cov3sym_mk]
  have e3 : isingExpectation G β h (spinProd ({o, x, y} : Finset V))
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) := by
    congr 1; funext s; unfold spinProd
    rw [Finset.prod_insert (by simp [hox, hoy]), Finset.prod_insert (by simp [hxy]),
        Finset.prod_singleton]
  have e2 : isingExpectation G β h (spinProd ({x, y} : Finset V))
      = isingExpectation G β h (fun s => spin s x * spin s y) := by
    congr 1; funext s; unfold spinProd
    rw [Finset.prod_insert (by simp [hxy]), Finset.prod_singleton]
  have e1 : isingExpectation G β h (spinProd ({o} : Finset V))
      = isingExpectation G β h (fun s => spin s o) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  rw [e3, e2, e1]; ring






























theorem gc9_eq20_perBond_cov3 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * cov3sym G β h o s(x, y)
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := by
  set Jc := ghostCoupling h β (fun _ => 1 : Sym2 V → ℝ) with hJc
  set GG := withGhost G with hGG
  set Z := currentSum GG β Jc ∅ with hZdef
  have hZne : Z ≠ 0 := ne_of_gt (gc9_sourceless_pos GG β Jc)
  have huv : (some o : Option V) ≠ none := by simp
  
  have hrep3 : isingExpectation G β h (spinProd ({o, x, y} : Finset V))
      = currentSum GG β Jc (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) / Z :=
    gc6_ghostGraph_currentRatio_odd G β h ({o, x, y} : Finset V) (gc9_eq20_card_oxy o x y hox hoy hxy)
  
  have hrep1 : isingExpectation G β h (spinProd ({x, y} : Finset V))
      = currentSum GG β Jc ((insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
            ∆ ({some o, none} : Finset (Option V))) / Z := by
    rw [gc9_eq20_symmDiff o x y hox hoy hxy]
    exact fgd_isingExpectation_eq_currentSum_ratio G β h ({x, y} : Finset V)
      (gc9_eq20_card_xy x y hxy)
  
  have hrep2 : isingExpectation G β h (spinProd ({o} : Finset V))
      = currentSum GG β Jc ({some o, none} : Finset (Option V)) / Z := by
    rw [gc9_eq20_uv o]
    exact gc6_ghostGraph_currentRatio_odd G β h ({o} : Finset V) (by simp)
  
  have hghost := gcr_ghostCurrentRep GG β Jc
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) huv
      Z (isingExpectation G β h (spinProd ({o, x, y} : Finset V)))
      (isingExpectation G β h (spinProd ({x, y} : Finset V)))
      (isingExpectation G β h (spinProd ({o} : Finset V)))
      hZdef hZne hrep3 hrep1 hrep2
  rw [gc9_cov3_spinProd_form G β h o x y hox hoy hxy]
  rw [show gc9_Z_normaliser G β Jc = Z ^ 2 from rfl]
  exact hghost












theorem gc9_ghostCoupling_nonneg (h β : ℝ) (hh : 0 ≤ h) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) :
    ∀ e, 0 ≤ ghostCoupling h β J e := by
  intro e
  induction e with
  | h a b =>
    cases a with
    | none =>
      cases b with
      | none => simp [ghostCoupling]
      | some y => simpa [ghostCoupling] using hh
    | some x =>
      cases b with
      | none => simpa [ghostCoupling] using hh
      | some y => rw [ghostCoupling_some_some]; exact hJ _






theorem gc9_disconnPivotal_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (A B : Finset (Option V)) (u v : Option V) :
    0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J) A B u v := by
  rw [sourcePairDisconnSum_eq_edgecopy]
  refine tsum_nonneg (fun m => mul_nonneg (Finset.sum_nonneg (fun S _ => ?_)) ?_)
  · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> · split <;> norm_num
  · exact acw_weight_nonneg (withGhost G) β (ghostCoupling h β J) hβ
      (gc9_ghostCoupling_nonneg h β hh J hJ) _



theorem gc9_eq20_pivotalMass_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none :=
  gc9_disconnPivotal_nonneg G β h hβ hh (fun _ => 1) (fun _ => by norm_num) _ _ _ _














theorem gc9_cov3_nonneg_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    0 ≤ cov3sym G β h o s(x, y) := by
  have hid := gc9_eq20_perBond_cov3 G β h o x y hox hoy hxy
  have hZ : 0 < gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) :=
    gc9_Z_normaliser_pos G β (ghostCoupling h β (fun _ => 1))
  have hδ : 0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none :=
    gc9_eq20_pivotalMass_nonneg G β h hβ hh o x y
  
  nlinarith [hid, hZ, hδ]

















noncomputable def gc9_deltaEdge (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y =>
    sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none,
    by intro a b; simp only []; congr 3; rw [Finset.pair_comm a b]⟩ e

@[simp] theorem gc9_deltaEdge_mk (β h : ℝ) (o x y : V) :
    gc9_deltaEdge G β h o s(x, y)
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := rfl






theorem gc9_eq20_perEdge_cov3 (β h : ℝ) (o : V) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (hoe : o ∉ e) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * cov3sym G β h o e
      = gc9_deltaEdge G β h o e := by
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hxy : x ≠ y := G.ne_of_adj he
    have hox : o ≠ x := fun h => hoe (by rw [h]; exact Sym2.mem_mk_left x y)
    have hoy : o ≠ y := fun h => hoe (by rw [h]; exact Sym2.mem_mk_right x y)
    rw [gc9_deltaEdge_mk]
    exact gc9_eq20_perBond_cov3 G β h o x y hox hoy hxy











theorem gc9_eq20_pivotalMass_sum (β h : ℝ) (o : V) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
        * (∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), cov3sym G β h o e)
      = ∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter] at he
  exact gc9_eq20_perEdge_cov3 G β h o he.1 he.2




theorem gc9_eq20_pivotalMass_sum_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ ∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e := by
  refine Finset.sum_nonneg (fun e he => ?_)
  induction e with
  | h x y => rw [gc9_deltaEdge_mk]; exact gc9_eq20_pivotalMass_nonneg G β h hβ hh o x y












theorem gc9_eq20_derivative_identity (β h : ℝ) (o : V) :
    gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
        * deriv (fun β => isingExpectation G β h (fun s => spin s o)) β
      = gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
            * (∑ e ∈ G.edgeFinset.filter (fun e => o ∈ e), cov3sym G β h o e)
          + (∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e)
          + gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1))
              * (h * susceptibility G β h o) := by
  rw [gc9_beta_deriv_cov3 G β h o]
  unfold bondEnergySusceptibility
  
  rw [← Finset.sum_filter_add_sum_filter_not G.edgeFinset (fun e => o ∈ e) (cov3sym G β h o)]
  
  have hpiv := gc9_eq20_pivotalMass_sum G β h o
  
  rw [mul_add]
  linarith [hpiv]














theorem gc9_cov3_degenerate_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o y : V) (hoy : o ≠ y) :
    0 ≤ cov3sym G β h o s(o, y) := by
  rw [cov3sym_mk]
  have h1 : isingExpectation G β h (fun s => spin s o * (spin s o * spin s y))
      = isingExpectation G β h (fun s => spin s y) := by
    congr 1; funext s
    rw [show spin s o * (spin s o * spin s y) = (spin s o * spin s o) * spin s y from by ring,
        spin_sq, one_mul]
  rw [h1]
  have hg := gks_second G β h hβ hh ({o} : Finset V) ({o, y} : Finset V)
  have hAB : ({o} : Finset V) ∆ ({o, y} : Finset V) = {y} := by
    ext z; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro (⟨rfl, hn⟩ | ⟨hz, hn⟩)
      · exact absurd (Or.inl rfl) hn
      · rcases hz with rfl | rfl
        · exact absurd rfl hn
        · rfl
    · rintro rfl; exact Or.inr ⟨Or.inr rfl, fun hh => hoy hh.symm⟩
  rw [hAB] at hg
  have e1 : isingExpectation G β h (spinProd ({o} : Finset V))
      = isingExpectation G β h (fun s => spin s o) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  have e2 : isingExpectation G β h (spinProd ({o, y} : Finset V))
      = isingExpectation G β h (fun s => spin s o * spin s y) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_insert (by simp [hoy]), Finset.prod_singleton]
  have e3 : isingExpectation G β h (spinProd ({y} : Finset V))
      = isingExpectation G β h (fun s => spin s y) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  rw [e1, e2, e3] at hg
  linarith [hg]





theorem gc9_cov3_edge_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    0 ≤ cov3sym G β h o e := by
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hxy : x ≠ y := G.ne_of_adj he
    by_cases hox : o = x
    · subst hox; exact gc9_cov3_degenerate_nonneg G β h hβ hh o y hxy
    · by_cases hoy : o = y
      · subst hoy
        rw [Sym2.eq_swap]
        exact gc9_cov3_degenerate_nonneg G β h hβ hh o x hox
      · exact gc9_cov3_nonneg_of_eq20 G β h hβ hh o x y hox hoy hxy




theorem gc9_cov2_self_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ cov2 G β h o o := by
  unfold cov2
  have h1 : isingExpectation G β h (fun s => spin s o * spin s o) = 1 := by
    rw [show (fun s => spin s o * spin s o) = (fun _ : ConfigSpace V => (1 : ℝ)) from by
      funext s; exact spin_sq s o]
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have hg := gks_second G β h hβ hh ({o} : Finset V) ({o} : Finset V)
  rw [symmDiff_self] at hg
  have eo : isingExpectation G β h (spinProd ({o} : Finset V))
      = isingExpectation G β h (fun s => spin s o) := by
    congr 1; funext s; unfold spinProd; rw [Finset.prod_singleton]
  have eb : isingExpectation G β h (spinProd (⊥ : Finset V)) = 1 := by
    rw [show (⊥ : Finset V) = (∅ : Finset V) from rfl,
        show spinProd (∅ : Finset V) = (fun _ : ConfigSpace V => (1 : ℝ)) from by
          funext s; exact spinProd_empty s]
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  rw [eo, eb] at hg
  rw [h1]
  linarith [hg]





theorem gc9_susceptibility_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ susceptibility G β h o := by
  unfold susceptibility
  refine Finset.sum_nonneg (fun x _ => ?_)
  by_cases hox : o = x
  · subst hox; exact gc9_cov2_self_nonneg G β h hβ hh o
  · exact StatMech.Ising.cov2_nonneg G β h hβ hh o x hox













theorem gc9_beta_deriv_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ deriv (fun β => isingExpectation G β h (fun s => spin s o)) β := by
  rw [gc9_beta_deriv_cov3 G β h o]
  refine add_nonneg ?_ (mul_nonneg hh (gc9_susceptibility_nonneg G β h hβ hh o))
  exact Finset.sum_nonneg (fun e he => gc9_cov3_edge_nonneg G β h hβ hh o he)



























def gc9_Eq20DerivativeIdentity (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    eg_ursell3 G β h o x y * gc9_Z_normaliser G β J'
      = - gc9_assembledD_pair ends F J o g x y






theorem gc9_core_ursell_nonpos_of_eq20 (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J)
    (x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hidxy := hid x y hox hoy hxy
  have hZ : 0 < gc9_Z_normaliser G β J' := gc9_Z_normaliser_pos G β J'
  have hD : 0 ≤ gc9_assembledD_pair ends F J o g x y :=
    gc9_assembledD_pair_nonneg ends F J o g x y hJ hF
  have hu : eg_ursell3 G β h o x y
      = - gc9_assembledD_pair ends F J o g x y / gc9_Z_normaliser G β J' := by
    rw [eq_div_iff (ne_of_gt hZ)]; linarith [hidxy]
  rw [hu]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le


theorem gc9_core_signDominance_of_eq20 (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
    GHSSignDominance G β h o :=
  fun x y hox hoy hxy =>
    gc9_core_ursell_nonpos_of_eq20 G β h o g J' ends F J hJ hF hid x y hox hoy hxy


theorem gc9_core_ursell_nonpos_all_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o g : V)
    (J' : Sym2 (Option V) → ℝ) (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc5_core_ursell_nonpos_of_signDominance G β h hβ hh o
    (gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid) x y


theorem gc9_core_ghs_concavity_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o g : V)
    (J' : Sym2 (Option V) → ℝ) (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
    GHSThreePointSym G β h o :=
  gc5_core_ghs_concavity_of_signDominance G β h hβ hh o
    (gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid)


theorem gc9_core_sharpness_of_eq20 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o g : V) (Jc : ℝ)
    (J' : Sym2 (Option V) → ℝ) (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc5_core_aizenman_barsky_of_signDominance G β h hβ hh o Jc
    (gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid) hfactor


theorem gc9_eq20_specific_pins_bridge (β h : ℝ) (o g : V) (J' : Sym2 (Option V) → ℝ)
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
    gc8_PivotalSignBridge G β h o := by
  intro x y hox hoy hxy
  exact ⟨gc9_assembledD_pair ends F J o g x y, gc9_Z_normaliser G β J',
    gc9_assembledD_pair_nonneg ends F J o g x y hJ hF,
    gc9_Z_normaliser_pos G β J',
    hid x y hox hoy hxy⟩



theorem gc9_eq20_not_circular {u3 Z' D : ℝ} (hZ : 0 < Z') (hD : 0 ≤ D) (hid : u3 * Z' = -D) :
    u3 ≤ 0 := by
  have hu : u3 = - D / Z' := by rw [eq_div_iff (ne_of_gt hZ)]; linarith [hid]
  rw [hu]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hZ.le




theorem gc9_core_normaliser_nonvacuous :
    0 < gc9_Z_normaliser (⊤ : SimpleGraph (Fin 3)) 1 (ghostCoupling 1 1 (fun _ => 1)) :=
  gc9_Z_normaliser_pos_nonvacuous



theorem gc9_core_pivotalMass_nonvacuous :
    0 ≤ gc9_assembledD_pair (witEnds : Fin 2 → Sym2 (Fin 4)) (fun _ => 1) (fun _ => 1)
          (0 : Fin 4) 3 1 2 :=
  gc9_assembledD_pair_nonneg witEnds (fun _ => 1) (fun _ => 1) 0 3 1 2
    (fun _ => by norm_num) (fun _ => by norm_num)

end StatMech.Walls
