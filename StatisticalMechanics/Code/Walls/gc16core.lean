/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Walls.gc15core
import Code.Ising.AizenmanSignDominance

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (S : SimpleGraph V) [DecidableRel S.Adj]










def gc16_swapSplit (m : ↥S.edgeFinset → ℕ) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} ≃
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} where
  toFun K := ⟨(K.1.2, K.1.1), fun e => by simp only; have := K.2 e; omega⟩
  invFun K := ⟨(K.1.2, K.1.1), fun e => by simp only; have := K.2 e; omega⟩
  left_inv K := by ext <;> simp
  right_inv K := by ext <;> simp









theorem gc16_tpsum_symm (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum S β J m A B = gc15_tpsum S β J m B A := by
  unfold gc15_tpsum
  rw [← Equiv.sum_comp (gc16_swapSplit S m)]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  simp only [gc16_swapSplit, Equiv.coe_fn_mk]
  have hsub : (fun e => m e - K.1.2 e - K.1.1 e) = (fun e => m e - K.1.1 e - K.1.2 e) := by
    ext e; omega
  rw [hsub]; ring









theorem gc16_tpsum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    0 ≤ gc15_tpsum S β J m A B := by
  unfold gc15_tpsum
  refine Finset.sum_nonneg (fun K _ => ?_)
  have hw : ∀ (n : ↥S.edgeFinset → ℕ), (0:ℝ) ≤ weight S β J (ofEdgeFun S n) :=
    fun n => asd_weight_nonneg S β J hβ hJ _
  have h1 : (0:ℝ) ≤ (if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0) := by
    split <;> [exact hw _; rfl]
  have h2 : (0:ℝ) ≤ (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0) := by
    split <;> [exact hw _; rfl]
  exact mul_nonneg (mul_nonneg h1 h2) (hw _)



theorem gc16_tFiber_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B C : Finset V) (m : ↥S.edgeFinset → ℕ) :
    0 ≤ gc15_tFiber S β J A B C m := by
  unfold gc15_tFiber
  split
  · exact gc16_tpsum_nonneg S β J hβ hJ m A B
  · rfl



















noncomputable def gc16_edgeNativeEquiv (p : ↥S.edgeFinset → ℕ) :
    {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ p e} ≃
      {K : Sharpness.Current V // ∀ e, K e ≤ ofEdgeFun S p e} where
  toFun K := ⟨ofEdgeFun S K.1, fun e => by
    simp only [ofEdgeFun]; by_cases he : e ∈ S.edgeFinset <;> simp [he, K.2]⟩
  invFun K := ⟨fun e => K.1 e.1, fun e => by
    have hk := K.2 e.1; simp only [ofEdgeFun, e.2, dif_pos] at hk; exact hk⟩
  left_inv K := by
    apply Subtype.ext; funext e
    simp only [ofEdgeFun, e.2, dif_pos]
  right_inv K := by
    apply Subtype.ext; funext e
    by_cases he : e ∈ S.edgeFinset
    · simp only [ofEdgeFun, he, dif_pos]
    · have hk := K.2 e; simp only [ofEdgeFun, he, dif_neg, not_false_iff] at hk ⊢
      omega










theorem gc16_inner_eq_splitWeightedSum (β : ℝ) (J : Sym2 V → ℝ)
    (p : ↥S.edgeFinset → ℕ) (A : Finset V) :
    (∑ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ p e},
        (if sources S (ofEdgeFun S K₁.1) = A then weight S β J (ofEdgeFun S K₁.1) else 0)
          * weight S β J (ofEdgeFun S (fun e => p e - K₁.1 e)))
      = splitWeightedSum S β J (ofEdgeFun S p) 1 A := by
  unfold splitWeightedSum
  rw [← Equiv.sum_comp (gc16_edgeNativeEquiv S p)]
  refine Finset.sum_congr rfl (fun K₁ _ => ?_)
  simp only [gc16_edgeNativeEquiv, Equiv.coe_fn_mk]
  
  have hsub : (ofEdgeFun S (fun e => p e - K₁.1 e))
      = (fun e => ofEdgeFun S p e - (ofEdgeFun S K₁.1) e) := by
    funext e
    simp only [ofEdgeFun]
    by_cases he : e ∈ S.edgeFinset <;> simp [he]
  rw [hsub]
  by_cases hA : sources S (ofEdgeFun S K₁.1) = A
  · rw [if_pos hA, if_pos hA, one_mul]
  · rw [if_neg hA, if_neg hA, zero_mul]





noncomputable def gc16_splitSigmaEquiv (m : ↥S.edgeFinset → ℕ) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} ≃
      Σ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e} where
  toFun K := ⟨⟨K.1.2, fun e => by have := K.2 e; omega⟩,
    ⟨K.1.1, fun e => by show K.1.1 e ≤ m e - K.1.2 e; have := K.2 e; omega⟩⟩
  invFun s := ⟨(s.2.1, s.1.1), fun e => by
    show s.2.1 e + s.1.1 e ≤ m e
    have h2 : s.2.1 e ≤ m e - s.1.1 e := s.2.2 e
    have h1 := s.1.2 e; omega⟩
  left_inv K := by ext <;> simp
  right_inv s := by rcases s with ⟨⟨K₂, hK₂⟩, ⟨K₁, hK₁⟩⟩; rfl





theorem gc16_tpsum_eq_sigma (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum S β J m A B
      = ∑ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources S (ofEdgeFun S K₂.1) = B then weight S β J (ofEdgeFun S K₂.1) else 0)
            * (∑ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e},
                (if sources S (ofEdgeFun S K₁.1) = A then weight S β J (ofEdgeFun S K₁.1) else 0)
                  * weight S β J (ofEdgeFun S (fun e => (m e - K₂.1 e) - K₁.1 e))) := by
  unfold gc15_tpsum
  rw [Fintype.sum_equiv (gc16_splitSigmaEquiv S m) _
    (fun s : Σ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e} =>
      (if sources S (ofEdgeFun S s.1.1) = B then weight S β J (ofEdgeFun S s.1.1) else 0)
      * ((if sources S (ofEdgeFun S s.2.1) = A then weight S β J (ofEdgeFun S s.2.1) else 0)
          * weight S β J (ofEdgeFun S (fun e => (m e - s.1.1 e) - s.2.1 e))))]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun K₂ _ => ?_)
    rw [Finset.mul_sum]
  · intro K
    simp only [gc16_splitSigmaEquiv, Equiv.coe_fn_mk]
    have hsub : (fun e => m e - K.1.2 e - K.1.1 e) = (fun e => m e - K.1.1 e - K.1.2 e) := by
      ext e; omega
    rw [hsub]; ring















theorem gc16_tpsum_bridge (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum S β J m A B
      = ∑ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources S (ofEdgeFun S K₂.1) = B then weight S β J (ofEdgeFun S K₂.1) else 0)
            * splitWeightedSum S β J (ofEdgeFun S (fun e => m e - K₂.1 e)) 1 A := by
  rw [gc16_tpsum_eq_sigma S β J m A B]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  congr 1
  rw [← gc16_inner_eq_splitWeightedSum S β J (fun e => m e - K₂.1 e) A]
















theorem gc16_threeGap_eq_gated (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m
      = gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  unfold gc15_threeGap gc15_tFiber
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  rw [if_pos hm, if_pos hm, if_pos hm, if_pos hm, if_pos hm]





theorem gc16_perConfig_off_boundary (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        ≠ ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m ≤ 0 := by
  rw [gc15_threeGap_vanish G β h o x y hox hoy hxy m hm]
























def gc16_PerConfigCert (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ,
    sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)) →
      gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x}
        - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y}
        + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
              {some o, none} {some x, none} ≤ 0






theorem gc16_perConfigSign_of_cert (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcert : gc16_PerConfigCert G β h o x y) :
    gc15_PerConfigUrsellSign G β h o x y := by
  intro m
  by_cases hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [gc16_threeGap_eq_gated G β h o x y hox hoy hxy m hm]
    exact hcert m hm
  · exact gc16_perConfig_off_boundary G β h o x y hox hoy hxy m hm













theorem gc16_cert_closes_u3 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcert : gc16_PerConfigCert G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy
    (gc16_perConfigSign_of_cert G β h o x y hox hoy hxy hcert)





theorem gc16_ghs_of_cert (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hcert : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc16_PerConfigCert G β h o x y) :
    GHSThreePointSym G β h o :=
  gc15_ghs_of_perConfig G β h hβ hh o
    (fun x y hox hoy hxy => gc16_perConfigSign_of_cert G β h o x y hox hoy hxy (hcert x y hox hoy hxy))





theorem gc16_aizenman_barsky_of_cert (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hcert : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc16_PerConfigCert G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc15_aizenman_barsky_of_perConfig G β h hβ hh o J
    (fun x y hox hoy hxy => gc16_perConfigSign_of_cert G β h o x y hox hoy hxy (hcert x y hox hoy hxy))
    hfactor












theorem gc16_cert_of_perConfigSign (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc15_PerConfigUrsellSign G β h o x y) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  have h1 := hsign m
  rwa [gc16_threeGap_eq_gated G β h o x y hox hoy hxy m hm] at h1








theorem gc16_cert_iff_perConfigSign (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc16_PerConfigCert G β h o x y ↔ gc15_PerConfigUrsellSign G β h o x y :=
  ⟨gc16_perConfigSign_of_cert G β h o x y hox hoy hxy,
   gc16_cert_of_perConfigSign G β h o x y hox hoy hxy⟩

end StatMech.Walls
