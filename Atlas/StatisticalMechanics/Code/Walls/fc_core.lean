/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.FK.EdgeConfigZ
import Code.Walls.fc_weightle
import Code.Walls.fc_allclosed
import Code.Walls.fc_bulkfraction

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace StatMech

namespace Walls

open StatMech.FK StatMech.Lattice








section Boundedness
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]




theorem fc_fkZEdge_le_qpow {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 1 ≤ q) :
    ecz_fkZEdge G p q ≤ (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
  unfold ecz_fkZEdge
  calc ∑ ω : ecz_ClosedOff G, fkWeight G p q ω.val
      ≤ ∑ ω : ecz_ClosedOff G, q ^ Fintype.card V :=
        Finset.sum_le_sum (fun ω _ => StatMech.Walls.FK.fc_fkWeight_le_qpow_card G hp hp1 hq ω.val)
    _ = (Fintype.card (ecz_ClosedOff G) : ℝ) * q ^ Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
        rw [ecz_closedOff_card G]; push_cast; ring

end Boundedness






variable {d : ℕ}




noncomputable def fc_u (d : ℕ) (q : ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  -Real.log (ecz_fkZEdge (boxGraph d n) (fsc_logistic t) q)


theorem fc_u_two (t : ℝ) (n : ℕ) : fc_u d 2 t n = ecz_u d t n := rfl


noncomputable def fc_edgeFreeEnergy (d : ℕ) (q : ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  -(fc_u d q t n / ((boxGraph d n).edgeFinset.card : ℝ)) + Real.log (1 + Real.exp t)


theorem fc_edgeFE_eq (q : ℝ) (t : ℝ) (n : ℕ) :
    fc_edgeFreeEnergy d q t n = -(fc_u d q t n / agl_E d n) + Real.log (1 + Real.exp t) := rfl


noncomputable def fc_f (d : ℕ) (q : ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  fc_u d q s n / ((boxGraph d n).edgeFinset.card : ℝ)








theorem fc_u_le_edges (q : ℝ) (hq : 1 ≤ q) (t : ℝ) (n : ℕ) :
    fc_u d q t n ≤ ((boxGraph d n).edgeFinset.card : ℝ) * (-Real.log (1 - fsc_logistic t)) := by
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  exact ecz_neglogZEdge_le_edges (boxGraph d n) hp0 hp1 hq












noncomputable def fc_C (q : ℝ) : ℝ := Real.log 2 + 2 * Real.log q

theorem fc_C_nonneg {q : ℝ} (hq : 1 ≤ q) : 0 ≤ fc_C q := by
  unfold fc_C
  have h1 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq
  linarith





theorem fc_edgeFE_le_const (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    fc_edgeFreeEnergy d q s n ≤ fc_C q + Real.log (1 + Real.exp s) := by
  unfold fc_edgeFreeEnergy fc_u
  set E := (boxGraph d n).edgeFinset.card with hEdef
  set V := Fintype.card (boxVerts d n) with hVdef
  set p := fsc_logistic s
  have hp0 : (0:ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hEr : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hZpos : 0 < ecz_fkZEdge (boxGraph d n) p q := ecz_fkZEdge_pos _ hp0 hp1 (by linarith)
  have hub : ecz_fkZEdge (boxGraph d n) p q ≤ (2:ℝ)^E * q^V :=
    fc_fkZEdge_le_qpow _ hp0.le hp1.le hq
  have hlogq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hqpow : (0:ℝ) < q^V := by positivity
  have hlog : Real.log (ecz_fkZEdge (boxGraph d n) p q) ≤ (E:ℝ) * Real.log 2 + (V:ℝ) * Real.log q := by
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ Real.log ((2:ℝ)^E * q^V) := Real.log_le_log hZpos hub
      _ = (E:ℝ) * Real.log 2 + (V:ℝ) * Real.log q := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hVle : (V:ℝ) ≤ 2 * E := by exact_mod_cast ecz_boxVerts_le_edges d n hd hn
  
  have hkey : -(-Real.log (ecz_fkZEdge (boxGraph d n) p q) / (E:ℝ)) ≤ fc_C q := by
    rw [neg_div, neg_neg, div_le_iff₀ hEr]
    have hstep : (V:ℝ) * Real.log q ≤ (2 * E) * Real.log q :=
      mul_le_mul_of_nonneg_right hVle hlogq
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ (E:ℝ) * Real.log 2 + (V:ℝ) * Real.log q := hlog
      _ ≤ (E:ℝ) * Real.log 2 + (2 * E) * Real.log q := by linarith
      _ = fc_C q * E := by unfold fc_C; ring
  linarith













theorem fc_box_neglog_doubling (d K : ℕ) {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    fc_u d q t (2 * K + 1) ≤ (2 : ℝ) ^ d * fc_u d q t K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hq0 : (0:ℝ) < q := by linarith
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    ecz_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p q hp0 hp1 hq0 Finset.univ
  have hrest : ecz_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q
      = fc_u d q t (2 * K + 1) := by
    rw [ecz_uu, fc_u, ecz_fkZEdge_iso (qp_restGUnivIso d K) p q]
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
      = ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q
        + (2 : ℝ) ^ d * fc_u d q t K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
          = ∑ τ : Option (Fin d → Bool),
              ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ s : Fin d → Bool,
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q = fc_u d q t K :=
      fun s => by rw [ecz_uu, ecz_block_fkZEdge]; rfl
    rw [Finset.sum_congr rfl (fun s _ => heach s), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool],
      nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q
      ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
    rw [ecz_uu]
    calc -Real.log (ecz_fkZEdge (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q)
        ≤ ((qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card : ℝ) * c :=
          ecz_neglogZEdge_le_edges _ hp0 hp1 hq
      _ ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
          apply mul_le_mul_of_nonneg_right _ hc0
          exact_mod_cast qp_blkNone_edge_le d K
  have hIbound : (I : ℝ) ≤ ((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) := by
    have h2 : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
          (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card)
        ≤ ∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))), 2 * d * (qp_Jset d K).card :=
      Finset.sum_le_sum (fun τ _ => qp_straddle_card_le_all d K τ)
    have h3 : (∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))), 2 * d * (qp_Jset d K).card)
        = (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      congr 1
      rw [show Fintype.card (Option (Fin d → Bool)) = Fintype.card (Fin d → Bool) + 1 from
          Fintype.card_option,
        show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool]]
    calc (I : ℝ) ≤ ((∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card : ℕ) : ℝ) := by
          exact_mod_cast hIbd
      _ ≤ (((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) := by
          exact_mod_cast le_trans h2 (le_of_eq h3)
  rw [hrest, hblksum] at hIle
  push_cast at hIle hnone hIbound ⊢
  nlinarith [hIle, hnone, hIbound, hc0, mul_le_mul_of_nonneg_right hIbound hc0]










def fc_AdditiveDoublingBound (d : ℕ) (q : ℝ) (t : ℝ) : Prop :=
  ∃ (I : ℕ → ℝ),
    (∀ j, 0 ≤ I j)
    ∧ Summable (fun j => I j / agl_E d (agl_K (j + 1)))
    ∧ (∀ j, fc_u d q t (agl_K (j + 1))
        ≤ (2 : ℝ) ^ d * fc_u d q t (agl_K j) + I j * (-Real.log (1 - fsc_logistic t)))
    ∧ (∀ j, |(2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))| ≤ I j)




theorem fc_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    fc_AdditiveDoublingBound d q t := by
  set c := -Real.log (1 - fsc_logistic t) with hc
  have hp0 : (0 : ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set N : ℕ → ℝ := fun j => ((2 * d * (qp_Jset d (agl_K j)).card
    + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card) : ℕ) : ℝ) with hN
  set G : ℕ → ℝ := fun j => agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) with hG
  have hKsucc : ∀ j, agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ
  have hGnn : ∀ j, 0 ≤ G j := by
    intro j; rw [hG]; simp only
    have h := qp_edge_le d (agl_K j) hd
    rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
    rw [agl_E, agl_E]; linarith [h]
  set I : ℕ → ℝ := fun j => N j + G j with hI
  have hInn : ∀ j, 0 ≤ I j := by
    intro j; rw [hI]; have : 0 ≤ N j := Nat.cast_nonneg _; linarith [hGnn j]
  refine ⟨I, hInn, ?_, ?_, ?_⟩
  · apply qp_summable_ratio d hd I _ hInn
    intro j
    have hNb : N j ≤ ((2 ^ d + 2) * (2 * d * d) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      simp only [hN]
      have hJ : (qp_Jset d (agl_K j)).card ≤ d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) :=
        qp_Jset_card_le d (agl_K j) hd
      rw [show (2 * d * (qp_Jset d (agl_K j)).card + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card))
            = (2 ^ d + 2) * (2 * d * (qp_Jset d (agl_K j)).card) from by ring]
      push_cast
      have hbase : (2 * (2 * (agl_K j : ℝ) + 1) + 1) = 4 * (agl_K j : ℝ) + 3 := by ring
      have hJR : ((qp_Jset d (agl_K j)).card : ℝ)
          ≤ (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
        calc ((qp_Jset d (agl_K j)).card : ℝ)
            ≤ ((d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hJ
          _ = (d : ℝ) * (2 * (2 * (agl_K j : ℝ) + 1) + 1) ^ (d - 1) := by push_cast; ring
          _ = (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by rw [hbase]
      calc ((2 : ℝ) ^ d + 2) * (2 * d * ((qp_Jset d (agl_K j)).card : ℝ))
          ≤ ((2 : ℝ) ^ d + 2) * (2 * d * ((d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left hJR (by positivity)
        _ = ((2 : ℝ) ^ d + 2) * (2 * d * d) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by ring
    have hGb : G j ≤ ((d : ℝ) * (d + 2)) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      rw [hG]; simp only
      rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
      have h := qp_edge_gap_le d (agl_K j) hd
      rw [agl_E, agl_E]; linarith [h]
    rw [hI]; linarith [hNb, hGb]
  · intro j
    have hdbl := fc_box_neglog_doubling d (agl_K j) hq t
    rw [show fc_u d q t (agl_K (j + 1)) = fc_u d q t (2 * agl_K j + 1) from by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      rw [hI]; apply mul_le_mul_of_nonneg_right _ hc0; linarith [hGnn j]
    calc fc_u d q t (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * fc_u d q t (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * fc_u d q t (agl_K j) + I j * c := by linarith
  · intro j
    have hGval : G j = agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) := rfl
    rw [abs_of_nonpos (by have := hGnn j; rw [hGval] at this; linarith)]
    rw [hI]; have hNn : 0 ≤ N j := Nat.cast_nonneg _
    have hGeq : -((2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))) = G j := by
      rw [hGval]; ring
    rw [hGeq]; linarith











theorem fc_box_vanHove_subadd (m n : ℕ) {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    fc_u d q t n ≤ ((ecz_T m n) ^ d : ℝ) * fc_u d q t m
      + (((boxGraph d n).edgeFinset.card : ℝ)
          - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic t)) := by
  classical
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hq0 : (0:ℝ) < q := by linarith
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set tag := ecz_vanHoveTag m n with htag
  set K₀ := boxGraph d n with hK₀
  have hsub := ecz_multiblock_subadd K₀ tag p q hp0 hp1 hq0 Finset.univ
  have hrest_u : ecz_uu (qp_restG K₀ tag Finset.univ) p q = fc_u d q t n := by
    rw [ecz_uu, fc_u, hp, ecz_fkZEdge_iso (ecz_restUnivIso m n) p q]
  have hrest_E : ((qp_restG K₀ tag Finset.univ).edgeFinset.card : ℝ)
      = ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [(ecz_restUnivIso m n).card_edgeFinset_eq]
  have hsplit_u : (∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q)
      = ecz_uu (qp_blkG K₀ tag none) p q
        + ((ecz_T m n) ^ d : ℝ) * fc_u d q t m := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ cc : Fin d → Fin (ecz_T m n),
        ecz_uu (qp_blkG K₀ tag (some cc)) p q = fc_u d q t m := fun cc => by
      rw [ecz_uu, fc_u, hp, ecz_cellBlock_fkZEdge m n cc]
    rw [Finset.sum_congr rfl (fun cc _ => heach cc), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hsplit_E : (∑ τ : Option (Fin d → Fin (ecz_T m n)),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
        + ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ cc : Fin d → Fin (ecz_T m n),
        ((qp_blkG K₀ tag (some cc)).edgeFinset.card : ℝ) = ((boxGraph d m).edgeFinset.card : ℝ) :=
      fun cc => by rw [ecz_cellBlock_edge_card m n cc]
    rw [Finset.sum_congr rfl (fun cc _ => heach cc), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG K₀ tag none) p q
      ≤ ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) * c := by
    rw [ecz_uu, hc]; exact ecz_neglogZEdge_le_edges _ hp0 hp1 hq
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ecz_uu (qp_blkG K₀ tag τ) p q)
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q from rfl] at hsub
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) from rfl]
    at hsub
  rw [hrest_u, hsplit_u, hrest_E, hsplit_E] at hsub
  set uNone : ℝ := ecz_uu (qp_blkG K₀ tag none) p q with huNone
  set ENone : ℝ := ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) with hENone
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  set Um : ℝ := fc_u d q t m with hUm
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEm
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEn
  have hexpand : (En - (ENone + Td * Em)) * c = (En - Td * Em) * c - ENone * c := by ring
  rw [hexpand] at hsub
  linarith [hsub, hnone]









theorem fc_perEdge_vanHove (m n : ℕ) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) (hEm : 0 < (boxGraph d m).edgeFinset.card) :
    fc_f d q s n
      ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  have hEmR : (0 : ℝ) < ((boxGraph d m).edgeFinset.card : ℝ) := by exact_mod_cast hEm
  have hsub := fc_box_vanHove_subadd (d := d) m n hq s
  rw [← hc] at hsub
  rw [fc_f, fc_f]
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEnDef
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEmDef
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  rw [div_le_iff₀ hEnR]
  have hEmne : Em ≠ 0 := ne_of_gt hEmR
  have hkey : (Td * Em / En * (fc_u d q s m / Em) + (1 - Td * Em / En) * c) * En
      = Td * fc_u d q s m + (En - Td * Em) * c := by
    field_simp
  calc fc_u d q s n ≤ Td * fc_u d q s m + (En - Td * Em) * c := hsub
    _ = (Td * Em / En * (fc_u d q s m / Em) + (1 - Td * Em / En) * c) * En := hkey.symm







theorem fc_dyadic_f_tendsto (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card) :
    ∃ L : ℝ, Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := fc_additiveDoublingBound d hd hq s
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  set M : ℝ := fc_C q + c with hM
  have hMc0 : 0 ≤ M + c := by
    rw [hM]; have := fc_C_nonneg hq; linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  have hmono : ∀ j, fc_edgeFreeEnergy d q s (agl_K j) - δ j ≤ fc_edgeFreeEnergy d q s (agl_K (j + 1)) := by
    intro j
    rw [fc_edgeFE_eq q s (agl_K j), fc_edgeFE_eq q s (agl_K (j + 1))]
    have hstep := bxt_perVolume_doubling_step (a := fc_u d q s (agl_K j))
      (A := fc_u d q s (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hupper : -(fc_u d q s (agl_K j) / agl_E d (agl_K j)) ≤ fc_C q := by
      have h := fc_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) hq s (hbox j)
      rw [fc_edgeFE_eq] at h
      have hlog1 : (0:ℝ) ≤ Real.log (1 + Real.exp s) :=
        Real.log_nonneg (by have := Real.exp_pos s; linarith)
      linarith
    have hlower : fc_u d q s (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hEr : (0:ℝ) < agl_E d (agl_K j) := hEpos j
      have hge := fc_u_le_edges (d := d) q hq s (agl_K j)
      rw [div_le_iff₀ hEr]
      show fc_u d q s (agl_K j) ≤ c * agl_E d (agl_K j)
      have : fc_u d q s (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [agl_E, hc] using hge
      linarith [mul_comm (agl_E d (agl_K j)) c, this]
    have huEbd : |fc_u d q s (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      have hquot : |fc_u d q s (agl_K j)| / agl_E d (agl_K j)
          = |fc_u d q s (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [hquot, abs_le]
      exact ⟨by rw [hM]; linarith [hupper, hc0], by rw [hM]; linarith [hlower, fc_C_nonneg hq]⟩
    have hdefle : (|fc_u d q s (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith [huEbd]
    have hgoal : -(fc_u d q s (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(fc_u d q s (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  have hbdd : BddAbove (Set.range fun j => fc_edgeFreeEnergy d q s (agl_K j)) := by
    refine ⟨fc_C q + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    exact fc_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) hq s (hbox j)
  obtain ⟨L', hL'⟩ := agl_subseq_almost_mono_converges
    (fun n => fc_edgeFreeEnergy d q s n) agl_K δ
    (fun j => mul_nonneg hMc0 (hIE0 j)) (hIsum.mul_left (M + c)) hmono hbdd
  refine ⟨Real.log (1 + Real.exp s) - L', ?_⟩
  have heq : ∀ j, fc_f d q s (agl_K j)
      = Real.log (1 + Real.exp s) - fc_edgeFreeEnergy d q s (agl_K j) := by
    intro j; rw [fc_f, fc_edgeFE_eq, agl_E]; ring
  rw [show (fun j => fc_f d q s (agl_K j))
      = (fun j => Real.log (1 + Real.exp s) - fc_edgeFreeEnergy d q s (agl_K j)) from
    funext heq]
  have := (hL'.const_sub (Real.log (1 + Real.exp s)))
  simpa using this












theorem fc_f_lower (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hbox : ∀ k, 1 ≤ k → 0 < (boxGraph d k).edgeFinset.card) (L : ℝ)
    (hL : Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L)) :
    ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n)
      ≤ fc_f d q s n := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hbox n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n := by positivity
  set rfun : ℕ → ℝ := fun j => ((ecz_T n (agl_K j)) ^ d : ℝ)
    * ((boxGraph d n).edgeFinset.card : ℝ) / ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) with hrfun
  have hr_tendsto : Tendsto rfun atTop (𝓝 (2 * (n : ℝ) / (2 * n + 1))) :=
    ecz_bulkFraction_tendsto hd n hn |>.comp agl_K_tendsto_atTop
  have hr_pos : ∀ j, 0 < ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) := fun j => by
    exact_mod_cast hbox (agl_K j) (agl_K_pos j)
  have hbound : ∀ j, n ≤ agl_K j →
      fc_f d q s (agl_K j) ≤ rfun j * fc_f d q s n + (1 - rfun j) * c := by
    intro j hj
    have := fc_perEdge_vanHove (d := d) n (agl_K j) hq s (hbox (agl_K j) (agl_K_pos j)) (hbox n hn)
    rw [← hc] at this
    simpa [hrfun] using this
  have hrinf_pos : (0 : ℝ) < 2 * (n : ℝ) / (2 * n + 1) := by positivity
  have hRHS_tendsto : Tendsto (fun j => rfun j * fc_f d q s n + (1 - rfun j) * c) atTop
      (𝓝 ((2 * (n : ℝ) / (2 * n + 1)) * fc_f d q s n
          + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)) :=
    ((hr_tendsto.mul tendsto_const_nhds).add
      (((tendsto_const_nhds).sub hr_tendsto).mul tendsto_const_nhds))
  have hKge : ∀ᶠ j in atTop, n ≤ agl_K j := agl_K_tendsto_atTop.eventually_ge_atTop n
  have hLle : L ≤ (2 * (n : ℝ) / (2 * n + 1)) * fc_f d q s n + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c := by
    refine le_of_tendsto_of_tendsto hL hRHS_tendsto ?_
    filter_upwards [hKge] with j hj using hbound j hj
  set R : ℝ := 2 * (n : ℝ) / (2 * n + 1) with hR
  have hRpos : 0 < R := hrinf_pos
  have h2n1 : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
  have hfn : (L - (1 - R) * c) / R ≤ fc_f d q s n := by
    rw [div_le_iff₀ hRpos]; nlinarith [hLle]
  have hsimp : (L - (1 - R) * c) / R
      = (2 * (n : ℝ) + 1) / (2 * n) * L - c / (2 * n) := by
    rw [hR]; field_simp; ring
  rw [hsimp] at hfn
  linarith [hfn]


noncomputable def fc_g (d : ℕ) (q : ℝ) (s : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) / (2 * m + 1)) * fc_f d q s m
    + (1 - 2 * (m : ℝ) / (2 * m + 1)) * (-Real.log (1 - fsc_logistic s))



theorem fc_g_dyadic_tendsto {q : ℝ} (s : ℝ) (L : ℝ)
    (hL : Tendsto (fun j => fc_f d q s (agl_K j)) atTop (𝓝 L)) :
    Tendsto (fun j => fc_g d q s (agl_K j)) atTop (𝓝 L) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hKtop : Tendsto (fun j => (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop atTop :=
    ecz_denom_tendsto_atTop.comp (by exact_mod_cast agl_K_tendsto_atTop)
  have h0 : Tendsto (fun j => (1 : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1:ℝ))).div_atTop hKtop
  have hR : Tendsto (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (𝓝 1) := by
    have heq : ∀ j, 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)
        = 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) := by
      intro j
      have hpos : (0:ℝ) < 2 * ((agl_K j : ℕ) : ℝ) + 1 := by positivity
      field_simp; ring
    rw [show (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
        = (fun j => 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1)) from funext heq]
    have := h0.const_sub (1 : ℝ); simpa using this
  have hprod : Tendsto (fun j => fc_g d q s (agl_K j)) atTop
      (𝓝 ((1 : ℝ) * L + (1 - 1) * c)) := by
    have heq : (fun j => fc_g d q s (agl_K j))
        = (fun j => (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * fc_f d q s (agl_K j)
          + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c) := by
      funext j; rw [fc_g, hc]
    rw [heq]
    exact ((hR.mul hL).add ((tendsto_const_nhds.sub hR).mul tendsto_const_nhds))
  rw [show (1 : ℝ) * L + (1 - 1) * c = L by ring] at hprod
  exact hprod



theorem fc_upperSeq_tendsto (hd : 1 ≤ d) {q : ℝ} (s : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n =>
        (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop
      (𝓝 (fc_g d q s m)) := by
  have hr := ecz_bulkFraction_tendsto (d := d) hd m hm
  rw [fc_g]
  exact ((hr.mul (tendsto_const_nhds (x := fc_f d q s m))).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub hr).mul
      (tendsto_const_nhds (x := -Real.log (1 - fsc_logistic s)))))










theorem fc_perEdgeDensityConverges (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    ∃ ρ : ℝ, Tendsto (fun n => fc_u d q s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 ρ) := by
  classical
  obtain ⟨L, hL⟩ := fc_dyadic_f_tendsto (d := d) hd hq s (fun j => hbox _ (agl_K_pos j))
  set c := -Real.log (1 - fsc_logistic s) with hc
  refine ⟨L, ?_⟩
  show Tendsto (fun n => fc_u d q s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 L)
  have hfdef : (fun n => fc_u d q s n / ((boxGraph d n).edgeFinset.card : ℝ)) = fc_f d q s := by
    funext n; rfl
  rw [hfdef]
  have hgK := fc_g_dyadic_tendsto (d := d) (q := q) s L hL
  have hℓ_tendsto : Tendsto (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n)) atTop
      (𝓝 L) := by
    have h1 : Tendsto (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L) atTop (𝓝 (1 * L)) :=
      ecz_oddEven_ratio_tendsto.mul tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => c / (2 * (n : ℝ))) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      exact (tendsto_const_nhds (x := c)).div_atTop hden
    have := h1.sub h2; simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hℓ_tendsto) (ε / 2) (by linarith)
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hgK) (ε / 2) (by linarith)
  set J := N0 with hJ
  have hgJ : fc_g d q s (agl_K J) < L + ε / 2 := by
    have := hN0 J (le_refl _); rw [Real.dist_eq, abs_lt] at this; linarith [this.2]
  have hupperseq := fc_upperSeq_tendsto (d := d) (q := q) hd s (agl_K J) (agl_K_pos J)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hupperseq) (ε / 2) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hℓle : ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) ≤ fc_f d q s n := by
      have := fc_f_lower (d := d) hd hq s n hn1 hbox L hL; rw [← hc] at this; exact this
    have hℓclose : |((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) - L| < ε / 2 := by
      have := hN1 n hnN1; rwa [Real.dist_eq] at this
    rw [abs_lt] at hℓclose; linarith [hℓclose.1, hℓle]
  · have hfle : fc_f d q s n
        ≤ (((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s (agl_K J)
          + (1 - ((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) :=
      fc_perEdge_vanHove (d := d) (agl_K J) n hq s (hbox n hn1) (hbox (agl_K J) (agl_K_pos J))
    have hclose : |(((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fc_f d q s (agl_K J)
          + (1 - ((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))
          - fc_g d q s (agl_K J)| < ε / 2 := by
      have := hN2 n hnN2; rwa [Real.dist_eq] at this
    rw [abs_lt] at hclose; linarith [hclose.2, hfle, hgJ]












def fc_PerEdgeDensityConverges (d : ℕ) (q : ℝ) (s : ℝ) : Prop :=
  ∃ ρ : ℝ, Tendsto (fun n => fc_u d q s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 ρ)






theorem fc_perEdgeDensityConverges_unconditional (hd : 1 ≤ d) {q : ℝ} (hq : 1 ≤ q) (s : ℝ) :
    fc_PerEdgeDensityConverges d q s :=
  fc_perEdgeDensityConverges hd hq s (fun n hn => ecz_box_edge_pos d hd hn)




theorem fc_perEdgeDensityConverges_two (s : ℝ) :
    fc_PerEdgeDensityConverges d 2 s ↔ ecz_PerEdgeDensityConverges d s := Iff.rfl




example : True := by
  have h := fc_perEdgeDensityConverges_unconditional (d := 2) (by norm_num) (q := 3) (by norm_num) 0
  obtain ⟨ρ, _⟩ := h
  trivial








































theorem fc_core_report : True := trivial

end Walls

end StatMech
