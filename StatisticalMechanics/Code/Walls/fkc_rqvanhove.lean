/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Walls.fkc_rqbdd
import Code.Walls.fkc_rqbulkfraction

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice




noncomputable def fkc_u (d : ℕ) (s q : ℝ) (n : ℕ) : ℝ :=
  -Real.log (ecz_fkZEdge (boxGraph d n) (fsc_logistic s) q)


noncomputable def fkc_f (d : ℕ) (s q : ℝ) (n : ℕ) : ℝ :=
  fkc_u d s q n / ((boxGraph d n).edgeFinset.card : ℝ)


theorem fkc_edgeFreeEnergy_eq (d : ℕ) (s q : ℝ) (n : ℕ) :
    fkc_edgeFreeEnergy d s q n = -fkc_f d s q n + Real.log (1 + Real.exp s) := by
  unfold fkc_edgeFreeEnergy fkc_f fkc_u
  rw [neg_div, neg_neg]


@[simp] theorem fkc_u_q2 (d : ℕ) (s : ℝ) (n : ℕ) : fkc_u d s 2 n = ecz_u d s n := rfl




theorem fkc_box_neglog_doubling (d K : ℕ) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_u d s q (2 * K + 1) ≤ (2 : ℝ) ^ d * fkc_u d s q K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic s)) := by
  set p := fsc_logistic s with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    ecz_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p q hp0 hp1 (by linarith) Finset.univ
  have hrest : ecz_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q
      = fkc_u d s q (2 * K + 1) := by
    rw [ecz_uu, fkc_u, ecz_fkZEdge_iso (qp_restGUnivIso d K) p q]
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
      = ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q
        + (2 : ℝ) ^ d * fkc_u d s q K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
          = ∑ τ : Option (Fin d → Bool),
              ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ t : Fin d → Bool,
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some t)) p q
          = fkc_u d s q K := fun t => by
      rw [ecz_uu, fkc_u, ecz_block_fkZEdge]
    rw [Finset.sum_congr rfl (fun t _ => heach t), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_bool],
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
    have h3 : (∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
          2 * d * (qp_Jset d K).card)
        = (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      congr 1
      rw [Fintype.card_option,
        show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_bool]]
    calc (I : ℝ) ≤ ((∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card : ℕ) : ℝ) := by
          exact_mod_cast hIbd
      _ ≤ (((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) := by
          exact_mod_cast le_trans h2 (le_of_eq h3)
  rw [hrest, hblksum] at hIle
  push_cast at hIle hnone hIbound ⊢
  nlinarith [hIle, hnone, hIbound, hc0, mul_le_mul_of_nonneg_right hIbound hc0]


theorem fkc_box_vanHove_subadd (d m n : ℕ) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_u d s q n ≤ ((ecz_T m n) ^ d : ℝ) * fkc_u d s q m
      + (((boxGraph d n).edgeFinset.card : ℝ)
          - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic s)) := by
  classical
  set p := fsc_logistic s with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  set c := -Real.log (1 - p) with hc
  set tag := ecz_vanHoveTag m n with htag
  set K₀ := boxGraph d n with hK₀
  have hsub := ecz_multiblock_subadd K₀ tag p q hp0 hp1 (by linarith) Finset.univ
  have hrest_u : ecz_uu (qp_restG K₀ tag Finset.univ) p q = fkc_u d s q n := by
    rw [ecz_uu, fkc_u, hp, ecz_fkZEdge_iso (ecz_restUnivIso m n) p q]
  have hrest_E : ((qp_restG K₀ tag Finset.univ).edgeFinset.card : ℝ)
      = ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [(ecz_restUnivIso m n).card_edgeFinset_eq]
  have hsplit_u : (∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q)
      = ecz_uu (qp_blkG K₀ tag none) p q
        + ((ecz_T m n) ^ d : ℝ) * fkc_u d s q m := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ a : Fin d → Fin (ecz_T m n),
        ecz_uu (qp_blkG K₀ tag (some a)) p q = fkc_u d s q m := fun a => by
      rw [ecz_uu, fkc_u, hp, ecz_cellBlock_fkZEdge m n a]
    rw [Finset.sum_congr rfl (fun a _ => heach a), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hsplit_E : (∑ τ : Option (Fin d → Fin (ecz_T m n)),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
        + ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ a : Fin d → Fin (ecz_T m n),
        ((qp_blkG K₀ tag (some a)).edgeFinset.card : ℝ)
          = ((boxGraph d m).edgeFinset.card : ℝ) := fun a => by
      rw [ecz_cellBlock_edge_card m n a]
    rw [Finset.sum_congr rfl (fun a _ => heach a), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG K₀ tag none) p q
      ≤ ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) * c := by
    rw [ecz_uu, hc]
    exact ecz_neglogZEdge_le_edges _ hp0 hp1 hq
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ecz_uu (qp_blkG K₀ tag τ) p q)
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q from rfl]
    at hsub
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)),
          ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) from rfl] at hsub
  rw [hrest_u, hsplit_u, hrest_E, hsplit_E] at hsub
  set uNone : ℝ := ecz_uu (qp_blkG K₀ tag none) p q
  set ENone : ℝ := ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ)
  set Um : ℝ := fkc_u d s q m
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ)
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)
  have hexpand : (En - (ENone + Td * Em)) * c = (En - Td * Em) * c - ENone * c := by ring
  rw [hexpand] at hsub
  linarith [hsub, hnone]


theorem fkc_perEdge_vanHove (d m n : ℕ) (s q : ℝ) (hq : 1 ≤ q)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) (hEm : 0 < (boxGraph d m).edgeFinset.card) :
    fkc_f d s q n
      ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fkc_f d s q m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  have hEmR : (0 : ℝ) < ((boxGraph d m).edgeFinset.card : ℝ) := by exact_mod_cast hEm
  have hsub := fkc_box_vanHove_subadd d m n s q hq
  rw [fkc_f, fkc_f]
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ)
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ)
  set c : ℝ := -Real.log (1 - fsc_logistic s)
  rw [div_le_iff₀ hEnR]
  have hkey : (Td * Em / En * (fkc_u d s q m / Em) + (1 - Td * Em / En) * c) * En
      = Td * fkc_u d s q m + (En - Td * Em) * c := by field_simp
  calc fkc_u d s q n ≤ Td * fkc_u d s q m + (En - Td * Em) * c := hsub
    _ = (Td * Em / En * (fkc_u d s q m / Em) + (1 - Td * Em / En) * c) * En := hkey.symm




def fkc_AdditiveDoublingBound (d : ℕ) (s q : ℝ) : Prop :=
  ∃ I : ℕ → ℝ,
    (∀ j, 0 ≤ I j)
    ∧ Summable (fun j => I j / agl_E d (agl_K (j + 1)))
    ∧ (∀ j, fkc_u d s q (agl_K (j + 1))
        ≤ (2 : ℝ) ^ d * fkc_u d s q (agl_K j)
          + I j * (-Real.log (1 - fsc_logistic s)))
    ∧ (∀ j, |(2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))| ≤ I j)


theorem fkc_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_AdditiveDoublingBound d s q := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0 : ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  set N : ℕ → ℝ := fun j => ((2 * d * (qp_Jset d (agl_K j)).card
    + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card) : ℕ) : ℝ) with hN
  set G : ℕ → ℝ := fun j => agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) with hG
  have hGnn : ∀ j, 0 ≤ G j := by
    intro j
    rw [hG]; simp only
    have h := qp_edge_le d (agl_K j) hd
    rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) by rw [agl_K_succ]]
    rw [agl_E, agl_E]
    linarith
  set I : ℕ → ℝ := fun j => N j + G j with hI
  have hInn : ∀ j, 0 ≤ I j := by
    intro j; rw [hI]; exact add_nonneg (Nat.cast_nonneg _) (hGnn j)
  refine ⟨I, hInn, ?_, ?_, ?_⟩
  · apply qp_summable_ratio d hd I _ hInn
    intro j
    have hNb : N j ≤ ((2 ^ d + 2) * (2 * d * d) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      simp only [hN]
      have hJ := qp_Jset_card_le d (agl_K j) hd
      rw [show (2 * d * (qp_Jset d (agl_K j)).card
          + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card))
          = (2 ^ d + 2) * (2 * d * (qp_Jset d (agl_K j)).card) by ring]
      push_cast
      have hJR : ((qp_Jset d (agl_K j)).card : ℝ)
          ≤ (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
        calc ((qp_Jset d (agl_K j)).card : ℝ)
            ≤ ((d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hJ
          _ = (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by push_cast; ring
      calc ((2 : ℝ) ^ d + 2) * (2 * d * ((qp_Jset d (agl_K j)).card : ℝ))
          ≤ ((2 : ℝ) ^ d + 2) * (2 * d * ((d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))) := by
            gcongr
        _ = ((2 : ℝ) ^ d + 2) * (2 * d * d) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by ring
    have hGb : G j ≤ ((d : ℝ) * (d + 2)) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      rw [hG]; simp only
      rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) by rw [agl_K_succ]]
      have h := qp_edge_gap_le d (agl_K j) hd
      rw [agl_E, agl_E]
      linarith
    rw [hI]
    linarith
  · intro j
    have hdbl := fkc_box_neglog_doubling d (agl_K j) s q hq
    rw [show fkc_u d s q (agl_K (j + 1)) = fkc_u d s q (2 * agl_K j + 1) by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      apply mul_le_mul_of_nonneg_right _ hc0
      rw [hI]
      exact le_add_of_nonneg_right (hGnn j)
    calc fkc_u d s q (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * fkc_u d s q (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * fkc_u d s q (agl_K j) + I j * c := by linarith
  · intro j
    rw [abs_of_nonpos]
    · rw [hI, hG]
      have hN0 : 0 ≤ N j := Nat.cast_nonneg _
      linarith
    · rw [hG] at hGnn
      linarith [hGnn j]


theorem fkc_dyadic_f_tendsto (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q) :
    ∃ L : ℝ, Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := fkc_additiveDoublingBound d hd s q hq
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0 : ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E
    exact_mod_cast ecz_box_edge_pos d hd (agl_K_pos j)
  set M : ℝ := Real.log 2 + 2 * Real.log q + c with hM
  have hMpc0 : 0 ≤ M + c := by
    rw [hM]
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq
    linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  have hmono : ∀ j, fkc_edgeFreeEnergy d s q (agl_K j) - δ j
      ≤ fkc_edgeFreeEnergy d s q (agl_K (j + 1)) := by
    intro j
    rw [fkc_edgeFreeEnergy_eq, fkc_edgeFreeEnergy_eq]
    have hstep := bxt_perVolume_doubling_step
      (a := fkc_u d s q (agl_K j)) (A := fkc_u d s q (agl_K (j + 1)))
      (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hupper : -(fkc_u d s q (agl_K j) / agl_E d (agl_K j))
        ≤ Real.log 2 + 2 * Real.log q := by
      have h := fkc_rq_bdd d (agl_K j) hd (agl_K_pos j) s q hq
      have h' : -(fkc_u d s q (agl_K j) / agl_E d (agl_K j))
          + Real.log (1 + Real.exp s)
          ≤ (Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s) := by
        simpa [fkc_edgeFreeEnergy_eq, fkc_f, agl_E] using h
      linarith
    have hlower : fkc_u d s q (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hge := ecz_neglogZEdge_le_edges (boxGraph d (agl_K j))
        (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq
      rw [div_le_iff₀ (hEpos j)]
      have : fkc_u d s q (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [fkc_u, agl_E, hc] using hge
      linarith
    have huEbd : |fkc_u d s q (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      rw [show |fkc_u d s q (agl_K j)| / agl_E d (agl_K j)
          = |fkc_u d s q (agl_K j) / agl_E d (agl_K j)| by
            rw [abs_div, abs_of_pos (hEpos j)], abs_le]
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq
      constructor <;> rw [hM] <;> linarith
    have hdefle : (|fkc_u d s q (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith
    have hgoal : -(fkc_u d s q (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(fkc_u d s q (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by
      linarith
    change -(fkc_u d s q (agl_K j) / agl_E d (agl_K j))
        + Real.log (1 + Real.exp s) - δ j
      ≤ -(fkc_u d s q (agl_K (j + 1)) / agl_E d (agl_K (j + 1)))
        + Real.log (1 + Real.exp s)
    linarith
  have hbdd : BddAbove (Set.range fun j => fkc_edgeFreeEnergy d s q (agl_K j)) := by
    refine ⟨(Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    exact fkc_rq_bdd d (agl_K j) hd (agl_K_pos j) s q hq
  obtain ⟨L', hL'⟩ := agl_subseq_almost_mono_converges
    (fun n => fkc_edgeFreeEnergy d s q n) agl_K δ
    (fun j => mul_nonneg hMpc0 (hIE0 j)) (hIsum.mul_left (M + c)) hmono hbdd
  refine ⟨Real.log (1 + Real.exp s) - L', ?_⟩
  have heq : ∀ j, fkc_f d s q (agl_K j)
      = Real.log (1 + Real.exp s) - fkc_edgeFreeEnergy d s q (agl_K j) := by
    intro j; rw [fkc_edgeFreeEnergy_eq]; ring
  rw [show (fun j => fkc_f d s q (agl_K j))
      = fun j => Real.log (1 + Real.exp s) - fkc_edgeFreeEnergy d s q (agl_K j) from funext heq]
  simpa using hL'.const_sub (Real.log (1 + Real.exp s))




def fkc_PerEdgeDensityConverges (d : ℕ) (s q : ℝ) : Prop :=
  ∃ ρ : ℝ, Tendsto (fun n => fkc_f d s q n) atTop (nhds ρ)


theorem fkc_f_lower (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q)
    (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L)) :
    ((2 * (n : ℝ) + 1) / (2 * n)) * L
        - (-Real.log (1 - fsc_logistic s)) / (2 * n) ≤ fkc_f d s q n := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  set rfun : ℕ → ℝ := fun j => ((ecz_T n (agl_K j)) ^ d : ℝ)
    * ((boxGraph d n).edgeFinset.card : ℝ)
      / ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) with hrfun
  have hr_tendsto : Tendsto rfun atTop (nhds (2 * (n : ℝ) / (2 * n + 1))) :=
    ecz_bulkFraction_tendsto hd n hn |>.comp agl_K_tendsto_atTop
  have hbound : ∀ j, n ≤ agl_K j →
      fkc_f d s q (agl_K j) ≤ rfun j * fkc_f d s q n + (1 - rfun j) * c := by
    intro j _hj
    have h := fkc_perEdge_vanHove d n (agl_K j) s q hq
      (ecz_box_edge_pos d hd (agl_K_pos j)) (ecz_box_edge_pos d hd hn)
    simpa [hrfun, hc] using h
  have hRHS : Tendsto (fun j => rfun j * fkc_f d s q n + (1 - rfun j) * c) atTop
      (nhds ((2 * (n : ℝ) / (2 * n + 1)) * fkc_f d s q n
        + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)) :=
    (hr_tendsto.mul tendsto_const_nhds).add
      ((tendsto_const_nhds.sub hr_tendsto).mul tendsto_const_nhds)
  have hKge : ∀ᶠ j in atTop, n ≤ agl_K j := agl_K_tendsto_atTop.eventually_ge_atTop n
  have hLle : L ≤ (2 * (n : ℝ) / (2 * n + 1)) * fkc_f d s q n
      + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c := by
    refine le_of_tendsto_of_tendsto hL hRHS ?_
    filter_upwards [hKge] with j hj using hbound j hj
  have h2n : (0 : ℝ) < 2 * n := by exact_mod_cast (show 0 < 2 * n by omega)
  have h2n1 : (0 : ℝ) < 2 * n + 1 := by positivity
  have hR : (0 : ℝ) < 2 * (n : ℝ) / (2 * n + 1) := by positivity
  have hsolve : (L - (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)
        / (2 * (n : ℝ) / (2 * n + 1)) ≤ fkc_f d s q n := by
    rw [div_le_iff₀ hR]
    linarith
  have halg : (L - (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)
        / (2 * (n : ℝ) / (2 * n + 1))
      = ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) := by
    field_simp
    ring
  rw [halg, hc] at hsolve
  exact hsolve


noncomputable def fkc_g (d : ℕ) (s q : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) / (2 * m + 1)) * fkc_f d s q m
    + (1 - 2 * (m : ℝ) / (2 * m + 1)) * (-Real.log (1 - fsc_logistic s))


theorem fkc_g_dyadic_tendsto (d : ℕ) (s q L : ℝ)
    (hL : Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L)) :
    Tendsto (fun j => fkc_g d s q (agl_K j)) atTop (nhds L) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hKtop : Tendsto (fun j => (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop atTop :=
    ecz_denom_tendsto_atTop.comp (by exact_mod_cast agl_K_tendsto_atTop)
  have h0 : Tendsto (fun j => (1 : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKtop
  have hR : Tendsto (fun j => 2 * ((agl_K j : ℕ) : ℝ)
      / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (nhds 1) := by
    have heq : ∀ j, 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)
        = 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) := by
      intro j; field_simp; ring
    rw [show (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
        = fun j => 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) from funext heq]
    simpa using h0.const_sub (1 : ℝ)
  have hprod : Tendsto (fun j =>
      (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
          * fkc_f d s q (agl_K j)
        + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c)
      atTop (nhds ((1 : ℝ) * L + (1 - 1) * c)) :=
    (hR.mul hL).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hR).mul
      (tendsto_const_nhds (x := c)))
  have heq : (fun j => fkc_g d s q (agl_K j))
      = fun j => (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
          * fkc_f d s q (agl_K j)
        + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c := by
    funext j; rw [fkc_g, hc]
  rw [heq]
  simpa using hprod


theorem fkc_upperSeq_tendsto (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n =>
        (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fkc_f d s q m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop
      (nhds (fkc_g d s q m)) := by
  have hr := ecz_bulkFraction_tendsto (d := d) hd m hm
  rw [fkc_g]
  exact (hr.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hr).mul tendsto_const_nhds)



theorem fkc_perEdgeDensityConverges (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_PerEdgeDensityConverges d s q := by
  classical
  obtain ⟨L, hL⟩ := fkc_dyadic_f_tendsto d hd s q hq
  set c := -Real.log (1 - fsc_logistic s) with hc
  refine ⟨L, ?_⟩
  have hgK := fkc_g_dyadic_tendsto d s q L hL
  have hlower : Tendsto
      (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n)) atTop (nhds L) := by
    have h1 := ecz_oddEven_ratio_tendsto.mul (tendsto_const_nhds (x := L))
    have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => c / (2 * (n : ℝ))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa using h1.sub h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hlower) (ε / 2) (by linarith)
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hgK) (ε / 2) (by linarith)
  have hgJ : fkc_g d s q (agl_K J) < L + ε / 2 := by
    have h := hJ J (le_refl _)
    rw [Real.dist_eq, abs_lt] at h
    linarith
  have hu := fkc_upperSeq_tendsto d hd s q (agl_K J) (agl_K_pos J)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hu) (ε / 2) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hle := fkc_f_lower d hd s q hq n hn1 L hL
    rw [← hc] at hle
    have hclose := hN1 n hnN1
    rw [Real.dist_eq, abs_lt] at hclose
    linarith
  · have hle := fkc_perEdge_vanHove d (agl_K J) n s q hq
      (ecz_box_edge_pos d hd hn1) (ecz_box_edge_pos d hd (agl_K_pos J))
    have hclose := hN2 n hnN2
    rw [Real.dist_eq, abs_lt] at hclose
    linarith

end StatMech.Walls
