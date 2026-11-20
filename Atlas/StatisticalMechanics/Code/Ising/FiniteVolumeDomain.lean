/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.FiniteVolumeSum
import Code.FK.AdditiveGluing
import Code.Sharpness.Simon

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem wJ_edgeFinset_const_eq_isingWeight (beta h : ℝ) (s : ConfigSpace V) :
    wJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) s =
      isingWeight G beta h s := by
  unfold wJ isingWeight hamiltonian
  congr 1
  rw [show (∑ e ∈ G.edgeFinset, beta * bond s e) =
      beta * ∑ e ∈ G.edgeFinset, bond s e by rw [Finset.mul_sum]]
  rw [show (∑ x : V, beta * h * spin s x) =
      (beta * h) * ∑ x : V, spin s x by rw [Finset.mul_sum]]
  ring



theorem ZJ_edgeFinset_const_eq_isingZ (beta h : ℝ) :
    ZJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) = isingZ G beta h := by
  unfold ZJ isingZ
  exact Finset.sum_congr rfl
    (fun s _ => wJ_edgeFinset_const_eq_isingWeight G beta h s)



theorem isingExpectation_spin_eq_expJ (beta h : ℝ) (z : V) :
    isingExpectation G beta h (fun s => spin s z) =
      expJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) (spinProd {z}) := by
  unfold isingExpectation isingProb expJ
  rw [ZJ_edgeFinset_const_eq_isingZ G]
  simp_rw [wJ_edgeFinset_const_eq_isingWeight G]
  apply (eq_div_iff (isingZ_ne_zero G beta h)).2
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun s _ => by
    field_simp [isingZ_ne_zero G beta h]
    simp [spinProd])



theorem isingExpectation_spinProd_eq_expJ (beta h : ℝ) (A : Finset V) :
    isingExpectation G beta h (spinProd A) =
      expJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) (spinProd A) := by
  unfold isingExpectation isingProb expJ
  rw [ZJ_edgeFinset_const_eq_isingZ G]
  simp_rw [wJ_edgeFinset_const_eq_isingWeight G]
  apply (eq_div_iff (isingZ_ne_zero G beta h)).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  field_simp [isingZ_ne_zero G beta h]



theorem isingExpectation_spin_mono_graph (H : SimpleGraph V) [DecidableRel H.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (hGH : G ≤ H) (z : V) :
    isingExpectation G beta h (fun s => spin s z) ≤
      isingExpectation H beta h (fun s => spin s z) := by
  rw [isingExpectation_spin_eq_expJ G, isingExpectation_spin_eq_expJ H]
  apply griffiths_mono_spin G.edgeFinset H.edgeFinset
    (fun _ => beta) (fun _ => beta * h)
  · exact SimpleGraph.edgeFinset_mono hGH
  · exact fun _ _ => hbeta
  · exact fun _ => mul_nonneg hbeta hh
  · exact fun e he _ => H.not_isDiag_of_mem_edgeFinset he

end Ising

namespace Sharpness

open Ising

variable {U : Type*} [Fintype U] [DecidableEq U]
variable (K : SimpleGraph U) [DecidableRel K.Adj]
variable (P : U → Prop) [DecidablePred P]





theorem isingExpectation_spin_induce_le (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (x : {u // P u}) :
    isingExpectation (K.comap (Subtype.val : {u // P u} → U)) beta h
        (fun s => spin s x) ≤
      isingExpectation K beta h (fun s => spin s x.1) := by
  let L : SimpleGraph {u // P u} := FK.agl_left K P
  let R : SimpleGraph {u // ¬ P u} := FK.agl_right K P
  let I : SimpleGraph {u // ¬ P u} := ⊥
  let S : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) := L ⊕g I
  let T : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) := FK.agl_glueGraph K P
  have hSI : S ≤ L ⊕g R := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
    · simpa [S, L, I, R, SimpleGraph.sum_adj] using hab
  have hST : S ≤ T :=
    le_trans hSI (show L ⊕g R ≤ T from (FK.agl_partitionCrossInterface K P).le)
  calc
    isingExpectation (K.comap (Subtype.val : {u // P u} → U)) beta h
        (fun s => spin s x) =
        isingExpectation S beta h (fun s => spin s (Sum.inl x)) := by
          symm
          exact isingExpectation_spin_sum_inl L I beta h x
    _ ≤ isingExpectation T beta h (fun s => spin s (Sum.inl x)) :=
      isingExpectation_spin_mono_graph S T beta h hbeta hh hST (Sum.inl x)
    _ = isingExpectation K beta h (fun s => spin s x.1) := by
      exact isingExpectation_spin_relabel T K (FK.agl_sumEquiv P)
        (FK.agl_glueGraph_adj K P) beta h (Sum.inl x)

end Sharpness

end StatMech
