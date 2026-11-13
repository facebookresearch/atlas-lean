/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopDefectEdge
import Code.FrontierA.KacWardArbitraryValenceClosure









open scoped BigOperators symmDiff
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.FrontierA

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem disorder_weight_term
    {F Q : Finset (Sym2 V)} {x : Real} (hx : x ≠ 0) :
    (x : Complex) ^ (F ∆ Q).card =
      (x : Complex) ^ Q.card *
        ∏ e ∈ F, if e ∈ Q then (x : Complex)⁻¹ else (x : Complex) := by
  have hxc : (x : Complex) ≠ 0 := by exact_mod_cast hx
  have hsymm : F ∆ Q = (F \ Q) ∪ (Q \ F) := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  have hdisj : Disjoint (F \ Q) (Q \ F) := by
    rw [Finset.disjoint_left]
    intro e heF heQ
    simp only [Finset.mem_sdiff] at heF heQ
    exact heF.2 heQ.1
  have hcardSymm : (F ∆ Q).card = (F \ Q).card + (Q \ F).card := by
    rw [hsymm, Finset.card_union_of_disjoint hdisj]
  have hcardQ : (Q \ F).card + (F ∩ Q).card = Q.card := by
    calc
      (Q \ F).card + (F ∩ Q).card =
          (Q \ F).card + (Q ∩ F).card := by rw [Finset.inter_comm F Q]
      _ = Q.card := Finset.card_sdiff_add_card_inter Q F
  rw [hcardSymm, pow_add]
  rw [show (∏ e ∈ F, if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)) =
      (x : Complex)⁻¹ ^ (F ∩ Q).card *
        (x : Complex) ^ (F \ Q).card by
    rw [Finset.prod_ite]
    rw [Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter F Q]
    simp only [Finset.prod_const]]
  rw [← hcardQ, pow_add, inv_pow]
  field_simp



theorem coe_ons_disorderX_eq_kwEvenPolynomial
    {Q : Finset (Sym2 V)} {x : Real} (hx : x ≠ 0) :
    (ons_disorderX G Q x : Complex) =
      (x : Complex) ^ Q.card *
        kwEvenPolynomial G
          (fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)) := by
  classical
  unfold ons_disorderX kwEvenPolynomial
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  exact disorder_weight_term (V := V) (F := F) (Q := Q) (x := x) hx



theorem coe_ons_sourceX_eq_kwEvenPolynomial_disorder
    {u v : V} {Q : Finset (Sym2 V)} {x : Real}
    (hQsub : Q ⊆ G.edgeFinset)
    (hQ : StatMech.Sharpness.HasOddBoundary Q {u, v}) (hx : x ≠ 0) :
    (ons_sourceX G {u, v} x : Complex) =
      (x : Complex) ^ Q.card *
        kwEvenPolynomial G
          (fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)) := by
  rw [ons_sourceX_eq_disorderX G hQsub hQ]
  exact coe_ons_disorderX_eq_kwEvenPolynomial G hx




theorem coe_ons_sourceX_sq_eq_defect_kwDet
    (embedding : KWStraightLineEmbedding G)
    {u v : V} {Q : Finset (Sym2 V)} {x : Real}
    (hQsub : Q ⊆ G.edgeFinset)
    (hQ : StatMech.Sharpness.HasOddBoundary Q {u, v}) (hx : x ≠ 0) :
    (ons_sourceX G {u, v} x : Complex) ^ 2 =
      (x : Complex) ^ (2 * Q.card) *
        (1 - kwGraphTransition G
          (fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex))
          embedding.turnPhase).det := by
  let weight : Sym2 V → Complex :=
    fun e => if e ∈ Q then (x : Complex)⁻¹ else (x : Complex)
  have hsource : (ons_sourceX G {u, v} x : Complex) =
      (x : Complex) ^ Q.card * kwEvenPolynomial G weight := by
    exact coe_ons_sourceX_eq_kwEvenPolynomial_disorder G hQsub hQ hx
  have hkw := kacWard_straightLine_arbitrary_adaptive G embedding weight
  rw [hsource, mul_pow, ← hkw]
  rw [← pow_mul]
  congr 2
  omega

end StatMech.Onsager
