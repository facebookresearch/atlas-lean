/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingTorusPlusBoundaryField
import Code.Ising.GinibreBoundaryMonomial









open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



def finiteCutConditionalSpinProd (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) : Real :=
  expJ (finiteCutGraph G S).edgeFinset (fun _ ↦ beta)
    (fun z ↦ beta * finiteCutBoundaryField G S outside z) (spinProd A)


def finiteCutPlusSpinProd (beta : Real) (S : Finset V)
    (A : Finset {v : V // v ∈ S}) : Real :=
  expJ (finiteCutGraph G S).edgeFinset (fun _ ↦ beta)
    (fun z ↦ beta * finiteCutPlusBoundaryField G S z) (spinProd A)



theorem finiteCutConditionalSpinProd_le_plus
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) :
    finiteCutConditionalSpinProd G beta S outside A ≤
      finiteCutPlusSpinProd G beta S A := by
  unfold finiteCutConditionalSpinProd finiteCutPlusSpinProd
  have hmono := ginibre_boundary_monomial_product_mono
    (finiteCutGraph G S).edgeFinset (fun _ ↦ beta)
    (fun z ↦ beta * finiteCutPlusBoundaryField G S z)
    (fun z ↦ beta * finiteCutBoundaryField G S outside z)
    (fun _ _ ↦ hbeta)
    (fun z ↦ by
      rw [abs_mul, abs_of_nonneg hbeta]
      exact mul_le_mul_of_nonneg_left
        (abs_finiteCutBoundaryField_le_plus G S outside z) hbeta)
    (spinProd A) (fun _ ↦ 1)
    (isSpinMonomial_spinProd A) IsSpinMonomial.const_one
  simpa only [mul_one] using hmono


def finiteCutConditionalSpinProdNumerator (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) : Real :=
  ∑ inside : ConfigSpace {v : V // v ∈ S},
    spinProd A inside *
      wJ (finiteCutGraph G S).edgeFinset (fun _ ↦ beta)
        (fun z ↦ beta * finiteCutBoundaryField G S outside z) inside

theorem finiteCutConditionalSpinProd_eq_div
    (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) :
    finiteCutConditionalSpinProd G beta S outside A =
      finiteCutConditionalSpinProdNumerator G beta S outside A /
        finiteCutConditionalZ G beta S outside := by
  rfl

@[simp] theorem spinProd_map_subtype_finiteCutMerge
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool)
    (A : Finset {v : V // v ∈ S}) :
    spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S))
        (finiteCutMerge S inside outside) = spinProd A inside := by
  unfold spinProd
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  exact spin_finiteCutMerge_inside S inside outside x



theorem sum_spinProd_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator
    (beta : Real) (S : Finset V) (A : Finset {v : V // v ∈ S}) :
    (∑ sigma : ConfigSpace V,
        spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) sigma *
          wJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) sigma) =
      ∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalSpinProdNumerator G beta S outside A := by
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun sigma ↦
      spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) sigma *
        wJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) sigma)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outside _
  unfold finiteCutConditionalSpinProdNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inside _
  change spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S))
      (finiteCutMerge S inside outside) *
        wJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
          (finiteCutMerge S inside outside) = _
  rw [spinProd_map_subtype_finiteCutMerge,
    wJ_finiteCutMerge_factor_fixedExterior]
  ring



theorem expJ_spinProd_le_finiteCutPlusSpinProd
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (A : Finset {v : V // v ∈ S}) :
    expJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
        (spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S))) ≤
      finiteCutPlusSpinProd G beta S A := by
  let P := finiteCutPlusSpinProd G beta S A
  have hcond (outside : {v : V // v ∉ S} → Bool) :
      finiteCutConditionalSpinProdNumerator G beta S outside A ≤
        P * finiteCutConditionalZ G beta S outside := by
    have hle := finiteCutConditionalSpinProd_le_plus
      G beta hbeta S outside A
    rw [finiteCutConditionalSpinProd_eq_div] at hle
    exact (div_le_iff₀ (ZJ_pos (finiteCutGraph G S).edgeFinset
      (fun _ ↦ beta)
      (fun z ↦ beta * finiteCutBoundaryField G S outside z))).mp hle
  unfold expJ
  rw [sum_spinProd_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator]
  change _ ≤ P
  apply (div_le_iff₀ (ZJ_pos G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0))).2
  calc
    (∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalSpinProdNumerator G beta S outside A) ≤
        ∑ outside : {v : V // v ∉ S} → Bool,
          finiteCutExteriorFactor G beta S outside *
            (P * finiteCutConditionalZ G beta S outside) := by
      exact Finset.sum_le_sum fun outside _ ↦
        mul_le_mul_of_nonneg_left (hcond outside)
          (finiteCutExteriorFactor_pos G beta S outside).le
    _ = P * ∑ outside : {v : V // v ∉ S} → Bool,
          finiteCutExteriorFactor G beta S outside *
            finiteCutConditionalZ G beta S outside := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outside _
      ring
    _ = P * ZJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) := by
      rw [ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ]



theorem expJ_spinProd_const_relabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ≃ W) (hadj : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
    (beta : Real) (fieldV : V → Real) (fieldW : W → Real)
    (hfield : ∀ x, fieldV x = fieldW (e x)) (A : Finset V) :
    expJ G.edgeFinset (fun _ ↦ beta) fieldV (spinProd A) =
      expJ H.edgeFinset (fun _ ↦ beta) fieldW
        (spinProd (A.map e.toEmbedding)) := by
  unfold expJ
  rw [ghsi_ZJ_const_relabel G H e hadj beta fieldV fieldW hfield]
  rw [← Equiv.sum_comp (isingCfgEquiv e)
    (fun omega ↦ spinProd A omega *
      wJ G.edgeFinset (fun _ ↦ beta) fieldV omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro omega _
  rw [StatMech.FrontierB.spinProd_isingCfgEquiv,
    ghsi_wJ_const_relabel G H e hadj beta fieldV fieldW hfield]



theorem finiteCutPlusSpinProd_relabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (S : Finset V) (T : Finset W)
    (e : {v : V // v ∈ S} ≃ {w : W // w ∈ T})
    (hadj : ∀ x y,
      (finiteCutGraph G S).Adj x y ↔
        (finiteCutGraph H T).Adj (e x) (e y))
    (hfield : ∀ x, finiteCutPlusBoundaryField G S x =
      finiteCutPlusBoundaryField H T (e x))
    (beta : Real) (A : Finset {v : V // v ∈ S}) :
    finiteCutPlusSpinProd G beta S A =
      finiteCutPlusSpinProd H beta T (A.map e.toEmbedding) := by
  unfold finiteCutPlusSpinProd
  apply expJ_spinProd_const_relabel
    (finiteCutGraph G S) (finiteCutGraph H T) e hadj beta
      (fun z ↦ beta * finiteCutPlusBoundaryField G S z)
      (fun z ↦ beta * finiteCutPlusBoundaryField H T z)
      (fun z ↦ congrArg (fun r : Real ↦ beta * r) (hfield z)) A



theorem expJ_spinProd_beta_field_eq_vertexFieldExpectation
    (beta : Real) (field : V → Real) (A : Finset V) :
    expJ G.edgeFinset (fun _ ↦ beta) (fun z ↦ beta * field z)
        (spinProd A) =
      vertexFieldExpectation G beta (unitEdgeCoupling G) field (spinProd A) := by
  unfold expJ vertexFieldExpectation
  have hweight (sigma : ConfigSpace V) :
      wJ G.edgeFinset (fun _ ↦ beta) (fun z ↦ beta * field z) sigma =
        vertexFieldWeight G beta (unitEdgeCoupling G) field sigma := by
    unfold wJ vertexFieldWeight
    congr 1
    have hedge : (∑ e ∈ G.edgeFinset,
        unitEdgeCoupling G e * bond sigma e) =
        ∑ e ∈ G.edgeFinset, bond sigma e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [unitEdgeCoupling_edgeFinset G he, one_mul]
    rw [hedge, mul_add]
    simp_rw [Finset.mul_sum]
    ring
  have hZ : ZJ G.edgeFinset (fun _ ↦ beta) (fun z ↦ beta * field z) =
      vertexFieldZ G beta (unitEdgeCoupling G) field := by
    unfold ZJ vertexFieldZ
    exact Finset.sum_congr rfl fun sigma _ ↦ hweight sigma
  rw [hZ]
  congr 1
  exact Finset.sum_congr rfl fun sigma _ ↦ congrArg (spinProd A sigma * ·)
    (hweight sigma)



theorem integral_gvPlus_spinProd_eq_vertexFieldExpectation
    {d : Nat} (S : Finset (Site d)) (beta : Real)
    (A : Finset {v : Site d // v ∈ S}) :
    (∫ omega,
        spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) omega
          ∂(gvPlusMeasure S beta 0)) =
      vertexFieldExpectation (graphS d S) beta
        (unitEdgeCoupling (graphS d S)) (plusBoundaryField S) (spinProd A) := by
  unfold gvPlusMeasure
  rw [integral_gvMeasure_eq_sum]
  unfold vertexFieldExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tau _
  rw [gvPlusProb_eq_vertexField]
  have hspin :
      spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S))
          (gvGlue (plusField d) S tau) = spinProd A tau := by
    unfold spinProd
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro x hx
    simp [spin, gvGlue, x.2]
  rw [hspin]
  ring



theorem finiteCutPlusSpinProd_torusImage_eq_gvPlus
    {d k R : Nat} (S : Finset (Site d))
    (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (beta : Real) (A : Finset {x // x ∈ S}) :
    finiteCutPlusSpinProd (isingTorusGraph d k) beta
        (isingTorusImageFinset k S)
        (A.map (isingTorusImageEquiv S hinj).toEmbedding) =
      ∫ omega,
        spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) omega
          ∂(gvPlusMeasure S beta 0) := by
  let e := isingTorusImageEquiv S hinj
  have hrel : finiteCutPlusSpinProd (isingTorusGraph d k) beta
      (isingTorusImageFinset k S) (A.map e.toEmbedding) =
      expJ (graphS d S).edgeFinset (fun _ ↦ beta)
        (fun z ↦ beta * plusBoundaryField S z) (spinProd A) := by
    unfold finiteCutPlusSpinProd
    have hadj' : ∀ u v : {z // z ∈ isingTorusImageFinset k S},
        (finiteCutGraph (isingTorusGraph d k)
          (isingTorusImageFinset k S)).Adj u v ↔
          (graphS d S).Adj (e.symm u) (e.symm v) := by
      intro u v
      change (isingTorusGraph d k).Adj u.1 v.1 ↔
        (graphS d S).Adj (e.symm u) (e.symm v)
      simpa only [e, Equiv.apply_symm_apply] using
        (isingTorusImageEquiv_adj S hS hside hinj
          (e.symm u) (e.symm v)).symm
    have hfield : ∀ u : {z // z ∈ isingTorusImageFinset k S},
        beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
            (isingTorusImageFinset k S) u =
          beta * plusBoundaryField S (e.symm u) := by
      intro u
      apply congrArg (fun r : Real ↦ beta * r)
      simpa only [e, Equiv.apply_symm_apply] using
        finiteCutPlusBoundaryField_isingTorusImageEquiv
          S hS hside hinj (e.symm u)
    have h := expJ_spinProd_const_relabel
      (finiteCutGraph (isingTorusGraph d k) (isingTorusImageFinset k S))
      (graphS d S) e.symm hadj' beta
      (fun z ↦ beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
        (isingTorusImageFinset k S) z)
      (fun z ↦ beta * plusBoundaryField S z) hfield
      (A.map e.toEmbedding)
    calc
      _ = expJ (graphS d S).edgeFinset (fun _ ↦ beta)
          (fun z ↦ beta * plusBoundaryField S z)
          (spinProd ((A.map e.toEmbedding).map e.symm.toEmbedding)) := h
      _ = _ := by
        congr 2
        rw [Finset.map_map]
        ext x
        simp
  rw [hrel, expJ_spinProd_beta_field_eq_vertexFieldExpectation]
  exact (integral_gvPlus_spinProd_eq_vertexFieldExpectation S beta A).symm



theorem freeSpinProd_le_isingTorusSpinProd
    {d k R : Nat} (S : Finset (Site d))
    (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (beta : Real) (hbeta : 0 ≤ beta)
    (A : Finset {x // x ∈ S}) :
    isingExpectation (graphS d S) beta 0 (spinProd A) ≤
      expJ (isingTorusGraph d k).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
        (spinProd ((A.map (isingTorusImageEquiv S
          (isingSiteToDyadicTorus_injectiveOn_finset S hS
            (lt_of_lt_of_le (by omega : 2 * R < 2 * (R + 1)) hside.le))).toEmbedding).map
              (Function.Embedding.subtype fun z ↦
                z ∈ isingTorusImageFinset k S))) := by
  let hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)) :=
    isingSiteToDyadicTorus_injectiveOn_finset S hS
      (lt_of_lt_of_le (by omega : 2 * R < 2 * (R + 1)) hside.le)
  let T := isingTorusImageFinset k S
  letI : Fintype {z : IsingDyadicTorus d k // z ∈ T} :=
    Finset.Subtype.fintype T
  let e := isingTorusImageEquiv S hinj
  have hadj : ∀ x y,
      (graphS d S).Adj x y ↔
        (finiteCutGraph (isingTorusGraph d k) T).Adj (e x) (e y) := by
    intro x y
    exact isingTorusImageEquiv_adj S hS hside hinj x y
  have hrel :
      expJ (graphS d S).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) (spinProd A) =
        expJ (finiteCutGraph (isingTorusGraph d k) T).edgeFinset
          (fun _ ↦ beta) (fun _ ↦ 0) (spinProd (A.map e.toEmbedding)) :=
    expJ_spinProd_const_relabel (graphS d S)
      (finiteCutGraph (isingTorusGraph d k) T) e hadj beta
      (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ rfl) A
  have hsub : StatMech.FrontierB.sym2FinsetImage
      (StatMech.FK.agl_sumEquiv fun z : IsingDyadicTorus d k ↦ z ∈ T)
      (StatMech.FrontierB.sym2FinsetInl
        (Y := {z : IsingDyadicTorus d k // z ∉ T})
        (finiteCutGraph (isingTorusGraph d k) T).edgeFinset) ⊆
      (isingTorusGraph d k).edgeFinset := by
    intro edge hedge
    unfold StatMech.FrontierB.sym2FinsetImage at hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨edge', hedge', rfl⟩ := hedge
    unfold StatMech.FrontierB.sym2FinsetInl at hedge'
    rw [Finset.mem_image] at hedge'
    obtain ⟨edge, hedge, rfl⟩ := hedge'
    induction edge using Sym2.inductionOn with
    | _ x y => simpa [finiteCutGraph, StatMech.FK.agl_sumEquiv,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
  have hinduce := StatMech.FrontierB.expJ_spinProd_induce_le
    (P := fun z : IsingDyadicTorus d k ↦ z ∈ T)
    (finiteCutGraph (isingTorusGraph d k) T).edgeFinset
    (isingTorusGraph d k).edgeFinset (fun _ ↦ beta)
    hsub (fun _ _ ↦ hbeta)
    (fun edge hedge ↦
      (isingTorusGraph d k).not_isDiag_of_mem_edgeFinset hedge)
    (A.map e.toEmbedding)
  have hfintype :
      (Subtype.fintype fun z : IsingDyadicTorus d k ↦ z ∈ T) =
        (inferInstance : Fintype {z : IsingDyadicTorus d k // z ∈ T}) :=
    Subsingleton.elim _ _
  rw [hfintype] at hinduce
  rw [isingExpectation_eq_expJ]
  simp only [mul_zero]
  rw [hrel]
  simpa only [T, e] using hinduce



theorem freeSpinProd_le_isingTorusSpinProd_le_gvPlus
    {d k R : Nat} (S : Finset (Site d))
    (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (beta : Real) (hbeta : 0 ≤ beta)
    (A : Finset {x // x ∈ S}) :
    isingExpectation (graphS d S) beta 0 (spinProd A) ≤
        expJ (isingTorusGraph d k).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
          (spinProd ((A.map (isingTorusImageEquiv S hinj).toEmbedding).map
            (Function.Embedding.subtype fun z ↦
              z ∈ isingTorusImageFinset k S))) ∧
      expJ (isingTorusGraph d k).edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
          (spinProd ((A.map (isingTorusImageEquiv S hinj).toEmbedding).map
            (Function.Embedding.subtype fun z ↦
              z ∈ isingTorusImageFinset k S))) ≤
        ∫ omega,
          spinProd (A.map (Function.Embedding.subtype fun v ↦ v ∈ S)) omega
            ∂(gvPlusMeasure S beta 0) := by
  constructor
  · have h := freeSpinProd_le_isingTorusSpinProd S hS hside beta hbeta A
    convert h using 1
  · have hupper := expJ_spinProd_le_finiteCutPlusSpinProd
      (isingTorusGraph d k) beta hbeta (isingTorusImageFinset k S)
      (A.map (isingTorusImageEquiv S hinj).toEmbedding)
    exact hupper.trans_eq
      (finiteCutPlusSpinProd_torusImage_eq_gvPlus
        S hS hside hinj beta A)

end

end StatMech.FrontierA
