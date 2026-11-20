/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Sharpness.MeanfieldIsingState
import Code.Ising.FiniteVolumeDomain
import Code.Ising.IsingTranslatedBoxClose
import Code.Lattice.UniqueInfiniteComponent
import Code.FrontierB.FiniteCurrentParity

open MeasureTheory Filter Topology
open scoped BigOperators symmDiff

namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isingExpectation_spinProd_mono_graph
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (hGH : G ≤ H)
    (A : Finset V) :
    isingExpectation G beta h (spinProd A) ≤
      isingExpectation H beta h (spinProd A) := by
  rw [isingExpectation_spinProd_eq_expJ G,
    isingExpectation_spinProd_eq_expJ H]
  apply griffiths_mono G.edgeFinset H.edgeFinset
    (fun _ ↦ beta) (fun _ ↦ beta * h)
  · exact SimpleGraph.edgeFinset_mono hGH
  · exact fun _ _ ↦ hbeta
  · exact fun _ ↦ mul_nonneg hbeta hh
  · exact fun e he _ ↦ H.not_isDiag_of_mem_edgeFinset he

theorem isingExpectation_spinProd_induce_le
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : V → Prop) [DecidablePred P]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (A : Finset {u // P u}) :
    isingExpectation (K.comap (Subtype.val : {u // P u} → V)) beta h
        (spinProd A) ≤
      isingExpectation K beta h
        (spinProd (A.map (Function.Embedding.subtype P))) := by
  let L : SimpleGraph {u // P u} := StatMech.FK.agl_left K P
  let R : SimpleGraph {u // ¬ P u} := StatMech.FK.agl_right K P
  let I : SimpleGraph {u // ¬ P u} := ⊥
  let S : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) := L ⊕g I
  let T : SimpleGraph ({u // P u} ⊕ {u // ¬ P u}) :=
    StatMech.FK.agl_glueGraph K P
  have hSI : S ≤ L ⊕g R := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · change L.Adj a b at hab ⊢
      exact hab
    · exfalso
      simpa only [S, SimpleGraph.sum_adj] using hab
    · exfalso
      simpa only [S, SimpleGraph.sum_adj] using hab
    · exfalso
      simpa only [S, I, SimpleGraph.sum_adj, SimpleGraph.bot_adj] using hab
  have hST : S ≤ T :=
    le_trans hSI (show L ⊕g R ≤ T from
      (StatMech.FK.agl_partitionCrossInterface K P).le)
  have hmap :
      (A.map ⟨Sum.inl, Sum.inl_injective⟩).map
          (StatMech.FK.agl_sumEquiv P).toEmbedding =
        A.map (Function.Embedding.subtype P) := by
    rw [Finset.map_map]
    apply congrArg (fun e : {u // P u} ↪ V ↦ A.map e)
    ext x
    rfl
  calc
    isingExpectation (K.comap (Subtype.val : {u // P u} → V)) beta h
        (spinProd A) =
        isingExpectation S beta h
          (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) := by
      symm
      exact isingExpectation_spinProd_sum_inl L I beta h A
    _ ≤ isingExpectation T beta h
          (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) :=
      isingExpectation_spinProd_mono_graph S T beta h hbeta hh hST _
    _ = isingExpectation K beta h
          (spinProd (A.map (Function.Embedding.subtype P))) := by
      rw [isingExpectation_spinProd_relabel T K
        (StatMech.FK.agl_sumEquiv P)
        (StatMech.FK.agl_glueGraph_adj K P) beta h
        (A.map ⟨Sum.inl, Sum.inl_injective⟩)]
      rw [hmap]

noncomputable def boxSpinSupport (d n : ℕ) (A : Finset (Site d)) :
    Finset (sctBox d n) :=
  Finset.univ.filter fun x ↦ x.1 ∈ A

theorem spinProd_glue_eq_boxSpinSupport
    (d n : ℕ) (A : Finset (Site d))
    (hA : ↑A ⊆ box d n) (tau : ConfigSpace (sctBox d n)) :
    spinProd A (glue (minusField d) tau) =
      spinProd (boxSpinSupport d n A) tau := by
  have hsupp : (boxSpinSupport d n A).image Subtype.val = A := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [boxSpinSupport] using hy
    · intro hx
      rw [Finset.mem_image]
      let y : sctBox d n := ⟨x, hA hx⟩
      exact ⟨y, by simp [boxSpinSupport, y, hx], rfl⟩
  unfold spinProd
  calc
    (∏ x ∈ A, spin (glue (minusField d) tau) x) =
        ∏ x ∈ (boxSpinSupport d n A).image Subtype.val,
          spin (glue (minusField d) tau) x := by rw [hsupp]
    _ = ∏ x ∈ boxSpinSupport d n A,
          spin (glue (minusField d) tau) x.1 := by
      rw [Finset.prod_image Subtype.val_injective.injOn]
    _ = ∏ x ∈ boxSpinSupport d n A, spin tau x := by
      apply Finset.prod_congr rfl
      intro x hx
      simp [spin, glue, x.2]

theorem integral_freeMeasure_spinProd
    (d n : ℕ) (beta h : ℝ) (A : Finset (Site d))
    (hA : ↑A ⊆ box d n) :
    ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d))) =
      isingExpectation (sctBoxGraph d n) beta h
        (spinProd (boxSpinSupport d n A)) := by
  change (∫ omega, spinProd A omega
    ∂(fvMeasure (minusField d) n (bondFinsetInternal d n) beta h)) = _
  rw [integral_fvMeasure_eq_sum]
  unfold isingExpectation
  apply Finset.sum_congr rfl
  intro tau htau
  rw [sct_fvProb_eq_isingProb]
  congr 1
  exact spinProd_glue_eq_boxSpinSupport d n A hA tau

theorem boxSpinSupport_map_inclusion
    (d : ℕ) {n m : ℕ} (hnm : n ≤ m) (A : Finset (Site d))
    (hA : ↑A ⊆ box d n) :
    ((boxSpinSupport d n A).map
        (sctBoxInclusionEquiv d hnm).toEmbedding).map
        (Function.Embedding.subtype (sctBoxInLarger d n m)) =
      boxSpinSupport d m A := by
  ext z
  simp only [Finset.mem_map, boxSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
  · intro hz
    let x : sctBox d n := ⟨z.1, hA hz⟩
    let w : {z : sctBox d m // sctBoxInLarger d n m z} :=
      sctBoxInclusionEquiv d hnm x
    refine ⟨w, ⟨x, ?_, rfl⟩, ?_⟩
    · exact hz
    · apply Subtype.ext
      rfl

theorem isingExpectation_boxSpinSupport_mono
    (d : ℕ) {n m : ℕ} (hnm : n ≤ m) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : Finset (Site d)) (hA : ↑A ⊆ box d n) :
    isingExpectation (sctBoxGraph d n) beta 0
        (spinProd (boxSpinSupport d n A)) ≤
      isingExpectation (sctBoxGraph d m) beta 0
        (spinProd (boxSpinSupport d m A)) := by
  let e := sctBoxInclusionEquiv d hnm
  calc
    isingExpectation (sctBoxGraph d n) beta 0
        (spinProd (boxSpinSupport d n A)) =
        isingExpectation
          ((sctBoxGraph d m).comap
            (Subtype.val :
              {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)) beta 0
          (spinProd ((boxSpinSupport d n A).map e.toEmbedding)) := by
      exact isingExpectation_spinProd_relabel (sctBoxGraph d n)
        ((sctBoxGraph d m).comap
          (Subtype.val :
            {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m))
        e (sctBoxInclusionEquiv_adj d hnm) beta 0 (boxSpinSupport d n A)
    _ ≤ isingExpectation (sctBoxGraph d m) beta 0
          (spinProd (((boxSpinSupport d n A).map e.toEmbedding).map
            (Function.Embedding.subtype (sctBoxInLarger d n m)))) :=
      isingExpectation_spinProd_induce_le (sctBoxGraph d m)
        (sctBoxInLarger d n m) beta 0 hbeta (le_refl 0) _
    _ = isingExpectation (sctBoxGraph d m) beta 0
          (spinProd (boxSpinSupport d m A)) := by
      rw [boxSpinSupport_map_inclusion d hnm A hA]

theorem isingExpectation_spinProd_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta h : ℝ) (A : Finset V) :
    isingExpectation G beta h (spinProd A) ≤ 1 := by
  unfold isingExpectation
  calc
    (∑ s : ConfigSpace V, isingProb G beta h s * spinProd A s) ≤
        ∑ s : ConfigSpace V, isingProb G beta h s * 1 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (spinProd_le_one A s)
        (isingProb_nonneg G beta h s)
    _ = 1 := by simp [isingProb_sum_eq_one]

theorem continuous_spinProd {d : ℕ} (A : Finset (Site d)) :
    Continuous (spinProd A : ConfigSpace (Site d) → ℝ) := by
  classical
  induction A using Finset.induction with
  | empty => simpa [spinProd] using
      (continuous_const : Continuous (fun _ : ConfigSpace (Site d) => (1 : ℝ)))
  | @insert x A hx ih =>
      rw [show spinProd (insert x A) =
          fun omega => spin omega x * spinProd A omega by
        funext omega
        simp [spinProd, hx]]
      exact (continuous_spin_apply x).mul ih

noncomputable def spinProdBCF (d : ℕ) (A : Finset (Site d)) :
    BoundedContinuousFunction (ConfigSpace (Site d)) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨spinProd A, continuous_spinProd A⟩

@[simp] theorem spinProdBCF_apply (d : ℕ) (A : Finset (Site d))
    (omega : ConfigSpace (Site d)) :
    spinProdBCF d A omega = spinProd A omega := rfl



theorem integral_freeMeasure_spinProd_tendsto_freeState
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  let a : ℕ → ℝ := fun n =>
    ∫ omega, spinProd A omega
      ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  have hA_add (k : ℕ) : ↑A ⊆ box d (k + N) :=
    hAN.trans (box_mono d (Nat.le_add_left N k))
  have htail_mono : Monotone (fun k => a (k + N)) := by
    intro k l hkl
    change a (k + N) ≤ a (l + N)
    rw [show a (k + N) = isingExpectation (sctBoxGraph d (k + N)) beta 0
        (spinProd (boxSpinSupport d (k + N) A)) by
      exact integral_freeMeasure_spinProd d (k + N) beta 0 A (hA_add k)]
    rw [show a (l + N) = isingExpectation (sctBoxGraph d (l + N)) beta 0
        (spinProd (boxSpinSupport d (l + N) A)) by
      exact integral_freeMeasure_spinProd d (l + N) beta 0 A (hA_add l)]
    exact isingExpectation_boxSpinSupport_mono d (Nat.add_le_add_right hkl N)
      beta hbeta A (hA_add k)
  have htail_bdd : BddAbove (Set.range (fun k => a (k + N))) := by
    refine ⟨1, ?_⟩
    rintro y ⟨k, rfl⟩
    change a (k + N) ≤ 1
    rw [show a (k + N) = isingExpectation (sctBoxGraph d (k + N)) beta 0
        (spinProd (boxSpinSupport d (k + N) A)) by
      exact integral_freeMeasure_spinProd d (k + N) beta 0 A (hA_add k)]
    exact isingExpectation_spinProd_le_one (sctBoxGraph d (k + N)) beta 0 _
  let L : ℝ := ⨆ k, a (k + N)
  have htail : Tendsto (fun k => a (k + N)) atTop (nhds L) := by
    simpa only [L] using tendsto_atTop_ciSup htail_mono htail_bdd
  have hfull : Tendsto a atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat N).1 htail
  obtain ⟨phi, hphi, hweak⟩ := freeState_isInfiniteVolumeState d beta 0
  have hsub_free := hweak.tendsto_integral (spinProdBCF d A)
  have hsub_L : Tendsto (fun k => a (phi k)) atTop (nhds L) :=
    hfull.comp hphi.tendsto_atTop
  have hsub_free' : Tendsto (fun k => a (phi k)) atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
    simpa only [a, Function.comp_apply, spinProdBCF_apply] using hsub_free
  have hL : L = ∫ omega, spinProd A omega
      ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
    tendsto_nhds_unique hsub_L hsub_free'
  simpa only [a, hL] using hfull

noncomputable def edgeBoundary {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset V :=
  Finset.fold (fun A B : Finset V => A ∆ B) ∅ Sym2.toFinset F

theorem prod_bond_eq_spinProd_edgeBoundary
    {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (s : ConfigSpace V) :
    (∏ e ∈ F, bond s e) = spinProd (edgeBoundary F) s := by
  classical
  induction F using Finset.induction with
  | empty => simp [edgeBoundary, spinProd]
  | @insert e F he ih =>
      have hediag : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F)
      have hF' : ∀ f ∈ F, ¬ f.IsDiag := fun f hf => hF f (Finset.mem_insert_of_mem hf)
      have hebond : bond s e = spinProd e.toFinset s := by
        induction e using Sym2.inductionOn with
        | _ x y =>
            have hxy : x ≠ y := by simpa [Sym2.IsDiag] using hediag
            rw [bond_mk, Sym2.toFinset_mk_eq, spinProd, Finset.prod_pair hxy]
      rw [Finset.prod_insert he, edgeBoundary, Finset.fold_insert he,
        hebond, ih hF', ← spinProd_mul_self]
      rfl

noncomputable def edgeExpansionCoeff {V : Type*} [DecidableEq V]
    (beta : ℝ) (F T : Finset (Sym2 V)) : ℝ :=
  (∏ _e ∈ T, Real.cosh (-beta)) *
    ∏ _e ∈ F \ T, Real.sinh (-beta)

theorem exp_neg_edgeSpinSum_eq_spinProd_sum
    {V : Type*} [DecidableEq V]
    (beta : ℝ) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) (s : ConfigSpace V) :
    Real.exp (-beta * edgeSpinSum F s) =
      ∑ T ∈ F.powerset,
        edgeExpansionCoeff beta F T * spinProd (edgeBoundary (F \ T)) s := by
  unfold edgeSpinSum
  rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [exp_mul_pm (-beta) (bond s _) (bond_eq_pm s _)]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold edgeExpansionCoeff
  rw [Finset.prod_mul_distrib]
  rw [prod_bond_eq_spinProd_edgeBoundary (F \ T)]
  · ring
  · intro e he
    exact hF e (Finset.mem_sdiff.mp he).1

theorem integral_spinProd_sum_tendsto_freeState
    {I : Type*} (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (K : Finset I) (c : I → ℝ) (support : I → Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  classical
  have hterm (i : I) (hi : i ∈ K) :
      Tendsto
        (fun n => c i * ∫ omega, spinProd (support i) omega
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
        atTop
        (nhds (c i * ∫ omega, spinProd (support i) omega
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) :=
    (integral_freeMeasure_spinProd_tendsto_freeState
      d beta hbeta (support i)).const_mul (c i)
  have hsum := tendsto_finsetSum K hterm
  have hint (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu] :
      (∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega ∂mu) =
        ∑ i ∈ K, c i * ∫ omega, spinProd (support i) omega ∂mu := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
    · intro i hi
      exact ((spinProdBCF d (support i)).integrable mu).const_mul (c i)
  simpa only [hint] using hsum



theorem integral_exp_neg_edgeSpinSum_tendsto_freeState
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    Tendsto
      (fun n => ∫ s, Real.exp (-beta * edgeSpinSum F s)
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ s, Real.exp (-beta * edgeSpinSum F s)
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hpoly := integral_spinProd_sum_tendsto_freeState d beta hbeta
    F.powerset (edgeExpansionCoeff beta F)
    (fun T => edgeBoundary (F \ T))
  simpa only [exp_neg_edgeSpinSum_eq_spinProd_sum beta F hF] using hpoly

noncomputable def plusSpinExpansionCoeff {d : ℕ}
    (A T : Finset (Site d)) : ℝ :=
  (2 : ℝ) ^ T.card * (-1 : ℝ) ^ (A \ T).card

theorem spinProd_eq_plusSpinExpansion {d : ℕ}
    (A : Finset (Site d)) (omega : ConfigSpace (Site d)) :
    spinProd A omega =
      ∑ T ∈ A.powerset,
        plusSpinExpansionCoeff A T * iti_monomialBcf T omega := by
  unfold spinProd
  have hspin (x : Site d) :
      spin omega x = 2 * pstc_coordCM x omega + (-1 : ℝ) := by
    simp only [pstc_coordCM_apply]
    by_cases hx : omega x
    · simp [spin, hx]
      norm_num
    · simp [spin, hx]
  simp_rw [hspin]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold plusSpinExpansionCoeff
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
  have hmono : (∏ x ∈ T, pstc_coordCM x omega) =
      iti_monomialBcf T omega := by
    change (∏ x ∈ T, pstc_coordCM x omega) = iti_monomialCM T omega
    rw [iti_monomialCM, ContinuousMap.prod_apply]
  rw [hmono]
  ring

theorem integral_plusMeasure_spinProd_full_tendsto
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : Finset (Site d)) :
    Tendsto
      (fun n => ∫ omega, spinProd A omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  have hterm (T : Finset (Site d)) (hT : T ∈ A.powerset) :
      Tendsto
        (fun n => plusSpinExpansionCoeff A T *
          (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
            (StatMech.FK.fmu_multiOpen T))
        atTop
        (nhds (plusSpinExpansionCoeff A T *
          (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
            (StatMech.FK.fmu_multiOpen T))) :=
    (itb_plus_multiOpen_full_tendsto hbeta le_rfl T hphi hconv).const_mul _
  have hsum := tendsto_finset_sum A.powerset hterm
  have hint (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu] :
      (∫ omega, spinProd A omega ∂mu) =
        ∑ T ∈ A.powerset, plusSpinExpansionCoeff A T *
          mu.real (StatMech.FK.fmu_multiOpen T) := by
    simp_rw [spinProd_eq_plusSpinExpansion A]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro T hT
      rw [integral_const_mul, iti_integral_monomialBcf]
    · intro T hT
      exact ((iti_monomialBcf T).integrable mu).const_mul _
  simpa only [hint] using hsum

theorem integral_plusMeasure_exp_neg_edgeSpinSum_full_tendsto
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    Tendsto
      (fun n => ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  have hterm (T : Finset (Sym2 (Site d))) (hT : T ∈ F.powerset) :
      Tendsto
        (fun n => edgeExpansionCoeff beta F T *
          ∫ omega, spinProd (edgeBoundary (F \ T)) omega
            ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
        atTop
        (nhds (edgeExpansionCoeff beta F T *
          ∫ omega, spinProd (edgeBoundary (F \ T)) omega
            ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) :=
    (integral_plusMeasure_spinProd_full_tendsto d beta hbeta _).const_mul _
  have hsum := tendsto_finset_sum F.powerset hterm
  have hint (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu] :
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu) =
        ∑ T ∈ F.powerset, edgeExpansionCoeff beta F T *
          ∫ omega, spinProd (edgeBoundary (F \ T)) omega ∂mu := by
    simp_rw [exp_neg_edgeSpinSum_eq_spinProd_sum beta F hF]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro T hT
      rw [integral_const_mul]
    · intro T hT
      exact ((spinProdBCF d (edgeBoundary (F \ T))).integrable mu).const_mul _
  simpa only [hint] using hsum

end StatMech.FrontierB
