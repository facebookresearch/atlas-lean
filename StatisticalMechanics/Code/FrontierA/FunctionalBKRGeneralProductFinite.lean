/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.FunctionalBKRGeneralProductTransport

open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]



section FiniteProductFamily

variable [∀ e, Fintype (S e)]

structure BernoulliBlockData {T : Type*} [Fintype T] (w : T → ℝ) where
  n : ℕ
  phi : Fin n → Bool → ℝ
  decode : (Fin n → Bool) → T
  phi_nonneg : ∀ i b, 0 ≤ phi i b
  phi_sum_one : ∀ i, phi i false + phi i true = 1
  decode_surjective : Function.Surjective decode
  expectation : ∀ h : T → ℝ,
    productExpectation phi (h ∘ decode) = ∑ t, w t * h t

noncomputable irreducible_def bernoulliBlockDataOfWeights {T : Type*} [Fintype T]
    (w : T → ℝ) (hw0 : ∀ t, 0 ≤ w t) (hw1 : (∑ t, w t) = 1) :
    BernoulliBlockData w :=
  Classical.choice <| by
    rcases exists_bernoulliBlockRepresentation w hw0 hw1 with
      ⟨n, phi, decode, hphi0, hphi1, hdecode, hexpect⟩
    exact ⟨
      { n := n
        phi := phi
        decode := decode
        phi_nonneg := hphi0
        phi_sum_one := hphi1
        decode_surjective := hdecode
        expectation := hexpect }⟩

set_option maxHeartbeats 50000 in
theorem functionalFamilyBKR_finiteProduct_primal_of_blocks
    (w : ∀ e, S e → ℝ)
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K))
    (n : E → ℕ) (Phi : Sigma (fun e => Fin (n e)) → Bool → ℝ)
    (decode : ∀ e, (Fin (n e) → Bool) → S e)
    (hPhi0 : ∀ z b, 0 ≤ Phi z b)
    (hPhi1 : ∀ z, Phi z false + Phi z true = 1)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (hexpect : ∀ e (h : S e → ℝ),
      productExpectation (fun d b => Phi ⟨e, d⟩ b) (h ∘ decode e) =
        ∑ s, w e s * h s) :
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤
        finitePiExpectation w (piFunctionalFamilyMax F) *
        finitePiExpectation w (piFunctionalFamilyMax G) := by
  classical
  have hpush (H : (∀ e, S e) → ℝ) :
      productExpectation Phi (H ∘ decodeDependentBlockConfig decode) =
        finitePiExpectation w H :=
    productExpectation_decodeDependent_eq_finitePiExpectation
      Phi decode w hexpect H
  have hbkr : productExpectation Phi (fun omega =>
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
      productExpectation Phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation Phi (fun omega =>
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) :=
    functionalFamilyBKR_dependentBlocks
      Phi hPhi0 hPhi1 decode hdecode F G hF0 hG0 hF hG
  calc
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) =
        productExpectation Phi
          (piFunctionalFamilyDisjointMax F G ∘
            decodeDependentBlockConfig decode) := (hpush _).symm
    _ ≤ productExpectation Phi
          (piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode) *
        productExpectation Phi
          (piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode) := hbkr
    _ = finitePiExpectation w (piFunctionalFamilyMax F) *
        finitePiExpectation w (piFunctionalFamilyMax G) := by
      rw [hpush, hpush]

set_option maxHeartbeats 100000 in
theorem functionalFamilyBKR_finiteProduct_primal_of_data
    (w : ∀ e, S e → ℝ)
    (hw0 : ∀ e s, 0 ≤ w e s) (hw1 : ∀ e, (∑ s, w e s) = 1)
    (rep : ∀ e, BernoulliBlockData (w e))
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤
      finitePiExpectation w (piFunctionalFamilyMax F) *
        finitePiExpectation w (piFunctionalFamilyMax G) := by
  classical
  let n : E → ℕ := fun e => (rep e).n
  letI finBlockFintype : ∀ e, Fintype (Fin (n e)) := fun e => Fin.fintype (n e)
  let phi : ∀ e, Fin (n e) → Bool → ℝ := fun e => (rep e).phi
  let decode : ∀ e, (Fin (n e) → Bool) → S e := fun e => (rep e).decode
  let Phi : Sigma (fun e => Fin (n e)) → Bool → ℝ :=
    fun z b => phi z.1 z.2 b
  have hPhi0 : ∀ z b, 0 ≤ Phi z b := fun z b => (rep z.1).phi_nonneg z.2 b
  have hPhi1 : ∀ z, Phi z false + Phi z true = 1 :=
    fun z => (rep z.1).phi_sum_one z.2
  have hdecode : ∀ e, Function.Surjective (decode e) :=
    fun e => (rep e).decode_surjective
  have hexpect : ∀ e (h : S e → ℝ),
      productExpectation (fun d b => Phi ⟨e, d⟩ b) (h ∘ decode e) =
        ∑ s, w e s * h s := fun e => (rep e).expectation
  have hpush (H : (∀ e, S e) → ℝ) :
      productExpectation Phi (H ∘ decodeDependentBlockConfig decode) =
        finitePiExpectation w H :=
    productExpectation_decodeDependent_eq_finitePiExpectation
      Phi decode w hexpect H
  have hbkr : productExpectation Phi (fun omega =>
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
      productExpectation Phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation Phi (fun omega =>
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) :=
    functionalFamilyBKR_dependentBlocks
      Phi hPhi0 hPhi1 decode hdecode F G hF0 hG0 hF hG
  calc
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) =
        productExpectation Phi
          (piFunctionalFamilyDisjointMax F G ∘
            decodeDependentBlockConfig decode) := (hpush _).symm
    _ ≤ productExpectation Phi
          (piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode) *
        productExpectation Phi
          (piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode) := hbkr
    _ = finitePiExpectation w (piFunctionalFamilyMax F) *
        finitePiExpectation w (piFunctionalFamilyMax G) := by
      rw [hpush, hpush]

theorem functionalFamilyBKR_finiteProduct_primal
    (w : ∀ e, S e → ℝ)
    (hw0 : ∀ e s, 0 ≤ w e s) (hw1 : ∀ e, (∑ s, w e s) = 1)
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤
      finitePiExpectation w (piFunctionalFamilyMax F) *
        finitePiExpectation w (piFunctionalFamilyMax G) :=
  functionalFamilyBKR_finiteProduct_primal_of_data w hw0 hw1
    (fun e => bernoulliBlockDataOfWeights (w e) (hw0 e) (hw1 e))
    F G hF0 hG0 hF hG

set_option maxHeartbeats 100000 in
theorem functionalFamilyBKR_finiteProduct_and_dual
    (w : ∀ e, S e → ℝ)
    (hw0 : ∀ e s, 0 ≤ w e s) (hw1 : ∀ e, (∑ s, w e s) = 1)
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤
        finitePiExpectation w (piFunctionalFamilyMax F) *
          finitePiExpectation w (piFunctionalFamilyMax G) ∧
      finitePiDualExpectation w (fun pair =>
          piFunctionalFamilyDisjointMaxAt F G pair.1 pair.2) ≤
        finitePiExpectation w (fun x =>
          piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) := by
  classical
  let rep : ∀ e, BernoulliBlockData (w e) := fun e =>
    bernoulliBlockDataOfWeights (w e) (hw0 e) (hw1 e)
  let n : E → ℕ := fun e => (rep e).n
  letI finBlockFintype : ∀ e, Fintype (Fin (n e)) := fun e => Fin.fintype (n e)
  let phi : ∀ e, Fin (n e) → Bool → ℝ := fun e => (rep e).phi
  let decode : ∀ e, (Fin (n e) → Bool) → S e := fun e => (rep e).decode
  let Phi : Sigma (fun e => Fin (n e)) → Bool → ℝ :=
    fun z b => phi z.1 z.2 b
  have hPhi0 : ∀ z b, 0 ≤ Phi z b := fun z b => (rep z.1).phi_nonneg z.2 b
  have hPhi1 : ∀ z, Phi z false + Phi z true = 1 :=
    fun z => (rep z.1).phi_sum_one z.2
  have hdecode : ∀ e, Function.Surjective (decode e) :=
    fun e => (rep e).decode_surjective
  have hexpect : ∀ e (h : S e → ℝ),
      productExpectation (fun d b => Phi ⟨e, d⟩ b) (h ∘ decode e) =
        ∑ s, w e s * h s := fun e => (rep e).expectation
  have hpush (H : (∀ e, S e) → ℝ) :
      productExpectation Phi (H ∘ decodeDependentBlockConfig decode) =
        finitePiExpectation w H :=
    productExpectation_decodeDependent_eq_finitePiExpectation
      Phi decode w hexpect H
  have hpushDual (H : ((∀ e, S e) × (∀ e, S e)) → ℝ) :
      dualProductExpectation Phi (fun pair =>
        H (decodeDependentBlockConfig decode pair.1,
          decodeDependentBlockConfig decode pair.2)) =
        finitePiDualExpectation w H :=
    dualProductExpectation_decodeDependent_eq_finitePiDualExpectation
      Phi decode w hexpect H
  constructor
  · have hbkr : productExpectation Phi (fun omega ↦
        piFunctionalFamilyDisjointMax F G
          (decodeDependentBlockConfig decode omega)) ≤
      productExpectation Phi (fun omega ↦
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) *
        productExpectation Phi (fun omega ↦
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) :=
      functionalFamilyBKR_dependentBlocks
        Phi hPhi0 hPhi1 decode hdecode F G hF0 hG0 hF hG
    calc
      finitePiExpectation w (piFunctionalFamilyDisjointMax F G) =
          productExpectation Phi
            (piFunctionalFamilyDisjointMax F G ∘
              decodeDependentBlockConfig decode) :=
        (hpush _).symm
      _ ≤ productExpectation Phi
            (piFunctionalFamilyMax F ∘ decodeDependentBlockConfig decode) *
          productExpectation Phi
            (piFunctionalFamilyMax G ∘ decodeDependentBlockConfig decode) := hbkr
      _ = finitePiExpectation w (piFunctionalFamilyMax F) *
          finitePiExpectation w (piFunctionalFamilyMax G) := by
        rw [hpush, hpush]
  · have hbkr : dualProductExpectation Phi (fun pair ↦
        piFunctionalFamilyDisjointMaxAt F G
          (decodeDependentBlockConfig decode pair.1)
          (decodeDependentBlockConfig decode pair.2)) ≤
      productExpectation Phi (fun omega ↦
        piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) *
          piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) :=
      dualFunctionalFamilyBKR_dependentBlocks
        Phi hPhi0 hPhi1 decode hdecode F G hF0 hG0 hF hG
    calc
      finitePiDualExpectation w (fun pair =>
          piFunctionalFamilyDisjointMaxAt F G pair.1 pair.2) =
          dualProductExpectation Phi (fun pair =>
            piFunctionalFamilyDisjointMaxAt F G
              (decodeDependentBlockConfig decode pair.1)
              (decodeDependentBlockConfig decode pair.2)) :=
        (hpushDual _).symm
      _ ≤ productExpectation Phi (fun omega =>
          piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) *
            piFunctionalFamilyMax G
              (decodeDependentBlockConfig decode omega)) := hbkr
      _ = finitePiExpectation w (fun x =>
          piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) :=
        hpush (fun x => piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)

theorem functionalFamilyBKR_finiteProduct
    (w : ∀ e, S e → ℝ)
    (hw0 : ∀ e s, 0 ≤ w e s) (hw1 : ∀ e, (∑ s, w e s) = 1)
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤
      finitePiExpectation w (piFunctionalFamilyMax F) *
        finitePiExpectation w (piFunctionalFamilyMax G) :=
  (functionalFamilyBKR_finiteProduct_and_dual w hw0 hw1 F G hF0 hG0 hF hG).1

theorem dualFunctionalFamilyBKR_finiteProduct
    (w : ∀ e, S e → ℝ)
    (hw0 : ∀ e s, 0 ≤ w e s) (hw1 : ∀ e, (∑ s, w e s) = 1)
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    finitePiDualExpectation w (fun pair =>
        piFunctionalFamilyDisjointMaxAt F G pair.1 pair.2) ≤
      finitePiExpectation w (fun x =>
        piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) :=
  (functionalFamilyBKR_finiteProduct_and_dual w hw0 hw1 F G hF0 hG0 hF hG).2

end FiniteProductFamily



section FiniteProductIntegral

variable [∀ e, Fintype (S e)] [∀ e, MeasurableSingletonClass (S e)]

theorem finitePiExpectation_nonneg
    (w : ∀ e, S e → ℝ) (hw0 : ∀ e s, 0 ≤ w e s)
    (H : (∀ e, S e) → ℝ) (hH0 : ∀ x, 0 ≤ H x) :
    0 ≤ finitePiExpectation w H := by
  unfold finitePiExpectation
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (Finset.prod_nonneg fun e _ => hw0 e (x e)) (hH0 x)

theorem lintegral_finitePi_eq_ofReal_expectation
    (nu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (nu e)]
    (H : (∀ e, S e) → ℝ) (hH0 : ∀ x, 0 ≤ H x) :
    (∫⁻ x, ENNReal.ofReal (H x) ∂Measure.pi nu) =
      ENNReal.ofReal
        (finitePiExpectation (fun e s => (nu e {s}).toReal) H) := by
  classical
  rw [lintegral_fintype]
  unfold finitePiExpectation
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro x _
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun e _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_prod_of_nonneg (fun e _ => ENNReal.toReal_nonneg)]
    simp_rw [ENNReal.ofReal_toReal (measure_ne_top (nu _) _)]
    have hsingleton : ({x} : Set (∀ e, S e)) =
        Set.pi Set.univ (fun e => ({x e} : Set (S e))) := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
      exact ⟨fun h e => congrFun h e, fun h => funext h⟩
    rw [hsingleton, Measure.pi_pi]
    ring
  · intro x _
    exact mul_nonneg (Finset.prod_nonneg fun e _ => ENNReal.toReal_nonneg) (hH0 x)

theorem lintegral_finitePiDual_eq_ofReal_expectation
    (nu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (nu e)]
    (H : ((∀ e, S e) × (∀ e, S e)) → ℝ)
    (hH0 : ∀ p, 0 ≤ H p) :
    (∫⁻ p, ENNReal.ofReal (H p)
        ∂(Measure.pi nu).prod (Measure.pi nu)) =
      ENNReal.ofReal
        (finitePiDualExpectation (fun e s => (nu e {s}).toReal) H) := by
  let w : ∀ e, S e → ℝ := fun e s => (nu e {s}).toReal
  have hw0 : ∀ e s, 0 ≤ w e s := fun _ _ => ENNReal.toReal_nonneg
  rw [lintegral_prod _ (measurable_of_finite _).aemeasurable]
  have hinner (x : ∀ e, S e) :
      (∫⁻ y, ENNReal.ofReal (H (x, y)) ∂Measure.pi nu) =
        ENNReal.ofReal (finitePiExpectation w (fun y => H (x, y))) :=
    lintegral_finitePi_eq_ofReal_expectation nu _ (fun y => hH0 (x, y))
  simp_rw [hinner]
  rw [lintegral_finitePi_eq_ofReal_expectation nu]
  · rfl
  · intro x
    exact finitePiExpectation_nonneg w hw0 _ (fun y => hH0 (x, y))

end FiniteProductIntegral



section FiniteFactor

variable {T : E → Type*} [∀ e, MeasurableSpace (T e)]
  [∀ e, Fintype (T e)] [∀ e, MeasurableSingletonClass (T e)]

theorem functionalFamilyBKR_finiteFactor_and_dual
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (q : ∀ e, S e → T e) (hq : ∀ e, Measurable (q e))
    (F G : Set E → (∀ e, T e) → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    (∫⁻ x, ENNReal.ofReal
        (piFunctionalFamilyDisjointMax F G (fun e => q e (x e)))
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F (fun e => q e (x e))) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax G (fun e => q e (x e))) ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G
            (fun e => q e (p.1 e)) (fun e => q e (p.2 e)))
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F (fun e => q e (x e)) *
            piFunctionalFamilyMax G (fun e => q e (x e)))
          ∂Measure.pi mu := by
  classical
  let nu : ∀ e, Measure (T e) := fun e => (mu e).map (q e)
  letI hnu : ∀ e, IsProbabilityMeasure (nu e) := fun e =>
    ⟨by
      rw [Measure.map_apply (hq e) MeasurableSet.univ]
      simp⟩
  let w : ∀ e, T e → ℝ := fun e t => (nu e {t}).toReal
  have hw0 : ∀ e t, 0 ≤ w e t := fun _ _ => ENNReal.toReal_nonneg
  have hw1 : ∀ e, (∑ t, w e t) = 1 := by
    intro e
    change ∑ t, (nu e).real {t} = 1
    simpa using
      (sum_measureReal_singleton (μ := nu e) (Finset.univ : Finset (T e)))
  have hfinite := functionalFamilyBKR_finiteProduct_and_dual
    w hw0 hw1 F G hF0 hG0 hF hG
  have hmaxF0 : ∀ x, 0 ≤ piFunctionalFamilyMax F x :=
    piFunctionalFamilyMax_nonneg F hF0
  have hmaxG0 : ∀ x, 0 ≤ piFunctionalFamilyMax G x :=
    piFunctionalFamilyMax_nonneg G hG0
  have hdisjoint0 : ∀ x, 0 ≤ piFunctionalFamilyDisjointMax F G x := by
    intro x
    unfold piFunctionalFamilyDisjointMax piFunctionalFamilyDisjointMaxAt
    have hempty : ((∅, ∅) : Set E × Set E) ∈ disjointCoordinatePairs E := by
      apply mem_disjointCoordinatePairs.mpr
      simp [Set.disjoint_left]
    calc
      0 ≤ F ∅ x * G ∅ x := mul_nonneg (hF0 ∅ x) (hG0 ∅ x)
      _ ≤ (disjointCoordinatePairs E).sup'
          (disjointCoordinatePairs_nonempty (E := E))
          (fun pair ↦ F pair.1 x * G pair.2 x) :=
        Finset.le_sup' (fun pair : Set E × Set E ↦
          F pair.1 x * G pair.2 x) hempty
  have hdisjointDual0 : ∀ p : (∀ e, T e) × (∀ e, T e), 0 ≤
      piFunctionalFamilyDisjointMaxAt F G p.1 p.2 := by
    intro p
    unfold piFunctionalFamilyDisjointMaxAt
    have hempty : ((∅, ∅) : Set E × Set E) ∈ disjointCoordinatePairs E := by
      apply mem_disjointCoordinatePairs.mpr
      simp [Set.disjoint_left]
    calc
      0 ≤ F ∅ p.1 * G ∅ p.2 := mul_nonneg (hF0 ∅ p.1) (hG0 ∅ p.2)
      _ ≤ (disjointCoordinatePairs E).sup'
          (disjointCoordinatePairs_nonempty (E := E))
          (fun pair ↦ F pair.1 p.1 * G pair.2 p.2) :=
        Finset.le_sup' (fun pair : Set E × Set E ↦
          F pair.1 p.1 * G pair.2 p.2) hempty
  have hnuPrimal :
      (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
          ∂Measure.pi nu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x)
          ∂Measure.pi nu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x)
          ∂Measure.pi nu := by
    have h := ENNReal.ofReal_le_ofReal hfinite.1
    rw [ENNReal.ofReal_mul
      (finitePiExpectation_nonneg w hw0 _ hmaxF0),
      ← lintegral_finitePi_eq_ofReal_expectation nu _ hdisjoint0,
      ← lintegral_finitePi_eq_ofReal_expectation nu _ hmaxF0,
      ← lintegral_finitePi_eq_ofReal_expectation nu _ hmaxG0] at h
    exact h
  have hnuDual :
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi nu).prod (Measure.pi nu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi nu := by
    have h := ENNReal.ofReal_le_ofReal hfinite.2
    rw [← lintegral_finitePiDual_eq_ofReal_expectation nu _ hdisjointDual0,
      ← lintegral_finitePi_eq_ofReal_expectation nu _
        (fun x => mul_nonneg (hmaxF0 x) (hmaxG0 x))] at h
    exact h
  let Q : (∀ e, S e) → (∀ e, T e) := fun x e => q e (x e)
  have hqmp : MeasurePreserving Q (Measure.pi mu) (Measure.pi nu) :=
    measurePreserving_pi mu nu (fun e => ⟨hq e, rfl⟩)
  constructor
  · simpa only [Q] using
      (show
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G (Q x))
            ∂Measure.pi mu) ≤
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F (Q x))
            ∂Measure.pi mu) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G (Q x))
            ∂Measure.pi mu from by
        have hdisjoint := hqmp.lintegral_comp
          (f := fun y ↦ ENNReal.ofReal (piFunctionalFamilyDisjointMax F G y))
          (measurable_of_finite _)
        have hmaxF := hqmp.lintegral_comp
          (f := fun y ↦ ENNReal.ofReal (piFunctionalFamilyMax F y))
          (measurable_of_finite _)
        have hmaxG := hqmp.lintegral_comp
          (f := fun y ↦ ENNReal.ofReal (piFunctionalFamilyMax G y))
          (measurable_of_finite _)
        rw [hdisjoint, hmaxF, hmaxG]
        exact hnuPrimal)
  · have hqmpProd := hqmp.prod hqmp
    simpa only [Q, Prod.map_apply] using
      (show
        (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt F G (Q p.1) (Q p.2))
            ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
          ∫⁻ x, ENNReal.ofReal
            (piFunctionalFamilyMax F (Q x) * piFunctionalFamilyMax G (Q x))
            ∂Measure.pi mu from by
        have hdisjoint := hqmpProd.lintegral_comp
          (f := fun p ↦ ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt F G p.1 p.2))
          (measurable_of_finite _)
        change (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt F G (Q p.1) (Q p.2))
            ∂(Measure.pi mu).prod (Measure.pi mu)) = _ at hdisjoint
        have hsame := hqmp.lintegral_comp
          (f := fun x ↦ ENNReal.ofReal
            (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x))
          (measurable_of_finite _)
        rw [hdisjoint, hsame]
        exact hnuDual)

end FiniteFactor

end StatMech.FrontierA
