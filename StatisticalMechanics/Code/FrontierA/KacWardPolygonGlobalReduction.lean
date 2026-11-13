/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardFinitePolygonEar
import Code.FrontierA.KacWardUnitCycleReduction













open scoped BigOperators
open Finset SimpleGraph Polynomial

namespace StatMech.FrontierA

open StatMech.Onsager
open StatMech.Ising

universe u



theorem kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct
        (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop =
      Complex.exp
        ((((∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) : ℂ) *
          Complex.I) / 2) := by
  unfold kwLoopPhaseProduct kwAngleTurnPhase
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.sum_div]



theorem kw_totalPrincipalTurn_eq_int_mul_two_pi
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    ∃ winding : ℤ,
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi) := by
  let s : ℝ := ∑ k,
    (angle (loop (k + 1)) - angle (loop k)).toReal
  have hcoe : (s : Real.Angle) = 0 := by
    calc
      (s : Real.Angle) =
          ∑ k, ((angle (loop (k + 1)) - angle (loop k)).toReal :
            Real.Angle) := by
        change Real.Angle.coeHom
          (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rfl
      _ = ∑ k, (angle (loop (k + 1)) - angle (loop k)) := by
        simp only [Real.Angle.coe_toReal]
      _ = 0 := by
        have hshift : (∑ k, angle (loop (k + 1))) =
            ∑ k, angle (loop k) := by
          change (∑ k, angle (loop ((Equiv.addRight (1 : Fin n)) k))) = _
          exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
            (fun k ↦ angle (loop k))
        rw [Finset.sum_sub_distrib, hshift, sub_self]
  obtain ⟨winding, hwinding⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  refine ⟨winding, ?_⟩
  simpa only [s, zsmul_eq_mul] using hwinding.symm





theorem kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D)
    (winding : ℤ)
    (hturn :
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi))
    (hodd : Odd winding) :
    kwLoopPhaseProduct
        (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop =
      -1 := by
  rw [kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum, hturn]
  obtain ⟨k, rfl⟩ := hodd.exists_bit1
  rw [show
      ((((((2 * k + 1 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) *
            Complex.I) / 2) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I, one_mul]



theorem kw_odd_winding_of_angleTurnPhase_eq_neg_one
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D)
    (winding : ℤ)
    (hturn :
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi))
    (hphase : kwLoopPhaseProduct
      (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop = -1) :
    Odd winding := by
  apply Int.not_even_iff_odd.mp
  intro heven
  obtain ⟨k, hk⟩ := heven
  have hproduct := kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum angle loop
  rw [hphase, hturn] at hproduct
  have hexponent :
      (((((winding : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) / 2) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hk]
    push_cast
    ring
  rw [hexponent, Complex.exp_int_mul_two_pi_mul_I] at hproduct
  norm_num at hproduct



def KWStraightLineCyclePhaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1



theorem KWStraightLineCycleEarDecomposition.toPhaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (h : KWStraightLineCycleEarDecomposition G embedding) :
    KWStraightLineCyclePhaseSign G embedding := by
  intro root p hp
  exact h.phaseProduct_eq_neg_one p hp



theorem KWStraightLineCyclePhaseSign.of_exists_removable
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCycleEarDecomposition.toPhaseSign
    (KWStraightLineCycleEarDecomposition.of_exists_removable
      hexists embedding)




theorem KWStraightLineCyclePhaseSign.of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega))
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCycleEarDecomposition.toPhaseSign
    (KWStraightLineCycleEarDecomposition.of_geometricEar_five_plus
      hgeneric embedding)



theorem KWStraightLineCyclePhaseSign.of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCycleEarDecomposition.toPhaseSign
    (KWStraightLineCycleEarDecomposition.of_alignedSideEar_five_plus
      hgeneric embedding)



theorem KWStraightLineCyclePhaseSign.of_strictParityEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneStrictParityEar)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCyclePhaseSign G embedding :=
  KWStraightLineCyclePhaseSign.of_exists_removable
    (KWFiniteSimplePolygon.exists_removable_of_strictParityEar_five_plus
      hgeneric) embedding





def KWStraightLineCycleOddTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∃ winding : ℤ,
      (∑ k, (embedding.dartAngle (kwGraphCycleDartLoop p (k + 1)) -
          embedding.dartAngle (kwGraphCycleDartLoop p k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi) ∧
      Odd winding



theorem kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D)
    (hturn :
      (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
          2 * Real.pi ∨
        (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) =
          -(2 * Real.pi)) :
    kwLoopPhaseProduct
        (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop =
      -1 := by
  rw [kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum]
  rcases hturn with hturn | hturn
  · rw [hturn]
    rw [show (((2 * Real.pi : ℝ) : ℂ) * Complex.I) / 2 =
      (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]
  · rw [hturn]
    rw [show ((((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) / 2) =
      -((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num



def KWStraightLineCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (embedding.dartAngle (kwGraphCycleDartLoop p (k + 1)) -
        embedding.dartAngle (kwGraphCycleDartLoop p k)).toReal : ℝ) =
        2 * Real.pi ∨
      (∑ k, (embedding.dartAngle (kwGraphCycleDartLoop p (k + 1)) -
        embedding.dartAngle (kwGraphCycleDartLoop p k)).toReal : ℝ) =
        -(2 * Real.pi)



theorem KWStraightLineCycleTurning.phaseProduct_eq_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hphase : embedding.turnPhase = fun dart next ↦
      kwAngleTurnPhase (embedding.dartAngle dart) (embedding.dartAngle next) := by
    funext dart next
    rw [← embedding.principalPhase_eq_turnPhase]
    rfl
  rw [hphase]
  exact kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn
    embedding.dartAngle (kwGraphCycleDartLoop p) (hturning p hp)




theorem KWStraightLineCycleOddTurning.phaseProduct_eq_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleOddTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hphase : embedding.turnPhase = fun dart next ↦
      kwAngleTurnPhase (embedding.dartAngle dart) (embedding.dartAngle next) := by
    funext dart next
    rw [← embedding.principalPhase_eq_turnPhase]
    rfl
  obtain ⟨winding, hsum, hodd⟩ := hturning p hp
  rw [hphase]
  exact kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding
    embedding.dartAngle (kwGraphCycleDartLoop p) winding hsum hodd

theorem KWStraightLineCycleOddTurning.toPhaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleOddTurning G embedding) :
    KWStraightLineCyclePhaseSign G embedding := by
  intro root p hp
  exact hturning.phaseProduct_eq_neg_one G embedding p hp

theorem KWStraightLineCyclePhaseSign.toOddTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hsign : KWStraightLineCyclePhaseSign G embedding) :
    KWStraightLineCycleOddTurning G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  obtain ⟨winding, hturn⟩ := kw_totalPrincipalTurn_eq_int_mul_two_pi
    embedding.dartAngle (kwGraphCycleDartLoop p)
  have hphaseEq : embedding.turnPhase = fun dart next ↦
      kwAngleTurnPhase (embedding.dartAngle dart) (embedding.dartAngle next) := by
    funext dart next
    rw [← embedding.principalPhase_eq_turnPhase]
    rfl
  have hphase : kwLoopPhaseProduct
      (fun dart next ↦ kwAngleTurnPhase
        (embedding.dartAngle dart) (embedding.dartAngle next))
      (kwGraphCycleDartLoop p) = -1 := by
    rw [← hphaseEq]
    exact hsign p hp
  exact ⟨winding, hturn,
    kw_odd_winding_of_angleTurnPhase_eq_neg_one
      embedding.dartAngle (kwGraphCycleDartLoop p) winding hturn hphase⟩

theorem kw_straightLineCycleOddTurning_iff_phaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleOddTurning G embedding ↔
      KWStraightLineCyclePhaseSign G embedding :=
  ⟨fun h ↦ h.toPhaseSign G embedding,
    fun h ↦ h.toOddTurning G embedding⟩



theorem KWStraightLineCycleTurning.toOddTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleTurning G embedding) :
    KWStraightLineCycleOddTurning G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rcases hturning p hp with hpos | hneg
  · exact ⟨1, by simpa using hpos, by norm_num⟩
  · refine ⟨-1, ?_, by norm_num⟩
    simpa using hneg



theorem kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleOddTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwGraphFormalLogCoeff G embedding.turnPhase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  exact kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one
    G embedding hdeg p hp
      (hturning.phaseProduct_eq_neg_one G embedding p hp)


theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_oddCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleOddTurning G embedding) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G := by
  exact kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff
    G embedding hdeg
      (kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning
        G embedding hdeg hturning)



theorem kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwGraphFormalLogCoeff G embedding.turnPhase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  exact kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one
    G embedding hdeg p hp
      (hturning.phaseProduct_eq_neg_one G embedding p hp)



theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G := by
  exact kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff
    G embedding hdeg
      (kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning
        G embedding hdeg hturning)




theorem kacWard_straightLine_trivalent_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding)
    (weight : Sym2 V → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  exact kacWard_straightLine_trivalent_of_cycleCoeff G embedding hdeg
    (kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning
      G embedding hdeg hturning)
    weight q hq hentry hcard




noncomputable def kwDetScalePolynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) : ℂ[X] :=
  ((1 : Matrix E E ℂ[X]) -
    Matrix.of (fun i j : E ↦ X * C (M i j))).det

theorem kwDetScalePolynomial_eval
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (t : ℂ) :
    (kwDetScalePolynomial M).eval t = (1 - t • M).det := by
  rw [kwDetScalePolynomial, ← Polynomial.coe_evalRingHom,
    RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [smul_eq_mul, h] <;> ring



noncomputable def kwEvenScalePolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) : ℂ[X] :=
  ∑ F ∈ evenSubgraphs G,
    Polynomial.monomial F.card (∏ e ∈ F, weight e)

theorem kwEvenScalePolynomial_eval
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (t : ℂ) :
    (kwEvenScalePolynomial G weight).eval t =
      kwEvenPolynomial G (fun edge ↦ t * weight edge) := by
  classical
  unfold kwEvenScalePolynomial kwEvenPolynomial evenSubgraphs
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib]
  simp
  ring





theorem kacWard_straightLine_trivalent_of_oddCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleOddTurning G embedding)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  let M := kwGraphTransition G weight embedding.turnPhase
  let P := kwDetScalePolynomial M
  let Q := (kwEvenScalePolynomial G weight) ^ 2
  let card : ℝ := Fintype.card G.Dart
  let q : ℝ := (2 * (1 + card))⁻¹
  let B : ℝ := ∑ dart : G.Dart, ∑ next : G.Dart, ‖M dart next‖
  let delta : ℝ := q / (1 + B)
  have hcard0 : 0 ≤ card := by positivity
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hcardq : card * q < 1 := by
    dsimp only [q]
    rw [mul_inv_lt_iff₀ (by positivity : 0 < 2 * (1 + card))]
    nlinarith
  have hraw (dart next : G.Dart) : ‖M dart next‖ ≤ B := by
    dsimp only [B]
    exact (Finset.single_le_sum
      (fun d _ ↦ Finset.sum_nonneg fun e _ ↦ norm_nonneg (M d e))
      (Finset.mem_univ dart)).trans' <|
        Finset.single_le_sum
          (fun e _ ↦ norm_nonneg (M dart e)) (Finset.mem_univ next)
  have heval (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) delta) :
      P.eval (r : ℂ) = Q.eval (r : ℂ) := by
    have hrnorm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    have hentry : ∀ dart next,
        ‖kwGraphTransition G (fun edge ↦ (r : ℂ) * weight edge)
          embedding.turnPhase dart next‖ ≤ q := by
      intro dart next
      rw [kwGraphTransition_smulWeight, norm_mul, hrnorm]
      have hlt : r * B < q := by
        have hden : 0 < 1 + B := by positivity
        have := hr.2
        dsimp only [delta] at this
        rw [lt_div_iff₀ hden] at this
        nlinarith
      exact (mul_le_mul_of_nonneg_left
        (hraw dart next) hr.1.le).trans hlt.le
    have hsmall := kacWard_straightLine_trivalent_of_cycleCoeff
      G embedding hdeg
        (kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning
          G embedding hdeg hturning)
      (fun edge ↦ (r : ℂ) * weight edge) q hq.le hentry hcardq
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval,
      Polynomial.eval_pow, kwEvenScalePolynomial_eval]
    have hmatrix : (r : ℂ) • M =
        kwGraphTransition G (fun edge ↦ (r : ℂ) * weight edge)
          embedding.turnPhase := by
      ext dart next
      change (r : ℂ) * M dart next = _
      dsimp only [M]
      rw [kwGraphTransition_smulWeight]
    rw [hmatrix]
    exact hsmall
  have hinfinite : Set.Infinite
      {z : ℂ | P.eval z = Q.eval z} := by
    have hI : Set.Infinite (Set.Ioo (0 : ℝ) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : ℝ ↦ (r : ℂ)) '' Set.Ioo (0 : ℝ) delta) :=
      hI.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q :=
    Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : ℂ)) hpoly
  dsimp only [P, Q] at hone
  simpa [kwDetScalePolynomial_eval,
    kwEvenScalePolynomial_eval, M] using hone



theorem kacWard_straightLine_trivalent_allWeights_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding)
    (weight : Sym2 V → ℂ) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  kacWard_straightLine_trivalent_of_oddCycleTurning G embedding hdeg
    (hturning.toOddTurning G embedding) weight

end StatMech.FrontierA
