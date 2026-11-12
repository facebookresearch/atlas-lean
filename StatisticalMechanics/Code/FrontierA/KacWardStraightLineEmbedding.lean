/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPrincipalCancellation
import Mathlib.Analysis.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine










open scoped BigOperators Affine EuclideanGeometry Real
open Finset SimpleGraph

namespace StatMech.FrontierA





structure KWStraightLineEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  vertex : V → ℂ
  vertex_injective : Function.Injective vertex
  vertex_not_strictly_between : ∀ (dart : G.Dart) (v : V),
    v ≠ dart.fst → v ≠ dart.snd →
      ¬Sbtw ℝ (vertex dart.fst) (vertex v) (vertex dart.snd)
  edgeInteriors_disjoint : ∀ (dart next : G.Dart),
    dart.edge ≠ next.edge →
      Disjoint
        {z : ℂ | Sbtw ℝ (vertex dart.fst) z (vertex dart.snd)}
        {z : ℂ | Sbtw ℝ (vertex next.fst) z (vertex next.snd)}


noncomputable def KWStraightLineEmbedding.dartAngle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart : G.Dart) : Real.Angle :=
  (Complex.arg (embedding.vertex dart.snd - embedding.vertex dart.fst) : ℝ)

theorem KWStraightLineEmbedding.dartVector_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart : G.Dart) :
    embedding.vertex dart.snd - embedding.vertex dart.fst ≠ 0 := by
  rw [sub_ne_zero]
  exact embedding.vertex_injective.ne dart.snd_ne_fst



noncomputable def KWStraightLineEmbedding.turnPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart) : ℂ :=
  Complex.exp
    (((Complex.arg
      ((embedding.vertex next.snd - embedding.vertex next.fst) /
        (embedding.vertex dart.snd - embedding.vertex dart.fst)) : ℂ) *
          Complex.I) / 2)



theorem KWStraightLineEmbedding.dartAngle_sub_eq_arg_div
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart) :
    embedding.dartAngle next - embedding.dartAngle dart =
      (Complex.arg
        ((embedding.vertex next.snd - embedding.vertex next.fst) /
          (embedding.vertex dart.snd - embedding.vertex dart.fst)) : ℝ) := by
  unfold dartAngle
  exact (Complex.arg_div_coe_angle
    (embedding.dartVector_ne_zero next)
    (embedding.dartVector_ne_zero dart)).symm



theorem KWStraightLineEmbedding.principalPhase_eq_turnPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart) :
    kwPrincipalHalfAnglePhase embedding.dartAngle dart next =
      embedding.turnPhase dart next := by
  unfold kwPrincipalHalfAnglePhase turnPhase
  rw [embedding.dartAngle_sub_eq_arg_div,
    Complex.arg_coe_angle_toReal_eq_arg]


theorem KWStraightLineEmbedding.dartAngle_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart : G.Dart) :
    embedding.dartAngle dart.symm =
      embedding.dartAngle dart + (Real.pi : Real.Angle) := by
  unfold dartAngle
  change (Complex.arg
      (embedding.vertex dart.fst - embedding.vertex dart.snd) : Real.Angle) = _
  rw [show embedding.vertex dart.fst - embedding.vertex dart.snd =
      -(embedding.vertex dart.snd - embedding.vertex dart.fst) by ring,
    Complex.arg_neg_coe_angle (embedding.dartVector_ne_zero dart)]



theorem KWStraightLineEmbedding.nonantipodal_of_nonbacktracking
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart)
    (hadj : G.DartAdj dart next) (hneq : dart.edge ≠ next.edge) :
    embedding.dartAngle next - embedding.dartAngle dart ≠
      (Real.pi : Real.Angle) := by
  letI : Fact (Module.finrank ℝ ℂ = 2) :=
    Complex.finrank_real_complex_fact
  letI : Module.Oriented ℝ ℂ (Fin 2) := ⟨Complex.orientation⟩
  intro hantipodal
  have hsnd : dart.snd = next.fst := hadj
  have hfirst_last : dart.fst ≠ next.snd := by
    intro h
    apply hneq
    change s(dart.fst, dart.snd) = s(next.fst, next.snd)
    rw [← hsnd, ← h]
    exact Sym2.eq_swap
  have hfirst_joint : dart.fst ≠ next.fst := by
    intro h
    exact dart.fst_ne_snd (h.trans hsnd.symm)
  have hlast_joint : next.snd ≠ dart.snd := by
    intro h
    exact next.snd_ne_fst (h.trans hsnd)
  let a : ℂ := embedding.vertex dart.fst
  let b : ℂ := embedding.vertex dart.snd
  let c : ℂ := embedding.vertex next.snd
  let dvec : ℂ := b - a
  let nvec : ℂ := c - b
  have hdvec : dvec ≠ 0 := by
    simpa only [dvec, a, b] using embedding.dartVector_ne_zero dart
  have hnvec : nvec ≠ 0 := by
    simpa only [nvec, b, c, hsnd] using embedding.dartVector_ne_zero next
  have hturn :
      (Complex.arg nvec : Real.Angle) -
          (Complex.arg dvec : Real.Angle) = (Real.pi : Real.Angle) := by
    simpa only [KWStraightLineEmbedding.dartAngle, dvec, nvec, a, b, c,
      hsnd] using hantipodal
  have hargAngle :
      (Complex.arg (-dvec) : Real.Angle) =
        (Complex.arg nvec : Real.Angle) := by
    rw [Complex.arg_neg_coe_angle hdvec]
    calc
      (Complex.arg dvec : Real.Angle) + (Real.pi : Real.Angle) =
          ((Complex.arg nvec : Real.Angle) - Complex.arg dvec) +
            Complex.arg dvec := by rw [hturn]; abel
      _ = (Complex.arg nvec : Real.Angle) := by abel
  have harg : Complex.arg (-dvec) = Complex.arg nvec :=
    Complex.arg_coe_angle_eq_iff.mp hargAngle
  have hray : SameRay ℝ (-dvec) nvec :=
    Complex.sameRay_of_arg_eq harg
  have hoangle :
      EuclideanGeometry.oangle a b c = 0 := by
    apply EuclideanGeometry.o.oangle_eq_zero_iff_sameRay.mpr
    convert hray using 1
    · simp only [dvec, a, b, vsub_eq_sub]
      ring
  rcases EuclideanGeometry.oangle_eq_zero_iff_wbtw.mp hoangle with
      habc | hacb
  · have hstrict :
        Sbtw ℝ (embedding.vertex next.fst)
          (embedding.vertex dart.fst) (embedding.vertex next.snd) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [a, b, c, hsnd] using habc
      · exact embedding.vertex_injective.ne hfirst_joint
      · exact embedding.vertex_injective.ne hfirst_last
    exact embedding.vertex_not_strictly_between next dart.fst
      hfirst_joint hfirst_last hstrict
  · have hstrict :
        Sbtw ℝ (embedding.vertex dart.fst)
          (embedding.vertex next.snd) (embedding.vertex dart.snd) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [wbtw_comm]
        simpa only [a, b, c, hsnd] using hacb
      · exact embedding.vertex_injective.ne hfirst_last.symm
      · exact embedding.vertex_injective.ne hlast_joint
    exact embedding.vertex_not_strictly_between dart next.snd
      hfirst_last.symm hlast_joint hstrict



theorem kwStraightLineGraphLoopWeight_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ)
    (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (kwPrincipalHalfAnglePhase embedding.dartAngle))
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (kwPrincipalHalfAnglePhase embedding.dartAngle)) loop := by
  exact kwGraphLoopWeight_principal_surgery_sign
    G weight embedding.dartAngle embedding.dartAngle_symm
    embedding.nonantipodal_of_nonbacktracking selected loop hboth



theorem kwStraightLineGraphLoopWeight_turnPhase_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ)
    (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase)
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase) loop := by
  have hphase : kwPrincipalHalfAnglePhase embedding.dartAngle =
      embedding.turnPhase := by
    funext dart next
    exact embedding.principalPhase_eq_turnPhase dart next
  rw [← hphase]
  exact kwStraightLineGraphLoopWeight_surgery_sign
    G embedding weight selected loop hboth


theorem kwStraightLineGraphLoopWeight_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ)
    (loop : Fin n → G.Dart) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase)
        (StatMech.Onsager.ons_involutiveLoopRev
          SimpleGraph.Dart.symm loop) =
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase) loop := by
  have hphase : kwPrincipalHalfAnglePhase embedding.dartAngle =
      embedding.turnPhase := by
    funext dart next
    exact embedding.principalPhase_eq_turnPhase dart next
  rw [← hphase]
  let reversed := StatMech.Onsager.ons_involutiveLoopRev
    SimpleGraph.Dart.symm loop
  let adjacencyProduct : (Fin n → G.Dart) → ℂ := fun path ↦
    ∏ k, kwGraphNonbacktrackingFactor G (path k) (path (k + 1))
  let reflected : Equiv.Perm (Fin n) :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hadjacency : adjacencyProduct reversed = adjacencyProduct loop := by
    change (∏ k, kwGraphNonbacktrackingFactor G
      (loop (-k)).symm (loop (-(k + 1))).symm) = _
    calc
      (∏ k, kwGraphNonbacktrackingFactor G
          (loop (-k)).symm (loop (-(k + 1))).symm) =
          ∏ k, kwGraphNonbacktrackingFactor G
            (loop (-(k + 1))) (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k _
        exact kwGraphNonbacktrackingFactor_reverse G _ _
      _ = ∏ k, kwGraphNonbacktrackingFactor G
          (loop (reflected k)) (loop (reflected k + 1)) := by
        apply Finset.prod_congr rfl
        intro k _
        congr 2
        change -k = -(k + 1) + 1
        abel
      _ = adjacencyProduct loop := Equiv.prod_comp reflected
        (fun k ↦ kwGraphNonbacktrackingFactor G
          (loop k) (loop (k + 1)))
  have hexponent : kwGraphLoopExponent G reversed =
      kwGraphLoopExponent G loop := by
    unfold kwGraphLoopExponent reversed
    simp only [StatMech.Onsager.ons_involutiveLoopRev,
      SimpleGraph.Dart.edge_symm]
    exact Equiv.sum_comp (Equiv.neg (Fin n))
      (fun k ↦ Finsupp.single (loop k).edge 1)
  have hscalar :
      kwGraphLoopScalar G (kwPrincipalHalfAnglePhase embedding.dartAngle)
          reversed =
        kwGraphLoopScalar G (kwPrincipalHalfAnglePhase embedding.dartAngle)
          loop := by
    by_cases hzero : adjacencyProduct loop = 0
    · rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
        kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
      change adjacencyProduct reversed * _ = adjacencyProduct loop * _
      rw [hadjacency, hzero]
      ring
    · have hvalid : ∀ k : Fin n,
          G.DartAdj (loop k) (loop (k + 1)) ∧
            (loop k).edge ≠ (loop (k + 1)).edge := by
        intro k
        have hfactor : kwGraphNonbacktrackingFactor G
            (loop k) (loop (k + 1)) ≠ 0 := by
          intro hk
          apply hzero
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          exact hk
        by_contra hstep
        simp [kwGraphNonbacktrackingFactor, hstep] at hfactor
      have hphaseProduct :=
        kwLoopPhaseProduct_principal_involutiveLoopRev
          SimpleGraph.Dart.symm embedding.dartAngle
          embedding.dartAngle_symm loop
          (fun k ↦ embedding.nonantipodal_of_nonbacktracking
            _ _ (hvalid k).1 (hvalid k).2)
      rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
        kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
      change adjacencyProduct reversed * _ = adjacencyProduct loop * _
      have hp :
          (∏ k, kwPrincipalHalfAnglePhase embedding.dartAngle
            (reversed k) (reversed (k + 1))) =
          ∏ k, kwPrincipalHalfAnglePhase embedding.dartAngle
            (loop k) (loop (k + 1)) := by
        simpa only [kwLoopPhaseProduct, reversed] using hphaseProduct
      rw [hadjacency, hp]
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor,
    hexponent, hscalar]



theorem kw_straightLineGraph_fixedOrbitExponent_cancel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ)
    (selected : G.Dart) (exponent : Sym2 G.Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (kwPrincipalHalfAnglePhase embedding.dartAngle)) loop) = 0 := by
  exact kw_principalAngleGraph_fixedOrbitExponent_cancel
    G weight embedding.dartAngle embedding.dartAngle_symm
    embedding.nonantipodal_of_nonbacktracking selected exponent



theorem kw_straightLineGraph_turnPhase_fixedOrbitExponent_cancel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ)
    (selected : G.Dart) (exponent : Sym2 G.Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase) loop) = 0 := by
  have hphase : kwPrincipalHalfAnglePhase embedding.dartAngle =
      embedding.turnPhase := by
    funext dart next
    exact embedding.principalPhase_eq_turnPhase dart next
  rw [← hphase]
  exact kw_straightLineGraph_fixedOrbitExponent_cancel
    G embedding weight selected exponent

end StatMech.FrontierA
