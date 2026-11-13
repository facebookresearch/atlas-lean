/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms





open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem exists_nat_abs_bound_on_finset (S : Finset V) (f : V → Real) :
    ∃ K : Nat, ∀ x ∈ S, |f x| ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨K, hK⟩ := exists_nat_ge (max |f a| N)
      refine ⟨K, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact (le_max_left _ _).trans hK
      · exact (hN x hxS).trans ((le_max_right _ _).trans hK)



def PeriodicPlaneEmbedding.primalHalfPlaneBarrierReady
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∃ a b C D : Real, a < b ∧ C < D ∧
    ∃ xl xu xj : V,
    ∃ lower : P.graph.Walk xl xj,
    ∃ upper : P.graph.Walk xu xj,
      ¬ lower.Nil ∧ ¬ upper.Nil ∧
      (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧
      (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧
      E.vertexCoord xl 1 < C ∧ D < E.vertexCoord xu 1 ∧
      (∀ t : unitInterval,
        a < E.coordinates (E.walkArc lower t) 0 ∧
          E.coordinates (E.walkArc lower t) 0 < b) ∧
      (∀ t : unitInterval,
        a < E.coordinates (E.walkArc upper t) 0 ∧
          E.coordinates (E.walkArc upper t) 0 < b)





theorem PeriodicPlaneEmbedding.exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ n : Nat,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r 0 1 n L U) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hmiss : Tendsto
      (fun N => 1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hsq
  have hroot : Tendsto
      (fun N => Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using hmiss.sqrt
  have htwo : Tendsto
      (fun N => 2 * Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : Real))).mul hroot
  have hev : ∀ᶠ N in atTop,
      2 * Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) <
        epsilon / 2 :=
    (tendsto_order.1 htwo).2 (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  have heta : 0 < epsilon / 6 := div_pos hepsilon (by norm_num)
  obtain ⟨z₀, z, n, hS, hSlo, hjoined⟩ :=
    E.exists_inward_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
      mu hFKG hTI hunique hrR (P.orbitBox N) heta
  let S := (P.orbitBox N).image (P.shift z₀)
  let Slo := S.image (P.shift (verticalShift z))
  let Shi := (S.image (P.shift (verticalShift 2))).image
    (P.shift (verticalShift z))
  have hfull : (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r)) := by
    have hSr : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
        E.rightHalfPlaneVertices r := by
      intro x hx
      exact hrR.trans (hS (by simpa only [S, Finset.coe_image] using hx))
    have h := E.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift
      mu hFKG hTI hunique r N z₀ hSr
    simpa only [S, Finset.coe_image] using h
  have hsqrt : Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) ≤
      Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) :=
    Real.sqrt_le_sqrt (sub_le_sub_left hfull 1)
  refine ⟨Slo, Shi, n, hSlo, ?_⟩
  linarith



theorem PeriodicPlaneEmbedding.exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ n : Nat,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      U = L.image (P.shift (verticalShift (1 + t))) ∧
      1 - epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n L U) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hmiss : Tendsto
      (fun N => 1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hsq
  have hroot : Tendsto
      (fun N => Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using hmiss.sqrt
  have htwo : Tendsto
      (fun N => 2 * Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : Real))).mul hroot
  have hev : ∀ᶠ N in atTop,
      2 * Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) <
        epsilon / 2 :=
    (tendsto_order.1 htwo).2 (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  have heta : 0 < epsilon / 6 := div_pos hepsilon (by norm_num)
  obtain ⟨z₀, z, n, hS, hSlo, hjoined⟩ :=
    E.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
      mu hFKG hTI hunique hrR s t (P.orbitBox N) heta
  let S := (P.orbitBox N).image (P.shift z₀)
  let Slo := S.image (P.shift (verticalShift z))
  let Shi := (S.image (P.shift (verticalShift (1 + t)))).image
    (P.shift (verticalShift z))
  have hShiTranslate : Shi =
      Slo.image (P.shift (verticalShift (1 + t))) := by
    ext y
    simp only [Shi, Slo, Finset.mem_image]
    constructor
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift z) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift (1 + t)) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  have hfull : (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r)) := by
    have hSr : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
        E.rightHalfPlaneVertices r := by
      intro x hx
      exact hrR.trans (hS (by simpa only [S, Finset.coe_image] using hx))
    have h := E.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift
      mu hFKG hTI hunique r N z₀ hSr
    simpa only [S, Finset.coe_image] using h
  have hsqrt : Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) ≤
      Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) :=
    Real.sqrt_le_sqrt (sub_le_sub_left hfull 1)
  refine ⟨Slo, Shi, n, hSlo, hShiTranslate, ?_⟩
  linarith




theorem PeriodicPlaneEmbedding.exists_highProbability_ordered_finiteJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (band buffer : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m : Nat, ∃ L U : Finset V, ∃ n : Nat,
      band + buffer < m ∧
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      U = L.image (P.shift (verticalShift (1 + 2 * (m : Int)))) ∧
      (∀ x ∈ L, ∀ y ∈ U,
        E.vertexCoord x 1 + 2 * (band + buffer : Nat) + 2 <
          E.vertexCoord y 1) ∧
      1 - epsilon < mu.real
        (E.finiteJoinedBoundaryArmEvent r (-(m : Real)) m n L U) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hmiss : Tendsto
      (fun N => 1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hsq
  have hroot : Tendsto
      (fun N => Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using hmiss.sqrt
  have htwo : Tendsto
      (fun N => 2 * Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : Real))).mul hroot
  have hev : ∀ᶠ N in atTop,
      2 * Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) <
        epsilon / 2 :=
    (tendsto_order.1 htwo).2 (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨K, hK⟩ :=
    exists_nat_abs_bound_on_finset (P.orbitBox N) (fun x => E.vertexCoord x 1)
  let m : Nat := K + band + buffer + 1
  let t : Int := 2 * m
  have ht : 0 < t := by
    dsimp only [t, m]
    positivity
  have hm : band + buffer < m := by
    dsimp only [m]
    omega
  have heta : 0 < epsilon / 6 := div_pos hepsilon (by norm_num)
  obtain ⟨z₀, z, n, hS, hSlo, hjoined⟩ :=
    E.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
      mu hFKG hTI hunique hrR (-(m : Real)) t (P.orbitBox N) heta
  let S := (P.orbitBox N).image (P.shift z₀)
  let Slo := S.image (P.shift (verticalShift z))
  let Shi := (S.image (P.shift (verticalShift (1 + t)))).image
    (P.shift (verticalShift z))
  have hShiTranslate : Shi =
      Slo.image (P.shift (verticalShift (1 + t))) := by
    ext y
    simp only [Shi, Slo, Finset.mem_image]
    constructor
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift z) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift (1 + t)) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  have horder : ∀ x ∈ Slo, ∀ y ∈ Shi,
      E.vertexCoord x 1 + 2 * (band + buffer : Nat) + 2 <
        E.vertexCoord y 1 := by
    intro x hx y hy
    obtain ⟨xS, hxS, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hxS
    obtain ⟨yT, hyT, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨yS, hyS, rfl⟩ := Finset.mem_image.mp hyT
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hyS
    have hxBound := abs_le.mp (hK x₀ hx₀)
    have hyBound := abs_le.mp (hK y₀ hy₀)
    simp only [E.vertexCoord_shift, verticalShift_one_apply,
      Int.cast_add, Int.cast_one] at ⊢
    dsimp only [t, m]
    push_cast
    linarith
  have hfull : (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r)) := by
    have hSr : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
        E.rightHalfPlaneVertices r := by
      intro x hx
      exact hrR.trans (hS (by simpa only [S, Finset.coe_image] using hx))
    have h := E.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift
      mu hFKG hTI hunique r N z₀ hSr
    simpa only [S, Finset.coe_image] using h
  have hsqrt : Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) ≤
      Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) :=
    Real.sqrt_le_sqrt (sub_le_sub_left hfull 1)
  have hend : (-(m : Real)) + (t : Int) = m := by
    dsimp only [t]
    push_cast
    ring
  refine ⟨m, Slo, Shi, n, hm, hSlo, ?_, horder, ?_⟩
  · simpa only [t] using hShiTranslate
  · rw [hend] at hjoined
    linarith




theorem PeriodicPlaneEmbedding.exists_highProbability_primalHalfPlaneBarrierReady
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r B : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ n : Nat,
      1 - epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r 0 1 n L U) ∧
      E.finiteJoinedBoundaryArmEvent r 0 1 n L U ⊆
        E.primalHalfPlaneBarrierReady := by
  have hrR : r ≤ r + B := by linarith
  obtain ⟨L, U, n, hL, hprob⟩ :=
    E.exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin
      mu hFKG hTI hunique hrR hepsilon
  refine ⟨L, U, n, hprob, ?_⟩
  intro omega homega
  exact E.finiteJoinedBoundaryArmEvent_barrierReady
    hB (by norm_num) hL homega



theorem PeriodicPlaneEmbedding.exists_highProbability_separated_primalHalfPlaneBarrierReady
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r B s : Real) (t : Int) (ht : 0 < t) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ n : Nat,
      1 - epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n L U) ∧
      E.finiteJoinedBoundaryArmEvent r s (s + t) n L U ⊆
        E.primalHalfPlaneBarrierReady := by
  have hrR : r ≤ r + B := by linarith
  obtain ⟨L, U, n, hL, _hU, hprob⟩ :=
    E.exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin
      mu hFKG hTI hunique hrR s t hepsilon
  have hcd : s < s + (t : Real) := by
    exact lt_add_of_pos_right s (by exact_mod_cast ht)
  refine ⟨L, U, n, hprob, ?_⟩
  intro omega homega
  exact E.finiteJoinedBoundaryArmEvent_barrierReady hB hcd hL homega

end StatMech.FK.PeriodicPlanar
