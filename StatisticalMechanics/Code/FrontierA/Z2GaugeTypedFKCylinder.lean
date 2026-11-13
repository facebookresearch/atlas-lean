/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeTypedFK
import Code.FrontierA.Z2GaugePerimeterReduction

open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedBondFirstEndpoints (ends : P -> V × V) (D : Finset P) :
    Finset V :=
  D.image (fun p => (ends p).1)

def typedBondSecondEndpoints (ends : P -> V × V) (D : Finset P) :
    Finset V :=
  D.image (fun p => (ends p).2)

def typedBondVertices (ends : P -> V × V) (D : Finset P) :
    Finset V :=
  typedBondFirstEndpoints ends D ∪ typedBondSecondEndpoints ends D



def typedTrueEndpoint (ends : P -> V × V) (chi : V -> Bool) (p : P) : V :=
  if chi (ends p).1 then (ends p).1 else (ends p).2

def typedFalseEndpoint (ends : P -> V × V) (chi : V -> Bool) (p : P) : V :=
  if chi (ends p).1 then (ends p).2 else (ends p).1

def typedMarkedBondVertices (mark : P -> V) (D : Finset P) : Finset V :=
  D.image mark

theorem typedTrueEndpoint_spin_eq_true_of_mem_cut
    (ends : P -> V × V) (chi : V -> Bool) (p : P)
    (hp : p ∈ multibondCut ends chi) :
    chi (typedTrueEndpoint ends chi p) = true := by
  have hne := (mem_multibondCut ends chi p).mp hp
  by_cases hchi : chi (ends p).1
  · simp [typedTrueEndpoint, hchi]
  · have hsecond : chi (ends p).2 = true := by
      cases hsecond : chi (ends p).2
      · exact (hne (by simp [hchi, hsecond])).elim
      · rfl
    simp [typedTrueEndpoint, hchi, hsecond]

theorem typedFalseEndpoint_spin_eq_false_of_mem_cut
    (ends : P -> V × V) (chi : V -> Bool) (p : P)
    (hp : p ∈ multibondCut ends chi) :
    chi (typedFalseEndpoint ends chi p) = false := by
  have hne := (mem_multibondCut ends chi p).mp hp
  by_cases hchi : chi (ends p).1
  · have hsecond : chi (ends p).2 = false := by
      cases hsecond : chi (ends p).2
      · rfl
      · exact (hne (by simp [hchi, hsecond])).elim
    simp [typedFalseEndpoint, hchi, hsecond]
  · simp [typedFalseEndpoint, hchi]

theorem typedMarkedOppositeSides_disjoint
    (ends : P -> V × V) (chi : V -> Bool) (B₁ B₂ : Finset P)
    (hB₁ : B₁ ⊆ multibondCut ends chi)
    (hB₂ : B₂ ⊆ multibondCut ends chi) :
    Disjoint
      (typedMarkedBondVertices (typedTrueEndpoint ends chi) B₁)
      (typedMarkedBondVertices (typedFalseEndpoint ends chi) B₂) := by
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hv₁
  obtain ⟨p₂, hp₂, heq⟩ := Finset.mem_image.mp hv₂
  have htrue := typedTrueEndpoint_spin_eq_true_of_mem_cut
    ends chi p₁ (hB₁ hp₁)
  have hfalse := typedFalseEndpoint_spin_eq_false_of_mem_cut
    ends chi p₂ (hB₂ hp₂)
  rw [heq, htrue] at hfalse
  cases hfalse




theorem typedBondEndpointDisconnections_subset_consistency
    (ends : P -> V × V) (hends : forall p, (ends p).1 ≠ (ends p).2)
    (D : Finset P) :
    finiteEventInter
        ((typedBondFirstEndpoints ends D).product
          (typedBondSecondEndpoints ends D))
        (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆
      typedFKConsistencyEvent ends D := by
  intro omega hall
  have hclosed : forall p, p ∈ D -> omega p ≠ true := by
    intro p hpD hpopen
    let uv : V × V := ((ends p).1, (ends p).2)
    have huv_mem : uv ∈
        (typedBondFirstEndpoints ends D).product
          (typedBondSecondEndpoints ends D) := by
      apply (Finset.mem_product).2
      constructor
      · exact Finset.mem_image.mpr ⟨p, hpD, rfl⟩
      · exact Finset.mem_image.mpr ⟨p, hpD, rfl⟩
    have hdisconn := hall uv huv_mem
    have hadj : (typedOpenGraph ends omega).Adj (ends p).1 (ends p).2 :=
      ⟨p, hpopen, Or.inl ⟨rfl, rfl⟩, hends p⟩
    exact hdisconn hadj.reachable
  refine ⟨fun _ => false, ?_⟩
  intro p hpopen
  have hpD : p ∉ D := fun hpD => hclosed p hpD hpopen
  simp [hpD]





theorem typedTwoCutCoveredDisconnections_subset_consistency
    (ends : P -> V × V) (hends : forall p, (ends p).1 ≠ (ends p).2)
    (D B₁ B₂ : Finset P) (U₁ U₂ : Finset V)
    (hcover₁ : forall p, p ∈ B₁ -> (ends p).1 ∈ U₁ ∨ (ends p).2 ∈ U₁)
    (hcover₂ : forall p, p ∈ B₂ -> (ends p).1 ∈ U₂ ∨ (ends p).2 ∈ U₂)
    (tau chi : V -> Bool)
    (hshift : multibondCut ends tau = D ∆ B₁)
    (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
    finiteEventInter
        (U₁.product U₂)
        (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆
      typedFKConsistencyEvent ends D := by
  intro omega hall
  let touched : V -> Prop := fun v =>
    exists u, u ∈ U₁ ∧
      (typedOpenGraph ends omega).Reachable u v
  let sigma : V -> Bool := fun v => if touched v then chi v else false
  have hcompatible : TypedSignedCompatible ends B₁ omega sigma := by
    intro p hpopen
    have hadj : (typedOpenGraph ends omega).Adj (ends p).1 (ends p).2 :=
      ⟨p, hpopen, Or.inl ⟨rfl, rfl⟩, hends p⟩
    have htouched : touched (ends p).1 <-> touched (ends p).2 := by
      constructor
      · rintro ⟨u, hu, hur⟩
        exact ⟨u, hu, hur.trans hadj.reachable⟩
      · rintro ⟨u, hu, hur⟩
        exact ⟨u, hu, hur.trans hadj.reachable.symm⟩
    by_cases hpB₁ : p ∈ B₁
    · have ht12 : touched (ends p).1 ∧ touched (ends p).2 := by
        rcases hcover₁ p hpB₁ with he1 | he2
        · have ht1 : touched (ends p).1 :=
            ⟨(ends p).1, he1, SimpleGraph.Reachable.refl _⟩
          exact ⟨ht1, htouched.mp ht1⟩
        · have ht2 : touched (ends p).2 :=
            ⟨(ends p).2, he2, SimpleGraph.Reachable.refl _⟩
          exact ⟨htouched.mpr ht2, ht2⟩
      obtain ⟨ht1, ht2⟩ := ht12
      have hpCut : p ∈ multibondCut ends chi := by
        rw [hboundary]
        exact Finset.mem_union_left B₂ hpB₁
      have hchi : chi (ends p).1 ≠ chi (ends p).2 :=
        (mem_multibondCut ends chi p).mp hpCut
      simp [sigma, ht1, ht2, hpB₁, hchi]
    · by_cases ht1 : touched (ends p).1
      · have ht2 : touched (ends p).2 := htouched.mp ht1
        have hchi : chi (ends p).1 = chi (ends p).2 := by
          by_contra hne
          have hpCut : p ∈ multibondCut ends chi :=
            (mem_multibondCut ends chi p).mpr hne
          rw [hboundary] at hpCut
          have hpB₂ : p ∈ B₂ := by
            rcases Finset.mem_union.mp hpCut with hp | hp
            · exact (hpB₁ hp).elim
            · exact hp
          obtain ⟨u, hu, hur⟩ := ht1
          rcases hcover₂ p hpB₂ with he1 | he2
          · let uv : V × V := (u, (ends p).1)
            have huv : uv ∈ U₁.product U₂ := by
              apply (Finset.mem_product).2
              exact ⟨hu, he1⟩
            exact hall uv huv hur
          · let uv : V × V := (u, (ends p).2)
            have huv : uv ∈ U₁.product U₂ := by
              apply (Finset.mem_product).2
              exact ⟨hu, he2⟩
            exact hall uv huv (hur.trans hadj.reachable)
        simp [sigma, ht1, ht2, hpB₁, hchi]
      · have ht2 : ¬ touched (ends p).2 :=
          fun ht2 => ht1 (htouched.mpr ht2)
        simp [sigma, ht1, ht2, hpB₁]
  have htwist : D ∆ multibondCut ends tau = B₁ := by
    rw [hshift]
    ext p
    simp only [Finset.mem_symmDiff]
    tauto
  refine ⟨typedSpinXor sigma tau, ?_⟩
  apply (typedSignedCompatible_xor_iff_symmDiff_cut
    ends D omega sigma tau).mpr
  rwa [htwist]

theorem typedTwoCutDisconnections_subset_consistency
    (ends : P -> V × V) (hends : forall p, (ends p).1 ≠ (ends p).2)
    (D B₁ B₂ : Finset P) (tau chi : V -> Bool)
    (hshift : multibondCut ends tau = D ∆ B₁)
    (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
    finiteEventInter
        ((typedBondVertices ends B₁).product (typedBondVertices ends B₂))
        (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆
      typedFKConsistencyEvent ends D := by
  refine typedTwoCutCoveredDisconnections_subset_consistency
    ends hends D B₁ B₂
    (typedBondVertices ends B₁) (typedBondVertices ends B₂)
    ?_ ?_ tau chi hshift hboundary
  · intro p hp
    exact Or.inl (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  · intro p hp
    exact Or.inl (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩))




theorem typedTwoCutMarkedDisconnections_subset_consistency
    (ends : P -> V × V) (hends : forall p, (ends p).1 ≠ (ends p).2)
    (D B₁ B₂ : Finset P) (tau chi : V -> Bool)
    (hshift : multibondCut ends tau = D ∆ B₁)
    (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
    finiteEventInter
        ((typedMarkedBondVertices (typedTrueEndpoint ends chi) B₁).product
          (typedMarkedBondVertices (typedFalseEndpoint ends chi) B₂))
        (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆
      typedFKConsistencyEvent ends D := by
  refine typedTwoCutCoveredDisconnections_subset_consistency
    ends hends D B₁ B₂
    (typedMarkedBondVertices (typedTrueEndpoint ends chi) B₁)
    (typedMarkedBondVertices (typedFalseEndpoint ends chi) B₂)
    ?_ ?_ tau chi hshift hboundary
  · intro p hp
    by_cases hchi : chi (ends p).1
    · exact Or.inl (Finset.mem_image.mpr ⟨p, hp, by
        simp [typedTrueEndpoint, hchi]⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨p, hp, by
        simp [typedTrueEndpoint, hchi]⟩)
  · intro p hp
    by_cases hchi : chi (ends p).1
    · exact Or.inr (Finset.mem_image.mpr ⟨p, hp, by
        simp [typedFalseEndpoint, hchi]⟩)
    · exact Or.inl (Finset.mem_image.mpr ⟨p, hp, by
        simp [typedFalseEndpoint, hchi]⟩)
theorem typedFKEventMass_nonneg
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) (A : Set (P -> Bool)) :
    0 <= typedFKEventMass ends rho A :=
  finiteEventMass_nonneg
    (fun omega => typedFKProb_nonneg_of_nonneg ends hrho0 hrho1 hZ omega) A

theorem typedFKEventMass_mono
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) {A B : Set (P -> Bool)}
    (hAB : A ⊆ B) :
    typedFKEventMass ends rho A <= typedFKEventMass ends rho B := by
  unfold typedFKEventMass
  apply Finset.sum_le_sum
  intro omega _
  have hprob := typedFKProb_nonneg_of_nonneg
    ends hrho0 hrho1 hZ omega
  by_cases hA : omega ∈ A
  · have hB := hAB hA
    simp [hA, hB]
  · by_cases hB : omega ∈ B
    · simpa [hA, hB] using hprob
    · simp [hA, hB]



theorem typedFKEventMass_disconn_eq_one_sub_twoPoint
    (ends : P -> V × V) (rho : P -> Real)
    (hZ : typedFKZ ends rho ≠ 0) (x y : V) :
    typedFKEventMass ends rho (typedFKDisconnEvent ends x y) =
      1 - typedFKTwoPoint ends rho x y := by
  unfold typedFKEventMass typedFKTwoPoint typedFKDisconnEvent
  calc
    (∑ omega : P -> Bool, typedFKProb ends rho omega *
        (typedFKConnEvent ends x y)ᶜ.indicator
          (fun _ => (1 : Real)) omega) =
        ∑ omega : P -> Bool, typedFKProb ends rho omega *
          (1 - (typedFKConnEvent ends x y).indicator
            (fun _ => (1 : Real)) omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      congr 1
      by_cases homega : omega ∈ typedFKConnEvent ends x y <;>
        simp [homega]
    _ = (∑ omega : P -> Bool, typedFKProb ends rho omega) -
        ∑ omega : P -> Bool, typedFKProb ends rho omega *
          (typedFKConnEvent ends x y).indicator
            (fun _ => (1 : Real)) omega := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ omega : P -> Bool, typedFKProb ends rho omega *
          (typedFKConnEvent ends x y).indicator
            (fun _ => (1 : Real)) omega := by
      rw [typedFKProb_sum_eq_one ends rho hZ]


theorem typedFK_finite_pair_nonconnection_product_bound
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) (upper lower : Finset V) :
    (∏ uv ∈ upper.product lower,
        (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <=
      typedFKEventMass ends rho
        (finiteEventInter (upper.product lower)
          (fun uv => typedFKDisconnEvent ends uv.1 uv.2)) := by
  have h := fkg_inequality_finite_decreasing_events
    (fun omega => typedFKProb_nonneg_of_nonneg
      ends hrho0 hrho1 hZ omega)
    (typedFKProb_sum_eq_one ends rho hZ.ne')
    (typedFKProb_FKGLatticeCondition ends hrho0 hrho1 hZ)
    (upper.product lower)
    (fun uv => typedFKDisconnEvent ends uv.1 uv.2)
    (fun uv _ => typedFKDisconnEvent_isDecreasing ends uv.1 uv.2)
  change (∏ uv ∈ upper.product lower,
      typedFKEventMass ends rho
        (typedFKDisconnEvent ends uv.1 uv.2)) <=
    typedFKEventMass ends rho
      (finiteEventInter (upper.product lower)
        (fun uv => typedFKDisconnEvent ends uv.1 uv.2)) at h
  simp_rw [typedFKEventMass_disconn_eq_one_sub_twoPoint
    ends rho hZ.ne'] at h
  exact h




theorem typedFK_consistencyMass_ge_pair_nonconnection_product
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) (D : Finset P)
    (upper lower : Finset V)
    (hgeometry :
      finiteEventInter (upper.product lower)
          (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆
        typedFKConsistencyEvent ends D) :
    (∏ uv ∈ upper.product lower,
        (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <=
      typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
  exact (typedFK_finite_pair_nonconnection_product_bound
    ends hrho0 hrho1 hZ upper lower).trans
      (typedFKEventMass_mono ends hrho0 hrho1 hZ hgeometry)


theorem typedFK_consistencyMass_ge_bondEndpoint_product
    (ends : P -> V × V) (hends : forall p, (ends p).1 ≠ (ends p).2)
    {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) (D : Finset P) :
    (∏ uv ∈ (typedBondFirstEndpoints ends D).product
        (typedBondSecondEndpoints ends D),
        (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <=
      typedFKEventMass ends rho (typedFKConsistencyEvent ends D) :=
  typedFK_consistencyMass_ge_pair_nonconnection_product
    ends hrho0 hrho1 hZ D
    (typedBondFirstEndpoints ends D) (typedBondSecondEndpoints ends D)
    (typedBondEndpointDisconnections_subset_consistency ends hends D)



theorem typedFK_consistencyMass_ge_twoCut_product
    (ends : P -> V × V) (hends : forall p, (ends p).1 ≠ (ends p).2)
    {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho)
    (D B₁ B₂ : Finset P) (tau chi : V -> Bool)
    (hshift : multibondCut ends tau = D ∆ B₁)
    (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
    (∏ uv ∈ (typedBondVertices ends B₁).product
        (typedBondVertices ends B₂),
        (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <=
      typedFKEventMass ends rho (typedFKConsistencyEvent ends D) :=
  typedFK_consistencyMass_ge_pair_nonconnection_product
    ends hrho0 hrho1 hZ D
    (typedBondVertices ends B₁) (typedBondVertices ends B₂)
    (typedTwoCutDisconnections_subset_consistency
      ends hends D B₁ B₂ tau chi hshift hboundary)


theorem multibondIsing_twist_ratio_ge_pair_correlation_product
    (ends : P -> V × V) (J : P -> Real) (hJ : forall p, 0 <= J p)
    (D : Finset P) (upper lower : Finset V)
    (hgeometry :
      finiteEventInter (upper.product lower)
          (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆
        typedFKConsistencyEvent ends D) :
    (∏ uv ∈ upper.product lower,
        (1 - multibondIsingTwoPoint ends J uv.1 uv.2)) <=
      multibondIsingPartition ends (multibondTwistCoupling J D) /
        multibondIsingPartition ends J := by
  let rho := fun p => 1 - Real.exp (-2 * J p)
  have hrho0 : forall p, 0 <= rho p := by
    intro p
    dsimp [rho]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith [hJ p]))
  have hrho1 : forall p, rho p <= 1 := by
    intro p
    dsimp [rho]
    linarith [Real.exp_pos (-2 * J p)]
  have hZ : 0 < typedFKZ ends rho :=
    typedFKZ_pos_of_coupling ends J
  have hbound := typedFK_consistencyMass_ge_pair_nonconnection_product
    ends hrho0 hrho1 hZ D upper lower hgeometry
  rw [← multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass
    ends J D] at hbound
  simpa only [rho, typedFKTwoPoint_eq_multibondIsingTwoPoint] using hbound

theorem multibondIsingTwoPoint_nonneg_of_nonneg
    (ends : P -> V × V) (J : P -> Real) (hJ : forall p, 0 <= J p)
    (x y : V) :
    0 <= multibondIsingTwoPoint ends J x y := by
  let rho := fun p => 1 - Real.exp (-2 * J p)
  have hrho0 : forall p, 0 <= rho p := by
    intro p
    dsimp [rho]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith [hJ p]))
  have hrho1 : forall p, rho p <= 1 := by
    intro p
    dsimp [rho]
    linarith [Real.exp_pos (-2 * J p)]
  have hZ : 0 < typedFKZ ends rho := typedFKZ_pos_of_coupling ends J
  rw [← typedFKTwoPoint_eq_multibondIsingTwoPoint]
  exact typedFKEventMass_nonneg ends hrho0 hrho1 hZ
    (typedFKConnEvent ends x y)

theorem multibondIsingTwoPoint_le_one_of_nonneg
    (ends : P -> V × V) (J : P -> Real) (hJ : forall p, 0 <= J p)
    (x y : V) :
    multibondIsingTwoPoint ends J x y <= 1 := by
  let rho := fun p => 1 - Real.exp (-2 * J p)
  have hrho0 : forall p, 0 <= rho p := by
    intro p
    dsimp [rho]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith [hJ p]))
  have hrho1 : forall p, rho p <= 1 := by
    intro p
    dsimp [rho]
    linarith [Real.exp_pos (-2 * J p)]
  have hZ : 0 < typedFKZ ends rho := typedFKZ_pos_of_coupling ends J
  rw [← typedFKTwoPoint_eq_multibondIsingTwoPoint]
  calc
    typedFKTwoPoint ends rho x y =
        typedFKEventMass ends rho (typedFKConnEvent ends x y) := rfl
    _ <= typedFKEventMass ends rho Set.univ :=
      typedFKEventMass_mono ends hrho0 hrho1 hZ (Set.subset_univ _)
    _ = 1 := by
      unfold typedFKEventMass
      simp [typedFKProb_sum_eq_one ends rho hZ.ne']




theorem cubicalXYWilsonExpectation_ge_pair_correlation_product
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p)
    (upper lower : Finset (CubicalDualVertex a b c))
    (hgeometry :
      finiteEventInter (upper.product lower)
          (fun uv => typedFKDisconnEvent cubicalDualEnds uv.1 uv.2) ⊆
        typedFKConsistencyEvent cubicalDualEnds (cubicalXYSheet k)) :
    (∏ uv ∈ upper.product lower,
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  have hJ : forall p, 0 <= gaugeDualCoupling (K p) :=
    fun p => (gaugeDualCoupling_pos (hK p)).le
  have hbound := multibondIsing_twist_ratio_ge_pair_correlation_product
    cubicalDualEnds (fun p => gaugeDualCoupling (K p)) hJ
    (cubicalXYSheet k) upper lower hgeometry
  rw [cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio
    ha hb hc k K hK]
  exact hbound





def cubicalBelowSpin {a b c : Nat} (k : Fin (c + 1)) :
    CubicalDualVertex a b c -> Bool
  | none => false
  | some q => decide (q.z.val < k.val)

theorem cubicalXYSheet_subset_belowCut
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    cubicalXYSheet (a := a) (b := b) k ⊆
      multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalBelowSpin (a := a) (b := b) k) := by
  intro p hp
  obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hp
  rw [mem_multibondCut]
  cases hback : finBackward k with
  | none =>
      have hk0 : k = 0 := (finBackward_eq_none_iff k).mp hback
      exfalso
      rw [hk0] at hk
      simp at hk
  | some z =>
      have hkz : k = z.succ := (finBackward_eq_some_iff k z).mp hback
      have hz : z.val < k.val := by rw [hkz]; simp
      rw [cubicalDualEnds, hback]
      cases hforward : finForward k with
      | none => simp [cubicalBelowSpin, hz]
      | some w =>
          have heq : k = w.castSucc :=
            (finForward_eq_some_iff k w).mp hforward
          have hw : ¬ w.val < k.val := by rw [heq]; simp
          simp [cubicalBelowSpin, hz, hw]


def cubicalLowerComplementSurface {a b c : Nat} (k : Fin (c + 1)) :
    Finset (CubicalPlaquette a b c) :=
  multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
      (cubicalBelowSpin (a := a) (b := b) k) \
    cubicalXYSheet (a := a) (b := b) k

theorem belowCut_eq_sheet_union_complement
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalBelowSpin (a := a) (b := b) k) =
      cubicalXYSheet (a := a) (b := b) k ∪
        cubicalLowerComplementSurface (a := a) (b := b) k := by
  have hsub := cubicalXYSheet_subset_belowCut
    (a := a) (b := b) k hk
  ext p
  simp only [cubicalLowerComplementSurface, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalXYSheet k
    · exact Or.inl hD
    · exact Or.inr ⟨hp, hD⟩
  · rintro (hp | ⟨hp, _⟩)
    · exact hsub hp
    · exact hp

theorem belowCut_eq_sheet_symmDiff_complement
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalBelowSpin (a := a) (b := b) k) =
      cubicalXYSheet (a := a) (b := b) k ∆
        cubicalLowerComplementSurface (a := a) (b := b) k := by
  have hsub := cubicalXYSheet_subset_belowCut
    (a := a) (b := b) k hk
  ext p
  simp only [cubicalLowerComplementSurface, Finset.mem_symmDiff,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalXYSheet k
    · exact Or.inl ⟨hD, fun h => h.2 hD⟩
    · exact Or.inr ⟨⟨hp, hD⟩, hD⟩
  · rintro (⟨hp, _⟩ | ⟨⟨hp, _⟩, _⟩)
    · exact hsub hp
    · exact hp

def cubicalLowerComplementInnerVertices {a b c : Nat}
    (k : Fin (c + 1)) : Finset (CubicalDualVertex a b c) :=
  typedMarkedBondVertices
    (typedTrueEndpoint (cubicalDualEnds (a := a) (b := b) (c := c))
      (cubicalBelowSpin (a := a) (b := b) k))
    (cubicalLowerComplementSurface (a := a) (b := b) k)

def cubicalXYSheetUpperVertices {a b c : Nat}
    (k : Fin (c + 1)) : Finset (CubicalDualVertex a b c) :=
  typedMarkedBondVertices
    (typedFalseEndpoint (cubicalDualEnds (a := a) (b := b) (c := c))
      (cubicalBelowSpin (a := a) (b := b) k))
    (cubicalXYSheet (a := a) (b := b) k)

theorem cubicalLowerMarkedSurfaces_disjoint
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    Disjoint
      (cubicalLowerComplementInnerVertices (a := a) (b := b) k)
      (cubicalXYSheetUpperVertices (a := a) (b := b) k) := by
  apply typedMarkedOppositeSides_disjoint
    (cubicalDualEnds (a := a) (b := b) (c := c))
    (cubicalBelowSpin (a := a) (b := b) k)
    (cubicalLowerComplementSurface (a := a) (b := b) k)
    (cubicalXYSheet (a := a) (b := b) k)
  · intro p hp
    exact (Finset.mem_sdiff.mp hp).1
  · exact cubicalXYSheet_subset_belowCut (a := a) (b := b) k hk

theorem cubicalLowerSlab_pair_ne
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val)
    (uv : CubicalDualVertex a b c × CubicalDualVertex a b c)
    (huv : uv ∈
      (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
        (cubicalXYSheetUpperVertices (a := a) (b := b) k)) :
    uv.1 ≠ uv.2 := by
  have hmem := (Finset.mem_product.mp huv)
  have hdisj := Finset.disjoint_left.mp
    (cubicalLowerMarkedSurfaces_disjoint (a := a) (b := b) k hk)
  intro heq
  exact hdisj hmem.1 (heq ▸ hmem.2)



theorem cubicalXYSheetUpperVertices_eq_layer
    {a b c : Nat} (k : Fin (c + 1))
    (hk : 0 < k.val) (hkTop : k.val < c) :
    cubicalXYSheetUpperVertices (a := a) (b := b) k =
      (Finset.univ : Finset (Fin a × Fin b)).image
        (fun ij => some (CubicalCell.mk ij.1 ij.2 ⟨k.val, hkTop⟩)) := by
  let w : Fin c := ⟨k.val, hkTop⟩
  have hforward : finForward k = some w := by
    rw [finForward_eq_some_iff]
    apply Fin.ext
    rfl
  cases hback : finBackward k with
  | none =>
      have hk0 : k = 0 := (finBackward_eq_none_iff k).mp hback
      rw [hk0] at hk
      simp at hk
  | some z =>
      have hkz : k = z.succ := (finBackward_eq_some_iff k z).mp hback
      have hz : z.val < k.val := by rw [hkz]; simp
      have hmark : forall ij : Fin a × Fin b,
          typedFalseEndpoint
              (cubicalDualEnds (a := a) (b := b) (c := c))
              (cubicalBelowSpin (a := a) (b := b) k)
              (CubicalPlaquette.xy ij.1 ij.2 k) =
            some (CubicalCell.mk ij.1 ij.2 w) := by
        intro ij
        simp [typedFalseEndpoint, cubicalDualEnds, cubicalBelowSpin,
          hback, hforward, hz]
      unfold cubicalXYSheetUpperVertices typedMarkedBondVertices cubicalXYSheet
      rw [Finset.image_image]
      apply Finset.image_congr
      intro ij _
      exact hmark ij




theorem cubicalLowerSlabDisconnections_subset_consistency
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val) :
    finiteEventInter
        ((cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k))
        (fun uv => typedFKDisconnEvent
          (cubicalDualEnds (a := a) (b := b) (c := c)) uv.1 uv.2) ⊆
      typedFKConsistencyEvent
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalXYSheet (a := a) (b := b) k) := by
  apply typedTwoCutMarkedDisconnections_subset_consistency
    cubicalDualEnds (cubicalDualEnds_ne ha hb hc)
    (cubicalXYSheet k) (cubicalLowerComplementSurface k)
    (cubicalXYSheet k) (cubicalBelowSpin k) (cubicalBelowSpin k)
  · exact belowCut_eq_sheet_symmDiff_complement k hk
  · rw [Finset.union_comm]
    exact belowCut_eq_sheet_union_complement k hk


theorem cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val)
    (K : CubicalPlaquette a b c -> Real) (hK : forall p, 0 < K p) :
    (∏ uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k),
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  apply cubicalXYWilsonExpectation_ge_pair_correlation_product
    ha hb hc k K hK
  exact cubicalLowerSlabDisconnections_subset_consistency ha hb hc k hk


theorem cubicalXYWilson_perimeterLower_of_lowerSlab_sum
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val)
    (K : CubicalPlaquette a b c -> Real) (hK : forall p, 0 < K p)
    {R C perimeter : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (hR : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k) ->
      multibondIsingTwoPoint cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= R)
    (hsum :
      (∑ uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k),
        multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <=
        C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  let s :=
    (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
      (cubicalXYSheetUpperVertices (a := a) (b := b) k)
  let corr : CubicalDualVertex a b c × CubicalDualVertex a b c -> Real :=
    fun uv => multibondIsingTwoPoint cubicalDualEnds
      (fun p => gaugeDualCoupling (K p)) uv.1 uv.2
  have hJ : forall p, 0 <= gaugeDualCoupling (K p) :=
    fun p => (gaugeDualCoupling_pos (hK p)).le
  apply gauge_perimeterLaw_of_product_and_sum_bounds hR0 hR1 s corr
  · intro uv _
    exact multibondIsingTwoPoint_nonneg_of_nonneg
      cubicalDualEnds (fun p => gaugeDualCoupling (K p)) hJ uv.1 uv.2
  · exact hR
  · exact cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product
      ha hb hc k hk K hK
  · exact hsum




theorem cubicalXYWilson_perimeterLower_of_lowerSlab_exponential
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val)
    (K : CubicalPlaquette a b c -> Real) (hK : forall p, 0 < K p)
    (decay C perimeter : Real) (hdecay : 0 < decay)
    (separation :
      CubicalDualVertex a b c × CubicalDualVertex a b c -> Real)
    (hsep : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k) ->
      1 <= separation uv)
    (hcorr : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k) ->
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
        Real.exp (-decay * separation uv))
    (hsumExp :
      (∑ uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k),
        Real.exp (-decay * separation uv)) <= C * perimeter) :
    Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) * C) * perimeter) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  apply cubicalXYWilson_perimeterLower_of_lowerSlab_sum
    ha hb hc k hk K hK (Real.exp_pos _) (by
      rw [Real.exp_lt_one_iff]
      linarith)
  · intro uv huv
    calc
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
          Real.exp (-decay * separation uv) := hcorr uv huv
      _ <= Real.exp (-decay) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsep uv huv]
  · have hsumCorr :
        (∑ uv ∈
          (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
            (cubicalXYSheetUpperVertices (a := a) (b := b) k),
          multibondIsingTwoPoint cubicalDualEnds
            (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <=
          ∑ uv ∈
            (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
              (cubicalXYSheetUpperVertices (a := a) (b := b) k),
            Real.exp (-decay * separation uv) := by
        exact Finset.sum_le_sum (fun uv huv => hcorr uv huv)
    exact hsumCorr.trans hsumExp



theorem cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p) :
    (∏ uv ∈
        (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product
          (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)),
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  apply cubicalXYWilsonExpectation_ge_pair_correlation_product
    ha hb hc k K hK
  exact typedBondEndpointDisconnections_subset_consistency
    cubicalDualEnds (cubicalDualEnds_ne ha hb hc) (cubicalXYSheet k)




theorem cubicalXYWilson_perimeterLower_of_sheetEndpoint_sum
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p)
    {R C perimeter : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (hR : forall uv, uv ∈
        (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product
          (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)) ->
      multibondIsingTwoPoint cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= R)
    (hsum :
      (∑ uv ∈
        (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product
          (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)),
        multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <=
        C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  let s : Finset
      (CubicalDualVertex a b c × CubicalDualVertex a b c) :=
    (typedBondFirstEndpoints
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalXYSheet (a := a) (b := b) (c := c) k)).product
      (typedBondSecondEndpoints
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalXYSheet (a := a) (b := b) (c := c) k))
  let corr : CubicalDualVertex a b c × CubicalDualVertex a b c -> Real :=
    fun uv => multibondIsingTwoPoint cubicalDualEnds
      (fun p => gaugeDualCoupling (K p)) uv.1 uv.2
  have hJ : forall p, 0 <= gaugeDualCoupling (K p) :=
    fun p => (gaugeDualCoupling_pos (hK p)).le
  apply gauge_perimeterLaw_of_product_and_sum_bounds
    hR0 hR1 s corr
  · intro uv _
    exact multibondIsingTwoPoint_nonneg_of_nonneg
      cubicalDualEnds (fun p => gaugeDualCoupling (K p)) hJ uv.1 uv.2
  · exact hR
  · exact cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product
      ha hb hc k K hK
  · exact hsum

end

end StatMech.FrontierA
