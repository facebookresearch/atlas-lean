/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeWilsonFreeEnergy
import Code.FK.FKG
import Code.FK.EdwardsSokal

open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def TypedSignedCompatible (ends : P -> V × V) (D : Finset P)
    (omega : P -> Bool) (sigma : V -> Bool) : Prop :=
  forall p, omega p = true ->
    (sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D)

instance typedSignedCompatibleDecidable (ends : P -> V × V) (D : Finset P)
    (omega : P -> Bool) (sigma : V -> Bool) :
    Decidable (TypedSignedCompatible ends D omega sigma) := by
  unfold TypedSignedCompatible
  infer_instance


def typedESEdgeFactor (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (p : P) (b : Bool) : Real :=
  if b then
    rho p * if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1 else 0
  else 1 - rho p


def typedESWeight (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (omega : P -> Bool) : Real :=
  ∏ p : P, typedESEdgeFactor ends rho D sigma p (omega p)


def typedESZ (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) : Real :=
  ∑ omega : P -> Bool, ∑ sigma : V -> Bool,
    typedESWeight ends rho D sigma omega

theorem typedESWeight_sum_omega (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) :
    (∑ omega : P -> Bool, typedESWeight ends rho D sigma omega) =
      ∏ p : P, ∑ b : Bool, typedESEdgeFactor ends rho D sigma p b := by
  unfold typedESWeight
  exact (Fintype.prod_sum _).symm

theorem typedESEdgeFactor_sum_bool (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (p : P) :
    (∑ b : Bool, typedESEdgeFactor ends rho D sigma p b) =
      if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1 else 1 - rho p := by
  rw [Fintype.sum_bool]
  unfold typedESEdgeFactor
  by_cases h : sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D
  · simp [h]
  · simp [h]

theorem typedESWeight_sum_omega_eq_shiftedCut
    (ends : P -> V × V) (J : P -> Real) (D : Finset P)
    (sigma : V -> Bool) :
    (∑ omega : P -> Bool,
      typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) D sigma omega) =
      ∏ p ∈ multibondCut ends sigma ∆ D, Real.exp (-2 * J p) := by
  rw [typedESWeight_sum_omega]
  simp_rw [typedESEdgeFactor_sum_bool]
  have hpoint : forall p : P,
      (if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1
        else 1 - (1 - Real.exp (-2 * J p))) =
      if p ∈ multibondCut ends sigma ∆ D then Real.exp (-2 * J p) else 1 := by
    intro p
    by_cases hs : sigma (ends p).1 = sigma (ends p).2 <;>
      by_cases hD : p ∈ D <;>
      simp [multibondCut, hs, hD, Finset.mem_symmDiff]
  simp_rw [hpoint]
  rw [Finset.prod_ite_mem]
  simp



theorem multibondIsingPartition_twist_eq_exp_mul_typedESZ
    (ends : P -> V × V) (J : P -> Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) =
      Real.exp (∑ p : P, J p) *
        typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) D := by
  unfold multibondIsingPartition typedESZ
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [multibondIsingWeight_twist_eq_shiftedActivity]
  congr 1
  exact (typedESWeight_sum_omega_eq_shiftedCut ends J D sigma).symm




def typedESActivity (rho : P -> Real) (omega : P -> Bool) : Real :=
  ∏ p : P, if omega p then rho p else 1 - rho p

theorem typedESWeight_factor (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (omega : P -> Bool) :
    typedESWeight ends rho D sigma omega =
      typedESActivity rho omega *
        (if TypedSignedCompatible ends D omega sigma then 1 else 0) := by
  unfold typedESWeight typedESActivity
  by_cases hcompat : TypedSignedCompatible ends D omega sigma
  · rw [if_pos hcompat]
    simp only [mul_one]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : omega p
    · have hrel := hcompat p (by simpa using hp)
      simp [typedESEdgeFactor, hp, hrel]
    · simp [typedESEdgeFactor, hp]
  · rw [if_neg hcompat, mul_zero]
    classical
    simp only [TypedSignedCompatible] at hcompat
    push Not at hcompat
    obtain ⟨p, hp⟩ := hcompat
    rw [Finset.prod_eq_zero_iff]
    refine ⟨p, Finset.mem_univ p, ?_⟩
    have hrel : ¬ (sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D) := by
      rcases hp.2 with ⟨heq, hD⟩ | ⟨hne, hnotD⟩
      · simp [heq, hD]
      · simp [hne, hnotD]
    simp [typedESEdgeFactor, hp.1, hrel]


def typedSpinXor (sigma tau : V -> Bool) : V -> Bool :=
  fun v => (sigma v).xor (tau v)

theorem bool_xor_eq_xor_iff_eq_iff_eq (a b c d : Bool) :
    (a.xor c = b.xor d) <-> ((a = b) <-> (c = d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem typedSpinXor_cancel_right (sigma tau : V -> Bool) :
    typedSpinXor (typedSpinXor sigma tau) tau = sigma := by
  funext v
  simp [typedSpinXor]



def typedSignedCompatibleEquiv (ends : P -> V × V) (D : Finset P)
    (omega : P -> Bool) (witness : V -> Bool)
    (hw : TypedSignedCompatible ends D omega witness) :
    {sigma : V -> Bool // TypedSignedCompatible ends D omega sigma} ≃
      {tau : V -> Bool // TypedSignedCompatible ends ∅ omega tau} where
  toFun sigma := ⟨typedSpinXor sigma.1 witness, by
    intro p hp
    have hs := sigma.2 p hp
    have hwe := hw p hp
    have heq :
        (sigma.1 (ends p).1 = sigma.1 (ends p).2) <->
          (witness (ends p).1 = witness (ends p).2) :=
      hs.trans hwe.symm
    constructor
    · intro _
      simp
    · intro _
      exact (bool_xor_eq_xor_iff_eq_iff_eq
        (sigma.1 (ends p).1) (sigma.1 (ends p).2)
        (witness (ends p).1) (witness (ends p).2)).2 heq⟩
  invFun tau := ⟨typedSpinXor tau.1 witness, by
    intro p hp
    have ht : tau.1 (ends p).1 = tau.1 (ends p).2 :=
      (tau.2 p hp).2 (by simp)
    have hwe := hw p hp
    change
      ((tau.1 (ends p).1).xor (witness (ends p).1) =
        (tau.1 (ends p).2).xor (witness (ends p).2)) <-> p ∉ D
    rw [bool_xor_eq_xor_iff_eq_iff_eq]
    simpa [ht] using hwe⟩
  left_inv sigma := by
    apply Subtype.ext
    exact typedSpinXor_cancel_right sigma.1 witness
  right_inv tau := by
    apply Subtype.ext
    exact typedSpinXor_cancel_right tau.1 witness

theorem typedESWeight_sum_sigma_eq_activity_mul_card
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    (omega : P -> Bool) :
    (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) =
      typedESActivity rho omega *
        ((Finset.univ.filter
          (TypedSignedCompatible ends D omega)).card : Real) := by
  simp_rw [typedESWeight_factor]
  rw [← Finset.mul_sum, Finset.sum_boole]

theorem typedESWeight_sum_sigma_signed_eq_ordinary_of_witness
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    (omega : P -> Bool) (witness : V -> Bool)
    (hw : TypedSignedCompatible ends D omega witness) :
    (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) =
      ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega := by
  rw [typedESWeight_sum_sigma_eq_activity_mul_card,
    typedESWeight_sum_sigma_eq_activity_mul_card]
  congr 1
  norm_cast
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (typedSignedCompatibleEquiv ends D omega witness hw)


def typedFKConsistencyEvent (ends : P -> V × V) (D : Finset P) :
    Set (P -> Bool) :=
  {omega | exists sigma : V -> Bool,
    TypedSignedCompatible ends D omega sigma}

instance typedFKConsistencyEventDecidable (ends : P -> V × V)
    (D : Finset P) (omega : P -> Bool) :
    Decidable (omega ∈ typedFKConsistencyEvent ends D) :=
  Classical.propDecidable _

theorem typedESWeight_sum_sigma_signed_eq_indicator
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    (omega : P -> Bool) :
    (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) =
      if omega ∈ typedFKConsistencyEvent ends D then
        ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega
      else 0 := by
  classical
  by_cases h : omega ∈ typedFKConsistencyEvent ends D
  · rw [if_pos h]
    obtain ⟨witness, hw⟩ := h
    exact typedESWeight_sum_sigma_signed_eq_ordinary_of_witness
      ends rho D omega witness hw
  · rw [if_neg h]
    rw [typedESWeight_sum_sigma_eq_activity_mul_card]
    have hnone : forall sigma : V -> Bool,
        ¬ TypedSignedCompatible ends D omega sigma := by
      intro sigma hsigma
      exact h ⟨sigma, hsigma⟩
    simp [hnone]





def typedFKWeight (ends : P -> V × V) (rho : P -> Real)
    (omega : P -> Bool) : Real :=
  ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega

def typedFKZ (ends : P -> V × V) (rho : P -> Real) : Real :=
  ∑ omega : P -> Bool, typedFKWeight ends rho omega

def typedFKProb (ends : P -> V × V) (rho : P -> Real)
    (omega : P -> Bool) : Real :=
  typedFKWeight ends rho omega / typedFKZ ends rho

def typedFKEventMass (ends : P -> V × V) (rho : P -> Real)
    (A : Set (P -> Bool)) : Real :=
  ∑ omega : P -> Bool,
    typedFKProb ends rho omega * A.indicator (fun _ => (1 : Real)) omega

theorem typedFKZ_eq_typedESZ_empty (ends : P -> V × V) (rho : P -> Real) :
    typedFKZ ends rho = typedESZ ends rho ∅ := rfl

theorem typedESZ_eq_typedFKWeight_filter
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P) :
    typedESZ ends rho D =
      ∑ omega : P -> Bool,
        typedFKWeight ends rho omega *
          (typedFKConsistencyEvent ends D).indicator
            (fun _ => (1 : Real)) omega := by
  unfold typedESZ typedFKWeight
  apply Finset.sum_congr rfl
  intro omega _
  rw [typedESWeight_sum_sigma_signed_eq_indicator]
  by_cases h : omega ∈ typedFKConsistencyEvent ends D
  · simp [h]
  · simp [h]

theorem typedFKZ_pos_of_coupling (ends : P -> V × V) (J : P -> Real) :
    0 < typedFKZ ends (fun p => 1 - Real.exp (-2 * J p)) := by
  have hpart := multibondIsingPartition_twist_eq_exp_mul_typedESZ
    ends J (∅ : Finset P)
  have hprod : 0 < Real.exp (∑ p : P, J p) *
      typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) ∅ := by
    rw [← hpart]
    simpa [multibondTwistCoupling] using multibondIsingPartition_pos ends J
  have hexp : 0 < Real.exp (∑ p : P, J p) := Real.exp_pos _
  have hZ : 0 < typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) ∅ := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact (not_lt_of_ge hexp.le h.1).elim
  simpa [typedFKZ_eq_typedESZ_empty] using hZ

theorem typedFKProb_nonneg_of_nonneg
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) (omega : P -> Bool) :
    0 <= typedFKProb ends rho omega := by
  apply div_nonneg
  · unfold typedFKWeight
    apply Finset.sum_nonneg
    intro sigma _
    unfold typedESWeight typedESEdgeFactor
    apply Finset.prod_nonneg
    intro p _
    by_cases hp : omega p
    · by_cases heq : sigma (ends p).1 = sigma (ends p).2
      · simp [hp, heq, hrho0 p]
      · simp [hp, heq]
    · have hpfalse : omega p = false := Bool.eq_false_of_not_eq_true hp
      simp [hpfalse, sub_nonneg.mpr (hrho1 p)]
  · exact hZ.le

theorem typedFKProb_sum_eq_one
    (ends : P -> V × V) (rho : P -> Real)
    (hZ : typedFKZ ends rho ≠ 0) :
    (∑ omega : P -> Bool, typedFKProb ends rho omega) = 1 := by
  unfold typedFKProb
  rw [← Finset.sum_div]
  change typedFKZ ends rho / typedFKZ ends rho = 1
  exact div_self hZ

theorem typedESZ_div_eq_consistencyMass
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    :
    typedESZ ends rho D / typedESZ ends rho ∅ =
      typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
  rw [typedESZ_eq_typedFKWeight_filter]
  unfold typedFKEventMass typedFKProb
  rw [typedFKZ_eq_typedESZ_empty]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro omega _
  ring





theorem multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass
    (ends : P -> V × V) (J : P -> Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) /
        multibondIsingPartition ends J =
      typedFKEventMass ends (fun p => 1 - Real.exp (-2 * J p))
        (typedFKConsistencyEvent ends D) := by
  let rho := fun p => 1 - Real.exp (-2 * J p)
  have hnum := multibondIsingPartition_twist_eq_exp_mul_typedESZ ends J D
  have hden0 := multibondIsingPartition_twist_eq_exp_mul_typedESZ
    ends J (∅ : Finset P)
  have hden : multibondIsingPartition ends J =
      Real.exp (∑ p : P, J p) * typedESZ ends rho ∅ := by
    simpa [rho, multibondTwistCoupling] using hden0
  rw [hnum, hden]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  exact typedESZ_div_eq_consistencyMass ends rho D



theorem cubicalXYWilsonExpectation_eq_typedFKConsistencyMass
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      typedFKEventMass cubicalDualEnds
        (fun p => 1 - Real.exp (-2 * gaugeDualCoupling (K p)))
        (typedFKConsistencyEvent cubicalDualEnds (cubicalXYSheet k)) := by
  rw [cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio
    ha hb hc k K hK]
  exact multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass
    cubicalDualEnds (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k)






def typedOpenGraph (ends : P -> V × V) (omega : P -> Bool) :
    SimpleGraph V where
  Adj x y := exists p : P, omega p = true ∧
    ((x = (ends p).1 ∧ y = (ends p).2) ∨
      (x = (ends p).2 ∧ y = (ends p).1)) ∧ x ≠ y
  symm := by
    rintro x y ⟨p, hp, hxy, hne⟩
    refine ⟨p, hp, ?_, hne.symm⟩
    rcases hxy with hxy | hxy
    · exact Or.inr ⟨hxy.2, hxy.1⟩
    · exact Or.inl ⟨hxy.2, hxy.1⟩
  loopless := ⟨fun x hx => by
    obtain ⟨p, hp, hxy, hne⟩ := hx
    exact hne rfl⟩

noncomputable instance typedOpenGraphDecidableRel
    (ends : P -> V × V) (omega : P -> Bool) :
    DecidableRel (typedOpenGraph ends omega).Adj :=
  Classical.decRel _

def typedNumClusters (ends : P -> V × V) (omega : P -> Bool) : Nat :=
  Nat.card (typedOpenGraph ends omega).ConnectedComponent

theorem typedOpenGraph_sup (ends : P -> V × V) (a b : P -> Bool) :
    typedOpenGraph ends (a ⊔ b) =
      typedOpenGraph ends a ⊔ typedOpenGraph ends b := by
  ext x y
  simp only [typedOpenGraph, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨p, hp, hxy, hne⟩
    change (a p || b p) = true at hp
    rw [Bool.or_eq_true] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨p, hp, hxy, hne⟩
    · exact Or.inr ⟨p, hp, hxy, hne⟩
  · rintro (⟨p, hp, hxy, hne⟩ | ⟨p, hp, hxy, hne⟩)
    · refine ⟨p, ?_, hxy, hne⟩
      change (a p || b p) = true
      rw [Bool.or_eq_true]
      exact Or.inl hp
    · refine ⟨p, ?_, hxy, hne⟩
      change (a p || b p) = true
      rw [Bool.or_eq_true]
      exact Or.inr hp

theorem typedOpenGraph_inf_le (ends : P -> V × V) (a b : P -> Bool) :
    typedOpenGraph ends (a ⊓ b) <=
      typedOpenGraph ends a ⊓ typedOpenGraph ends b := by
  intro x y
  simp only [typedOpenGraph, SimpleGraph.inf_adj]
  rintro ⟨p, hp, hxy, hne⟩
  change (a p && b p) = true at hp
  rw [Bool.and_eq_true] at hp
  obtain ⟨ha, hb⟩ := hp
  exact ⟨⟨p, ha, hxy, hne⟩, ⟨p, hb, hxy, hne⟩⟩

theorem typedNumClusters_supermodular (ends : P -> V × V)
    (a b : P -> Bool) :
    typedNumClusters ends a + typedNumClusters ends b <=
      typedNumClusters ends (a ⊔ b) + typedNumClusters ends (a ⊓ b) := by
  have hsub := FK.card_connectedComponent_submodular
    (typedOpenGraph ends a) (typedOpenGraph ends b)
  have hmeet : Nat.card
      (typedOpenGraph ends a ⊓ typedOpenGraph ends b).ConnectedComponent <=
      Nat.card (typedOpenGraph ends (a ⊓ b)).ConnectedComponent :=
    SimpleGraph.ConnectedComponent.card_le_card_of_le
      (typedOpenGraph_inf_le ends a b)
  have h :
      Nat.card (typedOpenGraph ends a).ConnectedComponent +
          Nat.card (typedOpenGraph ends b).ConnectedComponent <=
        Nat.card (typedOpenGraph ends a ⊔
          typedOpenGraph ends b).ConnectedComponent +
          Nat.card (typedOpenGraph ends (a ⊓ b)).ConnectedComponent := by
    omega
  rw [← typedOpenGraph_sup ends a b] at h
  simpa [typedNumClusters] using h

theorem typedSignedCompatible_empty_iff_graphConstant
    (ends : P -> V × V) (omega : P -> Bool) (sigma : V -> Bool) :
    TypedSignedCompatible ends ∅ omega sigma <->
      forall x y, (typedOpenGraph ends omega).Adj x y -> sigma x = sigma y := by
  constructor
  · intro h x y hxy
    obtain ⟨p, hp, hends, hne⟩ := hxy
    have heq : sigma (ends p).1 = sigma (ends p).2 := (h p hp).2 (by simp)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact heq
    · exact heq.symm
  · intro h p hp
    constructor
    · intro _
      simp
    · intro _
      by_cases hends : (ends p).1 = (ends p).2
      · rw [hends]
      · apply h (ends p).1 (ends p).2
        exact ⟨p, hp, Or.inl ⟨rfl, rfl⟩, hends⟩



noncomputable def typedConstOnOpenEquiv
    (ends : P -> V × V) (omega : P -> Bool) :
    ((typedOpenGraph ends omega).ConnectedComponent -> Bool) ≃
      {sigma : V -> Bool // TypedSignedCompatible ends ∅ omega sigma} where
  toFun tau := ⟨fun v => tau ((typedOpenGraph ends omega).connectedComponentMk v), by
    rw [typedSignedCompatible_empty_iff_graphConstant]
    intro x y hxy
    congr 1
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  invFun sigma := SimpleGraph.ConnectedComponent.lift sigma.1 (by
    intro v w path hpath
    clear hpath
    have hc := (typedSignedCompatible_empty_iff_graphConstant
      ends omega sigma.1).mp sigma.2
    induction path with
    | nil => rfl
    | @cons u v z huv p ih =>
        exact (hc u v huv).trans ih)
  left_inv tau := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv sigma := by
    apply Subtype.ext
    funext v
    rfl

theorem card_typedSignedCompatible_empty
    (ends : P -> V × V) (omega : P -> Bool) :
    Nat.card {sigma : V -> Bool // TypedSignedCompatible ends ∅ omega sigma} =
      2 ^ typedNumClusters ends omega := by
  classical
  rw [Nat.card_congr (typedConstOnOpenEquiv ends omega).symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]
  simp [typedNumClusters, Nat.card_eq_fintype_card]

theorem typedFKWeight_eq_activity_mul_clusters
    (ends : P -> V × V) (rho : P -> Real) (omega : P -> Bool) :
    typedFKWeight ends rho omega =
      typedESActivity rho omega * (2 : Real) ^ typedNumClusters ends omega := by
  unfold typedFKWeight
  rw [typedESWeight_sum_sigma_eq_activity_mul_card]
  congr 1
  have hcard := card_typedSignedCompatible_empty ends omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
  rw [hcard]
  push_cast
  rfl

theorem typedESActivity_logModular (rho : P -> Real) (a b : P -> Bool) :
    typedESActivity rho a * typedESActivity rho b =
      typedESActivity rho (a ⊔ b) * typedESActivity rho (a ⊓ b) := by
  unfold typedESActivity
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  cases ha : a p <;> cases hb : b p <;>
    simp [ha, hb, mul_comm]

theorem typedFKWeight_logSupermodular
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (a b : P -> Bool) :
    typedFKWeight ends rho a * typedFKWeight ends rho b <=
      typedFKWeight ends rho (a ⊔ b) * typedFKWeight ends rho (a ⊓ b) := by
  have hcluster :
      (2 : Real) ^ typedNumClusters ends a *
          (2 : Real) ^ typedNumClusters ends b <=
        (2 : Real) ^ typedNumClusters ends (a ⊔ b) *
          (2 : Real) ^ typedNumClusters ends (a ⊓ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num)
      (typedNumClusters_supermodular ends a b)
  have hactivity := typedESActivity_logModular rho a b
  have hnonneg : 0 <= typedESActivity rho a * typedESActivity rho b := by
    apply mul_nonneg
    · unfold typedESActivity
      apply Finset.prod_nonneg
      intro p _
      cases hp : a p <;> simp [hrho0 p, sub_nonneg.mpr (hrho1 p)]
    · unfold typedESActivity
      apply Finset.prod_nonneg
      intro p _
      cases hp : b p <;> simp [hrho0 p, sub_nonneg.mpr (hrho1 p)]
  simp_rw [typedFKWeight_eq_activity_mul_clusters]
  calc
    (typedESActivity rho a * 2 ^ typedNumClusters ends a) *
        (typedESActivity rho b * 2 ^ typedNumClusters ends b) =
      (typedESActivity rho a * typedESActivity rho b) *
        (2 ^ typedNumClusters ends a * 2 ^ typedNumClusters ends b) := by ring
    _ <= (typedESActivity rho a * typedESActivity rho b) *
        (2 ^ typedNumClusters ends (a ⊔ b) *
          2 ^ typedNumClusters ends (a ⊓ b)) :=
      mul_le_mul_of_nonneg_left hcluster hnonneg
    _ = (typedESActivity rho (a ⊔ b) *
          2 ^ typedNumClusters ends (a ⊔ b)) *
        (typedESActivity rho (a ⊓ b) *
          2 ^ typedNumClusters ends (a ⊓ b)) := by rw [hactivity]; ring




theorem typedFKProb_FKGLatticeCondition
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) :
    FKGLatticeCondition (typedFKProb ends rho) := by
  intro a b
  simp only [typedFKProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (typedFKWeight_logSupermodular ends hrho0 hrho1 a b)


theorem typedFKProb_positively_associated
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho)
    {f g : (P -> Bool) -> Real} (hf : Monotone f) (hg : Monotone g) :
    (∑ omega, typedFKProb ends rho omega * f omega) *
        (∑ omega, typedFKProb ends rho omega * g omega) <=
      ∑ omega, typedFKProb ends rho omega * (f omega * g omega) := by
  exact fkg_inequality
    (fun omega => typedFKProb_nonneg_of_nonneg
      ends hrho0 hrho1 hZ omega)
    (typedFKProb_sum_eq_one ends rho hZ.ne')
    (typedFKProb_FKGLatticeCondition ends hrho0 hrho1 hZ) hf hg


theorem typedFKProb_positively_associated_events
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho)
    {A B : Set (P -> Bool)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    typedFKEventMass ends rho A * typedFKEventMass ends rho B <=
      typedFKEventMass ends rho (A ∩ B) := by
  exact fkg_inequality_events
    (fun omega => typedFKProb_nonneg_of_nonneg
      ends hrho0 hrho1 hZ omega)
    (typedFKProb_sum_eq_one ends rho hZ.ne')
    (typedFKProb_FKGLatticeCondition ends hrho0 hrho1 hZ) hA hB


theorem typedOpenGraph_mono (ends : P -> V × V)
    {a b : P -> Bool} (hab : a <= b) :
    typedOpenGraph ends a <= typedOpenGraph ends b := by
  intro x y hxy
  obtain ⟨p, hp, hends, hne⟩ := hxy
  have hbp : b p = true := by
    have := hab p
    rw [hp] at this
    cases hbp : b p
    · exfalso
      rw [hbp] at this
      exact (by decide : ¬ (true : Bool) <= false) this
    · rfl
  exact ⟨p, hbp, hends, hne⟩


def typedFKConnEvent (ends : P -> V × V) (x y : V) :
    Set (P -> Bool) :=
  {omega | (typedOpenGraph ends omega).Reachable x y}

instance typedFKConnEventDecidable (ends : P -> V × V) (x y : V)
    (omega : P -> Bool) : Decidable (omega ∈ typedFKConnEvent ends x y) :=
  Classical.propDecidable _

theorem typedFKConnEvent_isIncreasing (ends : P -> V × V) (x y : V) :
    IsIncreasing (typedFKConnEvent ends x y) := by
  intro a b hab ha
  exact ha.mono (typedOpenGraph_mono ends hab)


def typedFKDisconnEvent (ends : P -> V × V) (x y : V) :
    Set (P -> Bool) :=
  (typedFKConnEvent ends x y)ᶜ

theorem typedFKDisconnEvent_isDecreasing
    (ends : P -> V × V) (x y : V) :
    IsDecreasing (typedFKDisconnEvent ends x y) :=
  (typedFKConnEvent_isIncreasing ends x y).compl


def typedFKTwoPoint (ends : P -> V × V) (rho : P -> Real)
    (x y : V) : Real :=
  typedFKEventMass ends rho (typedFKConnEvent ends x y)




def typedSpinProduct (sigma : V -> Bool) (x y : V) : Real :=
  if sigma x = sigma y then 1 else -1


def typedSpinXorEquiv (tau : V -> Bool) :
    (V -> Bool) ≃ (V -> Bool) where
  toFun sigma := typedSpinXor sigma tau
  invFun sigma := typedSpinXor sigma tau
  left_inv sigma := typedSpinXor_cancel_right sigma tau
  right_inv sigma := typedSpinXor_cancel_right sigma tau

theorem typedSignedCompatible_empty_eq_of_reachable
    (ends : P -> V × V) (omega : P -> Bool) (sigma : V -> Bool)
    (hsigma : TypedSignedCompatible ends ∅ omega sigma)
    {x y : V} (hxy : (typedOpenGraph ends omega).Reachable x y) :
    sigma x = sigma y := by
  have hadj := (typedSignedCompatible_empty_iff_graphConstant
    ends omega sigma).mp hsigma
  obtain ⟨path⟩ := hxy
  induction path with
  | nil => rfl
  | @cons u v z huv path ih => exact (hadj u v huv).trans ih



def typedReachabilitySpin (ends : P -> V × V) (omega : P -> Bool)
    (x : V) : V -> Bool :=
  fun v => decide ((typedOpenGraph ends omega).Reachable x v)

theorem typedReachabilitySpin_compatible
    (ends : P -> V × V) (omega : P -> Bool) (x : V) :
    TypedSignedCompatible ends ∅ omega
      (typedReachabilitySpin ends omega x) := by
  intro p hp
  have hagree : typedReachabilitySpin ends omega x (ends p).1 =
      typedReachabilitySpin ends omega x (ends p).2 := by
    by_cases heq : (ends p).1 = (ends p).2
    · rw [heq]
    · have hadj : (typedOpenGraph ends omega).Adj
          (ends p).1 (ends p).2 :=
        ⟨p, hp, Or.inl ⟨rfl, rfl⟩, heq⟩
      have huv := hadj.reachable
      by_cases hu : (typedOpenGraph ends omega).Reachable x (ends p).1
      · have hv := hu.trans huv
        simp [typedReachabilitySpin, hu, hv]
      · have hv : ¬ (typedOpenGraph ends omega).Reachable x (ends p).2 :=
          fun hv => hu (hv.trans huv.symm)
        simp [typedReachabilitySpin, hu, hv]
  simpa using hagree

theorem typedSignedCompatible_empty_xor_iff
    (ends : P -> V × V) (omega : P -> Bool)
    (sigma tau : V -> Bool)
    (htau : TypedSignedCompatible ends ∅ omega tau) :
    TypedSignedCompatible ends ∅ omega (typedSpinXor sigma tau) <->
      TypedSignedCompatible ends ∅ omega sigma := by
  have preserve : forall s : V -> Bool,
      TypedSignedCompatible ends ∅ omega s ->
      TypedSignedCompatible ends ∅ omega (typedSpinXor s tau) := by
    intro s hs p hp
    have hse : s (ends p).1 = s (ends p).2 := (hs p hp).2 (by simp)
    have hte : tau (ends p).1 = tau (ends p).2 :=
      (htau p hp).2 (by simp)
    simp [typedSpinXor, hse, hte]
  constructor
  · intro hs
    have h := preserve (typedSpinXor sigma tau) hs
    rwa [typedSpinXor_cancel_right] at h
  · exact preserve sigma


theorem typedSignedCompatible_xor_iff_symmDiff_cut
    (ends : P -> V × V) (D : Finset P) (omega : P -> Bool)
    (sigma tau : V -> Bool) :
    TypedSignedCompatible ends D omega (typedSpinXor sigma tau) <->
      TypedSignedCompatible ends (D ∆ multibondCut ends tau) omega sigma := by
  constructor <;> intro h p hp
  · have hh := h p hp
    change (((sigma (ends p).1).xor (tau (ends p).1) =
      (sigma (ends p).2).xor (tau (ends p).2)) <-> p ∉ D) at hh
    rw [bool_xor_eq_xor_iff_eq_iff_eq] at hh
    simp only [Finset.mem_symmDiff, mem_multibondCut]
    tauto
  · have hh := h p hp
    simp only [Finset.mem_symmDiff, mem_multibondCut] at hh
    change (((sigma (ends p).1).xor (tau (ends p).1) =
      (sigma (ends p).2).xor (tau (ends p).2)) <-> p ∉ D)
    rw [bool_xor_eq_xor_iff_eq_iff_eq]
    tauto

theorem typedSpinProduct_xor_reachability_of_not_reachable
    (ends : P -> V × V) (omega : P -> Bool) (sigma : V -> Bool)
    {x y : V} (hxy : ¬ (typedOpenGraph ends omega).Reachable x y) :
    typedSpinProduct
        (typedSpinXor sigma (typedReachabilitySpin ends omega x)) x y =
      -typedSpinProduct sigma x y := by
  cases hx : sigma x <;> cases hy : sigma y <;>
    simp [typedSpinProduct, typedSpinXor, typedReachabilitySpin, hxy, hx, hy]



theorem typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable
    (ends : P -> V × V) (omega : P -> Bool) {x y : V}
    (hxy : ¬ (typedOpenGraph ends omega).Reachable x y) :
    (∑ sigma : V -> Bool,
      (if TypedSignedCompatible ends ∅ omega sigma then (1 : Real) else 0) *
        typedSpinProduct sigma x y) = 0 := by
  let tau := typedReachabilitySpin ends omega x
  let F : (V -> Bool) -> Real := fun sigma =>
    (if TypedSignedCompatible ends ∅ omega sigma then (1 : Real) else 0) *
      typedSpinProduct sigma x y
  have htau : TypedSignedCompatible ends ∅ omega tau :=
    typedReachabilitySpin_compatible ends omega x
  have hmap : forall sigma : V -> Bool,
      F (typedSpinXor sigma tau) = -F sigma := by
    intro sigma
    have hcompat := typedSignedCompatible_empty_xor_iff
      ends omega sigma tau htau
    have hspin := typedSpinProduct_xor_reachability_of_not_reachable
      ends omega sigma hxy
    simp only [F]
    rw [if_congr hcompat rfl rfl, hspin]
    ring
  have hreindex := (typedSpinXorEquiv tau).sum_comp F
  have hneg : (∑ sigma : V -> Bool, F sigma) =
      -(∑ sigma : V -> Bool, F sigma) := by
    calc
      (∑ sigma : V -> Bool, F sigma) =
          ∑ sigma : V -> Bool, F (typedSpinXor sigma tau) := hreindex.symm
      _ = ∑ sigma : V -> Bool, -F sigma := by
        apply Finset.sum_congr rfl
        intro sigma _
        exact hmap sigma
      _ = -(∑ sigma : V -> Bool, F sigma) := by simp
  change (∑ sigma : V -> Bool, F sigma) = 0
  linarith



theorem typedESWeight_spinProduct_sum_eq
    (ends : P -> V × V) (rho : P -> Real) (omega : P -> Bool)
    (x y : V) :
    (∑ sigma : V -> Bool,
      typedESWeight ends rho ∅ sigma omega * typedSpinProduct sigma x y) =
      if (typedOpenGraph ends omega).Reachable x y then
        typedFKWeight ends rho omega else 0 := by
  by_cases hxy : (typedOpenGraph ends omega).Reachable x y
  · rw [if_pos hxy]
    unfold typedFKWeight
    apply Finset.sum_congr rfl
    intro sigma _
    by_cases hsigma : TypedSignedCompatible ends ∅ omega sigma
    · have heq := typedSignedCompatible_empty_eq_of_reachable
        ends omega sigma hsigma hxy
      rw [typedSpinProduct]
      simp [heq]
    · rw [typedESWeight_factor]
      simp [hsigma]
  · rw [if_neg hxy]
    simp_rw [typedESWeight_factor]
    have hzero := typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable
      ends omega hxy
    calc
      (∑ sigma : V -> Bool,
          (typedESActivity rho omega *
              if TypedSignedCompatible ends ∅ omega sigma then 1 else 0) *
            typedSpinProduct sigma x y) =
          typedESActivity rho omega *
            ∑ sigma : V -> Bool,
              (if TypedSignedCompatible ends ∅ omega sigma then 1 else 0) *
                typedSpinProduct sigma x y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma _
        ring
      _ = 0 := by rw [hzero, mul_zero]


def typedESTwoPoint (ends : P -> V × V) (rho : P -> Real)
    (x y : V) : Real :=
  (∑ omega : P -> Bool, ∑ sigma : V -> Bool,
      typedESWeight ends rho ∅ sigma omega * typedSpinProduct sigma x y) /
    typedESZ ends rho ∅



theorem typedESTwoPoint_eq_typedFKTwoPoint
    (ends : P -> V × V) (rho : P -> Real) (x y : V) :
    typedESTwoPoint ends rho x y = typedFKTwoPoint ends rho x y := by
  classical
  unfold typedESTwoPoint typedFKTwoPoint typedFKEventMass typedFKProb
  simp_rw [typedESWeight_spinProduct_sum_eq]
  rw [typedFKZ_eq_typedESZ_empty, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hxy : (typedOpenGraph ends omega).Reachable x y
  · simp [typedFKConnEvent, hxy]
  · simp [typedFKConnEvent, hxy]


def multibondIsingTwoPoint (ends : P -> V × V) (J : P -> Real)
    (x y : V) : Real :=
  (∑ sigma : V -> Bool,
      multibondIsingWeight ends J sigma * typedSpinProduct sigma x y) /
    multibondIsingPartition ends J

theorem exp_mul_typedES_spinProduct_sum_omega
    (ends : P -> V × V) (J : P -> Real) (sigma : V -> Bool)
    (x y : V) :
    Real.exp (∑ p : P, J p) *
        (∑ omega : P -> Bool,
          typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅
            sigma omega * typedSpinProduct sigma x y) =
      multibondIsingWeight ends J sigma * typedSpinProduct sigma x y := by
  rw [← Finset.sum_mul]
  rw [typedESWeight_sum_omega_eq_shiftedCut]
  have hempty : multibondCut ends sigma ∆ (∅ : Finset P) =
      multibondCut ends sigma := by
    ext p
    simp [Finset.mem_symmDiff]
  rw [hempty]
  rw [multibondIsingWeight_eq_activity]
  ring

theorem exp_mul_typedES_twoPointNumerator
    (ends : P -> V × V) (J : P -> Real) (x y : V) :
    Real.exp (∑ p : P, J p) *
        (∑ omega : P -> Bool, ∑ sigma : V -> Bool,
          typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅
            sigma omega * typedSpinProduct sigma x y) =
      ∑ sigma : V -> Bool,
        multibondIsingWeight ends J sigma * typedSpinProduct sigma x y := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  exact exp_mul_typedES_spinProduct_sum_omega ends J sigma x y



theorem typedESTwoPoint_coupling_eq_multibondIsingTwoPoint
    (ends : P -> V × V) (J : P -> Real) (x y : V) :
    typedESTwoPoint ends (fun p => 1 - Real.exp (-2 * J p)) x y =
      multibondIsingTwoPoint ends J x y := by
  unfold typedESTwoPoint multibondIsingTwoPoint
  let e := Real.exp (∑ p : P, J p)
  let A := ∑ omega : P -> Bool, ∑ sigma : V -> Bool,
    typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅ sigma omega *
      typedSpinProduct sigma x y
  let B := typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) ∅
  let C := ∑ sigma : V -> Bool,
    multibondIsingWeight ends J sigma * typedSpinProduct sigma x y
  let D := multibondIsingPartition ends J
  have hnum : e * A = C :=
    exp_mul_typedES_twoPointNumerator ends J x y
  have hden : e * B = D :=
    by
      have hpart :=
        multibondIsingPartition_twist_eq_exp_mul_typedESZ ends J ∅
      have htwist : multibondTwistCoupling J (∅ : Finset P) = J := by
        funext p
        simp [multibondTwistCoupling]
      rw [htwist] at hpart
      exact hpart.symm
  change A / B = C / D
  rw [← hnum, ← hden]
  exact (mul_div_mul_left (c := e) A B (by simp [e])).symm



theorem typedFKTwoPoint_eq_multibondIsingTwoPoint
    (ends : P -> V × V) (J : P -> Real) (x y : V) :
    typedFKTwoPoint ends (fun p => 1 - Real.exp (-2 * J p)) x y =
      multibondIsingTwoPoint ends J x y := by
  rw [← typedESTwoPoint_eq_typedFKTwoPoint]
  exact typedESTwoPoint_coupling_eq_multibondIsingTwoPoint ends J x y

end

end StatMech.FrontierA
