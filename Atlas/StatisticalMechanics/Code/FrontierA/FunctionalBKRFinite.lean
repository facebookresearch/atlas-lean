/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.Inequalities.DisjointOccurrence

namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]




noncomputable def agreementFiber (K : Set E) (omega : ConfigSpace E) :
    Finset (ConfigSpace E) := by
  classical
  exact Finset.univ.filter (agreeOn K omega)

@[simp] theorem mem_agreementFiber {K : Set E} {omega eta : ConfigSpace E} :
    eta ∈ agreementFiber K omega ↔ agreeOn K omega eta := by
  classical
  simp [agreementFiber]


theorem agreementFiber_nonempty (K : Set E) (omega : ConfigSpace E) :
    (agreementFiber K omega).Nonempty := by
  classical
  exact ⟨omega, mem_agreementFiber.mpr (agreeOn_refl K omega)⟩



noncomputable def cylinderMin (f : ConfigSpace E → ℝ) (K : Set E)
    (omega : ConfigSpace E) : ℝ :=
  (agreementFiber K omega).inf' (agreementFiber_nonempty K omega) f


theorem cylinderMin_le_self (f : ConfigSpace E → ℝ) (K : Set E)
    (omega : ConfigSpace E) : cylinderMin f K omega ≤ f omega := by
  classical
  exact Finset.inf'_le _ (mem_agreementFiber.mpr (agreeOn_refl K omega))


theorem cylinderMin_nonneg {f : ConfigSpace E → ℝ} (hf : ∀ omega, 0 ≤ f omega)
    (K : Set E) (omega : ConfigSpace E) : 0 ≤ cylinderMin f K omega := by
  classical
  apply Finset.le_inf'
  intro eta _
  exact hf eta


theorem cylinderMin_mono {f g : ConfigSpace E → ℝ} (hfg : ∀ omega, f omega ≤ g omega)
    (K : Set E) (omega : ConfigSpace E) :
    cylinderMin f K omega ≤ cylinderMin g K omega := by
  classical
  apply Finset.le_inf'
  intro eta heta
  exact le_trans (Finset.inf'_le _ heta) (hfg eta)


theorem agreementFiber_eq_of_agreeOn {K : Set E} {omega omega' : ConfigSpace E}
    (h : agreeOn K omega omega') : agreementFiber K omega = agreementFiber K omega' := by
  classical
  ext eta
  simp only [mem_agreementFiber]
  constructor
  · intro heta e he
    exact (heta e he).trans (h e he).symm
  · intro heta e he
    exact (heta e he).trans (h e he)


theorem cylinderMin_eq_of_agreeOn (f : ConfigSpace E → ℝ) {K : Set E}
    {omega omega' : ConfigSpace E} (h : agreeOn K omega omega') :
    cylinderMin f K omega = cylinderMin f K omega' := by
  classical
  simp only [cylinderMin, agreementFiber_eq_of_agreeOn h]


noncomputable def eventIndicator (A : Set (ConfigSpace E)) : ConfigSpace E → ℝ :=
  A.indicator (fun _ => 1)



theorem cylinderMin_eventIndicator (A : Set (ConfigSpace E)) (K : Set E)
    (omega : ConfigSpace E) :
    cylinderMin (eventIndicator A) K omega =
      eventIndicator {eta | OccursOn A K eta} omega := by
  classical
  by_cases hocc : OccursOn A K omega
  · change cylinderMin (A.indicator fun _ => (1 : ℝ)) K omega =
      {eta | OccursOn A K eta}.indicator (fun _ => (1 : ℝ)) omega
    rw [Set.indicator_of_mem hocc]
    apply Finset.inf'_eq_of_forall
    intro eta heta
    have hmem : eta ∈ A := hocc eta (mem_agreementFiber.mp heta)
    simp [hmem]
  · change cylinderMin (A.indicator fun _ => (1 : ℝ)) K omega =
      {eta | OccursOn A K eta}.indicator (fun _ => (1 : ℝ)) omega
    rw [Set.indicator_of_notMem hocc]
    simp only [OccursOn] at hocc
    push Not at hocc
    obtain ⟨eta, hagree, hnotmem⟩ := hocc
    apply le_antisymm
    · calc
        cylinderMin (eventIndicator A) K omega
            ≤ eventIndicator A eta := Finset.inf'_le _ (mem_agreementFiber.mpr hagree)
        _ = 0 := by simp [eventIndicator, hnotmem]
    · exact cylinderMin_nonneg
        (fun eta => Set.indicator_nonneg (fun _ _ => zero_le_one) eta) K omega





noncomputable def disjointCoordinatePairs (E : Type*) [Fintype E] :
    Finset (Set E × Set E) := by
  classical
  exact Finset.univ.filter fun pair => Disjoint pair.1 pair.2

omit [DecidableEq E] in
@[simp] theorem mem_disjointCoordinatePairs {pair : Set E × Set E} :
    pair ∈ disjointCoordinatePairs E ↔ Disjoint pair.1 pair.2 := by
  classical
  simp [disjointCoordinatePairs]

omit [DecidableEq E] in

theorem disjointCoordinatePairs_nonempty : (disjointCoordinatePairs E).Nonempty := by
  classical
  exact ⟨(∅, ∅), by simp⟩



noncomputable def functionalDisjointMaxAt (f g : ConfigSpace E → ℝ)
    (omega eta : ConfigSpace E) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => cylinderMin f pair.1 omega * cylinderMin g pair.2 eta


noncomputable def functionalDisjointMax (f g : ConfigSpace E → ℝ)
    (omega : ConfigSpace E) : ℝ :=
  functionalDisjointMaxAt f g omega omega



def dualDisjointOccurrence (A B : Set (ConfigSpace E)) :
    Set (ConfigSpace E × ConfigSpace E) :=
  {pair | ∃ K L : Set E, Disjoint K L ∧
    OccursOn A K pair.1 ∧ OccursOn B L pair.2}

omit [Fintype E] [DecidableEq E] in
theorem mem_dualDisjointOccurrence {A B : Set (ConfigSpace E)}
    {omega eta : ConfigSpace E} :
    (omega, eta) ∈ dualDisjointOccurrence A B ↔
      ∃ K L : Set E, Disjoint K L ∧ OccursOn A K omega ∧ OccursOn B L eta :=
  Iff.rfl

omit [Fintype E] [DecidableEq E] in


@[simp] theorem dualDisjointOccurrence_diagonal (A B : Set (ConfigSpace E))
    (omega : ConfigSpace E) :
    (omega, omega) ∈ dualDisjointOccurrence A B ↔
      omega ∈ disjointOccurrence A B :=
  Iff.rfl



theorem functionalDisjointMaxAt_eventIndicator (A B : Set (ConfigSpace E))
    (omega eta : ConfigSpace E) :
    functionalDisjointMaxAt (eventIndicator A) (eventIndicator B) omega eta =
      (dualDisjointOccurrence A B).indicator (fun _ => (1 : ℝ)) (omega, eta) := by
  classical
  by_cases hdual : (omega, eta) ∈ dualDisjointOccurrence A B
  · rw [Set.indicator_of_mem hdual]
    obtain ⟨K, L, hKL, hAK, hBL⟩ := hdual
    apply le_antisymm
    · apply Finset.sup'_le
      intro pair hpair
      rw [cylinderMin_eventIndicator, cylinderMin_eventIndicator]
      by_cases hA : OccursOn A pair.1 omega <;>
        by_cases hB : OccursOn B pair.2 eta <;> simp [eventIndicator, hA, hB]
    · have hpair : (K, L) ∈ disjointCoordinatePairs E := by
        simpa using hKL
      calc
        (1 : ℝ) = cylinderMin (eventIndicator A) K omega *
            cylinderMin (eventIndicator B) L eta := by
              rw [cylinderMin_eventIndicator, cylinderMin_eventIndicator]
              simp [eventIndicator, hAK, hBL]
        _ ≤ functionalDisjointMaxAt (eventIndicator A) (eventIndicator B) omega eta :=
          by
            unfold functionalDisjointMaxAt
            exact Finset.le_sup'
              (fun pair : Set E × Set E =>
                cylinderMin (eventIndicator A) pair.1 omega *
                  cylinderMin (eventIndicator B) pair.2 eta)
              hpair
  · rw [Set.indicator_of_notMem hdual]
    apply Finset.sup'_eq_of_forall
    intro pair hpair
    rw [cylinderMin_eventIndicator, cylinderMin_eventIndicator]
    have hnot : ¬ (OccursOn A pair.1 omega ∧ OccursOn B pair.2 eta) := by
      intro hocc
      exact hdual ⟨pair.1, pair.2, mem_disjointCoordinatePairs.mp hpair,
        hocc.1, hocc.2⟩
    by_cases hA : OccursOn A pair.1 omega <;>
      by_cases hB : OccursOn B pair.2 eta <;> simp_all [eventIndicator]



theorem functionalDisjointMax_eventIndicator (A B : Set (ConfigSpace E))
    (omega : ConfigSpace E) :
    functionalDisjointMax (eventIndicator A) (eventIndicator B) omega =
      (disjointOccurrence A B).indicator (fun _ => (1 : ℝ)) omega := by
  classical
  rw [functionalDisjointMax, functionalDisjointMaxAt_eventIndicator]
  by_cases h : omega ∈ disjointOccurrence A B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    exact dualDisjointOccurrence_diagonal A B omega |>.mpr h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    exact fun hdual => h (dualDisjointOccurrence_diagonal A B omega |>.mp hdual)

end StatMech.FrontierA
