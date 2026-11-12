/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]




noncomputable def sdrBondEnergy (s : ConfigSpace V) : ℝ := ∑ e ∈ G.edgeFinset, bond s e


noncomputable def sdrTotalSpin (s : ConfigSpace V) : ℝ := ∑ x, spin s x



theorem sdr_hasDerivAt_isingWeight_beta (β h : ℝ) (s : ConfigSpace V) :
    HasDerivAt (fun β => isingWeight G β h s)
      (isingWeight G β h s * (sdrBondEnergy G s + h * sdrTotalSpin s)) β := by
  unfold isingWeight hamiltonian sdrBondEnergy sdrTotalSpin
  set E := ∑ e ∈ G.edgeFinset, bond s e with hE
  set M := ∑ x, spin s x with hM
  have hrw : (fun β => Real.exp (-β * (-E - h * M)))
      = (fun β => Real.exp (β * (E + h * M))) := by funext β; congr 1; ring
  rw [hrw]
  have hlin : HasDerivAt (fun β : ℝ => β * (E + h * M)) (E + h * M) β := by
    simpa using (hasDerivAt_id β).mul_const (E + h * M)
  have hcomp := (Real.hasDerivAt_exp (β * (E + h * M))).comp β hlin
  have hval : Real.exp (-β * (-E - h * M)) = Real.exp (β * (E + h * M)) := by
    congr 1; ring
  rw [hval]
  exact hcomp


theorem sdr_hasDerivAt_num_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      (∑ s : ConfigSpace V,
        f s * (isingWeight G β h s * (sdrBondEnergy G s + h * sdrTotalSpin s))) β := by
  have hpt : (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      = ∑ s : ConfigSpace V, (fun β => f s * isingWeight G β h s) := by rw [Finset.sum_fn]
  rw [hpt]
  exact HasDerivAt.sum (fun s _ => (sdr_hasDerivAt_isingWeight_beta G β h s).const_mul (f s))


theorem sdr_hasDerivAt_isingZ_beta (β h : ℝ) :
    HasDerivAt (fun β => isingZ G β h)
      (∑ s : ConfigSpace V,
        isingWeight G β h s * (sdrBondEnergy G s + h * sdrTotalSpin s)) β := by
  have h1 := sdr_hasDerivAt_num_beta G β h (fun _ => 1)
  simp only [one_mul] at h1
  exact h1


theorem sdr_expectation_eq_div (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h f
      = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h := by
  unfold isingExpectation isingProb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [div_mul_eq_mul_div, mul_comm]








theorem sdr_hasDerivAt_expectation_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => isingExpectation G β h f)
      (isingExpectation G β h (fun s => f s * (sdrBondEnergy G s + h * sdrTotalSpin s))
        - isingExpectation G β h f
          * isingExpectation G β h (fun s => sdrBondEnergy G s + h * sdrTotalSpin s)) β := by
  have hN := sdr_hasDerivAt_num_beta G β h f
  have hZ := sdr_hasDerivAt_isingZ_beta G β h
  have hZne : isingZ G β h ≠ 0 := isingZ_ne_zero G β h
  have hfun : (fun β => isingExpectation G β h f)
      = (fun β => (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h) := by
    funext β; exact sdr_expectation_eq_div G β h f
  rw [hfun]
  have hdiv := hN.div hZ hZne
  set U := fun s => sdrBondEnergy G s + h * sdrTotalSpin s with hU
  have e1 : isingExpectation G β h (fun s => f s * U s)
      = (∑ s : ConfigSpace V, (f s * U s) * isingWeight G β h s) / isingZ G β h :=
    sdr_expectation_eq_div G β h _
  have e2 : isingExpectation G β h f
      = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h :=
    sdr_expectation_eq_div G β h f
  have e3 : isingExpectation G β h U
      = (∑ s : ConfigSpace V, U s * isingWeight G β h s) / isingZ G β h :=
    sdr_expectation_eq_div G β h U
  set Z := isingZ G β h with hZdef
  set A := ∑ s : ConfigSpace V, (f s * U s) * isingWeight G β h s with hAdef
  set B := ∑ s : ConfigSpace V, f s * isingWeight G β h s with hBdef
  set C := ∑ s : ConfigSpace V, U s * isingWeight G β h s with hCdef
  have hN'eq :
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * U s)) = A := by
    rw [hAdef]; apply Finset.sum_congr rfl; intro s _; ring
  have hZ'eq :
      (∑ s : ConfigSpace V, isingWeight G β h s * U s) = C := by
    rw [hCdef]; apply Finset.sum_congr rfl; intro s _; ring
  rw [e1, e2, e3]
  have hval : (A / Z - B / Z * (C / Z))
      = ((∑ s : ConfigSpace V, f s * (isingWeight G β h s * U s)) * Z
          - B * (∑ s : ConfigSpace V, isingWeight G β h s * U s)) / Z ^ 2 := by
    rw [hN'eq, hZ'eq]; field_simp
  rw [hval]
  exact hdiv




theorem sdr_expectation_sum (β h : ℝ) {ι : Type*} (s : Finset ι) (f : ι → ConfigSpace V → ℝ) :
    isingExpectation G β h (fun cfg => ∑ i ∈ s, f i cfg)
      = ∑ i ∈ s, isingExpectation G β h (f i) := by
  unfold isingExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]


theorem sdr_expectation_mul_bondEnergy (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s * sdrBondEnergy G s)
      = ∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => f s * bond s e) := by
  unfold sdrBondEnergy
  rw [show (fun s => f s * ∑ e ∈ G.edgeFinset, bond s e)
        = (fun cfg => ∑ e ∈ G.edgeFinset, (fun e s => f s * bond s e) e cfg) from by
      funext s; rw [Finset.mul_sum]]
  rw [sdr_expectation_sum]


theorem sdr_expectation_bondEnergy (β h : ℝ) :
    isingExpectation G β h (sdrBondEnergy G)
      = ∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => bond s e) := by
  rw [show (sdrBondEnergy G : ConfigSpace V → ℝ)
        = (fun cfg => ∑ e ∈ G.edgeFinset, (fun e s => bond s e) e cfg) from by
      funext s; rfl, sdr_expectation_sum]


theorem sdr_expectation_mul_totalSpin (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s * sdrTotalSpin s)
      = ∑ z, isingExpectation G β h (fun s => f s * spin s z) := by
  unfold sdrTotalSpin
  rw [show (fun s => f s * ∑ z, spin s z)
        = (fun cfg => ∑ z, (fun z s => f s * spin s z) z cfg) from by
      funext s; rw [Finset.mul_sum]]
  rw [sdr_expectation_sum]


theorem sdr_expectation_totalSpin (β h : ℝ) :
    isingExpectation G β h sdrTotalSpin
      = ∑ z, isingExpectation G β h (fun s => spin s z) := by
  rw [show (sdrTotalSpin : ConfigSpace V → ℝ)
        = (fun cfg => ∑ z, (fun z s => spin s z) z cfg) from by funext s; rfl, sdr_expectation_sum]















theorem sdr_deriv_magnetization_eq_bondCov (β h : ℝ) (o : V) :
    HasDerivAt (fun β => isingExpectation G β h (fun s => spin s o))
      ((∑ e ∈ G.edgeFinset,
          (isingExpectation G β h (fun s => spin s o * bond s e)
            - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => bond s e)))
        + h * ∑ z,
            (isingExpectation G β h (fun s => spin s o * spin s z)
              - isingExpectation G β h (fun s => spin s o)
                * isingExpectation G β h (fun s => spin s z)))
      β := by
  have hd := sdr_hasDerivAt_expectation_beta G β h (fun s => spin s o)
  convert hd using 1
  set m := isingExpectation G β h (fun s => spin s o) with hm
  have hsplit_mul :
      isingExpectation G β h (fun s => spin s o * (sdrBondEnergy G s + h * sdrTotalSpin s))
        = isingExpectation G β h (fun s => spin s o * sdrBondEnergy G s)
          + h * isingExpectation G β h (fun s => spin s o * sdrTotalSpin s) := by
    unfold isingExpectation
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  have hsplit_U :
      isingExpectation G β h (fun s => sdrBondEnergy G s + h * sdrTotalSpin s)
        = isingExpectation G β h (sdrBondEnergy G) + h * isingExpectation G β h sdrTotalSpin := by
    unfold isingExpectation
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [hsplit_mul, hsplit_U,
      sdr_expectation_mul_bondEnergy, sdr_expectation_bondEnergy,
      sdr_expectation_mul_totalSpin, sdr_expectation_totalSpin]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      show (∑ z, ((isingExpectation G β h fun s => spin s o * spin s z)
              - m * isingExpectation G β h fun s => spin s z))
        = (∑ z, isingExpectation G β h fun s => spin s o * spin s z)
          - m * ∑ z, isingExpectation G β h fun s => spin s z from by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]]
  ring
















theorem sdr_deltaIndicator_split {D P Q : Prop} [Decidable D] [Decidable P] [Decidable Q]
    (hdich : D → (P ↔ ¬ Q)) :
    (if D then (1 : ℝ) else 0)
      = (if D ∧ P then 1 else 0) + (if D ∧ Q then 1 else 0) := by
  by_cases hD : D
  · have hPQ := hdich hD
    by_cases hP : P
    · have hnQ : ¬ Q := hPQ.mp hP
      simp [hD, hP, hnQ]
    · have hQ : Q := by
        by_contra hnQ; exact hP (hPQ.mpr hnQ)
      simp [hD, hP, hQ]
  · simp [hD]


















theorem sdr_deltaRewrite_perEdge
    {Cur : Type*}
    (covTerm : ℝ)
    (pairSum : (Cur → Prop) → ℝ)
    (hpairSum_add : ∀ (P₁ P₂ : Cur → Prop) [DecidablePred P₁] [DecidablePred P₂]
        [DecidablePred (fun m => P₁ m ∨ P₂ m)],
        (∀ m, ¬ (P₁ m ∧ P₂ m)) →
        pairSum (fun m => P₁ m ∨ P₂ m) = pairSum P₁ + pairSum P₂)
    (disconn caseA caseB : Cur → Prop)
    [DecidablePred disconn] [DecidablePred caseA] [DecidablePred caseB]
    [DecidablePred (fun m => (disconn m ∧ caseA m) ∨ (disconn m ∧ caseB m))]
    (hcov : covTerm = pairSum disconn)
    (hdich : ∀ m, disconn m → (caseA m ↔ ¬ caseB m)) :
    covTerm
      = pairSum (fun m => disconn m ∧ caseA m) + pairSum (fun m => disconn m ∧ caseB m) := by
  classical
  
  have hdisj : ∀ m, ¬ ((disconn m ∧ caseA m) ∧ (disconn m ∧ caseB m)) := by
    rintro m ⟨⟨hd, hA⟩, ⟨_, hB⟩⟩
    exact (hdich m hd).mp hA hB
  have hunion : disconn = (fun m => (disconn m ∧ caseA m) ∨ (disconn m ∧ caseB m)) := by
    funext m
    by_cases hd : disconn m
    · simp only [hd, true_and, eq_iff_iff, true_iff]
      by_cases hA : caseA m
      · exact Or.inl hA
      · have hB : caseB m := by
          by_contra hnB; exact hA ((hdich m hd).mpr hnB)
        exact Or.inr hB
    · simp [hd]
  rw [hcov]
  have hcong : pairSum disconn
      = pairSum (fun m => (disconn m ∧ caseA m) ∨ (disconn m ∧ caseB m)) :=
    congrArg pairSum hunion
  rw [hcong, hpairSum_add _ _ hdisj]






theorem sdr_indicatorPairSum_add {Cur : Type*} (W : (Cur × Cur) → ℝ) (Z2 : ℝ)
    (sup : (Cur × Cur) → Cur)
    (P₁ P₂ : Cur → Prop) [DecidablePred P₁] [DecidablePred P₂]
    [DecidablePred (fun m => P₁ m ∨ P₂ m)]
    (hsummable : Summable (fun pq : Cur × Cur => W pq))
    (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
    (1 / Z2) * ∑' pq : Cur × Cur,
        W pq * (if (fun m => P₁ m ∨ P₂ m) (sup pq) then 1 else 0)
      = ((1 / Z2) * ∑' pq : Cur × Cur, W pq * (if P₁ (sup pq) then 1 else 0))
        + ((1 / Z2) * ∑' pq : Cur × Cur, W pq * (if P₂ (sup pq) then 1 else 0)) := by
  classical
  have hmask : ∀ Q : Cur → Prop, ∀ _ : DecidablePred Q,
      Summable (fun pq : Cur × Cur => W pq * (if Q (sup pq) then (1:ℝ) else 0)) := by
    intro Q _
    have heq : (fun pq : Cur × Cur => W pq * (if Q (sup pq) then (1:ℝ) else 0))
        = Set.indicator {pq | Q (sup pq)} W := by
      funext pq; by_cases h : Q (sup pq) <;> simp [Set.indicator, h]
    rw [heq]; exact hsummable.indicator _
  rw [← mul_add]
  rw [show (∑' pq : Cur × Cur, W pq * (if P₁ (sup pq) then (1:ℝ) else 0))
        + ∑' pq : Cur × Cur, W pq * (if P₂ (sup pq) then (1:ℝ) else 0)
      = ∑' pq : Cur × Cur,
          (W pq * (if P₁ (sup pq) then (1:ℝ) else 0)
            + W pq * (if P₂ (sup pq) then (1:ℝ) else 0)) from
      (Summable.tsum_add (hmask P₁ _) (hmask P₂ _)).symm]
  congr 1
  apply tsum_congr; intro pq
  by_cases h1 : P₁ (sup pq) <;> by_cases h2 : P₂ (sup pq)
  · exact absurd ⟨h1, h2⟩ (hdisj _)
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

end Sharpness
end StatMech
