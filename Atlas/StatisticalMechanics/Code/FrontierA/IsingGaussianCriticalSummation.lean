/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalCubeInfrared
import Code.FrontierA.IsingGaussianIndependentDisentangling










open Filter Finset Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


def criticalFreeBoxSusceptibility (d R : Nat) : Real :=
  ∑ x ∈ boxSV_boxF d R,
    currentContinuityFreePairKernel d (IsingFK.betaC (magnetization d)) x

private theorem criticalFreePairKernel_nonneg
    (hd : 2 ≤ d) (x : Site d) :
    0 ≤ currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) x := by
  by_cases hx : x = 0
  · simp [currentContinuityFreePairKernel, hx]
  · rw [currentContinuityFreePairKernel, if_neg hx]
    have hbeta : 0 < IsingFK.betaC (magnetization d) := by
      rw [isingFK_betaC_eq_tildeBetaCIsing hd]
      exact tildeBetaCIsing_pos hd
    rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      _ hbeta (by omega) (Percolation.origin d) x]
    · unfold StatMech.FK.infiniteTwoPointReal
      exact MeasureTheory.measureReal_nonneg
    · simpa [Percolation.origin] using Ne.symm hx


theorem criticalFreeBoxSusceptibility_nonneg
    (hd : 2 ≤ d) (R : Nat) :
    0 ≤ criticalFreeBoxSusceptibility d R := by
  unfold criticalFreeBoxSusceptibility
  exact Finset.sum_nonneg fun x _ => criticalFreePairKernel_nonneg hd x



theorem one_le_criticalFreeBoxSusceptibility
    (hd : 2 ≤ d) (R : Nat) :
    1 ≤ criticalFreeBoxSusceptibility d R := by
  rw [criticalFreeBoxSusceptibility]
  have hzero : (0 : Site d) ∈ boxSV_boxF d R := by
    rw [boxSV_mem_boxF]
    intro i
    simp
  have hterm := Finset.single_le_sum
    (s := boxSV_boxF d R)
    (f := fun x => currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) x)
    (fun x _ => criticalFreePairKernel_nonneg hd x) hzero
  simpa [currentContinuityFreePairKernel] using hterm

private theorem boxSV_boxF_succ_disjoint (d R : Nat) :
    boxSV_boxF d (R + 1) =
      boxSV_boxF d R ∪ boxSV_vbF d (R + 1) := by
  classical
  ext x
  simp only [boxSV_vbF, Finset.mem_union, Finset.mem_sdiff,
    Nat.add_sub_cancel]
  constructor
  · intro hx
    by_cases hinner : x ∈ boxSV_boxF d R
    · exact Or.inl hinner
    · exact Or.inr ⟨hx, hinner⟩
  · rintro (hx | ⟨hx, _⟩)
    · exact boxSV_boxF_subset d (Nat.le_succ R) hx
    · exact hx

private theorem boxSV_boxF_disjoint_vbF_succ (d R : Nat) :
    Disjoint (boxSV_boxF d R) (boxSV_vbF d (R + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hboundary
  exact (Finset.mem_sdiff.mp hboundary).2 hx



theorem sum_boxSV_boxF_eq_sum_shells
    (f : Site d → Real) (R : Nat) :
    ∑ x ∈ boxSV_boxF d R, f x =
      f 0 + ∑ r ∈ Finset.range R,
        ∑ x ∈ boxSV_vbF d (r + 1), f x := by
  induction R with
  | zero =>
      have hbox : boxSV_boxF d 0 = {0} := by
        classical
        apply Finset.coe_injective
        rw [boxSV_coe_boxF]
        ext x
        simp only [Finset.coe_singleton, Set.mem_singleton_iff]
        rw [mem_box]
        constructor
        · intro hx
          funext i
          change x i = 0
          exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp (hx i))
        · intro hx
          subst x
          intro i
          simp
      simp [hbox]
  | succ R ih =>
      rw [boxSV_boxF_succ_disjoint,
        Finset.sum_union (boxSV_boxF_disjoint_vbF_succ d R), ih,
        Finset.sum_range_succ]
      ring




theorem exists_criticalFreeBoxSusceptibility_le_quadratic
    (hd : 2 < d) :
    ∃ A : Real, 0 < A ∧ ∀ R : Nat,
      criticalFreeBoxSusceptibility d R ≤ A * (R + 1 : Real) ^ 2 := by
  obtain ⟨C, hC, hshell⟩ := exists_criticalFreeTwoPoint_shell_le_power
    (d := d) hd
  let r0 : Nat := 2 * d
  let A : Real :=
    1 + r0 * ((boxSV_boxF d r0).card : Real) +
      2 * d * 3 ^ (d - 1) * C
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro R
  rw [criticalFreeBoxSusceptibility,
    sum_boxSV_boxF_eq_sum_shells]
  let f : Site d → Real := fun x =>
    currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) x
  let S := (Finset.range R).filter (fun r => r + 1 < r0)
  let L := (Finset.range R).filter (fun r => r0 ≤ r + 1)
  have hsmall :
      ∑ r ∈ S, ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
        (r0 : Real) * ((boxSV_boxF d r0).card : Real) := by
    have hterm (r : Nat) (hr : r ∈ S) :
        ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
          ((boxSV_boxF d r0).card : Real) := by
      have hr0 : r + 1 ≤ r0 := by
        have := (Finset.mem_filter.mp hr).2
        omega
      calc
        ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
            ∑ _x ∈ boxSV_vbF d (r + 1), (1 : Real) := by
          apply Finset.sum_le_sum
          intro x hx
          dsimp [f]
          by_cases hx0 : x = 0
          · simp [currentContinuityFreePairKernel, hx0]
          · rw [currentContinuityFreePairKernel, if_neg hx0]
            have hbeta : 0 < IsingFK.betaC (magnetization d) := by
              rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
              exact tildeBetaCIsing_pos (by omega)
            rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
              _ hbeta (by omega) (Percolation.origin d) x]
            · unfold StatMech.FK.infiniteTwoPointReal
              exact MeasureTheory.measureReal_le_one
            · simpa [Percolation.origin] using Ne.symm hx0
        _ = ((boxSV_vbF d (r + 1)).card : Real) := by simp
        _ ≤ ((boxSV_boxF d r0).card : Real) := by
          exact_mod_cast Finset.card_le_card (fun x hx =>
            boxSV_boxF_subset d hr0 (Finset.mem_sdiff.mp hx).1)
    calc
      _ ≤ ∑ _r ∈ S, ((boxSV_boxF d r0).card : Real) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hterm r hr
      _ = (S.card : Real) * ((boxSV_boxF d r0).card : Real) := by
        simp [nsmul_eq_mul]
      _ ≤ (r0 : Real) * ((boxSV_boxF d r0).card : Real) := by
        gcongr
        have hcardS : S.card ≤ r0 :=
          (Finset.card_le_card (show S ⊆ Finset.range r0 by
          intro r hr
          rw [Finset.mem_range]
          have := (Finset.mem_filter.mp hr).2
          omega)).trans_eq (Finset.card_range r0)
        exact_mod_cast hcardS
  have hlargeTerm (r : Nat) (hr : r ∈ L) :
      ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
        (2 * d * 3 ^ (d - 1) * C) * (r + 1 : Real) := by
    let s := r + 1
    have hs0 : 1 ≤ s := by omega
    have hsr0 : r0 ≤ s := (Finset.mem_filter.mp hr).2
    have hpowPos : 0 < (s : Real) ^ (d - 2) := by positivity
    have hpoint (x : Site d) (hx : x ∈ boxSV_vbF d s) :
        f x ≤ C / (s : Real) ^ (d - 2) := by
      have hx0 : x ≠ 0 := by
        intro h
        subst x
        have hnot := (Finset.mem_sdiff.mp hx).2
        apply hnot
        rw [boxSV_mem_boxF]
        intro i
        simp
      dsimp [f]
      rw [currentContinuityFreePairKernel, if_neg hx0]
      exact hshell s (by simpa [r0] using hsr0) x hx
    have hcard := integerMomentumShell_card_le d s hs0
    have hthree : 2 * (s : Real) + 1 ≤ 3 * s := by
      have hsR : (1 : Real) ≤ s := by exact_mod_cast hs0
      linarith
    have hcard' : ((boxSV_vbF d s).card : Real) ≤
        2 * d * 3 ^ (d - 1) * (s : Real) ^ (d - 1) := by
      calc
        ((boxSV_vbF d s).card : Real) ≤
            2 * d * (2 * (s : Real) + 1) ^ (d - 1) := hcard
        _ ≤ 2 * d * (3 * (s : Real)) ^ (d - 1) := by gcongr
        _ = 2 * d * 3 ^ (d - 1) * (s : Real) ^ (d - 1) := by
          rw [mul_pow]
          ring
    calc
      ∑ x ∈ boxSV_vbF d s, f x ≤
          ∑ _x ∈ boxSV_vbF d s,
            C / (s : Real) ^ (d - 2) := by
        exact Finset.sum_le_sum fun x hx => hpoint x hx
      _ = ((boxSV_vbF d s).card : Real) *
          (C / (s : Real) ^ (d - 2)) := by simp [nsmul_eq_mul]
      _ ≤ (2 * d * 3 ^ (d - 1) * (s : Real) ^ (d - 1)) *
          (C / (s : Real) ^ (d - 2)) := by
        gcongr
      _ = (2 * d * 3 ^ (d - 1) * C) * (s : Real) := by
        have he : d - 1 = (d - 2) + 1 := by omega
        rw [he, pow_add, pow_one]
        field_simp [ne_of_gt hpowPos]
        ring
      _ = (2 * d * 3 ^ (d - 1) * C) * (r + 1 : Real) := by
        simp [s]
  have hlarge :
      ∑ r ∈ L, ∑ x ∈ boxSV_vbF d (r + 1), f x ≤
        (2 * d * 3 ^ (d - 1) * C) * (R + 1 : Real) ^ 2 := by
    let K : Real := 2 * d * 3 ^ (d - 1) * C
    have hK : 0 ≤ K := by positivity
    calc
      _ ≤ ∑ _r ∈ L, K * (R + 1 : Real) := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          ∑ x ∈ boxSV_vbF d (r + 1), f x ≤ K * (r + 1 : Real) :=
            hlargeTerm r hr
          _ ≤ K * (R + 1 : Real) := by
            gcongr
            exact_mod_cast (Nat.le_of_lt
              (Finset.mem_range.mp (Finset.mem_filter.mp hr).1))
      _ = (L.card : Real) * (K * (R + 1 : Real)) := by
        simp [nsmul_eq_mul]
      _ ≤ (R + 1 : Real) * (K * (R + 1 : Real)) := by
        gcongr
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
          (by simp)
      _ = K * (R + 1 : Real) ^ 2 := by ring
  have hsplit :
      (∑ r ∈ Finset.range R, ∑ x ∈ boxSV_vbF d (r + 1), f x) =
        (∑ r ∈ S, ∑ x ∈ boxSV_vbF d (r + 1), f x) +
        ∑ r ∈ L, ∑ x ∈ boxSV_vbF d (r + 1), f x := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.range R) (p := fun r => r + 1 < r0)]
    congr 2
    ext r
    simp [L]
  rw [hsplit]
  rw [show currentContinuityFreePairKernel d
      (IsingFK.betaC (magnetization d)) 0 = 1 by
    simp [currentContinuityFreePairKernel]]
  have hsq : (1 : Real) ≤ (R + 1 : Real) ^ 2 := by
    have hR : (0 : Real) ≤ R := Nat.cast_nonneg R
    nlinarith
  dsimp [A]
  nlinarith [mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ (r0 : Real) * ((boxSV_boxF d r0).card : Real) by positivity)]



theorem criticalRenormalizedCoupling_tendsto_zero_of_treeDiagram
    (d : Nat) (hd : 4 < d) (coupling : Nat → Real)
    (htree : ∀ R,
      0 ≤ coupling R ∧
        coupling R ≤
          criticalFreeBoxSusceptibility d R ^ 2 / (R + 1 : Real) ^ d) :
    Tendsto coupling atTop (nhds 0) := by
  obtain ⟨A, hA, hchi⟩ :=
    exists_criticalFreeBoxSusceptibility_le_quadratic (d := d) (by omega)
  let radius : Nat → Real := fun R => (R + 1 : Nat)
  have hradius : Tendsto radius atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpower : Tendsto (fun R => radius R ^ (d - 4)) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun R => ?_) hradius
    have hradiusOne : 1 ≤ radius R := by
      dsimp [radius]
      norm_num
    simpa only [pow_one] using
      pow_le_pow_right₀ hradiusOne (show 1 ≤ d - 4 by omega)
  have henvelope : Tendsto
      (fun R => A ^ 2 / radius R ^ (d - 4)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpower
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun R => (htree R).1) _ henvelope
  filter_upwards with R
  have hradiusPos : 0 < radius R := by
    dsimp [radius]
    positivity
  have hchiNonneg : 0 ≤ criticalFreeBoxSusceptibility d R :=
    criticalFreeBoxSusceptibility_nonneg (d := d) (by omega) R
  have hchiSq : criticalFreeBoxSusceptibility d R ^ 2 ≤
      (A * radius R ^ 2) ^ 2 := by
    exact (sq_le_sq₀ hchiNonneg (by positivity)).2
      (by simpa [radius] using hchi R)
  calc
    coupling R ≤
        criticalFreeBoxSusceptibility d R ^ 2 / radius R ^ d := by
      simpa [radius] using (htree R).2
    _ ≤ (A * radius R ^ 2) ^ 2 / radius R ^ d := by
      exact div_le_div_of_nonneg_right hchiSq (pow_nonneg hradiusPos.le d)
    _ = A ^ 2 / radius R ^ (d - 4) := by
      have hd' : d = (d - 4) + 4 := by omega
      rw [hd', pow_add]
      field_simp
      congr 3
      omega

section FiniteTree

variable {V : Type*} [Fintype V] [DecidableEq V]



def finiteDistinctIntegratedFourthCumulant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i : V) : Real :=
  ∑ j : V, ∑ k : V, ∑ l : V,
    if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
      finiteIsingFourthUrsell G beta J i j k l
    else 0

private theorem finitePairCorrelation_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (x y : V) :
    0 ≤ expectationJ G beta J (grahamPairSupport x y) := by
  rw [current_representation]
  exact div_nonneg
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)

private theorem finiteCurrentTreeDiagram_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (i j k l : V) :
    0 ≤ finiteCurrentTreeDiagram G beta J i j k l := by
  unfold finiteCurrentTreeDiagram
  exact Finset.sum_nonneg fun y _ => by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (finitePairCorrelation_nonneg G beta J hbeta hJ i y)
          (finitePairCorrelation_nonneg G beta J hbeta hJ j y))
        (finitePairCorrelation_nonneg G beta J hbeta hJ k y))
      (finitePairCorrelation_nonneg G beta J hbeta hJ l y)

omit [DecidableEq V] in
private theorem finite_sum_three_mul
    (a : Real) (A B C : V → Real) :
    (∑ j : V, ∑ k : V, ∑ l : V, a * A j * B k * C l) =
      a * (∑ j : V, A j) * (∑ k : V, B k) * (∑ l : V, C l) := by
  calc
    _ = ∑ j : V, ∑ k : V,
        (a * A j * B k) * (∑ l : V, C l) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ j : V,
        (a * A j) * (∑ k : V, B k) * (∑ l : V, C l) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = a * (∑ j : V, A j) * (∑ k : V, B k) *
        (∑ l : V, C l) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [show (∑ j : V, a * A j) = a * (∑ j : V, A j) by
        rw [Finset.mul_sum]]

set_option maxHeartbeats 2000000 in




theorem finiteDistinctIntegratedFourthCumulant_treeDiagram_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (chi : Real) (hchi : 0 ≤ chi)
    (hrow : ∀ y : V,
      ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi)
    (i : V) :
    0 ≤ -finiteDistinctIntegratedFourthCumulant G beta J i ∧
      -finiteDistinctIntegratedFourthCumulant G beta J i ≤ 2 * chi ^ 4 := by
  let C : V → V → Real := fun x y =>
    expectationJ G beta J (grahamPairSupport x y)
  have hC (x y : V) : 0 ≤ C x y :=
    finitePairCorrelation_nonneg G beta J hbeta hJ x y
  have hpoint (j k l : V) :
      0 ≤ -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
          j ≠ k ∧ j ≠ l ∧ k ≠ l then
        finiteIsingFourthUrsell G beta J i j k l else 0) ∧
      -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
          j ≠ k ∧ j ≠ l ∧ k ≠ l then
        finiteIsingFourthUrsell G beta J i j k l else 0) ≤
        2 * finiteCurrentTreeDiagram G beta J i j k l := by
    by_cases h : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
        j ≠ k ∧ j ≠ l ∧ k ≠ l
    · simp only [if_pos h]
      exact finiteIsing_treeDiagram_bound G beta J hbeta hJ
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    · simp only [if_neg h, neg_zero]
      exact ⟨le_rfl, mul_nonneg (by norm_num)
        (finiteCurrentTreeDiagram_nonneg G beta J hbeta hJ i j k l)⟩
  have hnonneg :
      0 ≤ ∑ j : V, ∑ k : V, ∑ l : V,
        -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
          finiteIsingFourthUrsell G beta J i j k l else 0) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => (hpoint j k l).1
  have hupper :
      (∑ j : V, ∑ k : V, ∑ l : V,
        -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
          finiteIsingFourthUrsell G beta J i j k l else 0)) ≤
      ∑ j : V, ∑ k : V, ∑ l : V,
        2 * finiteCurrentTreeDiagram G beta J i j k l :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun l _ => (hpoint j k l).2
  have hreorder :
      (∑ j : V, ∑ k : V, ∑ l : V,
          2 * finiteCurrentTreeDiagram G beta J i j k l) =
        2 * ∑ y : V, C i y *
          (∑ x : V, C x y) ^ 3 := by
    unfold finiteCurrentTreeDiagram C
    calc
      _ = 2 * ∑ j : V, ∑ k : V, ∑ l : V, ∑ y : V,
          expectationJ G beta J (grahamPairSupport i y) *
          expectationJ G beta J (grahamPairSupport j y) *
          expectationJ G beta J (grahamPairSupport k y) *
          expectationJ G beta J (grahamPairSupport l y) := by
        simp_rw [Finset.mul_sum]
      _ = 2 * ∑ y : V, ∑ j : V, ∑ k : V, ∑ l : V,
          expectationJ G beta J (grahamPairSupport i y) *
          expectationJ G beta J (grahamPairSupport j y) *
          expectationJ G beta J (grahamPairSupport k y) *
          expectationJ G beta J (grahamPairSupport l y) := by
        congr 1
        calc
          _ = ∑ j : V, ∑ k : V, ∑ y : V, ∑ l : V,
              expectationJ G beta J (grahamPairSupport i y) *
              expectationJ G beta J (grahamPairSupport j y) *
              expectationJ G beta J (grahamPairSupport k y) *
              expectationJ G beta J (grahamPairSupport l y) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
          _ = ∑ j : V, ∑ y : V, ∑ k : V, ∑ l : V,
              expectationJ G beta J (grahamPairSupport i y) *
              expectationJ G beta J (grahamPairSupport j y) *
              expectationJ G beta J (grahamPairSupport k y) *
              expectationJ G beta J (grahamPairSupport l y) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
      _ = 2 * ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        rw [finite_sum_three_mul]
        ring
  have hdiagram :
      2 * ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 ≤
        2 * chi ^ 4 := by
    have hsum :
        ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 ≤
          ∑ y : V, C i y * chi ^ 3 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hC i y)
      exact pow_le_pow_left₀
        (Finset.sum_nonneg fun x _ => hC x y) (hrow y) 3
    have hsymm (x y : V) : C x y = C y x := by
      dsimp [C]
      unfold grahamPairSupport
      rw [symmDiff_comm]
    have hrowi : ∑ y : V, C i y ≤ chi := by
      calc
        ∑ y : V, C i y = ∑ y : V, C y i := by
          apply Finset.sum_congr rfl
          intro y _
          exact hsymm i y
        _ ≤ chi := hrow i
    calc
      2 * ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 ≤
          2 * ∑ y : V, C i y * chi ^ 3 := by gcongr
      _ = 2 * (∑ y : V, C i y) * chi ^ 3 := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ 2 * chi * chi ^ 3 := by
        gcongr
      _ = 2 * chi ^ 4 := by ring
  have hneg :
      (∑ j : V, ∑ k : V, ∑ l : V,
        -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
          finiteIsingFourthUrsell G beta J i j k l else 0)) =
        -finiteDistinctIntegratedFourthCumulant G beta J i := by
    simp [finiteDistinctIntegratedFourthCumulant]
  rw [hneg] at hnonneg hupper
  exact ⟨hnonneg, hupper.trans (hreorder.le.trans hdiagram)⟩

end FiniteTree

section CriticalFiniteBox



def criticalFiniteBoxPairCorrelation (d n : Nat)
    (x y : sctBox d n) : Real :=
  expectationJ (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
    (fun _ => 1) (grahamPairSupport x y)

private theorem criticalFiniteBoxPairCorrelation_le_infinite
    (hd : 2 ≤ d) (n : Nat) (x y : sctBox d n) :
    criticalFiniteBoxPairCorrelation d n x y ≤
      currentContinuityFreePairKernel d
        (IsingFK.betaC (magnetization d)) (y.1 - x.1) := by
  by_cases hxy : x = y
  · subst y
    simpa [criticalFiniteBoxPairCorrelation, twoPointJ,
      grahamPairSupport, currentContinuityFreePairKernel] using
      (twoPointJ_self (sctBoxGraph d n)
        (IsingFK.betaC (magnetization d)) (fun _ => 1) x).le
  have hvals : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hsupport :
      boxSpinSupport d n ({x.1, y.1} : Finset (Site d)) =
        ({x, y} : Finset (sctBox d n)) := by
    ext z
    simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · exact Or.inl (Subtype.ext hz)
      · exact Or.inr (Subtype.ext hz)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hfinite : criticalFiniteBoxPairCorrelation d n x y =
      currentContinuityFreeBoxTwoPoint d n
        (IsingFK.betaC (magnetization d)) x.1 y.1 := by
    rw [criticalFiniteBoxPairCorrelation,
      expectationJ_one_eq_isingExpectation]
    unfold currentContinuityFreeBoxTwoPoint
    rw [integral_freeMeasure_spinProd d n
      (IsingFK.betaC (magnetization d)) 0 ({x.1, y.1} : Finset (Site d))]
    · rw [hsupport]
      congr 1
      funext sigma
      rw [spinProd_grahamPairSupport]
      simp [spinProd, hxy]
    · intro z hz
      simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact x.2
      · exact y.2
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have hdomain := currentContinuityFreeBoxTwoPoint_le_freeTwoPoint
    (IsingFK.betaC (magnetization d)) hbeta n x.1 y.1 (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Ising.mem_boxFinset.mpr x.2
      · exact Ising.mem_boxFinset.mpr y.2)
  rw [hfinite]
  apply hdomain.trans_eq
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-x.1)
  have hgx : g • x.1 = Percolation.origin d := by
    change -x.1 + x.1 = 0
    rw [neg_add_cancel]
  have hgy : g • y.1 = y.1 - x.1 := by
    change -x.1 + y.1 = y.1 - x.1
    abel
  have himage :
      ({x.1, y.1} : Finset (Site d)).image (fun z => g • z) =
        ({Percolation.origin d, y.1 - x.1} : Finset (Site d)) := by
    simp only [Finset.image_insert, Finset.image_singleton, hgx, hgy]
  have htranslate := integral_freeState_spinProd_translate d
    (IsingFK.betaC (magnetization d)) hbeta g
    ({x.1, y.1} : Finset (Site d))
  rw [himage] at htranslate
  unfold currentContinuityFreeTwoPoint currentContinuityFreePairKernel
  have hdiff : y.1 - x.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hvals)
  rw [if_neg hdiff]
  exact htranslate.symm


def criticalFiniteBoxRowSusceptibility (d n : Nat)
    (y : sctBox d n) : Real :=
  ∑ x : sctBox d n, criticalFiniteBoxPairCorrelation d n x y



theorem criticalFiniteBoxRowSusceptibility_le
    (hd : 2 ≤ d) (n : Nat) (y : sctBox d n) :
    criticalFiniteBoxRowSusceptibility d n y ≤
      criticalFreeBoxSusceptibility d (2 * n) := by
  let shift : sctBox d n → Site d := fun x => y.1 - x.1
  have hshift : Function.Injective shift := by
    intro x z hxz
    apply Subtype.ext
    exact sub_right_inj.mp hxz
  have himage : Finset.univ.image shift ⊆ boxSV_boxF d (2 * n) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨x, _hx, rfl⟩ := hw
    change y.1 - x.1 ∈ (boxSV_boxF d (2 * n) : Set (Site d))
    rw [boxSV_coe_boxF]
    exact sct_translate_box_subset_double x.2 ⟨y.1, y.2, rfl⟩
  calc
    criticalFiniteBoxRowSusceptibility d n y ≤
        ∑ x : sctBox d n,
          currentContinuityFreePairKernel d
            (IsingFK.betaC (magnetization d)) (shift x) := by
      unfold criticalFiniteBoxRowSusceptibility
      apply Finset.sum_le_sum
      intro x _hx
      exact criticalFiniteBoxPairCorrelation_le_infinite hd n x y
    _ = ∑ w ∈ Finset.univ.image shift,
          currentContinuityFreePairKernel d
            (IsingFK.betaC (magnetization d)) w := by
      rw [Finset.sum_image hshift.injOn]
    _ ≤ ∑ w ∈ boxSV_boxF d (2 * n),
          currentContinuityFreePairKernel d
            (IsingFK.betaC (magnetization d)) w := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun w _hw _ => criticalFreePairKernel_nonneg hd w)
    _ = criticalFreeBoxSusceptibility d (2 * n) := by
      rw [criticalFreeBoxSusceptibility]



theorem criticalFiniteBoxDistinctIntegratedFourthCumulant_treeDiagram_bound
    (hd : 2 ≤ d) (n : Nat) (i : sctBox d n) :
    0 ≤ -finiteDistinctIntegratedFourthCumulant
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ∧
      -finiteDistinctIntegratedFourthCumulant
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ≤
        2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 := by
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  exact finiteDistinctIntegratedFourthCumulant_treeDiagram_bound
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    hbeta (fun _ => by norm_num) (criticalFreeBoxSusceptibility d (2 * n))
    (criticalFreeBoxSusceptibility_nonneg hd (2 * n))
    (criticalFiniteBoxRowSusceptibility_le hd n) i


def criticalFiniteBoxOrigin (d n : Nat) : sctBox d n :=
  ⟨Percolation.origin d, origin_mem_box' n⟩



def criticalFiniteBoxRenormalizedFourthCoupling (d n : Nat) : Real :=
  -finiteDistinctIntegratedFourthCumulant
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
      (criticalFiniteBoxOrigin d n) /
    (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)



theorem criticalFiniteBoxRenormalizedFourthCoupling_bounds
    (hd : 2 ≤ d) (n : Nat) :
    0 ≤ criticalFiniteBoxRenormalizedFourthCoupling d n ∧
      criticalFiniteBoxRenormalizedFourthCoupling d n ≤
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 /
          ((2 * n + 1 : Nat) : Real) ^ d := by
  let U : Real := -finiteDistinctIntegratedFourthCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    (criticalFiniteBoxOrigin d n)
  let chi : Real := criticalFreeBoxSusceptibility d (2 * n)
  let radius : Real := ((2 * n + 1 : Nat) : Real)
  have hU : 0 ≤ U ∧ U ≤ 2 * chi ^ 4 := by
    simpa [U, chi] using
      criticalFiniteBoxDistinctIntegratedFourthCumulant_treeDiagram_bound
        hd n (criticalFiniteBoxOrigin d n)
  have hchi : 0 < chi := by
    have := one_le_criticalFreeBoxSusceptibility hd (2 * n)
    dsimp [chi]
    linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hden : 0 < 2 * chi ^ 2 * radius ^ d := by positivity
  change 0 ≤ U / (2 * chi ^ 2 * radius ^ d) ∧
    U / (2 * chi ^ 2 * radius ^ d) ≤ chi ^ 2 / radius ^ d
  constructor
  · exact div_nonneg hU.1 hden.le
  · rw [div_le_iff₀ hden]
    calc
      U ≤ 2 * chi ^ 4 := hU.2
      _ = (chi ^ 2 / radius ^ d) *
          (2 * chi ^ 2 * radius ^ d) := by
        field_simp [ne_of_gt hradius]



theorem criticalFiniteBoxRenormalizedFourthCoupling_tendsto_zero
    (d : Nat) (hd : 4 < d) :
    Tendsto (fun n => criticalFiniteBoxRenormalizedFourthCoupling d n)
      atTop (nhds 0) := by
  obtain ⟨A, hA, hchiUpper⟩ :=
    exists_criticalFreeBoxSusceptibility_le_quadratic (d := d) (by omega)
  let radius : Nat → Real := fun n => ((2 * n + 1 : Nat) : Real)
  let chi : Nat → Real := fun n => criticalFreeBoxSusceptibility d (2 * n)
  have hradiusNat : Tendsto (fun n : Nat => 2 * n + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hradius : Tendsto radius atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hradiusNat
  have hpower : Tendsto (fun n => radius n ^ (d - 4)) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => ?_) hradius
    have hradiusOne : 1 ≤ radius n := by
      dsimp [radius]
      norm_num
    simpa only [pow_one] using
      pow_le_pow_right₀ hradiusOne (show 1 ≤ d - 4 by omega)
  have henvelope : Tendsto
      (fun n => A ^ 2 / radius n ^ (d - 4)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpower
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      (criticalFiniteBoxRenormalizedFourthCoupling_bounds (d := d)
        (by omega) n).1) _ henvelope
  filter_upwards with n
  have hradiusPos : 0 < radius n := by
    dsimp [radius]
    positivity
  have hchiNonneg : 0 ≤ chi n := by
    dsimp [chi]
    exact criticalFreeBoxSusceptibility_nonneg (by omega) (2 * n)
  have hchiLe : chi n ≤ A * radius n ^ 2 := by
    simpa [chi, radius] using hchiUpper (2 * n)
  have hchiSq : chi n ^ 2 ≤ (A * radius n ^ 2) ^ 2 :=
    (sq_le_sq₀ hchiNonneg (by positivity)).2 hchiLe
  calc
    criticalFiniteBoxRenormalizedFourthCoupling d n ≤
        chi n ^ 2 / radius n ^ d := by
      simpa [chi, radius] using
        (criticalFiniteBoxRenormalizedFourthCoupling_bounds (d := d)
          (by omega) n).2
    _ ≤ (A * radius n ^ 2) ^ 2 / radius n ^ d := by
      exact div_le_div_of_nonneg_right hchiSq (pow_nonneg hradiusPos.le d)
    _ = A ^ 2 / radius n ^ (d - 4) := by
      have hd' : d = (d - 4) + 4 := by omega
      rw [hd', pow_add]
      field_simp
      congr 3
      omega

end CriticalFiniteBox

end

end StatMech.FrontierA
