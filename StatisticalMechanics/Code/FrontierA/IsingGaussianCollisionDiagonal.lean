/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianCriticalSummation










open Filter Finset Set Topology
open scoped BigOperators symmDiff

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



def finiteParityFourthUrsell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k l : V) : Real :=
  expectationJ G beta J (grahamFourSupport i j k l) -
    expectationJ G beta J (grahamPairSupport i j) *
      expectationJ G beta J (grahamPairSupport k l) -
    expectationJ G beta J (grahamPairSupport i k) *
      expectationJ G beta J (grahamPairSupport j l) -
    expectationJ G beta J (grahamPairSupport i l) *
      expectationJ G beta J (grahamPairSupport j k)

private theorem pairCorrelation_self
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (x : V) :
    expectationJ G beta J (grahamPairSupport x x) = 1 := by
  simpa [twoPointJ, grahamPairSupport] using
    twoPointJ_self G beta J x

private theorem pairCorrelation_comm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (x y : V) :
    expectationJ G beta J (grahamPairSupport x y) =
      expectationJ G beta J (grahamPairSupport y x) := by
  unfold grahamPairSupport
  rw [symmDiff_comm]

theorem finiteParityFourthUrsell_eq_of_firstPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i k l : V) :
    finiteParityFourthUrsell G beta J i i k l =
      -2 * expectationJ G beta J (grahamPairSupport i k) *
        expectationJ G beta J (grahamPairSupport i l) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i i ∆ grahamPairSupport k l =
      grahamPairSupport k l by simp [grahamPairSupport]]
  rw [pairCorrelation_self]
  ring

theorem finiteParityFourthUrsell_eq_of_secondPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j l : V) :
    finiteParityFourthUrsell G beta J i j j l =
      -2 * expectationJ G beta J (grahamPairSupport j i) *
        expectationJ G beta J (grahamPairSupport j l) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [grahamPairSupport_chain]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J i j]
  ring

theorem finiteParityFourthUrsell_eq_of_firstThird
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j l : V) :
    finiteParityFourthUrsell G beta J i j i l =
      -2 * expectationJ G beta J (grahamPairSupport i j) *
        expectationJ G beta J (grahamPairSupport i l) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i j ∆ grahamPairSupport i l =
      grahamPairSupport j l by
    rw [show grahamPairSupport i j = grahamPairSupport j i by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    exact grahamPairSupport_chain j i l]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J j i]
  ring

theorem finiteParityFourthUrsell_eq_of_firstFourth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k : V) :
    finiteParityFourthUrsell G beta J i j k i =
      -2 * expectationJ G beta J (grahamPairSupport i j) *
        expectationJ G beta J (grahamPairSupport i k) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i j ∆ grahamPairSupport k i =
      grahamPairSupport j k by
    rw [show grahamPairSupport i j = grahamPairSupport j i by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    rw [show grahamPairSupport k i = grahamPairSupport i k by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    exact grahamPairSupport_chain j i k]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J j i,
    pairCorrelation_comm G beta J k i]
  ring

theorem finiteParityFourthUrsell_eq_of_secondFourth
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k : V) :
    finiteParityFourthUrsell G beta J i j k j =
      -2 * expectationJ G beta J (grahamPairSupport j i) *
        expectationJ G beta J (grahamPairSupport j k) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport i j ∆ grahamPairSupport k j =
      grahamPairSupport i k by
    rw [show grahamPairSupport k j = grahamPairSupport j k by
      unfold grahamPairSupport; rw [symmDiff_comm]]
    exact grahamPairSupport_chain i j k]
  rw [pairCorrelation_self]
  rw [pairCorrelation_comm G beta J i j,
    pairCorrelation_comm G beta J k j]
  ring

theorem finiteParityFourthUrsell_eq_of_thirdPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k : V) :
    finiteParityFourthUrsell G beta J i j k k =
      -2 * expectationJ G beta J (grahamPairSupport k i) *
        expectationJ G beta J (grahamPairSupport k j) := by
  unfold finiteParityFourthUrsell grahamFourSupport
  rw [show grahamPairSupport k k = ∅ by simp [grahamPairSupport]]
  rw [show grahamPairSupport i j ∆ (∅ : Finset V) =
      grahamPairSupport i j by
    ext x
    simp [Finset.mem_symmDiff]]
  rw [show expectationJ G beta J (∅ : Finset V) = 1 by
    simpa [grahamPairSupport] using pairCorrelation_self G beta J k]
  rw [pairCorrelation_comm G beta J i k,
    pairCorrelation_comm G beta J j k]
  ring

private theorem pairCorrelation_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (x y : V) :
    0 ≤ expectationJ G beta J (grahamPairSupport x y) := by
  rw [current_representation]
  exact div_nonneg
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)


def finiteCollisionFourthMajorant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k l : V) : Real :=
  let C := fun x y => expectationJ G beta J (grahamPairSupport x y)
  2 * ((if i = j then C i k * C i l else 0) +
    (if i = k then C i j * C i l else 0) +
    (if i = l then C i j * C i k else 0) +
    (if j = k then C j i * C j l else 0) +
    (if j = l then C j i * C j k else 0) +
    (if k = l then C k i * C k j else 0))



def finiteCollisionFourthWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i j k l : V) : Real :=
  if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then 0
  else -finiteParityFourthUrsell G beta J i j k l

theorem finiteCollisionFourthWeight_nonneg_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (i j k l : V) :
    0 ≤ finiteCollisionFourthWeight G beta J i j k l ∧
      finiteCollisionFourthWeight G beta J i j k l ≤
        finiteCollisionFourthMajorant G beta J i j k l := by
  have hC (x y : V) :
      0 ≤ expectationJ G beta J (grahamPairSupport x y) :=
    pairCorrelation_nonneg G beta J hbeta hJ x y
  have hite (p : Prop) [Decidable p] (a b c e : V) :
      0 ≤ if p then
        expectationJ G beta J (grahamPairSupport a b) *
          expectationJ G beta J (grahamPairSupport c e) else 0 := by
    split
    · exact mul_nonneg (hC a b) (hC c e)
    · rfl
  have h1 := hite (i = j) i k i l
  have h2 := hite (i = k) i j i l
  have h3 := hite (i = l) i j i k
  have h4 := hite (j = k) j i j l
  have h5 := hite (j = l) j i j k
  have h6 := hite (k = l) k i k j
  by_cases hij : i = j
  · subst j
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_firstPair]
    constructor
    · have hp := mul_nonneg (hC i k) (hC i l)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hik : i = k
  · subst k
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_firstThird]
    constructor
    · have hp := mul_nonneg (hC i j) (hC i l)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hil : i = l
  · subst l
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_firstFourth]
    constructor
    · have hp := mul_nonneg (hC i j) (hC i k)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hjk : j = k
  · subst k
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_secondPair]
    constructor
    · have hp := mul_nonneg (hC j i) (hC j l)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hjl : j = l
  · subst l
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_secondFourth]
    constructor
    · have hp := mul_nonneg (hC j i) (hC j k)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hkl : k = l
  · subst l
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_thirdPair]
    constructor
    · have hp := mul_nonneg (hC k i) (hC k j)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  · rw [finiteCollisionFourthWeight, if_pos]
    · constructor
      · rfl
      · unfold finiteCollisionFourthMajorant
        simp [hij, hik, hil, hjk, hjl, hkl]
    · exact ⟨hij, hik, hil, hjk, hjl, hkl⟩


def finiteCollisionIntegratedFourthCumulant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i : V) : Real :=
  ∑ j : V, ∑ k : V, ∑ l : V,
    finiteCollisionFourthWeight G beta J i j k l


theorem finiteCollisionIntegratedFourthCumulant_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (chi : Real) (hchi : 0 ≤ chi)
    (hrow : ∀ y : V,
      ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi)
    (i : V) :
    0 ≤ finiteCollisionIntegratedFourthCumulant G beta J i ∧
      finiteCollisionIntegratedFourthCumulant G beta J i ≤ 12 * chi ^ 2 := by
  let C : V → V → Real := fun x y =>
    expectationJ G beta J (grahamPairSupport x y)
  have hC (x y : V) : 0 ≤ C x y :=
    pairCorrelation_nonneg G beta J hbeta hJ x y
  have hsymm (x y : V) : C x y = C y x := by
    exact pairCorrelation_comm G beta J x y
  have hrow' (y : V) : ∑ x : V, C y x ≤ chi := by
    calc
      ∑ x : V, C y x = ∑ x : V, C x y := by
        apply Finset.sum_congr rfl
        intro x _
        exact hsymm y x
      _ ≤ chi := hrow y
  let A1 := ∑ j : V, ∑ k : V, ∑ l : V,
    if i = j then C i k * C i l else 0
  let A2 := ∑ j : V, ∑ k : V, ∑ l : V,
    if i = k then C i j * C i l else 0
  let A3 := ∑ j : V, ∑ k : V, ∑ l : V,
    if i = l then C i j * C i k else 0
  let A4 := ∑ j : V, ∑ k : V, ∑ l : V,
    if j = k then C j i * C j l else 0
  let A5 := ∑ j : V, ∑ k : V, ∑ l : V,
    if j = l then C j i * C j k else 0
  let A6 := ∑ j : V, ∑ k : V, ∑ l : V,
    if k = l then C k i * C k j else 0
  have hA1 : A1 ≤ chi ^ 2 := by
    dsimp [A1]
    calc
      _ = (∑ k : V, C i k) * (∑ l : V, C i l) := by
        simp [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ chi * chi := mul_le_mul (hrow' i) (hrow' i)
        (Finset.sum_nonneg fun x _ => hC i x) hchi
      _ = chi ^ 2 := by ring
  have hA2 : A2 ≤ chi ^ 2 := by
    dsimp [A2]
    calc
      _ = (∑ j : V, C i j) * (∑ l : V, C i l) := by
        simp [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ chi * chi := mul_le_mul (hrow' i) (hrow' i)
        (Finset.sum_nonneg fun x _ => hC i x) hchi
      _ = chi ^ 2 := by ring
  have hA3 : A3 ≤ chi ^ 2 := by
    dsimp [A3]
    calc
      _ = (∑ j : V, C i j) * (∑ k : V, C i k) := by
        simp [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ chi * chi := mul_le_mul (hrow' i) (hrow' i)
        (Finset.sum_nonneg fun x _ => hC i x) hchi
      _ = chi ^ 2 := by ring
  have hA4 : A4 ≤ chi ^ 2 := by
    dsimp [A4]
    calc
      _ = ∑ j : V, C j i * (∑ l : V, C j l) := by
        simp [Finset.mul_sum]
      _ ≤ ∑ j : V, C j i * chi := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hrow' j) (hC j i)
      _ = (∑ j : V, C j i) * chi := by rw [Finset.sum_mul]
      _ ≤ chi * chi := mul_le_mul_of_nonneg_right (hrow i) hchi
      _ = chi ^ 2 := by ring
  have hA5 : A5 ≤ chi ^ 2 := by
    dsimp [A5]
    calc
      _ = ∑ j : V, C j i * (∑ k : V, C j k) := by
        simp [Finset.mul_sum]
      _ ≤ ∑ j : V, C j i * chi := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hrow' j) (hC j i)
      _ = (∑ j : V, C j i) * chi := by rw [Finset.sum_mul]
      _ ≤ chi * chi := mul_le_mul_of_nonneg_right (hrow i) hchi
      _ = chi ^ 2 := by ring
  have hA6 : A6 ≤ chi ^ 2 := by
    dsimp [A6]
    calc
      _ = ∑ k : V, C k i * (∑ j : V, C k j) := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
      _ ≤ ∑ k : V, C k i * chi := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hrow' k) (hC k i)
      _ = (∑ k : V, C k i) * chi := by rw [Finset.sum_mul]
      _ ≤ chi * chi := mul_le_mul_of_nonneg_right (hrow i) hchi
      _ = chi ^ 2 := by ring
  have hnonneg : 0 ≤ finiteCollisionIntegratedFourthCumulant G beta J i := by
    unfold finiteCollisionIntegratedFourthCumulant
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ =>
        (finiteCollisionFourthWeight_nonneg_le G beta J hbeta hJ i j k l).1
  refine ⟨hnonneg, ?_⟩
  calc
    finiteCollisionIntegratedFourthCumulant G beta J i ≤
        ∑ j : V, ∑ k : V, ∑ l : V,
          finiteCollisionFourthMajorant G beta J i j k l := by
      unfold finiteCollisionIntegratedFourthCumulant
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun l _ =>
          (finiteCollisionFourthWeight_nonneg_le G beta J hbeta hJ i j k l).2
    _ = 2 * (A1 + A2 + A3 + A4 + A5 + A6) := by
      dsimp [A1, A2, A3, A4, A5, A6, C]
      simp only [finiteCollisionFourthMajorant]
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 12 * chi ^ 2 := by
      have hsum : A1 + A2 + A3 + A4 + A5 + A6 ≤ 6 * chi ^ 2 := by
        linarith
      nlinarith

private theorem finiteParityFourthUrsell_eq_finiteIsing_of_distinct
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteParityFourthUrsell G beta J i j k l =
      finiteIsingFourthUrsell G beta J i j k l := by
  have hpair (x y : V) (hxy : x ≠ y) :
      grahamPairSupport x y = {x, y} := by
    ext z
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    aesop
  have hquad : grahamFourSupport i j k l = {i, j, k, l} := by
    rw [grahamFourSupport, hpair i j hij, hpair k l hkl]
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  unfold finiteParityFourthUrsell finiteIsingFourthUrsell
  rw [hquad, hpair i j hij, hpair i k hik, hpair i l hil,
    hpair j k hjk, hpair j l hjl, hpair k l hkl]



def finiteParityIntegratedFourthCumulant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i : V) : Real :=
  ∑ j : V, ∑ k : V, ∑ l : V,
    finiteParityFourthUrsell G beta J i j k l



theorem neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i : V) :
    -finiteParityIntegratedFourthCumulant G beta J i =
      -finiteDistinctIntegratedFourthCumulant G beta J i +
        finiteCollisionIntegratedFourthCumulant G beta J i := by
  unfold finiteParityIntegratedFourthCumulant
    finiteDistinctIntegratedFourthCumulant
    finiteCollisionIntegratedFourthCumulant
  simp_rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l
  · rw [finiteCollisionFourthWeight, if_pos h, if_pos h, add_zero]
    exact congrArg Neg.neg
      (finiteParityFourthUrsell_eq_finiteIsing_of_distinct
        G beta J h.1 h.2.1 h.2.2.1 h.2.2.2.1
          h.2.2.2.2.1 h.2.2.2.2.2)
  · rw [finiteCollisionFourthWeight, if_neg h, if_neg h]
    ring



theorem finiteParityIntegratedFourthCumulant_treeDiagram_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (chi : Real) (hchi : 0 ≤ chi)
    (hrow : ∀ y : V,
      ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi)
    (i : V) :
    0 ≤ -finiteParityIntegratedFourthCumulant G beta J i ∧
      -finiteParityIntegratedFourthCumulant G beta J i ≤
        2 * chi ^ 4 + 12 * chi ^ 2 := by
  have hdist := finiteDistinctIntegratedFourthCumulant_treeDiagram_bound
    G beta J hbeta hJ chi hchi hrow i
  have hcollision := finiteCollisionIntegratedFourthCumulant_le
    G beta J hbeta hJ chi hchi hrow i
  rw [neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision]
  exact ⟨add_nonneg hdist.1 hcollision.1,
    add_le_add hdist.2 hcollision.2⟩

section CriticalFiniteBox



def criticalFiniteBoxParityIntegratedFourthCumulant (d n : Nat) : Real :=
  finiteParityIntegratedFourthCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    (criticalFiniteBoxOrigin d n)



def criticalFiniteBoxFullRenormalizedFourthCoupling (d n : Nat) : Real :=
  -criticalFiniteBoxParityIntegratedFourthCumulant d n /
    (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)

theorem criticalFiniteBoxFullRenormalizedFourthCoupling_bounds
    (hd : 2 ≤ d) (n : Nat) :
    0 ≤ criticalFiniteBoxFullRenormalizedFourthCoupling d n ∧
      criticalFiniteBoxFullRenormalizedFourthCoupling d n ≤
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 /
            ((2 * n + 1 : Nat) : Real) ^ d +
          6 / ((2 * n + 1 : Nat) : Real) ^ d := by
  let U : Real := -criticalFiniteBoxParityIntegratedFourthCumulant d n
  let chi : Real := criticalFreeBoxSusceptibility d (2 * n)
  let radius : Real := ((2 * n + 1 : Nat) : Real)
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have hU : 0 ≤ U ∧ U ≤ 2 * chi ^ 4 + 12 * chi ^ 2 := by
    simpa [U, chi, criticalFiniteBoxParityIntegratedFourthCumulant] using
      finiteParityIntegratedFourthCumulant_treeDiagram_bound
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
        hbeta (fun _ => by norm_num) chi
        (criticalFreeBoxSusceptibility_nonneg hd (2 * n))
        (criticalFiniteBoxRowSusceptibility_le hd n)
        (criticalFiniteBoxOrigin d n)
  have hchi : 0 < chi := by
    have := one_le_criticalFreeBoxSusceptibility hd (2 * n)
    dsimp [chi]
    linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hden : 0 < 2 * chi ^ 2 * radius ^ d := by positivity
  change 0 ≤ U / (2 * chi ^ 2 * radius ^ d) ∧
    U / (2 * chi ^ 2 * radius ^ d) ≤
      chi ^ 2 / radius ^ d + 6 / radius ^ d
  constructor
  · exact div_nonneg hU.1 hden.le
  · rw [div_le_iff₀ hden]
    calc
      U ≤ 2 * chi ^ 4 + 12 * chi ^ 2 := hU.2
      _ = (chi ^ 2 / radius ^ d + 6 / radius ^ d) *
          (2 * chi ^ 2 * radius ^ d) := by
        field_simp [ne_of_gt hradius]
        ring



theorem criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero
    (d : Nat) (hd : 4 < d) :
    Tendsto (fun n => criticalFiniteBoxFullRenormalizedFourthCoupling d n)
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
  have hpower (p : Nat) (hp : 0 < p) :
      Tendsto (fun n => radius n ^ p) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => ?_) hradius
    have hradiusOne : 1 ≤ radius n := by
      dsimp [radius]
      norm_num
    simpa only [pow_one] using pow_le_pow_right₀ hradiusOne hp
  have hmain : Tendsto
      (fun n => A ^ 2 / radius n ^ (d - 4)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (hpower (d - 4) (by omega))
  have hcollision : Tendsto
      (fun n => 6 / radius n ^ d) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (hpower d (by omega))
  have henvelope : Tendsto
      (fun n => A ^ 2 / radius n ^ (d - 4) + 6 / radius n ^ d)
      atTop (nhds 0) := by
    simpa using hmain.add hcollision
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      (criticalFiniteBoxFullRenormalizedFourthCoupling_bounds (d := d)
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
    criticalFiniteBoxFullRenormalizedFourthCoupling d n ≤
        chi n ^ 2 / radius n ^ d + 6 / radius n ^ d := by
      simpa [chi, radius] using
        (criticalFiniteBoxFullRenormalizedFourthCoupling_bounds (d := d)
          (by omega) n).2
    _ ≤ (A * radius n ^ 2) ^ 2 / radius n ^ d +
          6 / radius n ^ d := by
      gcongr
    _ = A ^ 2 / radius n ^ (d - 4) + 6 / radius n ^ d := by
      congr 1
      have hd' : d = (d - 4) + 4 := by omega
      rw [hd', pow_add]
      field_simp
      congr 3
      omega

end CriticalFiniteBox

end

end StatMech.FrontierA
