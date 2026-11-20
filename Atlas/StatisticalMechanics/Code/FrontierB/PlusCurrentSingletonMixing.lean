/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.PlusParityPatternMixing

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice

def mergeLocalPattern {E A : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (a : ↑S -> A) (b : ↑T -> A) : ↑(S ∪ T) -> A :=
  fun i => if hi : i.1 ∈ S then a ⟨i.1, hi⟩
    else b ⟨i.1, (Finset.mem_union.mp i.2).resolve_left hi⟩

@[simp] theorem mergeLocalPattern_left {E A : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (a : ↑S -> A) (b : ↑T -> A) (e : E) (he : e ∈ S) :
    mergeLocalPattern S T hdisj a b ⟨e, Finset.mem_union_left T he⟩ =
      a ⟨e, he⟩ := by
  simp [mergeLocalPattern, he]

@[simp] theorem mergeLocalPattern_right {E A : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (a : ↑S -> A) (b : ↑T -> A) (e : E) (he : e ∈ T) :
    mergeLocalPattern S T hdisj a b ⟨e, Finset.mem_union_right S he⟩ =
      b ⟨e, he⟩ := by
  have hnot : e ∉ S := Finset.disjoint_right.mp hdisj he
  simp [mergeLocalPattern, hnot]

theorem finiteParityKernel_merge {E : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T) (beta : Real)
    (odd : ↑S -> Bool) (odd' : ↑T -> Bool)
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    finiteParityKernel (S ∪ T) beta
        (mergeLocalPattern S T hdisj odd odd')
        (mergeLocalPattern S T hdisj a b) =
      finiteParityKernel S beta odd a * finiteParityKernel T beta odd' b := by
  unfold finiteParityKernel
  calc
    (∏ i, parityEdgeKernel beta (mergeLocalPattern S T hdisj odd odd' i)
        (mergeLocalPattern S T hdisj a b i)) =
        ∏ z : ↑S ⊕ ↑T, match z with
          | Sum.inl i => parityEdgeKernel beta (odd i) (a i)
          | Sum.inr i => parityEdgeKernel beta (odd' i) (b i) := by
      symm
      apply Fintype.prod_equiv (Equiv.Finset.union S T hdisj)
      intro i
      cases i with
      | inl i => simp [mergeLocalPattern]
      | inr i =>
          have hnot : i.1 ∉ S := Finset.disjoint_right.mp hdisj i.2
          simp [mergeLocalPattern, hnot]
    _ = (∏ i, parityEdgeKernel beta (odd i) (a i)) *
        ∏ i, parityEdgeKernel beta (odd' i) (b i) :=
      Fintype.prod_sum_type _

theorem finiteParityPMF_merge {E : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T) (beta : Real) (hbeta : 0 < beta)
    (odd : ↑S -> Bool) (odd' : ↑T -> Bool)
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    finiteParityPMF (S ∪ T) beta hbeta
        (mergeLocalPattern S T hdisj odd odd')
        (mergeLocalPattern S T hdisj a b) =
      finiteParityPMF S beta hbeta odd a *
        finiteParityPMF T beta hbeta odd' b := by
  rw [finiteParityPMF_apply, finiteParityPMF_apply, finiteParityPMF_apply,
    finiteParityKernel_merge]
  rw [ENNReal.ofReal_mul]
  exact Finset.prod_nonneg fun i _ => parityEdgeKernel_nonneg beta hbeta _ _

theorem currentLocalParity_merge {E : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    currentLocalParity (mergeLocalPattern S T hdisj a b) =
      mergeLocalPattern S T hdisj (currentLocalParity a) (currentLocalParity b) := by
  funext i
  by_cases hi : i.1 ∈ S
  · simp [currentLocalParity, mergeLocalPattern, hi]
  · have hit : i.1 ∈ T := (Finset.mem_union.mp i.2).resolve_left hi
    simp [currentLocalParity, mergeLocalPattern, hi, hit]

theorem currentCylinder_singleton_inter_of_disjoint {E : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    currentCylinder S {a} ∩ currentCylinder T {b} =
      currentCylinder (S ∪ T) {mergeLocalPattern S T hdisj a b} := by
  ext m
  simp only [currentCylinder, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hb⟩
    funext i
    by_cases hi : i.1 ∈ S
    · rw [mergeLocalPattern]
      simp only [dif_pos hi]
      exact congrFun ha ⟨i.1, hi⟩
    · have hit : i.1 ∈ T := (Finset.mem_union.mp i.2).resolve_left hi
      rw [mergeLocalPattern]
      simp only [dif_neg hi]
      exact congrFun hb ⟨i.1, hit⟩
  · intro h
    constructor
    · funext i
      have hi := congrFun h ⟨i.1, Finset.mem_union_left T i.2⟩
      simpa using hi
    · funext i
      have hi := congrFun h ⟨i.1, Finset.mem_union_right S i.2⟩
      simpa using hi

theorem currentParityPatternCylinder_inter_of_disjoint
    {E : Type*} [DecidableEq E]
    (S T : Finset E) (hdisj : Disjoint S T)
    (odd : ↑S -> Bool) (odd' : ↑T -> Bool) :
    currentParityPatternCylinder S odd ∩ currentParityPatternCylinder T odd' =
      currentParityPatternCylinder (S ∪ T)
        (mergeLocalPattern S T hdisj odd odd') := by
  ext m
  change currentLocalParity (restrictCurrent S m) = odd ∧
      currentLocalParity (restrictCurrent T m) = odd' ↔
    currentLocalParity (restrictCurrent (S ∪ T) m) =
      mergeLocalPattern S T hdisj odd odd'
  constructor
  · rintro ⟨hodd, hodd'⟩
    funext i
    by_cases hi : i.1 ∈ S
    · rw [mergeLocalPattern]
      simp only [dif_pos hi]
      exact congrFun hodd ⟨i.1, hi⟩
    · have hit : i.1 ∈ T := (Finset.mem_union.mp i.2).resolve_left hi
      rw [mergeLocalPattern]
      simp only [dif_neg hi]
      exact congrFun hodd' ⟨i.1, hit⟩
  · intro h
    constructor
    · funext i
      have hi := congrFun h ⟨i.1, Finset.mem_union_left T i.2⟩
      simpa using hi
    · funext i
      have hi := congrFun h ⟨i.1, Finset.mem_union_right S i.2⟩
      simpa using hi

theorem currentCylinder_singleton_inter_shift_of_disjoint
    {E H : Type*} [DecidableEq E] [Group H] [MulAction H E]
    (g : H) (S T : Finset E)
    (hdisj : Disjoint S (currentShiftFinset g T))
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b} =
      currentCylinder (S ∪ currentShiftFinset g T)
        {mergeLocalPattern S (currentShiftFinset g T) hdisj a
          (currentShiftPattern g T b)} := by
  rw [preimage_currentCylinder_singleton_currentShift]
  exact currentCylinder_singleton_inter_of_disjoint S
    (currentShiftFinset g T) hdisj a (currentShiftPattern g T b)

theorem currentParityPatternCylinder_inter_shift_of_disjoint
    {E H : Type*} [DecidableEq E] [Group H] [MulAction H E]
    (g : H) (S T : Finset E)
    (hdisj : Disjoint S (currentShiftFinset g T))
    (odd : ↑S -> Bool) (odd' : ↑T -> Bool) :
    currentParityPatternCylinder S odd ∩
        (currentShift g) ⁻¹' currentParityPatternCylinder T odd' =
      currentParityPatternCylinder (S ∪ currentShiftFinset g T)
        (mergeLocalPattern S (currentShiftFinset g T) hdisj odd
          (currentShiftPattern g T odd')) := by
  rw [preimage_currentParityPatternCylinder_currentShift]
  exact currentParityPatternCylinder_inter_of_disjoint S
    (currentShiftFinset g T) hdisj odd (currentShiftPattern g T odd')

theorem infinitePlusCurrentMeasure_singleton_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) (a : ↑S -> Nat) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentCylinder S {a}) =
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityPatternCylinder S (currentLocalParity a)) *
        ENNReal.toReal
          (finiteParityPMF S beta hbeta (currentLocalParity a) a) := by
  have hfactor := plusCurrentLimit_pattern_factor d beta hbeta S hS
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
    (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le) a
  rw [Measure.real, Measure.real, hfactor, ENNReal.toReal_mul]



theorem infinitePlusCurrentMeasure_singleton_inter_shift_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (S T : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hT : (↑T : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint S (currentShiftFinset g T))
    (a : ↑S -> Nat) (b : ↑T -> Nat) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentCylinder S {a} ∩ (currentShift g) ⁻¹' currentCylinder T {b}) =
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S (currentLocalParity a) ∩
          (currentShift g) ⁻¹'
            currentParityPatternCylinder T (currentLocalParity b)) *
        (ENNReal.toReal
          (finiteParityPMF S beta hbeta (currentLocalParity a) a) *
        ENNReal.toReal
          (finiteParityPMF T beta hbeta (currentLocalParity b) b)) := by
  let G := currentShiftFinset g T
  let bG := currentShiftPattern g T b
  let c := mergeLocalPattern S G hdisj a bG
  have hG : (↑G : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := currentShiftFinset_lattice d g T hT
  have hSG : (↑(S ∪ G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    intro e he
    change e ∈ S ∪ G at he
    rw [Finset.mem_union] at he
    exact he.elim (fun h => hS h) (fun h => hG h)
  rw [currentCylinder_singleton_inter_shift_of_disjoint g S T hdisj a b]
  rw [infinitePlusCurrentMeasure_singleton_real_eq hbeta (S ∪ G) hSG c]
  have hparity : currentLocalParity c =
      mergeLocalPattern S G hdisj (currentLocalParity a)
        (currentShiftPattern g T (currentLocalParity b)) := by
    dsimp [c, bG]
    rw [currentLocalParity_merge, currentLocalParity_shiftPattern]
  rw [hparity]
  rw [← currentParityPatternCylinder_inter_shift_of_disjoint g S T hdisj
    (currentLocalParity a) (currentLocalParity b)]
  have hkernel := finiteParityPMF_merge S G hdisj beta hbeta
    (currentLocalParity a) (currentShiftPattern g T (currentLocalParity b)) a bG
  rw [show c = mergeLocalPattern S G hdisj a bG by rfl]
  rw [hkernel, finiteParityPMF_shiftPattern g T beta hbeta
    (currentLocalParity b) b, ENNReal.toReal_mul]



theorem infinitePlusCurrentMeasure_singleton_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S T : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hT : (↑T : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (a : ↑S -> Nat) (b : ↑T -> Nat)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g T) ∧
      abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentCylinder S {a} ∩
            (currentShift g) ⁻¹' currentCylinder T {b}) -
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder S {a}) *
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentCylinder T {b})) < epsilon := by
  obtain ⟨g, hdisj, hmix⟩ :=
    infinitePlusCurrentMeasure_parityPattern_pairMixing hd hbeta S T
      (currentLocalParity a) (currentLocalParity b) hS hT epsilon hepsilon
  let k := ENNReal.toReal
    (finiteParityPMF S beta hbeta (currentLocalParity a) a)
  let k' := ENNReal.toReal
    (finiteParityPMF T beta hbeta (currentLocalParity b) b)
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  have hk' : 0 ≤ k' := ENNReal.toReal_nonneg
  have hkle : k ≤ 1 := by
    dsimp [k]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (finiteParityPMF S beta hbeta (currentLocalParity a)) a)
  have hk'le : k' ≤ 1 := by
    dsimp [k']
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (finiteParityPMF T beta hbeta (currentLocalParity b)) b)
  refine ⟨g, hdisj, ?_⟩
  rw [infinitePlusCurrentMeasure_singleton_inter_shift_real_eq hbeta g S T
      hS hT hdisj a b,
    infinitePlusCurrentMeasure_singleton_real_eq hbeta S hS a,
    infinitePlusCurrentMeasure_singleton_real_eq hbeta T hT b]
  let p := (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a) ∩
      (currentShift g) ⁻¹' currentParityPatternCylinder T (currentLocalParity b))
  let q := (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder S (currentLocalParity a))
  let r := (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
    (currentParityPatternCylinder T (currentLocalParity b))
  change abs (p * (k * k') - (q * k) * (r * k')) < epsilon
  have hfactor : p * (k * k') - (q * k) * (r * k') =
      (k * k') * (p - q * r) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg (mul_nonneg hk hk')]
  calc
    k * k' * abs (p - q * r) ≤ 1 * abs (p - q * r) := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith
    _ < epsilon := by simpa [p, q, r] using hmix

end StatMech.FrontierB
