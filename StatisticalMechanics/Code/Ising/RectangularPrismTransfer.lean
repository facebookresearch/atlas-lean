/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.CylinderPathExpansion
import Code.Ising.CenterMarkedPath
import Code.Ising.PositiveTransferCenterObservable
import Code.FrontierA.IsingRectangularDobrushinSpinFlip

open Finset Matrix Filter Topology
open scoped BigOperators

namespace StatMech.Ising

noncomputable section

abbrev RectangularLayerConfig (m n : Nat) :=
  ConfigSpace (Fin m × Fin n)


def rectangularPrismLayer {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) (z : Fin (2 * h + 1)) :
    RectangularLayerConfig m n :=
  fun p => sigma ⟨p.1, p.2, z⟩


def rectangularPrismLayerEquiv (m n h : Nat) :
    RectangularPrismConfig m n h ≃
      (Fin (2 * h + 1) -> RectangularLayerConfig m n) where
  toFun := rectangularPrismLayer
  invFun q := fun v => q v.z (v.x, v.y)
  left_inv sigma := by
    funext v
    rfl
  right_inv q := by
    funext z p
    rfl

@[simp] theorem rectangularPrismLayer_equiv_symm
    {m n h : Nat}
    (q : Fin (2 * h + 1) -> RectangularLayerConfig m n)
    (z : Fin (2 * h + 1)) :
    rectangularPrismLayer ((rectangularPrismLayerEquiv m n h).symm q) z =
      q z := by
  rfl


def rectangularPrismSiteEquiv (m n h : Nat) :
    RectangularPrismSite m n h ≃
      Fin m × Fin n × Fin (2 * h + 1) where
  toFun v := (v.x, v.y, v.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv v := by cases v; rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

theorem sum_rectangularPrismSite_eq
    {m n h : Nat} (f : RectangularPrismSite m n h -> Real) :
    (∑ v, f v) = ∑ x : Fin m, ∑ y : Fin n,
      ∑ z : Fin (2 * h + 1), f ⟨x, y, z⟩ := by
  calc
    (∑ v, f v) = ∑ p : Fin m × Fin n × Fin (2 * h + 1),
        f ((rectangularPrismSiteEquiv m n h).symm p) :=
      (Equiv.sum_comp (rectangularPrismSiteEquiv m n h).symm f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rfl

theorem sum_comm_three
    {A B C R : Type*} [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid R] (f : A -> B -> C -> R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem mul_mul_fintype_sum
    {A : Type*} [Fintype A] (a b : Real) (f : A -> Real) :
    a * b * (∑ x, f x) = ∑ x, a * b * f x := by
  rw [Finset.mul_sum]


def rectangularLayerInternalInteraction {m n : Nat}
    (s : RectangularLayerConfig m n) : Real :=
  (∑ x : Fin (m - 1), ∑ y : Fin n,
      spin s (⟨x.val, by omega⟩, y) *
        spin s (⟨x.val + 1, by omega⟩, y)) +
    ∑ x : Fin m, ∑ y : Fin (n - 1),
      spin s (x, ⟨y.val, by omega⟩) *
        spin s (x, ⟨y.val + 1, by omega⟩)


def rectangularLayerBoundaryDegree {m n : Nat} (p : Fin m × Fin n) : Nat :=
  (if p.1.val = 0 then 1 else 0) +
  (if p.1.val + 1 = m then 1 else 0) +
  (if p.2.val = 0 then 1 else 0) +
  (if p.2.val + 1 = n then 1 else 0)



def rectangularLayerBoltzmannInteraction (J beta : Real) {m n : Nat}
    (s : RectangularLayerConfig m n) : Real :=
  beta * J * (rectangularLayerInternalInteraction s +
    ∑ p : Fin m × Fin n,
      rectangularLayerBoundaryDegree p * spin s p)


def rectangularLayerVerticalInteraction (J beta : Real) {m n : Nat}
    (s t : RectangularLayerConfig m n) : Real :=
  beta * J * ∑ p : Fin m × Fin n, spin s p * spin t p


def rectangularLayerFaceBoundary (J beta : Real) {m n : Nat}
    (s : RectangularLayerConfig m n) : Real :=
  beta * J * ∑ p : Fin m × Fin n, spin s p

theorem rectangularPrismSpin_layer
    {m n h : Nat} (sigma : RectangularPrismConfig m n h)
    (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) :
    rectangularPrismSpin sigma x y z =
      spin (rectangularPrismLayer sigma z) (x, y) := rfl

theorem rectangularPrismInternalInteraction_eq_layers
    {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    rectangularPrismInternalInteraction sigma =
      (∑ z : Fin (2 * h + 1),
        rectangularLayerInternalInteraction (rectangularPrismLayer sigma z)) +
      ∑ z : Fin (2 * h), ∑ p : Fin m × Fin n,
        spin (rectangularPrismLayer sigma z.castSucc) p *
          spin (rectangularPrismLayer sigma z.succ) p := by
  unfold rectangularPrismInternalInteraction
    rectangularLayerInternalInteraction rectangularPrismSpin
  rw [Finset.sum_add_distrib]
  rw [sum_comm_three (fun (x : Fin (m - 1)) (y : Fin n)
    (z : Fin (2 * h + 1)) =>
      spin sigma ⟨⟨x.val, by omega⟩, y, z⟩ *
        spin sigma ⟨⟨x.val + 1, by omega⟩, y, z⟩)]
  rw [sum_comm_three (fun (x : Fin m) (y : Fin (n - 1))
    (z : Fin (2 * h + 1)) =>
      spin sigma ⟨x, ⟨y.val, by omega⟩, z⟩ *
        spin sigma ⟨x, ⟨y.val + 1, by omega⟩, z⟩)]
  rw [sum_comm_three (fun (x : Fin m) (y : Fin n) (z : Fin (2 * h)) =>
    spin sigma ⟨x, y, ⟨z.val, by omega⟩⟩ *
      spin sigma ⟨x, y, ⟨z.val + 1, by omega⟩⟩)]
  simp_rw [Fintype.sum_prod_type]
  rfl

theorem rectangularPrismBoundaryDegree_split
    {m n h : Nat} (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) :
    rectangularPrismBoundaryDegree ⟨x, y, z⟩ =
      rectangularLayerBoundaryDegree (x, y) +
        (if z.val = 0 then 1 else 0) +
        (if z.val + 1 = 2 * h + 1 then 1 else 0) := by
  rfl

theorem rectangularPrismPlusBoundaryInteraction_eq_layers
    {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    rectangularPrismPlusBoundaryInteraction sigma =
      (∑ z : Fin (2 * h + 1), ∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p *
          spin (rectangularPrismLayer sigma z) p) +
      (∑ p : Fin m × Fin n,
        spin (rectangularPrismLayer sigma 0) p) +
      ∑ p : Fin m × Fin n,
        spin (rectangularPrismLayer sigma (Fin.last (2 * h))) p := by
  unfold rectangularPrismPlusBoundaryInteraction
  rw [sum_rectangularPrismSite_eq]
  simp_rw [rectangularPrismBoundaryDegree_split]
  simp_rw [Nat.cast_add, add_mul, Finset.sum_add_distrib]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm_three (fun (x : Fin m) (y : Fin n)
    (z : Fin (2 * h + 1)) =>
      (rectangularLayerBoundaryDegree (x, y) : Real) * spin sigma ⟨x, y, z⟩)]
  simp_rw [Fintype.sum_prod_type]
  have hzero (z : Fin (2 * h + 1)) : z.val = 0 ↔ z = 0 := by
    constructor
    · intro hz
      apply Fin.ext
      exact hz
    · intro hz
      subst z
      rfl
  have hlast (z : Fin (2 * h + 1)) :
      z.val + 1 = 2 * h + 1 ↔ z = Fin.last (2 * h) := by
    constructor
    · intro hz
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · intro hz
      subst z
      simp
  simp_rw [hzero, hlast]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl


theorem rectangularPrismPlusExponent_eq_layers
    (J beta : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    -beta * rectangularPrismPlusEnergy J sigma =
      rectangularLayerFaceBoundary J beta
          (rectangularPrismLayer sigma 0) +
        rectangularLayerFaceBoundary J beta
          (rectangularPrismLayer sigma (Fin.last (2 * h))) +
        (∑ z : Fin (2 * h + 1),
          rectangularLayerBoltzmannInteraction J beta
            (rectangularPrismLayer sigma z)) +
        ∑ z : Fin (2 * h),
          rectangularLayerVerticalInteraction J beta
            (rectangularPrismLayer sigma z.castSucc)
            (rectangularPrismLayer sigma z.succ) := by
  rw [rectangularPrismPlusEnergy,
    rectangularPrismInternalInteraction_eq_layers,
    rectangularPrismPlusBoundaryInteraction_eq_layers]
  unfold rectangularLayerFaceBoundary rectangularLayerBoltzmannInteraction
    rectangularLayerVerticalInteraction
  simp only [← mul_assoc]
  ring_nf
  simp_rw [mul_mul_fintype_sum]
  simp_rw [Finset.sum_add_distrib]
  ring


def rectangularPrismTransfer (J beta : Real) (m n : Nat) :
    Matrix (RectangularLayerConfig m n) (RectangularLayerConfig m n) Real :=
  fun s t => Real.exp
    (rectangularLayerBoltzmannInteraction J beta s / 2 +
      rectangularLayerVerticalInteraction J beta s t +
      rectangularLayerBoltzmannInteraction J beta t / 2)


def rectangularPrismTransferBoundaryVector (J beta : Real) (m n : Nat) :
    RectangularLayerConfig m n -> Real :=
  fun s => Real.exp
    (rectangularLayerBoltzmannInteraction J beta s / 2 +
      rectangularLayerFaceBoundary J beta s)


def rectangularPrismTransferPartition
    (J beta : Real) (m n h : Nat) : Real :=
  let A := rectangularPrismTransfer J beta m n
  let a := rectangularPrismTransferBoundaryVector J beta m n
  ∑ s, a s * ((A ^ (2 * h)) *ᵥ a) s

theorem rectangularPrismTransfer_isHermitian
    (J beta : Real) (m n : Nat) :
    (rectangularPrismTransfer J beta m n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  simp only [rectangularPrismTransfer, star_trivial]
  unfold rectangularLayerVerticalInteraction
  congr 1
  rw [show (∑ p : Fin m × Fin n, spin s p * spin t p) =
      ∑ p : Fin m × Fin n, spin t p * spin s p by
    apply Finset.sum_congr rfl
    intro p hp
    ring]
  ring

theorem rectangularPrismTransfer_pos
    (J beta : Real) (m n : Nat)
    (s t : RectangularLayerConfig m n) :
    0 < rectangularPrismTransfer J beta m n s t := Real.exp_pos _

theorem rectangularPrismTransferBoundaryVector_pos
    (J beta : Real) (m n : Nat) (s : RectangularLayerConfig m n) :
    0 < rectangularPrismTransferBoundaryVector J beta m n s := Real.exp_pos _

theorem rectangularPrismTransferPathWeight_eq_exp
    (J beta : Real) (m n h : Nat)
    (q : Fin (2 * h + 1) -> RectangularLayerConfig m n) :
    rectangularPrismTransferBoundaryVector J beta m n (q 0) *
        (∏ z : Fin (2 * h),
          rectangularPrismTransfer J beta m n
            (q z.castSucc) (q z.succ)) *
        rectangularPrismTransferBoundaryVector J beta m n
          (q (Fin.last (2 * h))) =
      Real.exp
        (rectangularLayerFaceBoundary J beta (q 0) +
          rectangularLayerFaceBoundary J beta (q (Fin.last (2 * h))) +
          (∑ z : Fin (2 * h + 1),
            rectangularLayerBoltzmannInteraction J beta (q z)) +
          ∑ z : Fin (2 * h),
            rectangularLayerVerticalInteraction J beta
              (q z.castSucc) (q z.succ)) := by
  simp only [rectangularPrismTransferBoundaryVector,
    rectangularPrismTransfer]
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hfirst := Fin.sum_univ_succ
    (f := fun z : Fin (2 * h + 1) =>
      rectangularLayerBoltzmannInteraction J beta (q z))
  have hlast := Fin.sum_univ_castSucc
    (f := fun z : Fin (2 * h + 1) =>
      rectangularLayerBoltzmannInteraction J beta (q z))
  linear_combination -(1 / 2 : Real) * hfirst - (1 / 2 : Real) * hlast

theorem rectangularPrismTransferPartition_eq_sum_path
    (J beta : Real) (m n h : Nat) :
    rectangularPrismTransferPartition J beta m n h =
      ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n,
        Real.exp
          (rectangularLayerFaceBoundary J beta (q 0) +
            rectangularLayerFaceBoundary J beta (q (Fin.last (2 * h))) +
            (∑ z : Fin (2 * h + 1),
              rectangularLayerBoltzmannInteraction J beta (q z)) +
            ∑ z : Fin (2 * h),
              rectangularLayerVerticalInteraction J beta
                (q z.castSucc) (q z.succ)) := by
  rw [rectangularPrismTransferPartition, dot_mulVec_pow_eq_sum_path]
  apply Finset.sum_congr rfl
  intro q hq
  exact rectangularPrismTransferPathWeight_eq_exp J beta m n h q


theorem rectangularPrismPlusPartition_eq_transferPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismPlusPartition J beta m n h =
      rectangularPrismTransferPartition J beta m n h := by
  rw [rectangularPrismTransferPartition_eq_sum_path]
  unfold rectangularPrismPlusPartition Z
  rw [show (∑ sigma : RectangularPrismConfig m n h,
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma)) =
      ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n,
        Real.exp (-beta * rectangularPrismPlusEnergy J
          ((rectangularPrismLayerEquiv m n h).symm q)) by
    exact (Equiv.sum_comp (rectangularPrismLayerEquiv m n h).symm
      (fun sigma => Real.exp
        (-beta * rectangularPrismPlusEnergy J sigma))).symm]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  exact rectangularPrismPlusExponent_eq_layers J beta
    ((rectangularPrismLayerEquiv m n h).symm q)



theorem rectangularPrismPlusPartition_eq_centerDenominator
    (J beta : Real) (m n h : Nat) :
    rectangularPrismPlusPartition J beta m n h =
      ∑ s, (((rectangularPrismTransfer J beta m n) ^ h) *ᵥ
        rectangularPrismTransferBoundaryVector J beta m n) s ^ 2 := by
  rw [rectangularPrismPlusPartition_eq_transferPartition]
  unfold rectangularPrismTransferPartition
  exact hermitian_twoTail_contraction_eq_sum_sq
    (rectangularPrismTransfer J beta m n)
    (rectangularPrismTransfer_isHermitian J beta m n)
    (rectangularPrismTransferBoundaryVector J beta m n) h



def rectangularPrismPlusCentralSpinNumerator
    (J beta : Real) (m n h : Nat) (p : Fin m × Fin n) : Real :=
  ∑ sigma : RectangularPrismConfig m n h,
    rectangularPrismSpin sigma p.1 p.2 ⟨h, by omega⟩ *
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma)

theorem rectangularPrismPlusCentralSpinNumerator_eq_markedPath
    (J beta : Real) (m n h : Nat) (p : Fin m × Fin n) :
    rectangularPrismPlusCentralSpinNumerator J beta m n h p =
      centerMarkedPathSum
        (rectangularPrismTransfer J beta m n)
        (rectangularPrismTransferBoundaryVector J beta m n)
        (fun s => spin s p) h := by
  unfold rectangularPrismPlusCentralSpinNumerator centerMarkedPathSum
  rw [show (∑ sigma : RectangularPrismConfig m n h,
      rectangularPrismSpin sigma p.1 p.2 ⟨h, by omega⟩ *
        Real.exp (-beta * rectangularPrismPlusEnergy J sigma)) =
      ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n,
        rectangularPrismSpin ((rectangularPrismLayerEquiv m n h).symm q)
            p.1 p.2 ⟨h, by omega⟩ *
          Real.exp (-beta * rectangularPrismPlusEnergy J
            ((rectangularPrismLayerEquiv m n h).symm q)) by
    exact (Equiv.sum_comp (rectangularPrismLayerEquiv m n h).symm
      (fun sigma =>
        rectangularPrismSpin sigma p.1 p.2 ⟨h, by omega⟩ *
          Real.exp (-beta * rectangularPrismPlusEnergy J sigma))).symm]
  apply Finset.sum_congr rfl
  intro q hq
  change spin (q ⟨h, by omega⟩) p *
      Real.exp (-beta * rectangularPrismPlusEnergy J
        ((rectangularPrismLayerEquiv m n h).symm q)) =
    rectangularPrismTransferBoundaryVector J beta m n (q 0) *
      spin (q ⟨h, by omega⟩) p *
      (∏ z : Fin (2 * h), rectangularPrismTransfer J beta m n
        (q z.castSucc) (q z.succ)) *
      rectangularPrismTransferBoundaryVector J beta m n
        (q (Fin.last (2 * h)))
  rw [rectangularPrismPlusExponent_eq_layers]
  simp only [rectangularPrismLayer_equiv_symm]
  rw [← rectangularPrismTransferPathWeight_eq_exp J beta m n h q]
  ring

theorem rectangularPrismPlusCentralSpinNumerator_eq_transferSquare
    (J beta : Real) (m n h : Nat) (p : Fin m × Fin n) :
    rectangularPrismPlusCentralSpinNumerator J beta m n h p =
      ∑ s, spin s p *
        (((rectangularPrismTransfer J beta m n) ^ h) *ᵥ
          rectangularPrismTransferBoundaryVector J beta m n) s ^ 2 := by
  rw [rectangularPrismPlusCentralSpinNumerator_eq_markedPath]
  apply centerMarkedPathSum_eq_sum_sq
  intro s t
  simpa using
    (rectangularPrismTransfer_isHermitian J beta m n).apply t s



def rectangularPrismPlusCentralSpinMean
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) (h : Nat) : Real :=
  rectangularPrismPlusCentralSpinNumerator J beta m n h p /
    rectangularPrismPlusPartition J beta m n h



theorem rectangularPrismPlusPartition_log_div_tendsto
    (J beta : Real) (m n : Nat) :
    ∃ lam : Real, 0 < lam ∧
      Tendsto (fun h : Nat =>
        Real.log (rectangularPrismPlusPartition J beta m n h) /
          (2 * h : Real)) atTop (nhds (Real.log lam)) := by
  obtain ⟨lam, hlam, hlim⟩ :=
    positiveTransfer_log_dotProduct_div_tendsto
      (rectangularPrismTransfer J beta m n)
      (rectangularPrismTransfer_isHermitian J beta m n)
      (rectangularPrismTransfer_pos J beta m n)
      (rectangularPrismTransferBoundaryVector J beta m n)
      (rectangularPrismTransferBoundaryVector J beta m n)
      (rectangularPrismTransferBoundaryVector_pos J beta m n)
      (rectangularPrismTransferBoundaryVector_pos J beta m n)
  refine ⟨lam, hlam, ?_⟩
  rw [show (fun h : Nat =>
      Real.log (rectangularPrismPlusPartition J beta m n h) /
        (2 * h : Real)) =
      fun h : Nat =>
        (Real.log (rectangularPrismTransferPartition J beta m n h) /
          (2 * h : Real)) by
    funext h
    rw [rectangularPrismPlusPartition_eq_transferPartition]]
  have htwo : Tendsto (fun h : Nat => 2 * h) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 ⟨N, fun h hh => by omega⟩
  have hcomp := hlim.comp htwo
  simpa [rectangularPrismTransferPartition, Function.comp_def] using hcomp



def rectangularPrismCenterSpinMean
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) (h : Nat) : Real :=
  let A := rectangularPrismTransfer J beta m n
  let a := rectangularPrismTransferBoundaryVector J beta m n
  (∑ s, spin s p * ((A ^ h) *ᵥ a) s ^ 2) /
    ∑ s, ((A ^ h) *ᵥ a) s ^ 2

theorem rectangularPrismPlusCentralSpinMean_eq_transfer
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) (h : Nat) :
    rectangularPrismPlusCentralSpinMean J beta m n p h =
      rectangularPrismCenterSpinMean J beta m n p h := by
  unfold rectangularPrismPlusCentralSpinMean rectangularPrismCenterSpinMean
  rw [rectangularPrismPlusCentralSpinNumerator_eq_transferSquare,
    rectangularPrismPlusPartition_eq_centerDenominator]


theorem rectangularPrismCenterSpinMean_tendsto
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) :
    ∃ m0 : Real, Tendsto
      (rectangularPrismCenterSpinMean J beta m n p)
      atTop (nhds m0) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, hlim⟩ :=
    positiveTransfer_centerObservable_tendsto
      (rectangularPrismTransfer J beta m n)
      (rectangularPrismTransfer_isHermitian J beta m n)
      (rectangularPrismTransfer_pos J beta m n)
      (rectangularPrismTransferBoundaryVector J beta m n)
      (rectangularPrismTransferBoundaryVector_pos J beta m n)
      (fun s => spin s p)
  exact ⟨(∑ s, spin s p * (u s) ^ 2) / ∑ s, (u s) ^ 2, by
    simpa [rectangularPrismCenterSpinMean] using hlim⟩

theorem rectangularPrismPlusCentralSpinMean_tendsto
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) :
    ∃ m0 : Real, Tendsto
      (rectangularPrismPlusCentralSpinMean J beta m n p)
      atTop (nhds m0) := by
  obtain ⟨m0, hlim⟩ := rectangularPrismCenterSpinMean_tendsto J beta m n p
  refine ⟨m0, ?_⟩
  rw [show rectangularPrismPlusCentralSpinMean J beta m n p =
      rectangularPrismCenterSpinMean J beta m n p by
    funext h
    exact rectangularPrismPlusCentralSpinMean_eq_transfer J beta m n p h]
  exact hlim

end

end StatMech.Ising
