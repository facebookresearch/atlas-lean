/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalTorusLocalObservables
import Code.FrontierA.IsingGaussianTorusCumulants
import Code.FrontierA.IsingGaussianPhysicalPolarization










open Filter Finset Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness

noncomputable section



theorem finiteIsingWeighted_physical_newmanFourthCumulantControl_nonnegative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (hbeta : 0 ≤ beta) (a : V → Real)
    (ha : ∀ v, 0 ≤ a v) :
    NewmanFourthCumulantControl
      (fun _ order ↦ PhysicalIsing.finiteIsingWeightedCumulant
        G beta a order) := by
  let epsilon : Nat → Real := fun m ↦ 1 / (m + 1 : Real)
  let one : V → Real := fun _ ↦ 1
  let perturbed : Nat → V → Real := fun m ↦ a + epsilon m • one
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat ↦ (1 : Real) / (n + 1)) atTop (nhds 0))
  have hperturbed (m : Nat) (v : V) : 0 < perturbed m v := by
    dsimp [perturbed, epsilon, one]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    exact add_pos_of_nonneg_of_pos (ha v) (by positivity)
  have hpositive :=
    finiteIsingWeighted_physical_newmanFourthCumulantControl_unconditional
      G (fun _ ↦ beta) (fun _ ↦ hbeta) perturbed hperturbed
  have hcumulant (order : Nat) : Tendsto
      (fun m ↦ PhysicalIsing.finiteIsingWeightedCumulant
        G beta (perturbed m) order)
      atTop
      (nhds (PhysicalIsing.finiteIsingWeightedCumulant G beta a order)) := by
    let p := finiteIsingWeightedCumulantLinePolynomial
      G beta a one order
    have hp := p.continuousAt.tendsto.comp hepsilon
    have heval (m : Nat) :
        p.eval (epsilon m) =
          PhysicalIsing.finiteIsingWeightedCumulant
            G beta (perturbed m) order := by
      exact finiteIsingWeightedCumulantLinePolynomial_eval
        G beta a one order (epsilon m)
    have heval0 : p.eval 0 =
        PhysicalIsing.finiteIsingWeightedCumulant G beta a order := by
      simpa [one] using
        finiteIsingWeightedCumulantLinePolynomial_eval
          G beta a one order 0
    have hp' : Tendsto (fun m ↦ p.eval (epsilon m)) atTop
        (nhds (p.eval 0)) := by
      simpa only [Function.comp_apply] using hp
    convert hp' using 1
    · funext m
      exact (heval m).symm
    · exact congrArg nhds heval0.symm
  refine ⟨?_, ?_, ?_⟩
  · intro scale
    exact PhysicalIsing.finiteIsingWeightedCumulant_zero G beta a
  · intro scale order horder
    exact PhysicalIsing.finiteIsingWeightedCumulant_odd G beta a order horder
  · intro scale halfOrder hhalf
    have hleft := (hcumulant (2 * halfOrder)).abs
    have hfourth := (hcumulant 4).abs
    have hsecond := (hcumulant 2).abs
    have hright : Tendsto
        (fun m ↦ (Nat.factorial (2 * halfOrder) : Real) *
          |PhysicalIsing.finiteIsingWeightedCumulant
            G beta (perturbed m) 4| *
          (1 + |PhysicalIsing.finiteIsingWeightedCumulant
            G beta (perturbed m) 2|) ^ (halfOrder - 2))
        atTop
        (nhds ((Nat.factorial (2 * halfOrder) : Real) *
          |PhysicalIsing.finiteIsingWeightedCumulant G beta a 4| *
          (1 + |PhysicalIsing.finiteIsingWeightedCumulant G beta a 2|) ^
            (halfOrder - 2))) := by
      exact ((tendsto_const_nhds.mul hfourth).mul
        ((tendsto_const_nhds.add hsecond).pow (halfOrder - 2)))
    exact le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall fun m ↦
        hpositive.even_order m halfOrder hhalf)



theorem criticalTorusGrowingCompactWeighted_newmanFourthCumulantControl
    {d : Nat} (hd : 2 ≤ d)
    (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (torusScale : Nat → Nat) (ha : ∀ n x, 0 ≤ a n x) :
    NewmanFourthCumulantControl
      (fun n order ↦ criticalTorusCompactWeightedCumulant
        (A n) (a n) (torusScale n) order) := by
  have hweight (n : Nat) (z : IsingDyadicTorus d (torusScale n)) :
      0 ≤ compactTorusWeight (A n) (a n) (torusScale n) z := by
    unfold compactTorusWeight
    apply Finset.sum_nonneg
    intro x hx
    split
    · exact ha n x.1
    · exact le_rfl
  have hpoint (n : Nat) : NewmanFourthCumulantControl
      (fun _ order ↦ PhysicalIsing.finiteIsingWeightedCumulant
        (isingTorusGraph d (torusScale n))
        (IsingFK.betaC (magnetization d))
        (compactTorusWeight (A n) (a n) (torusScale n)) order) := by
    apply finiteIsingWeighted_physical_newmanFourthCumulantControl_nonnegative
    · rw [isingFK_betaC_eq_tildeBetaCIsing hd]
      exact tildeBetaCIsing_nonneg
    · exact hweight n
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (hpoint n).order_zero 0
  · intro n order horder
    exact (hpoint n).odd_order 0 order horder
  · intro n halfOrder hhalf
    exact (hpoint n).even_order 0 halfOrder hhalf

end

end StatMech.FrontierA
