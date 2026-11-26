/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
public import Domains.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward

/-!
# The Kronecker form and stochasticity of the Lander–Green transition

For a pedigree with `n` meioses, the inheritance vector at a locus records, for each meiosis,
whether the grandpaternal or grandmaternal allele was transmitted: a vector `v : Fin n → Bool`.
With no interference, the transition between inheritance vectors at adjacent loci with
recombination fraction `θ` is `T(θ)_{vw} = θᵈ (1 - θ)ⁿ⁻ᵈ` where `d` is the Hamming distance
(`transition`). This file proves that the transition is the product over meioses of `1 - θ`
(no change) or `θ` (change) (the Kronecker form), that its rows sum to `1` (stochasticity),
that it is symmetric, and that the uniform law (`uniformPrior`) is stationary.

## Main definitions

* `InheritanceVector n`: an inheritance vector for `n` meioses.
* `transition θ v w`: the Lander–Green transition probability between inheritance vectors.
* `uniformPrior n`: the uniform law of the inheritance vector at the first locus.

## Main results

* `transition_kronecker_stochastic`: the Kronecker form, row stochasticity, symmetry and
  uniform stationarity of the transition.

## References

* E. S. Lander and P. Green, "Construction of multilocus genetic linkage maps in humans",
  Proc. Natl. Acad. Sci. USA 84 (1987) 2363–2367, pp. 2365–2366.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LanderGreenWanted

open Finset

private theorem transition_eq_prod (n : ℕ) (θ : ℝ) (v w : InheritanceVector n) :
    transition θ v w = ∏ i, if v i = w i then 1 - θ else θ := by
  have hsplit : (∏ i ∈ Finset.univ.filter (fun i => v i = w i),
        (if v i = w i then (1 - θ) else θ)) *
      (∏ i ∈ Finset.univ.filter (fun i => ¬ v i = w i),
        (if v i = w i then (1 - θ) else θ)) =
      ∏ i, (if v i = w i then (1 - θ) else θ) :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hp : (∏ i ∈ Finset.univ.filter (fun i => v i = w i),
        (if v i = w i then (1 - θ) else θ)) =
      (1 - θ) ^ (Finset.univ.filter (fun i => v i = w i)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => ite_eq_left (Finset.mem_filter.mp hi).2
  have hq : (∏ i ∈ Finset.univ.filter (fun i => ¬ v i = w i),
        (if v i = w i then (1 - θ) else θ)) =
      θ ^ (Finset.univ.filter (fun i => ¬ v i = w i)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun i hi => ite_eq_right (Finset.mem_filter.mp hi).2
  have hcard_ne : (Finset.univ.filter (fun i => ¬ v i = w i)).card = hammingDist v w := rfl
  have hcard : (Finset.univ.filter (fun i => v i = w i)).card +
      (Finset.univ.filter (fun i => ¬ v i = w i)).card = n := by
    have h : (Finset.univ.filter (fun i => v i = w i)).card +
        (Finset.univ.filter (fun i => ¬ v i = w i)).card =
        (Finset.univ : Finset (Fin n)).card :=
      Finset.card_filter_add_card_filter_not _
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hcard_eq : (Finset.univ.filter (fun i => v i = w i)).card =
      n - hammingDist v w := by
    rw [hcard_ne] at hcard
    omega
  simp only [transition]
  rw [← hsplit, hp, hq, hcard_ne, hcard_eq, mul_comm]

private theorem sum_bool_factor (v : Bool) (θ : ℝ) :
    (∑ b : Bool, if v = b then (1 - θ) else θ) = 1 := by
  cases v <;> simp

private theorem sum_transition (n : ℕ) (θ : ℝ) (v : InheritanceVector n) :
    ∑ w, transition θ v w = 1 := by
  have hkron : ∀ w, transition θ v w = ∏ i, if v i = w i then (1 - θ) else θ :=
    fun w => transition_eq_prod n θ v w
  simp only [hkron]
  calc (∑ w : Fin n → Bool, ∏ i, if v i = w i then (1 - θ) else θ)
      = ∏ i, ∑ b, if v i = b then (1 - θ) else θ := by
        have h := Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
          (fun i b => if v i = b then (1 - θ) else θ)
        rwa [Fintype.piFinset_univ] at h
    _ = 1 := by simp only [sum_bool_factor, Finset.prod_const_one]

private theorem transition_symm (n : ℕ) (θ : ℝ) (v w : InheritanceVector n) :
    transition θ v w = transition θ w v := by
  simp only [transition, hammingDist_comm]

private theorem sum_stationary (n : ℕ) (θ : ℝ) (w : InheritanceVector n) :
    ∑ v, uniformPrior n * transition θ v w = uniformPrior n := by
  have hrow : ∀ v : InheritanceVector n, ∑ u, transition θ v u = 1 :=
    fun v => sum_transition n θ v
  calc ∑ v, uniformPrior n * transition θ v w
      = ∑ v, uniformPrior n * transition θ w v :=
        Finset.sum_congr rfl fun v _ => by rw [transition_symm n θ v w]
    _ = uniformPrior n * ∑ v, transition θ w v := (Finset.mul_sum _ _ _).symm
    _ = uniformPrior n := by rw [hrow w, mul_one]

/-- **The Kronecker form and stochasticity of the transition** (Lander and Green 1987, p. 2365):
for a recombination fraction `θ` with `0 ≤ θ ≤ 1/2` and any number `n` of meioses, the
transition is the product over meioses of `1 - θ` (no change) or `θ` (change); its rows sum to
`1`; it is symmetric; and the uniform law is stationary.

Source: Lander and Green (1987), p. 2365. -/
public theorem transition_kronecker_stochastic (n : ℕ) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1 / 2) :
    (∀ v w : InheritanceVector n,
        transition θ v w = ∏ i, if v i = w i then 1 - θ else θ) ∧
      (∀ v : InheritanceVector n, ∑ w, transition θ v w = 1) ∧
      (∀ v w : InheritanceVector n, transition θ v w = transition θ w v) ∧
      (∀ w : InheritanceVector n, ∑ v, uniformPrior n * transition θ v w = uniformPrior n)
    := by
  have _ := hθ₀
  have _ := hθ₁
  exact ⟨fun v w => transition_eq_prod n θ v w,
    fun v => sum_transition n θ v,
    fun v w => transition_symm n θ v w,
    fun w => sum_stationary n θ w⟩

end WantedExt.Biology.StatisticalGenetics.LanderGreenWanted
