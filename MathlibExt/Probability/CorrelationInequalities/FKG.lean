/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

@[expose] public section

/-!
# The FKG and Holley inequalities on `ConfigSpace E`

For a finite set `E`, configurations `ω : E → Bool` form a finite distributive lattice. This file
specializes Mathlib's four functions theorem consequences (`fkg`, `holley`) to that lattice, in
the probabilistic form used by percolation and the Ising model.

## Main results

* `StatMech.fkg_inequality`: the **FKG inequality**. If a probability weight `π` satisfies the
  FKG lattice condition, any two monotone real functions are positively correlated under `π`.
  Unlike Mathlib's `fkg`, no sign condition is imposed on the functions.
* `StatMech.fkg_inequality_events`: the FKG inequality for two increasing events.
* `StatMech.holley_dominates`: the **Holley inequality** for increasing events: if
  `μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)` and the total masses agree, then `μ₂` gives every
  increasing event at least the mass `μ₁` gives it.

## References

* C. M. Fortuin, P. W. Kasteleyn, J. Ginibre, *Correlation inequalities on some partially ordered
  sets*, Comm. Math. Phys. 22 (1971).
* R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974).
-/

open Finset

namespace StatMech

variable {E : Type*}

/-- The **FKG inequality** (Fortuin, Kasteleyn, Ginibre 1971). Let `π` be a probability weight on
`ConfigSpace E` (`π ≥ 0`, `∑ π = 1`) satisfying the FKG lattice condition. Then any two monotone
functions `f g : ConfigSpace E → ℝ` are positively correlated:
`E_π[f] * E_π[g] ≤ E_π[f * g]`.

See also Mathlib's `fkg`, which assumes `f, g ≥ 0` and does not normalize `π`; this version
removes the sign condition by shifting `f` and `g` by their values at `⊥`. -/
theorem fkg_inequality [Fintype E] [DecidableEq E] {π : ConfigSpace E → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ ω, π ω = 1) (hπ : FKGLatticeCondition π)
    {f g : ConfigSpace E → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ ω, π ω * f ω) * (∑ ω, π ω * g ω) ≤ ∑ ω, π ω * (f ω * g ω) := by
  have key : ∀ (f g : ConfigSpace E → ℝ), Monotone f → Monotone g →
      (0 : ConfigSpace E → ℝ) ≤ f → (0 : ConfigSpace E → ℝ) ≤ g →
      (∑ ω, π ω * f ω) * (∑ ω, π ω * g ω) ≤ ∑ ω, π ω * (f ω * g ω) := by
    intro f g hf hg hf0 hg0
    have hlatt : ∀ a b, π a * π b ≤ π (a ⊓ b) * π (a ⊔ b) :=
      fun a b => (hπ a b).trans (le_of_eq (mul_comm _ _))
    have h := fkg f g π hπ₀ hf0 hg0 hf hg hlatt
    rwa [hnorm, one_mul] at h
  have hfc : ∀ ω, f ⊥ ≤ f ω := fun ω => hf bot_le
  have hgd : ∀ ω, g ⊥ ≤ g ω := fun ω => hg bot_le
  set c := f ⊥ with hc
  set d := g ⊥ with hd
  have hf'm : Monotone (fun ω => f ω - c) := fun a b h => sub_le_sub_right (hf h) c
  have hg'm : Monotone (fun ω => g ω - d) := fun a b h => sub_le_sub_right (hg h) d
  have hf'0 : (0 : ConfigSpace E → ℝ) ≤ fun ω => f ω - c := fun ω => sub_nonneg.mpr (hfc ω)
  have hg'0 : (0 : ConfigSpace E → ℝ) ≤ fun ω => g ω - d := fun ω => sub_nonneg.mpr (hgd ω)
  have hk := key _ _ hf'm hg'm hf'0 hg'0
  have e1 : ∑ ω, π ω * (f ω - c) = (∑ ω, π ω * f ω) - c := by
    have h : ∀ ω, π ω * (f ω - c) = π ω * f ω - c * π ω := fun ω => by ring
    simp_rw [h]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one]
  have e2 : ∑ ω, π ω * (g ω - d) = (∑ ω, π ω * g ω) - d := by
    have h : ∀ ω, π ω * (g ω - d) = π ω * g ω - d * π ω := fun ω => by ring
    simp_rw [h]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, mul_one]
  have e3 : ∑ ω, π ω * ((f ω - c) * (g ω - d))
      = (∑ ω, π ω * (f ω * g ω)) - c * (∑ ω, π ω * g ω) - d * (∑ ω, π ω * f ω) + c * d := by
    have h : ∀ ω, π ω * ((f ω - c) * (g ω - d))
        = π ω * (f ω * g ω) - c * (π ω * g ω) - d * (π ω * f ω) + (c * d) * π ω :=
      fun ω => by ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, mul_one]
  rw [e1, e2, e3] at hk
  nlinarith [hk]

/-- The **FKG inequality for events**: under a probability weight `π` satisfying the FKG lattice
condition, two increasing events are positively correlated, `π(A) * π(B) ≤ π(A ∩ B)`. -/
theorem fkg_inequality_events [Fintype E] [DecidableEq E] {π : ConfigSpace E → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ ω, π ω = 1) (hπ : FKGLatticeCondition π)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, π ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, π ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, π ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hAB : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
      simp [Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  exact fkg_inequality hπ₀ hnorm hπ hA.indicator_monotone hB.indicator_monotone

/-- The **Holley inequality** for increasing events (Holley 1974). If `μ₁, μ₂ ≥ 0` have equal
total mass and satisfy `μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)`, then `μ₁(A) ≤ μ₂(A)` for every
increasing event `A`. This is Mathlib's `holley` applied to the indicator of `A`. -/
theorem holley_dominates [Fintype E] [DecidableEq E] {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 ≤ μ₁) (h₂ : 0 ≤ μ₂) (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b))
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * μ₁ ω
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * μ₂ ω :=
  holley μ₁ μ₂ _ (fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) h₁ h₂
    hA.indicator_monotone hsum hcond

end StatMech
