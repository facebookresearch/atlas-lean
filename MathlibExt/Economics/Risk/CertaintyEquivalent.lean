/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-!
# Certainty equivalents of finite monetary lotteries

A finite monetary lottery pays `z x` in state `x` with probability `p.weights x`, where
`p : Convexity.StdSimplex ℝ X` (the lottery type of
`MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern`, whose `expectedUtility` is reused).
A certainty equivalent on an interval `I` is a sure amount `c ∈ I` with
`u c = E_p[u ∘ z]`. Uniqueness follows from strict monotonicity (`StrictMonoOn.injOn`); existence
on `[a, b]` follows from the intermediate value theorem (`intermediate_value_Icc`) when every prize
lies in `[a, b]` and `u` is continuous there.

## Main results

* `IsCertaintyEquivalent.unique`: at most one certainty equivalent under a strictly increasing
  utility.
* `existsUnique_isCertaintyEquivalent`: exactly one certainty equivalent in `[a, b]`.

## References

* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 6.C (certainty equivalent).
* J. W. Pratt, "Risk aversion in the small and in the large", Econometrica 32 (1964), 122--136.
-/

namespace MathlibExt.Economics.Risk

open Convexity MathlibExt.Economics.ExpectedUtility

/-- `c` is a certainty equivalent on the interval `I` of the finite monetary lottery that pays
`z x` in state `x` with probability `p.weights x`, for the Bernoulli utility `u`: the sure amount
`c ∈ I` has the same utility as the lottery, `u c = E_p[u ∘ z]`. -/
def IsCertaintyEquivalent {X : Type*} [Fintype X] (I : Set ℝ) (u : ℝ → ℝ) (z : X → ℝ)
    (p : StdSimplex ℝ X) (c : ℝ) : Prop :=
  c ∈ I ∧ u c = expectedUtility (u ∘ z) p

/-- Uniqueness: under a utility strictly increasing on `I`, a lottery has at most one certainty
equivalent in `I`. -/
theorem IsCertaintyEquivalent.unique {X : Type*} [Fintype X] {I : Set ℝ} {u : ℝ → ℝ}
    {z : X → ℝ} {p : StdSimplex ℝ X} {c d : ℝ} (hu : StrictMonoOn u I)
    (hc : IsCertaintyEquivalent I u z p c) (hd : IsCertaintyEquivalent I u z p d) : c = d := by
  exact hu.injOn hc.1 hd.1 (hc.2.trans hd.2.symm)

/-- Existence and uniqueness: if every prize lies in `[a, b]` and `u` is continuous and strictly
increasing on `[a, b]`, the lottery has exactly one certainty equivalent in `[a, b]`. -/
theorem existsUnique_isCertaintyEquivalent {X : Type*} [Fintype X] {a b : ℝ} {u : ℝ → ℝ}
    {z : X → ℝ} (p : StdSimplex ℝ X) (hcont : ContinuousOn u (Set.Icc a b))
    (hu : StrictMonoOn u (Set.Icc a b)) (hz : ∀ x, z x ∈ Set.Icc a b) :
    ∃! c, IsCertaintyEquivalent (Set.Icc a b) u z p c := by
  obtain ⟨x₀⟩ := p.nonempty
  have hab : a ≤ b :=
    (Set.mem_Icc.mp (hz x₀)).1.trans (Set.mem_Icc.mp (hz x₀)).2
  have hmon := hu.monotoneOn
  have ha_mem : a ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨hab, le_rfl⟩
  have hlo : ∀ x, u a ≤ u (z x) :=
    fun x => hmon ha_mem (hz x) (Set.mem_Icc.mp (hz x)).1
  have hhi : ∀ x, u (z x) ≤ u b :=
    fun x => hmon (hz x) hb_mem (Set.mem_Icc.mp (hz x)).2
  have hE_lo : u a ≤ expectedUtility (u ∘ z) p := by
    have h : ∀ x, p.weights x * u a ≤ p.weights x * u (z x) :=
      fun x => mul_le_mul_of_nonneg_left (hlo x) (p.weights_nonneg x)
    calc u a = (∑ x, p.weights x) * u a := by rw [p.total_of_fintype, one_mul]
      _ = ∑ x, p.weights x * u a := by rw [Finset.sum_mul]
      _ ≤ ∑ x, p.weights x * u (z x) := Finset.sum_le_sum (fun x _ => h x)
      _ = expectedUtility (u ∘ z) p := rfl
  have hE_hi : expectedUtility (u ∘ z) p ≤ u b := by
    have h : ∀ x, p.weights x * u (z x) ≤ p.weights x * u b :=
      fun x => mul_le_mul_of_nonneg_left (hhi x) (p.weights_nonneg x)
    calc expectedUtility (u ∘ z) p = ∑ x, p.weights x * u (z x) := rfl
      _ ≤ ∑ x, p.weights x * u b := Finset.sum_le_sum (fun x _ => h x)
      _ = (∑ x, p.weights x) * u b := by rw [Finset.sum_mul]
      _ = u b := by rw [p.total_of_fintype, one_mul]
  have hmem : expectedUtility (u ∘ z) p ∈ Set.Icc (u a) (u b) :=
    Set.mem_Icc.mpr ⟨hE_lo, hE_hi⟩
  obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Icc hab hcont hmem
  have hc : IsCertaintyEquivalent (Set.Icc a b) u z p c := ⟨hc_mem, hc_eq⟩
  exact ⟨c, hc, fun d hd => IsCertaintyEquivalent.unique hu hd hc⟩

end MathlibExt.Economics.Risk
