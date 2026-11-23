/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

open Finset

/-! # Exact potential games

In a finite game with an exact potential `Φ`, a unilateral deviation
changes the deviator's cost by exactly the change in `Φ`. Hence a
minimizer of `Φ` is a pure Nash equilibrium, and every improvement
path is finite: improvement steps strictly decrease `Φ`, which takes
only finitely many values. This file covers roadmap package DPA-37 of
the Atlas TCS canon roadmap (Rosenthal congestion games are a
follow-up package).

Source: Monderer and Shapley, "Potential games", Games and Economic
Behavior 14 (1996), 124--143.
-/

/-- `Φ` is an exact potential for the finite game with cost functions
`c`: a unilateral deviation changes the deviator's cost by exactly the
change in `Φ`. -/
def IsExactPotential {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (c : ι → (∀ i, S i) → ℝ) (Φ : (∀ i, S i) → ℝ) : Prop :=
  ∀ (i : ι) (s : ∀ i, S i) (a : S i),
    c i (Function.update s i a) - c i s = Φ (Function.update s i a) - Φ s

/-- A pure Nash equilibrium: no unilateral deviation lowers the
deviator's cost. -/
def IsPureNash {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (c : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ (i : ι) (a : S i), c i s ≤ c i (Function.update s i a)

/-- A minimizer of an exact potential is a pure Nash equilibrium. -/
theorem pureNash_of_min_potential {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {c : ι → (∀ i, S i) → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hΦ : IsExactPotential c Φ) (s : ∀ i, S i) (hmin : ∀ t, Φ s ≤ Φ t) :
    IsPureNash c s := by
  intro i a
  have h := hΦ i s a
  have hle := hmin (Function.update s i a)
  linarith

/-- Every improvement path in a finite exact-potential game is finite:
there is no infinite sequence of profiles in which each step is a
strict unilateral cost improvement. -/
theorem no_infinite_improvement_path {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {c : ι → (∀ i, S i) → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hΦ : IsExactPotential c Φ) (s : ℕ → ∀ i, S i)
    (hstep : ∀ k, ∃ (i : ι) (a : S i), s (k + 1) = Function.update (s k) i a ∧
      c i (s (k + 1)) < c i (s k)) : False := by
  have hsucc : ∀ k, (Φ ∘ s) (k + 1) < (Φ ∘ s) k := by
    intro k
    obtain ⟨i, a, hEq, hlt⟩ := hstep k
    have h := hΦ i (s k) a
    show Φ (s (k + 1)) < Φ (s k)
    rw [hEq] at hlt ⊢
    linarith
  have hanti : StrictAnti (Φ ∘ s) := strictAnti_nat_of_succ_lt hsucc
  have hinj : Function.Injective (Φ ∘ s) := hanti.injective
  have hinf : Set.Infinite (Set.range (Φ ∘ s)) := Set.infinite_range_of_injective hinj
  have hsub : Set.range (Φ ∘ s) ⊆ ↑(Finset.image Φ Finset.univ) := by
    rintro y ⟨k, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s k, Finset.mem_univ _, rfl⟩)
  have hfin : Set.Finite (Set.range (Φ ∘ s)) := (Finset.finite_toSet _).subset hsub
  exact hinf hfin
