/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Selection principles for sets of reals and `C_p(X)`: shared definitions

Shared helper for the UnsolvedMath entries on problems from B. Tsaban, *Selection principles in
mathematics: A milestone of open problems* (arXiv:math/0312182), whose answers are recorded in that
paper's Notes added in proof:
`WantedExt/Topology/OmegaGroupableNotSfinAMR134Problem0020Wanted.lean`,
`WantedExt/Topology/FanTightnessNotWeakSSPAMR134Problem0040Wanted.lean`,
`WantedExt/Topology/MonotonicNotWeakSSPAMR134Problem0041Wanted.lean` and
`WantedExt/Topology/BaireSpaceCpReznichenkoAMR134Problem0043Wanted.lean`.
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Set Filter Topology

namespace MathlibExt.Topology.SelectionPrinciplesShared

/-!
Conventions of the source (Tsaban, Sections 2 and 10): a cover `𝒰` of a space `X` is nontrivial
(`⋃ 𝒰 = X` and `X ∉ 𝒰`), and for sets of reals the covers are countable; an `ω`-cover has every
finite subset of `X` inside a member. `Ω` is the collection of open `ω`-covers, and a cover is
`Ω`-groupable (Section 10, following Kočinac and Scheepers) if it can be partitioned into finite
sets `𝓕ₙ` such that for every infinite `A ⊆ ℕ` the sets `⋃ 𝓕ₙ`, `n ∈ A`, form an `ω`-cover; `Ω^gp`
is the collection of `Ω`-groupable members of `Ω`. `C_p(X)` is the space of continuous real-valued
functions on `X` with the topology of pointwise convergence (a subspace of the product `ℝ^X`).

`IsOpenCover`, `IsOmegaFamily`, `omegaCovers`, `omegaGroupableCovers`, `Sfin`, `Choose` and `Cp`
repeat, under the same names and with the same bodies, the definitions in
`OpenConjectures.SetTheory.AMR134Problem0004.Helper.SelectionPrinciples`, and
`HasReznichenkoProperty` repeats the definition in `OpenConjectures.SetTheory.AMR134Problem0042`:
`WantedExt` cannot import `OpenConjectures`.
-/

section Covers

variable {T : Type*}

/-- A countable nontrivial open cover of `T`. -/
def IsOpenCover [TopologicalSpace T] (𝒰 : Set (Set T)) : Prop :=
  𝒰.Countable ∧ (∀ U ∈ 𝒰, IsOpen U) ∧ ⋃₀ 𝒰 = univ ∧ univ ∉ 𝒰

/-- `𝒰` is an `ω`-family: every finite set lies in a member. -/
def IsOmegaFamily (𝒰 : Set (Set T)) : Prop := ∀ F : Finset T, ∃ U ∈ 𝒰, (F : Set T) ⊆ U

/-- `Ω`: open `ω`-covers. -/
def omegaCovers (T : Type*) [TopologicalSpace T] : Set (Set (Set T)) :=
  {𝒰 | IsOpenCover 𝒰 ∧ IsOmegaFamily 𝒰}

/-- `Ω^gp` (the source's `Ω`-groupable `ω`-covers): `ω`-covers partitioned into nonempty finite
pieces `𝓕ₙ` such that the unions of the pieces indexed by any infinite `A ⊆ ℕ` form an
`ω`-cover. -/
def omegaGroupableCovers (T : Type*) [TopologicalSpace T] : Set (Set (Set T)) :=
  {𝒰 | 𝒰 ∈ omegaCovers T ∧ ∃ F : ℕ → Finset (Set T), (∀ n, (F n).Nonempty) ∧
    Pairwise (fun m n => Disjoint (F m) (F n)) ∧ (⋃ n, (F n : Set (Set T))) = 𝒰 ∧
    ∀ A : Set ℕ, A.Infinite → ((fun n => ⋃₀ (F n : Set (Set T))) '' A) ∈ omegaCovers T}

end Covers

section Selection

variable {T : Type*}

/-- The selection hypothesis `S_fin(𝔘, 𝔙)`. -/
def Sfin (𝔘 𝔙 : Set (Set (Set T))) : Prop :=
  ∀ 𝒰 : ℕ → Set (Set T), (∀ n, 𝒰 n ∈ 𝔘) →
    ∃ F : ℕ → Finset (Set T), (∀ n, (F n : Set (Set T)) ⊆ 𝒰 n) ∧ (⋃ n, (F n : Set (Set T))) ∈ 𝔙

/-- The property `(𝔘 𝔙)`: every member of `𝔘` contains a member of `𝔙`. -/
def Choose (𝔘 𝔙 : Set (Set (Set T))) : Prop := ∀ 𝒰 ∈ 𝔘, ∃ 𝒱 ⊆ 𝒰, 𝒱 ∈ 𝔙

end Selection

section FunctionSpaces

/-- `C_p(X)`: continuous real-valued functions on `X` with the pointwise (product) topology. -/
abbrev Cp (X : Type*) [TopologicalSpace X] : Type _ := {f : X → ℝ // Continuous f}

/-- The constant zero function `𝟎` as a point of `C_p(X)`. -/
def cpZero (X : Type*) [TopologicalSpace X] : Cp X := ⟨fun _ => 0, continuous_const⟩

/-- The Reznichenko (weak Fréchet–Urysohn) property: for `y ∈ cl A \ A` there are pairwise
disjoint finite subsets of `A` such that every neighbourhood of `y` meets all but finitely many. -/
def HasReznichenkoProperty (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ A : Set Y, ∀ y ∈ closure A \ A, ∃ F : ℕ → Finset Y, (∀ n, (F n : Set Y) ⊆ A) ∧
    Pairwise (fun m n => Disjoint (F m) (F n)) ∧
      ∀ U ∈ 𝓝 y, ∀ᶠ n in atTop, ((F n : Set Y) ∩ U).Nonempty

/-- The weak sequence selection property of `C_p(X)` (Scheepers; Tsaban, Section 15): for every
sequence `(f^n_k)_{k ∈ ℕ}`, `n ∈ ℕ`, of sequences in `C_p(X)` each converging to `𝟎`, there are
indices `k_n` with `𝟎` in the closure of `{f^n_{k_n} : n ∈ ℕ}`. -/
def HasWeakSSP (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : ℕ → ℕ → Cp X, (∀ n, Tendsto (f n) atTop (𝓝 (cpZero X))) →
    ∃ k : ℕ → ℕ, cpZero X ∈ closure (range fun n => f n (k n))

end FunctionSpaces

end MathlibExt.Topology.SelectionPrinciplesShared
