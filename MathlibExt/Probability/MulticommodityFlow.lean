/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CanonicalPaths
public import MathlibExt.Probability.MarkovMixing
public import MathlibExt.Probability.PoincareMixing
public import Mathlib.LinearAlgebra.Matrix.Stochastic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multicommodity flows in a reversible Markov chain

Sinclair generalises canonical paths to *flows*: for each ordered pair of distinct states `x, y`,
`π(x) π(y)` units of commodity `(x, y)` are split over several simple paths from `x` to `y` in the
graph of the chain (`MulticommodityFlow`). The load of an oriented edge is the total flow through
it (`MulticommodityFlow.load`), and the *resistance* of the chain is the least `ρ` such that some
flow has every load at most `ρ` times the edge capacity `Q(u, v) = π(u) P(u, v)`.

## Main definitions and results

* `MulticommodityFlow π P`: a flow routing `π(x) π(y)` from `x` to `y` over simple paths that use
  only transitions with `π(u) P(u, v) > 0` (A. Sinclair 1992, Section 4).
* `MulticommodityFlow.load`: the flow `f(e) = ∑_{p ∋ e} f(p)` through an oriented edge.
* `MulticommodityFlow.elongatedLoad`, `MulticommodityFlow.sum_sq_sub_mul_le_of_elongatedLoad_le`
  and `MulticommodityFlow.one_le_mul_one_sub_of_eigenvector`: the length-weighted load, the flow
  Poincaré inequality and **Theorem 5′**, `λ₁ ≤ 1 - 1/ρ̄(f)`.
* `MulticommodityFlow.mul_sum_compl_le`: **inequality (13) for flows**,
  `π(A) π(Aᶜ) ≤ ρ Q(A, Aᶜ)` whenever every load is at most `ρ · Q`;
  `MulticommodityFlow.sum_le_two_mul` derives **Theorem 3′**, `π(A) ≤ 2 ρ Q(A, Aᶜ)` when
  `π(A) ≤ 1/2`.
* `pow_detailedBalance`: detailed balance passes to every power `Pⁿ`.
* `div_eight_le_pow_apply`: **Sinclair's Lemma 7**. If `P` is stochastic and reversible with
  respect to a positive probability vector `π`, and every row of `Pᵗ` is within total variation
  `1/4` of `π` for all `t ≥ τ`, then `Pᵗ(x, y) ≥ π(y)/8` for all `t ≥ 2τ` and all `x, y`.
  This is the key step of Theorem 8 (resistance at most `16 τ`), proved as
  `MathlibExt.Probability.MulticommodityFlowWanted.exists_multicommodityFlow_load_le_sixteen_mul`
  in `MathlibExt.Probability.MulticommodityFlowRapidMixing`.
* `div_eight_le_pow_apply_of_isMixedAt`: Lemma 7 from `IsMixedAt P π τ`, using
  `PoincareMixing.isMixedAt_mono` (being `1/4`-mixed persists).

The declarations live in the namespace `MathlibExt.Probability.Flows` rather than one mirroring
the module name, so that the structure is not called `…MulticommodityFlow.MulticommodityFlow`.
Detailed balance is the repository's `ProbabilityTheory.IsDetailedBalance π P`.

## References

* A. Sinclair, "Improved bounds for mixing rates of Markov chains and multicommodity flow",
  *Combinatorics, Probability and Computing* **1** (1992), 351–370: Section 4, Theorems 3′ and 5′,
  inequality (13) and Lemma 7.
-/

@[expose] public section

open Finset Matrix
open MathlibExt.Probability.CanonicalPaths MathlibExt.Probability.MarkovMixing
open MathlibExt.Probability.PoincareMixing ProbabilityTheory

namespace MathlibExt.Probability.Flows

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Multicommodity flow in a Markov chain** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
Section 4). For each ordered pair `x ≠ y`, a finite set of paths from `x` (each given by the list
of states it visits after `x`, as in `CanonicalPaths.pathEdges`) with nonnegative weights summing
to `π(x) π(y)`; every path is simple, ends at `y`, and uses only oriented edges `(u, v)` of the
graph of the chain, i.e. with `π(u) P(u, v) > 0`. -/
structure MulticommodityFlow (π : S → ℝ) (P : Matrix S S ℝ) where
  /-- The paths carrying commodity `(x, y)`. -/
  paths : S → S → Finset (List S)
  /-- The amount of commodity `(x, y)` sent along a path. -/
  weight : S → S → List S → ℝ
  weight_nonneg : ∀ x y p, 0 ≤ weight x y p
  pathEnd_eq : ∀ x y, x ≠ y → ∀ p ∈ paths x y, pathEnd x p = y
  nodup : ∀ x y, x ≠ y → ∀ p ∈ paths x y, (x :: p).Nodup
  edge_pos : ∀ x y, x ≠ y → ∀ p ∈ paths x y, ∀ e ∈ pathEdges x p, 0 < π e.1 * P e.1 e.2
  demand : ∀ x y, x ≠ y → ∑ p ∈ paths x y, weight x y p = π x * π y

namespace MulticommodityFlow

variable {π : S → ℝ} {P : Matrix S S ℝ}

/-- **Flow through an oriented edge** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
Section 4): `f(u, v) = ∑_{x ≠ y} ∑_{p} f(p) · #{times p uses (u, v)}`; for the simple paths of a
flow the multiplicity is `0` or `1`, so this is `∑_{p ∋ (u, v)} f(p)`. -/
noncomputable def load (F : MulticommodityFlow π P) (u v : S) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else
    ∑ p ∈ F.paths x y, F.weight x y p * ((pathEdges x p).count (u, v) : ℝ)

/-- **Inequality (13) for flows: `π(A) π(Aᶜ) ≤ ρ Q(A, Aᶜ)`** (A. Sinclair, *Combin. Probab.
Comput.* 1 (1992), inequality (13), stated there for flows; it implies Theorem 3′, see
`sum_le_two_mul`). If every edge carries at most
`ρ · π(u) P(u, v)` units of a flow `F`, then for every set `A` of states
`π(A) π(Aᶜ) ≤ ρ ∑_{u ∈ A, v ∉ A} π(u) P(u, v)`. -/
theorem mul_sum_compl_le (F : MulticommodityFlow π P) {ρ : ℝ}
    (hρ : ∀ u v, F.load u v ≤ ρ * (π u * P u v)) (A : Finset S) :
    (∑ x ∈ A, π x) * (∑ y ∈ Aᶜ, π y) ≤ ρ * ∑ u ∈ A, ∑ v ∈ Aᶜ, π u * P u v := by
  set c : S → List S → ℝ := fun x p =>
    ∑ u ∈ A, ∑ v ∈ Aᶜ, ((pathEdges x p).count (u, v) : ℝ) with hc
  have hc0 : ∀ x p, 0 ≤ c x p := fun x p =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hc1 : ∀ x ∈ A, ∀ y ∈ Aᶜ, ∀ p ∈ F.paths x y, 1 ≤ c x p := by
    intro x hx y hy p hp
    have hxy : x ≠ y := by rintro rfl; simp_all
    have hend : pathEnd x p ∉ A := by rw [F.pathEnd_eq x y hxy p hp]; simpa using hy
    obtain ⟨⟨u, v⟩, he, hu, hv⟩ := exists_mem_pathEdges_of_mem_of_not_mem A p hx hend
    calc (1 : ℝ) ≤ ((pathEdges x p).count (u, v) : ℝ) := by
          exact_mod_cast List.count_pos_iff.mpr he
      _ ≤ ∑ v' ∈ Aᶜ, ((pathEdges x p).count (u, v') : ℝ) :=
          Finset.single_le_sum (f := fun v' => ((pathEdges x p).count (u, v') : ℝ))
            (fun _ _ => Nat.cast_nonneg _) (by simpa using hv)
      _ ≤ c x p :=
          Finset.single_le_sum (f := fun u' => ∑ v' ∈ Aᶜ, ((pathEdges x p).count (u', v') : ℝ))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hu
  set T : S → S → ℝ := fun x y =>
    if x = y then 0 else ∑ p ∈ F.paths x y, F.weight x y p * c x p with hT
  have hT0 : ∀ x y, 0 ≤ T x y := by
    intro x y; simp only [hT]; split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun p _ => mul_nonneg (F.weight_nonneg x y p) (hc0 x p)
  have key : ∑ u ∈ A, ∑ v ∈ Aᶜ, F.load u v = ∑ x, ∑ y, T x y := by
    simp only [load]
    rw [sum_sum_sum_sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hT]
    split_ifs
    · simp
    · simp only [hc, Finset.mul_sum]
      exact (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm
  have hflow : (∑ x ∈ A, π x) * (∑ y ∈ Aᶜ, π y) ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, F.load u v := by
    rw [key, Finset.sum_mul_sum]
    calc ∑ x ∈ A, ∑ y ∈ Aᶜ, π x * π y ≤ ∑ x ∈ A, ∑ y ∈ Aᶜ, T x y := by
          refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
          have hxy : x ≠ y := by rintro rfl; simp_all
          simp only [hT, hxy, ↓reduceIte]
          rw [← F.demand x y hxy]
          refine Finset.sum_le_sum fun p hp => ?_
          have := hc1 x hx y hy p hp
          have h0 := F.weight_nonneg x y p
          nlinarith
      _ ≤ ∑ x ∈ A, ∑ y, T x y :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) fun y _ _ => hT0 x y
      _ ≤ ∑ x, ∑ y, T x y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun x _ _ => Finset.sum_nonneg fun y _ => hT0 x y
  refine hflow.trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ => by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun v _ => hρ u v

/-- **Sinclair's Theorem 3′: `Φ ≥ 1/(2ρ(f))`** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
Theorem 3′), set by set. If `π` is a probability vector, every edge carries at most
`ρ · π(u) P(u, v)` units of a flow `F`, and `π(A) ≤ 1/2`, then `π(A) ≤ 2 ρ Q(A, Aᶜ)`, where
`Q(A, Aᶜ) = ∑_{u ∈ A, v ∉ A} π(u) P(u, v)`. -/
theorem sum_le_two_mul (F : MulticommodityFlow π P) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    {ρ : ℝ} (hρ : ∀ u v, F.load u v ≤ ρ * (π u * P u v)) (A : Finset S)
    (hA : ∑ x ∈ A, π x ≤ 1 / 2) :
    ∑ x ∈ A, π x ≤ 2 * (ρ * ∑ u ∈ A, ∑ v ∈ Aᶜ, π u * P u v) := by
  have h := F.mul_sum_compl_le hρ A
  have hsplit : ∑ y ∈ Aᶜ, π y = 1 - ∑ x ∈ A, π x := by
    rw [← hπ1, ← Finset.sum_add_sum_compl A π]; ring
  rw [hsplit] at h
  have h0 : 0 ≤ ∑ x ∈ A, π x := Finset.sum_nonneg fun x _ => hπ x
  nlinarith

/-- **Length-weighted flow through an oriented edge** (A. Sinclair, *Combin. Probab. Comput.* 1
(1992), Section 4: the elongated flow `f̄(e) = ∑_{p ∋ e} f(p) |p|`):
`∑_{x ≠ y} ∑_p f(p) |p| · #{times p uses (u, v)}`, where `|p|` is the number of edges of `p`. -/
noncomputable def elongatedLoad (F : MulticommodityFlow π P) (u v : S) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else
    ∑ p ∈ F.paths x y, F.weight x y p * (p.length : ℝ) * ((pathEdges x p).count (u, v) : ℝ)

/-- **The flow Poincaré inequality** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992), proof of
Theorem 5′: "the proof of Theorem 5 carries over almost unchanged"). If every length-weighted edge
load of a flow `F` is at most `B · π(u) P(u, v)` (`B = ρ̄(f)`), then for every `ψ : S → ℝ`,
`∑_{x,y} (ψ x - ψ y)² π(x) π(y) ≤ B ∑_{x,y} (ψ x - ψ y)² π(x) P(x, y)`. -/
theorem sum_sq_sub_mul_le_of_elongatedLoad_le (F : MulticommodityFlow π P) {B : ℝ}
    (hB : ∀ u v, F.elongatedLoad u v ≤ B * (π u * P u v)) (ψ : S → ℝ) :
    ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y) := by
  set g : S → S → ℝ := fun u v => (ψ v - ψ u) ^ 2 with hg
  -- Step 1: split the demand over the paths and apply Cauchy–Schwarz along each path.
  have step1 : ∀ x y, (ψ x - ψ y) ^ 2 * (π x * π y) ≤
      if x = y then 0 else ∑ p ∈ F.paths x y, F.weight x y p * (p.length : ℝ) *
        ∑ u, ∑ v, ((pathEdges x p).count (u, v) : ℝ) * g u v := by
    intro x y
    split_ifs with hxy
    · simp [hxy]
    · rw [← F.demand x y hxy, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have htel := sum_pathEdges_sub ψ x p
      rw [F.pathEnd_eq x y hxy p hp] at htel
      have hcs := sq_sum_map_le (pathEdges x p) (fun e => ψ e.2 - ψ e.1)
      rw [htel, length_pathEdges, sum_map_eq_sum_count] at hcs
      have hsq : (ψ x - ψ y) ^ 2 = (ψ y - ψ x) ^ 2 := by ring
      rw [hsq]
      have hw := F.weight_nonneg x y p
      calc (ψ y - ψ x) ^ 2 * F.weight x y p
          ≤ ((p.length : ℝ) * ∑ u, ∑ v, ((pathEdges x p).count (u, v) : ℝ) *
              (ψ (u, v).2 - ψ (u, v).1) ^ 2) * F.weight x y p :=
            mul_le_mul_of_nonneg_right hcs hw
        _ = _ := by simp only [hg]; ring
  -- Step 2: regroup by edges.
  have step2 : ∑ x, ∑ y, (if x = y then (0 : ℝ) else ∑ p ∈ F.paths x y,
        F.weight x y p * (p.length : ℝ) * ∑ u, ∑ v, ((pathEdges x p).count (u, v) : ℝ) * g u v) =
      ∑ u, ∑ v, g u v * F.elongatedLoad u v := by
    calc _ = ∑ x, ∑ y, ∑ u, ∑ v, g u v * (if x = y then (0 : ℝ) else ∑ p ∈ F.paths x y,
            F.weight x y p * (p.length : ℝ) * ((pathEdges x p).count (u, v) : ℝ)) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          split_ifs
          · simp
          · simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun p _ => by ring
      _ = ∑ u, ∑ v, ∑ x, ∑ y, g u v * (if x = y then (0 : ℝ) else ∑ p ∈ F.paths x y,
            F.weight x y p * (p.length : ℝ) * ((pathEdges x p).count (u, v) : ℝ)) :=
          sum_sum_sum_sum_comm _ _ _ _ _
      _ = _ := by simp only [elongatedLoad, Finset.mul_sum]
  calc ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * π y)
      ≤ ∑ x, ∑ y, (if x = y then (0 : ℝ) else ∑ p ∈ F.paths x y, F.weight x y p *
          (p.length : ℝ) * ∑ u, ∑ v, ((pathEdges x p).count (u, v) : ℝ) * g u v) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => step1 x y
    _ = ∑ u, ∑ v, g u v * F.elongatedLoad u v := step2
    _ ≤ ∑ u, ∑ v, g u v * (B * (π u * P u v)) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hB u v) (sq_nonneg _)
    _ = B * ∑ x, ∑ y, (ψ x - ψ y) ^ 2 * (π x * P x y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [hg]; ring

/-- **Sinclair's Theorem 5′: flows bound the spectral gap** (A. Sinclair, *Combin. Probab.
Comput.* 1 (1992), Theorem 5′: `λ₁ ≤ 1 - 1/ρ̄(f)`). Let `P` have unit row sums and satisfy
detailed balance with respect to a positive probability vector `π`, and let `F` be a flow whose
length-weighted load on every oriented edge is at most `B · π(u) P(u, v)`. Then every real
eigenvalue `μ ≠ 1` of `P` satisfies `1 ≤ B (1 - μ)`. -/
theorem one_le_mul_one_sub_of_eigenvector (F : MulticommodityFlow π P) (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : IsDetailedBalance π P) {B : ℝ}
    (hB : ∀ u v, F.elongatedLoad u v ≤ B * (π u * P u v)) {μ : ℝ} {f : S → ℝ}
    (hf : f ≠ 0) (heig : P *ᵥ f = μ • f) (hμ : μ ≠ 1) :
    1 ≤ B * (1 - μ) :=
  one_le_mul_one_sub_of_poincare hπ hπ1 hrow hrev (F.sum_sq_sub_mul_le_of_elongatedLoad_le hB)
    hf heig hμ

end MulticommodityFlow

/-- **Detailed balance for powers.** If `π(x) P(x, y) = π(y) P(y, x)` for all `x, y`, then
`π(x) Pⁿ(x, y) = π(y) Pⁿ(y, x)` for every `n` (used in A. Sinclair, *Combin. Probab. Comput.* 1
(1992), proof of Lemma 7). -/
theorem pow_detailedBalance {π : S → ℝ} {P : Matrix S S ℝ}
    (hrev : IsDetailedBalance π P) (n : ℕ) (x y : S) :
    π x * (P ^ n) x y = π y * (P ^ n) y x := by
  induction n generalizing x y with
  | zero =>
    by_cases h : x = y
    · subst h; rfl
    · simp [h, Ne.symm h]
  | succ n ih =>
    rw [show (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y by rw [pow_succ, Matrix.mul_apply],
      show (P ^ (n + 1)) y x = ∑ z, P y z * (P ^ n) z x by rw [pow_succ', Matrix.mul_apply],
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    calc π x * ((P ^ n) x z * P z y) = (π x * (P ^ n) x z) * P z y := by ring
      _ = (π z * (P ^ n) z x) * P z y := by rw [ih x z]
      _ = (π z * P z y) * (P ^ n) z x := by ring
      _ = (π y * P y z) * (P ^ n) z x := by rw [hrev z y]
      _ = π y * (P y z * (P ^ n) z x) := by ring

omit [DecidableEq S] in
/-- **Excess mass on a set is at most the total variation distance.** For two vectors `μ, ν`
with entries summing to `1`, `∑_{z ∈ T} (ν z - μ z) ≤ d_TV(μ, ν)` for every set `T`. -/
theorem sum_sub_le_tvDist {μ ν : S → ℝ} (hμ : ∑ y, μ y = 1) (hν : ∑ y, ν y = 1) (T : Finset S) :
    ∑ z ∈ T, (ν z - μ z) ≤ tvDist μ ν := by
  classical
  have htot : ∑ z ∈ T, (ν z - μ z) + ∑ z ∈ Tᶜ, (ν z - μ z) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, hμ, hν, sub_self]
  have h1 : ∑ z ∈ T, (ν z - μ z) ≤ ∑ z ∈ T, |μ z - ν z| :=
    Finset.sum_le_sum fun z _ => by rw [abs_sub_comm]; exact le_abs_self _
  have h2 : -∑ z ∈ Tᶜ, (ν z - μ z) ≤ ∑ z ∈ Tᶜ, |μ z - ν z| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun z _ => by rw [neg_sub]; exact le_abs_self _
  have h3 : ∑ z ∈ T, |μ z - ν z| + ∑ z ∈ Tᶜ, |μ z - ν z| = ∑ z, |μ z - ν z| :=
    Finset.sum_add_sum_compl T _
  simp only [tvDist]
  linarith

/-- **Sinclair's Lemma 7** (A. Sinclair, *Combin. Probab. Comput.* 1 (1992), Lemma 7). Let `P`
be a stochastic matrix satisfying detailed balance with respect to a probability vector `π > 0`,
and suppose every row of `Pᵗ` is within total variation distance `1/4` of `π` for all `t ≥ τ`
(so `τ ≥ max_x τ_x(1/4)`). Then for every `t ≥ 2τ` and all states `x, y`,
`Pᵗ(x, y) ≥ π(y)/8`. -/
theorem div_eight_le_pow_apply {π : S → ℝ} (hπ : ∀ x, 0 < π x) (hπ1 : ∑ x, π x = 1)
    {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hrev : IsDetailedBalance π P)
    {τ : ℕ} (hτ : ∀ x, ∀ t, τ ≤ t → tvDist (fun y => (P ^ t) x y) π ≤ 1 / 4) {t : ℕ}
    (ht : 2 * τ ≤ t) (x y : S) :
    π y / 8 ≤ (P ^ t) x y := by
  have hrow : ∀ n w, ∑ z, (P ^ n) w z = 1 := fun n w =>
    sum_row_of_mem_rowStochastic (pow_mem hP n) w
  have hnn : ∀ n w z, 0 ≤ (P ^ n) w z := fun n w z =>
    nonneg_of_mem_rowStochastic (pow_mem hP n)
  -- `Z`: the states `z` with `P^τ(y, z) ≥ π(z)/2`; it has `π(Z) ≥ 1/2`.
  set Z : Finset S := Finset.univ.filter fun z => π z / 2 ≤ (P ^ τ) y z with hZ
  have hZc : ∑ z ∈ Zᶜ, π z ≤ 1 / 2 := by
    have h := sum_sub_le_tvDist (μ := fun z => (P ^ τ) y z) (ν := π) (hrow τ y) hπ1 Zᶜ
    have hτy := hτ y τ le_rfl
    have hlt : ∑ z ∈ Zᶜ, π z / 2 ≤ ∑ z ∈ Zᶜ, (π z - (P ^ τ) y z) :=
      Finset.sum_le_sum fun z hz => by
        simp only [hZ, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_le] at hz
        linarith
    rw [← Finset.sum_div] at hlt
    linarith
  -- From `x`, after `t - τ ≥ τ` steps the chain is in `Z` with probability at least `1/4`.
  have hs : τ ≤ t - τ := by omega
  have hZx : 1 / 4 ≤ ∑ z ∈ Z, (P ^ (t - τ)) x z := by
    have h := sum_sub_le_tvDist (μ := fun z => (P ^ (t - τ)) x z) (ν := π) (hrow _ x) hπ1 Z
    have hd := hτ x (t - τ) hs
    have hsplit : ∑ z ∈ Z, π z = 1 - ∑ z ∈ Zᶜ, π z := by
      rw [← hπ1, ← Finset.sum_add_sum_compl Z π]; ring
    rw [Finset.sum_sub_distrib, hsplit] at h
    linarith
  -- For `z ∈ Z`, reversibility of `P^τ` gives `P^τ(z, y) ≥ π(y)/2`.
  have hzy : ∀ z ∈ Z, π y / 2 ≤ (P ^ τ) z y := by
    intro z hz
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hdb := pow_detailedBalance hrev τ y z
    have hπz := hπ z
    have hπy := hπ y
    -- `π z P^τ(z, y) = π y P^τ(y, z) ≥ π y π z / 2`.
    have : π z * (π y / 2) ≤ π z * (P ^ τ) z y := by
      rw [← hdb]; nlinarith
    exact le_of_mul_le_mul_left this hπz
  have hsplit : t = (t - τ) + τ := by omega
  calc π y / 8 = (π y / 2) * (1 / 4) := by ring
    _ ≤ (π y / 2) * ∑ z ∈ Z, (P ^ (t - τ)) x z :=
        mul_le_mul_of_nonneg_left hZx (by linarith [hπ y])
    _ = ∑ z ∈ Z, (P ^ (t - τ)) x z * (π y / 2) := by rw [Finset.mul_sum]; simp [mul_comm]
    _ ≤ ∑ z ∈ Z, (P ^ (t - τ)) x z * (P ^ τ) z y :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hzy z hz) (hnn _ _ _)
    _ ≤ ∑ z, (P ^ (t - τ)) x z * (P ^ τ) z y :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun z _ _ => mul_nonneg (hnn _ _ _) (hnn _ _ _)
    _ = (P ^ t) x y := by rw [← Matrix.mul_apply, ← pow_add, ← hsplit]

/-- **Sinclair's Lemma 7 from a single mixing time.** If `P` is stochastic and reversible with
respect to a probability vector `π > 0` and `1/4`-mixed at time `τ` (`MarkovMixing.IsMixedAt`),
then `Pᵗ(x, y) ≥ π(y)/8` for all `t ≥ 2τ` (A. Sinclair, *Combin. Probab. Comput.* 1 (1992),
Lemma 7, with `isMixedAt_mono` supplying the later times). -/
theorem div_eight_le_pow_apply_of_isMixedAt {π : S → ℝ} (hπ : ∀ x, 0 < π x)
    (hπ1 : ∑ x, π x = 1) {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hrev : IsDetailedBalance π P) {τ : ℕ} (hτ : IsMixedAt P π τ) {t : ℕ}
    (ht : 2 * τ ≤ t) (x y : S) :
    π y / 8 ≤ (P ^ t) x y := by
  have hstat : π ᵥ* P = π := by
    funext j
    simp only [vecMul, dotProduct]
    calc ∑ i, π i * P i j = ∑ i, π j * P j i := Finset.sum_congr rfl fun i _ => hrev i j
      _ = π j := by rw [← Finset.mul_sum, sum_row_of_mem_rowStochastic hP j, mul_one]
  exact div_eight_le_pow_apply hπ hπ1 hP hrev
    (fun x t htt => isMixedAt_mono hP hstat hτ htt x) ht x y

end MathlibExt.Probability.Flows
