/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic.Ring

/-!
# Finite conditioning cells: tower property and total variance

For a finite type `α` with nonnegative real weights `p : α → ℝ` and an
observation map `G : α → C` into a finite cell type `C`, the cell of `c` is
`{x | G x = c}`. Its mass is `cellMass p G c`, its mean `cellMean p G Y c`,
and its variance `cellVar p G Y c`, each a ratio by the cell mass. A cell of
mass `0` gets mean and variance `0` by Lean's `x / 0 = 0`; every identity is
stated so that a null cell enters only multiplied by its mass `0`, and
`sum_mul_comp_eq_sum_mul_of_eq_cellMean` shows that any value on null cells
works.

The results are the pointwise finite-cell forms of the tower property
(`E[Y] = ∑ c, P(G = c) E[Y | G = c]`, its version-robust composed form, and
the nested tower under coarsening) and of the total-variance decomposition
(within-cell plus between-cell variance). Only `0 ≤ p` is assumed:
normalization `∑ x, p x = 1` is not used, so the identities hold for any
nonnegative finite measure, with the probabilistic reading as the normalized
case.

This module imports Mathlib only, so the cell functional sits below both
`MathlibExt.Probability.FiniteProbability` and the causal-adjustment and
missing-data modules; statements use raw finite sums, which are
definitionally the finite `expectation`/`variance` vocabulary.
-/

@[expose] public section

open Finset

namespace MathlibExt.Probability.FiniteConditioning

/-- The mass `∑ x ∈ {x | G x = c}, p x` of the cell `G = c` under the weight `p`. For a finite
distribution `p` this is `P(G = c)`; `c ↦ cellMass p G c` is the law of the observation `G`. -/
noncomputable def cellMass {α C : Type*} [Fintype α] [DecidableEq C] (p : α → ℝ) (G : α → C)
    (c : C) : ℝ :=
  ∑ x ∈ univ.filter (fun x => G x = c), p x

/-- The cell mean: the weighted sum `∑ x ∈ {G = c}, p x * Y x` divided by `cellMass p G c`. On a
cell of mass `0` Lean's `x / 0 = 0` gives the value `0`; no statement in this file depends on
that value. For nonnegative weights `p` and a cell of positive mass it is the conditional
expectation `E[Y | G = c]` under the law proportional to `p`. With signed weights it is only a
weighted quotient: the weights `(2, -1)` with the values `(0, 1)` on one cell give `-1`. -/
noncomputable def cellMean {α C : Type*} [Fintype α] [DecidableEq C] (p : α → ℝ) (G : α → C)
    (Y : α → ℝ) (c : C) : ℝ :=
  (∑ x ∈ univ.filter (fun x => G x = c), p x * Y x) / cellMass p G c

/-- The weighted sum `∑ x ∈ {G = c}, p x * (Y x - cellMean p G Y c) ^ 2` divided by
`cellMass p G c`; `0` on a cell of mass `0`. For nonnegative weights `p` and a cell of positive
mass it is the within-cell variance `Var(Y | G = c) = E[(Y - E[Y | G = c]) ^ 2 | G = c]`; with
negative weights it can be negative. -/
noncomputable def cellVar {α C : Type*} [Fintype α] [DecidableEq C] (p : α → ℝ) (G : α → C)
    (Y : α → ℝ) (c : C) : ℝ :=
  (∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - cellMean p G Y c) ^ 2) / cellMass p G c

/-- Total mass: the cell masses sum to the total weight (total probability over the cells). -/
theorem sum_cellMass {α C : Type*} [Fintype α] [Fintype C] [DecidableEq C] (p : α → ℝ)
    (G : α → C) : ∑ c, cellMass p G c = ∑ x, p x := by
  simp only [cellMass]
  exact Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _) p

/-- Change of variables to the cell law: the weighted sum of a function of the cell is its
sum against the cell masses (`E[f(G)] = ∑ c, P(G = c) f c`). No hypothesis is needed. -/
theorem sum_mul_comp_eq_sum_cellMass_mul {α C : Type*} [Fintype α] [Fintype C] [DecidableEq C]
    (p : α → ℝ) (G : α → C) (f : C → ℝ) :
    ∑ x, p x * f (G x) = ∑ c, cellMass p G c * f c := by
  simp only [cellMass, Finset.sum_mul]
  symm
  calc ∑ c, ∑ x ∈ univ.filter (fun x => G x = c), p x * f c
      = ∑ c, ∑ x ∈ univ.filter (fun x => G x = c), p x * f (G x) := by
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun x hx => ?_))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx]
    _ = ∑ x, p x * f (G x) :=
        Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _) _

/-- Cell mass times cell mean recovers the cell's weighted sum, including on a null cell,
where nonnegativity makes both sides `0`. -/
theorem cellMass_mul_cellMean {α C : Type*} [Fintype α] [DecidableEq C] {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (Y : α → ℝ) (c : C) :
    cellMass p G c * cellMean p G Y c = ∑ x ∈ univ.filter (fun x => G x = c), p x * Y x := by
  by_cases h : cellMass p G c = 0
  · rw [h, zero_mul]
    have hsum : ∑ x ∈ univ.filter (fun x => G x = c), p x = 0 := h
    have hall : ∀ x ∈ univ.filter (fun x => G x = c), p x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp0 x)).mp hsum
    exact (Finset.sum_eq_zero (fun x hx => by rw [hall x hx, zero_mul])).symm
  · unfold cellMean
    exact mul_div_cancel₀ _ h

/-- **Tower property, cell form** (total expectation):
`E[Y] = ∑ c, P(G = c) E[Y | G = c]`. -/
theorem sum_mul_eq_sum_cellMass_mul_cellMean {α C : Type*} [Fintype α] [Fintype C]
    [DecidableEq C] {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (Y : α → ℝ) :
    ∑ x, p x * Y x = ∑ c, cellMass p G c * cellMean p G Y c := by
  calc ∑ x, p x * Y x
      = ∑ c, ∑ x ∈ univ.filter (fun x => G x = c), p x * Y x :=
        (Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _) _).symm
    _ = ∑ c, cellMass p G c * cellMean p G Y c :=
        Finset.sum_congr rfl (fun c _ => (cellMass_mul_cellMean hp0 G Y c).symm)

/-- **Tower property for every version of the conditional mean**: if `m` agrees with the cell
mean on every cell of nonzero mass (and is arbitrary on null cells), then
`E[m(G)] = E[Y]`. -/
theorem sum_mul_comp_eq_sum_mul_of_eq_cellMean {α C : Type*} [Fintype α] [Fintype C]
    [DecidableEq C] {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (Y : α → ℝ) (m : C → ℝ)
    (hm : ∀ c, cellMass p G c ≠ 0 → m c = cellMean p G Y c) :
    ∑ x, p x * m (G x) = ∑ x, p x * Y x := by
  rw [sum_mul_comp_eq_sum_cellMass_mul p G m, sum_mul_eq_sum_cellMass_mul_cellMean hp0 G Y]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h : cellMass p G c = 0
  · rw [h, zero_mul, zero_mul]
  · rw [hm c h]

/-- **Nested tower property**: conditioning first on the fine cells of `G` and then on the
coarser cells of `f ∘ G` is conditioning on `f ∘ G`, cell by cell:
`E[E[Y | G] | f(G) = d] = E[Y | f(G) = d]`. This holds for every `d`, null coarse cells
included (both sides are `0` there). -/
theorem cellMean_comp_cellMean {α C D : Type*} [Fintype α] [Fintype C] [DecidableEq C]
    [DecidableEq D] {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (f : C → D) (Y : α → ℝ)
    (d : D) :
    cellMean p (fun x => f (G x)) (fun x => cellMean p G Y (G x)) d =
      cellMean p (fun x => f (G x)) Y d := by
  set q : α → ℝ := fun x => if f (G x) = d then p x else 0 with hq
  have hq0 : ∀ x, 0 ≤ q x := by
    intro x
    by_cases h : f (G x) = d
    · simp [hq, h, hp0 x]
    · simp [hq, h]
  have hS1 : (∑ x ∈ univ.filter (fun x => f (G x) = d), p x * cellMean p G Y (G x))
      = ∑ x, q x * cellMean p G Y (G x) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : f (G x) = d <;> simp [hq, h]
  have hS2 : (∑ x ∈ univ.filter (fun x => f (G x) = d), p x * Y x)
      = ∑ x, q x * Y x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : f (G x) = d <;> simp [hq, h]
  have hm : ∀ c, cellMass q G c ≠ 0 → (fun c => cellMean p G Y c) c = cellMean q G Y c := by
    intro c hc
    show cellMean p G Y c = cellMean q G Y c
    have hfc : f c = d := by
      by_contra hne
      apply hc
      simp only [cellMass]
      refine Finset.sum_eq_zero (fun x hx => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hneg : ¬ f (G x) = d := by rw [hx]; exact hne
      simp [hq, hneg]
    have hqp : ∀ x ∈ univ.filter (fun x => G x = c), q x = p x := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hpos : f (G x) = d := by rw [hx, hfc]
      simp [hq, hpos]
    have hmass : (∑ x ∈ univ.filter (fun x => G x = c), q x)
        = ∑ x ∈ univ.filter (fun x => G x = c), p x :=
      Finset.sum_congr rfl hqp
    have hsum : (∑ x ∈ univ.filter (fun x => G x = c), q x * Y x)
        = ∑ x ∈ univ.filter (fun x => G x = c), p x * Y x :=
      Finset.sum_congr rfl (fun x hx => by rw [hqp x hx])
    simp only [cellMean, cellMass]
    rw [hsum, hmass]
  have htower : ∑ x, q x * cellMean p G Y (G x) = ∑ x, q x * Y x :=
    sum_mul_comp_eq_sum_mul_of_eq_cellMean hq0 G Y (fun c => cellMean p G Y c) hm
  show (∑ x ∈ univ.filter (fun x => f (G x) = d), p x * cellMean p G Y (G x)) /
      cellMass p (fun x => f (G x)) d
    = (∑ x ∈ univ.filter (fun x => f (G x) = d), p x * Y x) /
      cellMass p (fun x => f (G x)) d
  rw [hS1, hS2, htower]

/-- **Total-variance decomposition**: the variance of `Y` is the mean within-cell variance
plus the variance of the cell means under the cell law,
`Var(Y) = E[Var(Y | G)] + Var(E[Y | G])`. The centre of the second term is the cell-law mean
of the cell means, which equals `E[Y]` by `sum_mul_eq_sum_cellMass_mul_cellMean`. -/
theorem sum_mul_sq_sub_eq_within_add_between {α C : Type*} [Fintype α] [Fintype C]
    [DecidableEq C] {p : α → ℝ} (hp0 : ∀ x, 0 ≤ p x) (G : α → C) (Y : α → ℝ) :
    ∑ x, p x * (Y x - ∑ y, p y * Y y) ^ 2 =
      ∑ c, cellMass p G c * cellVar p G Y c +
        ∑ c, cellMass p G c *
          (cellMean p G Y c - ∑ c', cellMass p G c' * cellMean p G Y c') ^ 2 := by
  rw [← sum_mul_eq_sum_cellMass_mul_cellMean hp0 G Y]
  have key : ∀ c (a : ℝ), (∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - a) ^ 2)
      = cellMass p G c * cellVar p G Y c
        + cellMass p G c * (cellMean p G Y c - a) ^ 2 := by
    intro c a
    have hW : cellMass p G c * cellVar p G Y c
        = ∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - cellMean p G Y c) ^ 2 :=
      cellMass_mul_cellMean hp0 G (fun x => (Y x - cellMean p G Y c) ^ 2) c
    have hB : cellMass p G c * (cellMean p G Y c - a) ^ 2
        = ∑ x ∈ univ.filter (fun x => G x = c), p x * (cellMean p G Y c - a) ^ 2 := by
      simp only [cellMass]
      exact Finset.sum_mul _ _ _
    have hcross : (∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - cellMean p G Y c)) = 0 := by
      calc (∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - cellMean p G Y c))
          = ∑ x ∈ univ.filter (fun x => G x = c), (p x * Y x - p x * cellMean p G Y c) :=
            Finset.sum_congr rfl (fun x _ => by ring)
        _ = (∑ x ∈ univ.filter (fun x => G x = c), p x * Y x)
            - ∑ x ∈ univ.filter (fun x => G x = c), p x * cellMean p G Y c :=
            Finset.sum_sub_distrib _ _
        _ = 0 := by
            rw [← cellMass_mul_cellMean hp0 G Y c, ← Finset.sum_mul]
            simp only [cellMass]
            exact sub_self _
    have hmid : (∑ x ∈ univ.filter (fun x => G x = c),
        2 * (cellMean p G Y c - a) * (p x * (Y x - cellMean p G Y c))) = 0 := by
      rw [← Finset.mul_sum, hcross, mul_zero]
    have halg : ∀ x, p x * (Y x - a) ^ 2
        = p x * (Y x - cellMean p G Y c) ^ 2
          + 2 * (cellMean p G Y c - a) * (p x * (Y x - cellMean p G Y c))
          + p x * (cellMean p G Y c - a) ^ 2 := fun x => by ring
    calc (∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - a) ^ 2)
        = ∑ x ∈ univ.filter (fun x => G x = c), (p x * (Y x - cellMean p G Y c) ^ 2
            + 2 * (cellMean p G Y c - a) * (p x * (Y x - cellMean p G Y c))
            + p x * (cellMean p G Y c - a) ^ 2) :=
          Finset.sum_congr rfl (fun x _ => halg x)
      _ = (∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - cellMean p G Y c) ^ 2)
          + (∑ x ∈ univ.filter (fun x => G x = c),
            2 * (cellMean p G Y c - a) * (p x * (Y x - cellMean p G Y c)))
          + ∑ x ∈ univ.filter (fun x => G x = c), p x * (cellMean p G Y c - a) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = cellMass p G c * cellVar p G Y c + cellMass p G c * (cellMean p G Y c - a) ^ 2 := by
          rw [← hW, hmid, ← hB, add_zero]
  calc ∑ x, p x * (Y x - ∑ y, p y * Y y) ^ 2
      = ∑ c, ∑ x ∈ univ.filter (fun x => G x = c), p x * (Y x - ∑ y, p y * Y y) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _) _).symm
    _ = ∑ c, cellMass p G c * cellVar p G Y c +
        ∑ c, cellMass p G c * (cellMean p G Y c - ∑ x, p x * Y x) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact key c (∑ y, p y * Y y)

end MathlibExt.Probability.FiniteConditioning
