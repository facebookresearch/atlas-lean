/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith

/-!
# Stieltjes product integrals

For a real function `A` and `a ≤ b`, the **product integral**
`∏_{(a, b]} (1 + dA)` is the limit of the finite products
`∏ᵢ (1 + (A tᵢ - A tᵢ₋₁))` over partitions `a = t₀ < t₁ < ⋯ < tₙ = b`, the limit
being taken along refinement of partitions.

## Main definitions

* `prev P x`: the largest element of the finite set `P` strictly below `x` (or `x` itself).
* `gridProd A P`: the product `∏_{x ∈ P} (1 + (A x - A (prev P x)))` of the factors
  `1 + ΔA` over the consecutive cells of the finite set `P`.
* `partitionPts a b s`: the partition of `[a, b]` with interior points `s ∩ (a, b)`.
* `partitionProd A a b s = gridProd A (partitionPts a b s)`: the net of partition products,
  indexed by finite sets `s : Finset ℝ` ordered by inclusion (that is, by refinement).
* `productIntegral A a b`: the limit of `partitionProd A a b` along `atTop`.

## Main results

* `tendsto_partitionProd`: if `A` is dominated on `[a, b]` by a monotone control `V`, that
  is, `|A x - A y| ≤ V x - V y` for `a ≤ y ≤ x ≤ b`, the partition products converge to
  `productIntegral A a b`. `exists_control_of_boundedVariationOn` supplies such a `V` (the
  variation function) for every function of bounded variation, giving
  `tendsto_partitionProd_of_boundedVariationOn`.
* `abs_partitionProd_insert_sub_le`, `abs_partitionProd_sub_le_of_subset`: the
  **majorant inequality**: refining a partition changes the `A`-product by at most the
  change of the `V`-product. This is the heart of the existence proof.
* `productIntegral_mul`: **multiplicativity** over adjacent intervals,
  `∏_{(a,c]} = ∏_{(a,b]} · ∏_{(b,c]}`.
* `productIntegral_sub_eq_sum`: the exact **Duhamel identity** on any partition, and
  `tendsto_duhamelSum`: the **Duhamel identity** in Riemann–Stieltjes form,
  `∏(1 + dB) - ∏(1 + dA) = ∫_{(a,b]} ∏_{(a,u)}(1 + dA) d(B - A)(u) ∏_{(u,b]}(1 + dB)`.
  Taking `A = 0` or `B = 0` gives the backward and forward **Volterra equations**
  `tendsto_volterra_backward` and `tendsto_volterra_forward`.
* Basic properties: `productIntegral_self`, `productIntegral_const`,
  `productIntegral_step` (a single jump `J` gives `1 + J`), the bounds
  `abs_productIntegral_le` and `productIntegral_le_exp`, and
  `one_add_sub_le_productIntegral` for monotone integrators.

## Implementation notes

Partitions are encoded by finite sets of reals, and `prev P x` picks the left endpoint of the
cell ending at `x`; the minimum of `P` contributes the trivial factor `1 + 0`. Indexing the
net by `Finset ℝ` with `atTop` makes "limit along refinement" literal: `s ≤ t` means `t`
refines `s`. Convergence is proved without any regularity of `A` beyond domination by a
monotone `V`: the `V`-products increase under refinement and are bounded by
`exp (V b - V a)`, and the majorant inequality transfers their Cauchy property to the
`A`-products. In particular no right-continuity is assumed. This file does not relate the
refinement limit to the mesh → 0 limit; that for a right-continuous integrator the two agree
and give the classical product integral over `(a, b]` is a standard fact (Gill–Johansen 1990,
§2) that is not proved here.

The fixed-grid product `MathlibExt.Probability.Statistics.FunctionalDelta.prodIntegral`
(products of `1 + xᵢ` over given increments) is the discrete analogue; this file supplies the
continuous-time limit over refining partitions. The development is scalar (real-valued
integrators). Hadamard differentiability of
`A ↦ ∏(1 + dA)` is deliberately not treated here, and neither is what it needs beyond this
file: the Duhamel operator as a continuous linear map on bounded functions (a
Riemann–Stieltjes integral `∫ f dh` against a general integrator `h`, with a sup-norm bound and
continuity in `B`), and step integrators with several jumps.

## References

* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward
  application in survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
-/

open Finset Filter Topology

@[expose] public section

namespace MathlibExt.Analysis.StieltjesProductIntegral

/-! ### Cells of a finite set -/

/-- The **left neighbour** of `x` in the finite set `P`: the largest element of `P` strictly
below `x`, or `x` itself if there is none. For `x ∈ P` this is the left endpoint of the cell
of the partition `P` whose right endpoint is `x`. -/
noncomputable def prev (P : Finset ℝ) (x : ℝ) : ℝ :=
  if h : (P.filter (· < x)).Nonempty then (P.filter (· < x)).max' h else x

theorem prev_spec {P : Finset ℝ} {x : ℝ} (h : ∃ z ∈ P, z < x) :
    prev P x ∈ P ∧ prev P x < x ∧ ∀ z ∈ P, z < x → z ≤ prev P x := by
  have hne : (P.filter (· < x)).Nonempty := by
    obtain ⟨z, hz, hzx⟩ := h
    exact ⟨z, mem_filter.2 ⟨hz, hzx⟩⟩
  have hmem := (P.filter (· < x)).max'_mem hne
  rw [prev, dite_eq_left hne]
  refine ⟨(mem_filter.1 hmem).1, (mem_filter.1 hmem).2, fun z hz hzx => ?_⟩
  exact (P.filter (· < x)).le_max' z (mem_filter.2 ⟨hz, hzx⟩)

theorem prev_eq_self {P : Finset ℝ} {x : ℝ} (h : ¬∃ z ∈ P, z < x) : prev P x = x := by
  have hne : ¬(P.filter (· < x)).Nonempty := by
    rintro ⟨z, hz⟩
    exact h ⟨z, (mem_filter.1 hz).1, (mem_filter.1 hz).2⟩
  rw [prev, dite_eq_right hne]

/-- Characterization of `prev`: `y` is the left neighbour of `x` in `P` if `y ∈ P`, `y < x`
and no element of `P` lies strictly between them. -/
theorem prev_eq_of {P : Finset ℝ} {x y : ℝ} (hy : y ∈ P) (hyx : y < x)
    (hmax : ∀ z ∈ P, z < x → z ≤ y) : prev P x = y := by
  obtain ⟨h1, h2, h3⟩ := prev_spec ⟨y, hy, hyx⟩
  exact le_antisymm (hmax _ h1 h2) (h3 y hy hyx)

theorem prev_le (P : Finset ℝ) (x : ℝ) : prev P x ≤ x := by
  by_cases h : ∃ z ∈ P, z < x
  · exact (prev_spec h).2.1.le
  · exact (prev_eq_self h).le

/-- `prev P x` is either in `P` or equal to `x`. -/
theorem prev_mem_or_eq (P : Finset ℝ) (x : ℝ) : prev P x ∈ P ∨ prev P x = x := by
  by_cases h : ∃ z ∈ P, z < x
  · exact Or.inl (prev_spec h).1
  · exact Or.inr (prev_eq_self h)

theorem prev_mem {P : Finset ℝ} {x : ℝ} (hx : x ∈ P) : prev P x ∈ P := by
  rcases prev_mem_or_eq P x with h | h
  · exact h
  · rw [h]; exact hx


/-! ### Inserting one point into a finite set -/

section Insert

variable {P : Finset ℝ} {p v : ℝ}

/-- Every finite set with an element above `p` has a least element above `p`. -/
theorem exists_next {P : Finset ℝ} {p : ℝ} (h : ∃ y ∈ P, p < y) :
    ∃ v ∈ P, p < v ∧ ∀ y ∈ P, p < y → v ≤ y := by
  have hne : (P.filter (p < ·)).Nonempty := by
    obtain ⟨y, hy, hpy⟩ := h
    exact ⟨y, mem_filter.2 ⟨hy, hpy⟩⟩
  have hmem := (P.filter (p < ·)).min'_mem hne
  exact ⟨_, (mem_filter.1 hmem).1, (mem_filter.1 hmem).2,
    fun y hy hpy => (P.filter (p < ·)).min'_le y (mem_filter.2 ⟨hy, hpy⟩)⟩

variable (hp : p ∉ P) (hv : v ∈ P) (hpv : p < v) (hvmin : ∀ y ∈ P, p < y → v ≤ y)
  (hlow : ∃ y ∈ P, y < p)
include hp hv hpv hvmin hlow

omit hv hpv hlow in
private theorem lt_of_lt_next {z : ℝ} (hz : z ∈ P) (hzv : z < v) : z < p := by
  rcases lt_trichotomy z p with h | h | h
  · exact h
  · exact absurd (h ▸ hz) hp
  · exact absurd (hvmin z hz h) (not_le.2 hzv)

omit hv in
theorem prev_insert_self : prev (insert p P) p = prev P p := by
  obtain ⟨h1, h2, h3⟩ := prev_spec hlow
  refine prev_eq_of (mem_insert_of_mem h1) h2 fun z hz hzp => ?_
  rcases mem_insert.1 hz with rfl | hz
  · exact absurd hzp (lt_irrefl _)
  · exact h3 z hz hzp

omit hv in
theorem prev_next : prev P v = prev P p := by
  obtain ⟨h1, h2, h3⟩ := prev_spec hlow
  exact prev_eq_of h1 (h2.trans hpv) fun z hz hzv =>
    h3 z hz (lt_of_lt_next hp hvmin hz hzv)

omit hv in
theorem prev_insert_next : prev (insert p P) v = p := by
  refine prev_eq_of (mem_insert_self p P) hpv fun z hz hzv => ?_
  rcases mem_insert.1 hz with rfl | hz
  · exact le_rfl
  · exact (lt_of_lt_next hp hvmin hz hzv).le

theorem prev_insert_of_ne {x : ℝ} (hx : x ∈ P) (hxv : x ≠ v) : prev (insert p P) x = prev P x := by
  rcases lt_or_gt_of_ne (show x ≠ p by rintro rfl; exact hp hx) with hxp | hxp
  · by_cases h : ∃ z ∈ P, z < x
    · obtain ⟨h1, h2, h3⟩ := prev_spec h
      refine prev_eq_of (mem_insert_of_mem h1) h2 fun z hz hzx => ?_
      rcases mem_insert.1 hz with rfl | hz
      · exact absurd (hzx.trans hxp) (lt_irrefl _)
      · exact h3 z hz hzx
    · rw [prev_eq_self h]
      refine prev_eq_self ?_
      rintro ⟨z, hz, hzx⟩
      rcases mem_insert.1 hz with rfl | hz
      · exact absurd (hzx.trans hxp) (lt_irrefl _)
      · exact h ⟨z, hz, hzx⟩
  · have hvx : v < x := lt_of_le_of_ne (hvmin x hx hxp) (Ne.symm hxv)
    obtain ⟨h1, h2, h3⟩ := prev_spec ⟨v, hv, hvx⟩
    refine prev_eq_of (mem_insert_of_mem h1) h2 fun z hz hzx => ?_
    rcases mem_insert.1 hz with rfl | hz
    · exact (hpv.trans_le (h3 v hv hvx)).le
    · exact h3 z hz hzx

/-- Products over cells before an interior insertion: the cell `(u, v]` with
`u = prev P p` contributes `φ u v`. -/
theorem prod_cells_eq_erase (φ : ℝ → ℝ → ℝ) :
    ∏ x ∈ P, φ (prev P x) x = (∏ x ∈ P.erase v, φ (prev P x) x) * φ (prev P p) v := by
  rw [← prev_next hp hpv hvmin hlow, prod_erase_mul _ _ hv]

/-- Products over cells after an interior insertion of `p` between `u = prev P p` and `v`:
the cell `(u, v]` is replaced by the two cells `(u, p]` and `(p, v]`. -/
theorem prod_cells_insert (φ : ℝ → ℝ → ℝ) :
    ∏ x ∈ insert p P, φ (prev (insert p P) x) x =
      (∏ x ∈ P.erase v, φ (prev P x) x) * (φ (prev P p) p * φ p v) := by
  rw [prod_insert hp, prev_insert_self hp hpv hvmin hlow,
    ← prod_erase_mul _ _ hv, prev_insert_next hp hpv hvmin hlow]
  have hcongr : ∏ x ∈ P.erase v, φ (prev (insert p P) x) x = ∏ x ∈ P.erase v, φ (prev P x) x :=
    prod_congr rfl fun x hx =>
      by rw [prev_insert_of_ne hp hv hpv hvmin hlow (mem_of_mem_erase hx) (ne_of_mem_erase hx)]
  rw [hcongr]
  ring

/-- Additive version of `prod_cells_eq_erase`. -/
theorem sum_cells_eq_erase (ψ : ℝ → ℝ → ℝ) :
    ∑ x ∈ P, ψ (prev P x) x = (∑ x ∈ P.erase v, ψ (prev P x) x) + ψ (prev P p) v := by
  rw [← prev_next hp hpv hvmin hlow, sum_erase_add _ _ hv]

/-- Additive version of `prod_cells_insert`. -/
theorem sum_cells_insert (ψ : ℝ → ℝ → ℝ) :
    ∑ x ∈ insert p P, ψ (prev (insert p P) x) x =
      (∑ x ∈ P.erase v, ψ (prev P x) x) + (ψ (prev P p) p + ψ p v) := by
  rw [sum_insert hp, prev_insert_self hp hpv hvmin hlow,
    ← sum_erase_add _ _ hv, prev_insert_next hp hpv hvmin hlow]
  have hcongr : ∑ x ∈ P.erase v, ψ (prev (insert p P) x) x = ∑ x ∈ P.erase v, ψ (prev P x) x :=
    sum_congr rfl fun x hx =>
      by rw [prev_insert_of_ne hp hv hpv hvmin hlow (mem_of_mem_erase hx) (ne_of_mem_erase hx)]
  rw [hcongr]
  ring

end Insert


/-! ### Partitions of `[a, b]` -/

/-- The **partition of `[a, b]` generated by `s`**: the endpoints `a`, `b` together with the
points of `s` lying strictly between them. As `s` ranges over `Finset ℝ` ordered by
inclusion, `partitionPts a b s` ranges cofinally over the partitions of `[a, b]`. -/
noncomputable def partitionPts (a b : ℝ) (s : Finset ℝ) : Finset ℝ :=
  insert a (insert b (s.filter fun x => a < x ∧ x < b))

section Partition

variable {a b : ℝ}

theorem mem_partitionPts {s : Finset ℝ} {x : ℝ} :
    x ∈ partitionPts a b s ↔ x = a ∨ x = b ∨ (x ∈ s ∧ a < x ∧ x < b) := by
  simp [partitionPts]

theorem left_mem_partitionPts (s : Finset ℝ) : a ∈ partitionPts a b s :=
  mem_partitionPts.2 (Or.inl rfl)

theorem right_mem_partitionPts (s : Finset ℝ) : b ∈ partitionPts a b s :=
  mem_partitionPts.2 (Or.inr (Or.inl rfl))

theorem mem_Icc_of_mem_partitionPts (hab : a ≤ b) {s : Finset ℝ} {x : ℝ}
    (hx : x ∈ partitionPts a b s) : a ≤ x ∧ x ≤ b := by
  rcases mem_partitionPts.1 hx with rfl | rfl | ⟨-, h1, h2⟩
  · exact ⟨le_rfl, hab⟩
  · exact ⟨hab, le_rfl⟩
  · exact ⟨h1.le, h2.le⟩

theorem partitionPts_mono {s t : Finset ℝ} (hst : s ⊆ t) :
    partitionPts a b s ⊆ partitionPts a b t := fun x hx => by
  rcases mem_partitionPts.1 hx with h | h | ⟨h1, h2⟩
  · exact mem_partitionPts.2 (Or.inl h)
  · exact mem_partitionPts.2 (Or.inr (Or.inl h))
  · exact mem_partitionPts.2 (Or.inr (Or.inr ⟨hst h1, h2⟩))

theorem partitionPts_empty : partitionPts a b ∅ = {a, b} := by
  simp [partitionPts]

theorem partitionPts_insert_of_mem {s : Finset ℝ} {p : ℝ} (hap : a < p) (hpb : p < b) :
    partitionPts a b (insert p s) = insert p (partitionPts a b s) := by
  ext x
  simp only [mem_partitionPts, mem_insert]
  constructor
  · rintro (h | h | ⟨h | h, h'⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨h, h'⟩))
  · rintro (rfl | h | h | ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨Or.inl rfl, hap, hpb⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨Or.inr h, h'⟩)

theorem partitionPts_insert_of_not_mem {s : Finset ℝ} {p : ℝ} (hp : ¬(a < p ∧ p < b)) :
    partitionPts a b (insert p s) = partitionPts a b s := by
  ext x
  simp only [mem_partitionPts, mem_insert]
  constructor
  · rintro (h | h | ⟨rfl | h, h'⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h' hp
    · exact Or.inr (Or.inr ⟨h, h'⟩)
  · rintro (h | h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨Or.inr h, h'⟩)

/-- **Induction along interior insertions.** A property of finite sets that holds for
`{a, b}` and is preserved by inserting a new point `p ∈ (a, b)` (with right neighbour `v`)
holds for every partition `partitionPts a b s`. -/
theorem partitionPts_induction (motive : Finset ℝ → Prop) (base : motive {a, b})
    (step : ∀ (P : Finset ℝ) (p v : ℝ), a ∈ P → b ∈ P → a < p → p < b → p ∉ P → v ∈ P →
      p < v → (∀ y ∈ P, p < y → v ≤ y) → motive P → motive (insert p P))
    (s : Finset ℝ) : motive (partitionPts a b s) := by
  induction s using Finset.induction_on with
  | empty => rwa [partitionPts_empty]
  | insert p s _ ih =>
    by_cases hp : a < p ∧ p < b
    · rw [partitionPts_insert_of_mem hp.1 hp.2]
      by_cases hmem : p ∈ partitionPts a b s
      · rwa [insert_eq_of_mem hmem]
      · obtain ⟨v, hv, hpv, hvmin⟩ := exists_next ⟨b, right_mem_partitionPts s, hp.2⟩
        exact step _ p v (left_mem_partitionPts s) (right_mem_partitionPts s) hp.1 hp.2 hmem hv
          hpv hvmin ih
    · rwa [partitionPts_insert_of_not_mem hp]

/-- **Telescoping products over cells.** If `φ t t = 1` at `t = a` and `φ` is multiplicative
over adjacent cells inside `[a, b]`, the product of `φ` over the cells of any partition of
`[a, b]` is `φ a b`. -/
theorem prod_cells_partitionPts (hab : a ≤ b) (φ : ℝ → ℝ → ℝ) (h1 : φ a a = 1)
    (hmul : ∀ u p v, a ≤ u → u < p → p < v → v ≤ b → φ u p * φ p v = φ u v) (s : Finset ℝ) :
    ∏ x ∈ partitionPts a b s, φ (prev (partitionPts a b s) x) x = φ a b := by
  refine partitionPts_induction (fun P => (∀ x ∈ P, a ≤ x ∧ x ≤ b) →
    ∏ x ∈ P, φ (prev P x) x = φ a b) ?_ ?_ s (fun x hx => mem_Icc_of_mem_partitionPts hab hx)
  · intro _
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp [prev_eq_self, h1]
    · rw [prod_pair hlt.ne, prev_eq_self (by simp [hab]), prev_eq_of (by simp) hlt (by simp), h1,
        one_mul]
  · intro P p v haP hbP hap hpb hp hv hpv hvmin ih hIcc
    have hlow : ∃ y ∈ P, y < p := ⟨a, haP, hap⟩
    have hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b := fun x hx => hIcc x (mem_insert_of_mem hx)
    rw [prod_cells_insert hp hv hpv hvmin hlow, ← ih hP, prod_cells_eq_erase hp hv hpv hvmin hlow]
    obtain ⟨hu, hup, -⟩ := prev_spec hlow
    rw [hmul _ p v (hP _ hu).1 hup hpv (hP v hv).2]

/-- **Telescoping sums over cells**, the additive version of `prod_cells_partitionPts`. -/
theorem sum_cells_partitionPts (hab : a ≤ b) (ψ : ℝ → ℝ → ℝ) (h0 : ψ a a = 0)
    (hadd : ∀ u p v, a ≤ u → u < p → p < v → v ≤ b → ψ u p + ψ p v = ψ u v) (s : Finset ℝ) :
    ∑ x ∈ partitionPts a b s, ψ (prev (partitionPts a b s) x) x = ψ a b := by
  refine partitionPts_induction (fun P => (∀ x ∈ P, a ≤ x ∧ x ≤ b) →
    ∑ x ∈ P, ψ (prev P x) x = ψ a b) ?_ ?_ s (fun x hx => mem_Icc_of_mem_partitionPts hab hx)
  · intro _
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp [prev_eq_self, h0]
    · rw [sum_pair hlt.ne, prev_eq_self (by simp [hab]), prev_eq_of (by simp) hlt (by simp), h0,
        zero_add]
  · intro P p v haP hbP hap hpb hp hv hpv hvmin ih hIcc
    have hlow : ∃ y ∈ P, y < p := ⟨a, haP, hap⟩
    have hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b := fun x hx => hIcc x (mem_insert_of_mem hx)
    rw [sum_cells_insert hp hv hpv hvmin hlow, ← ih hP, sum_cells_eq_erase hp hv hpv hvmin hlow]
    obtain ⟨hu, hup, -⟩ := prev_spec hlow
    rw [hadd _ p v (hP _ hu).1 hup hpv (hP v hv).2]

end Partition


/-! ### Grid products and the product integral -/

/-- The **grid product** of `A` over the finite set `P`: the product of the factors
`1 + (A x - A (prev P x))` over the cells `(prev P x, x]` of `P`. The minimum of `P`
contributes the trivial factor `1`. -/
noncomputable def gridProd (A : ℝ → ℝ) (P : Finset ℝ) : ℝ :=
  ∏ x ∈ P, (1 + (A x - A (prev P x)))

/-- The **partition product** `∏ᵢ (1 + (A tᵢ - A tᵢ₋₁))` over the partition
`partitionPts a b s` of `[a, b]`. As a function of `s : Finset ℝ` this is the net whose limit
along refinement (`atTop`) is the product integral. -/
noncomputable def partitionProd (A : ℝ → ℝ) (a b : ℝ) (s : Finset ℝ) : ℝ :=
  gridProd A (partitionPts a b s)

/-- The **Stieltjes product integral** `∏_{(a, b]} (1 + dA)`: the limit of the partition
products `partitionProd A a b s` along refinement of partitions. The limit exists whenever
`A` has bounded variation on `[a, b]` (`tendsto_partitionProd_of_boundedVariationOn`), and
more generally whenever `A` is dominated by a monotone control (`tendsto_partitionProd`).
It is intended for `a ≤ b`. -/
noncomputable def productIntegral (A : ℝ → ℝ) (a b : ℝ) : ℝ :=
  limUnder atTop (partitionProd A a b)

/-- `V` is a **monotone control** for `A` on `[a, b]`: every increment of `A` inside `[a, b]`
is dominated by the corresponding increment of `V`. The variation function of a function of
bounded variation is a control (`exists_control_of_boundedVariationOn`); a monotone function
is its own control (`isControl_self_of_monotoneOn`). -/
def IsControl (A V : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x y, a ≤ y → y ≤ x → x ≤ b → |A x - A y| ≤ V x - V y

section Control

variable {A V : ℝ → ℝ} {a b : ℝ}

theorem IsControl.mono (hc : IsControl A V a b) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    IsControl A V a' b' := fun x y hy hyx hx =>
  hc x y (ha.trans hy) hyx (hx.trans hb)

theorem IsControl.sub_nonneg (hc : IsControl A V a b) {x y : ℝ} (hy : a ≤ y) (hyx : y ≤ x)
    (hx : x ≤ b) : 0 ≤ V x - V y :=
  (abs_nonneg _).trans (hc x y hy hyx hx)

/-- A function monotone on `[a, b]` is its own control. -/
theorem isControl_self_of_monotoneOn (h : MonotoneOn A (Set.Icc a b)) : IsControl A A a b :=
  fun x y hy hyx hx => by
    have : A y ≤ A x := h ⟨hy, hyx.trans hx⟩ ⟨hy.trans hyx, hx⟩ hyx
    rw [abs_of_nonneg (sub_nonneg.2 this)]

/-- A control of `A` also controls `-A`. -/
theorem IsControl.neg (hc : IsControl A V a b) : IsControl (fun t => -A t) V a b :=
  fun x y hy hyx hx => by
    rw [show -A x - -A y = -(A x - A y) by ring, abs_neg]
    exact hc x y hy hyx hx

/-- Every function of bounded variation on `[a, b]` is controlled by its variation function
`t ↦ variationOnFromTo A (Icc a b) a t`. -/
theorem exists_control_of_boundedVariationOn (h : BoundedVariationOn A (Set.Icc a b)) :
    IsControl A (variationOnFromTo A (Set.Icc a b) a) a b := by
  intro x y hy hyx hx
  have hab : a ≤ b := hy.trans (hyx.trans hx)
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hy' : y ∈ Set.Icc a b := ⟨hy, hyx.trans hx⟩
  have hx' : x ∈ Set.Icc a b := ⟨hy.trans hyx, hx⟩
  rw [← variationOnFromTo.add h.locallyBoundedVariationOn ha hy' hx', add_sub_cancel_left,
    variationOnFromTo.eq_of_le _ _ hyx, ← Real.dist_eq, dist_edist]
  have hfin : eVariationOn A (Set.Icc a b ∩ Set.Icc y x) ≠ ⊤ :=
    ne_top_of_le_ne_top h (eVariationOn.mono A Set.inter_subset_left)
  exact ENNReal.toReal_mono hfin
    (eVariationOn.edist_le A ⟨hx', le_trans hyx le_rfl, le_rfl⟩ ⟨hy', le_rfl, hyx⟩)

end Control

section GridProd

variable {A V : ℝ → ℝ} {a b : ℝ}

/-- The grid product over a pair `{a, b}` with `a ≤ b` is the single factor `1 + (A b - A a)`. -/
theorem gridProd_pair (A : ℝ → ℝ) (hab : a ≤ b) : gridProd A {a, b} = 1 + (A b - A a) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [gridProd, prev_eq_self]
  · rw [gridProd, prod_pair hlt.ne, prev_eq_self (by simp [hab]),
      prev_eq_of (by simp) hlt (by simp), sub_self, add_zero, one_mul]

theorem partitionProd_empty (A : ℝ → ℝ) (hab : a ≤ b) :
    partitionProd A a b ∅ = 1 + (A b - A a) := by
  rw [partitionProd, partitionPts_empty, gridProd_pair A hab]

/-- Factors of a controlled grid product are dominated by the factors of the control. -/
private theorem abs_cell_le (hc : IsControl A V a b) {P : Finset ℝ}
    (hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b) {x : ℝ} (hx : x ∈ P) :
    |1 + (A x - A (prev P x))| ≤ 1 + (V x - V (prev P x)) := by
  have hu := hP _ (prev_mem hx)
  calc |1 + (A x - A (prev P x))| ≤ |1| + |A x - A (prev P x)| := abs_add_le _ _
    _ ≤ 1 + (V x - V (prev P x)) := by
      rw [abs_one]
      exact add_le_add_right (hc x _ hu.1 (prev_le P x) (hP x hx).2) 1

private theorem abs_prod_cells_le (hc : IsControl A V a b) {P : Finset ℝ}
    (hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b) (Q : Finset ℝ) (hQ : Q ⊆ P) :
    |∏ x ∈ Q, (1 + (A x - A (prev P x)))| ≤ ∏ x ∈ Q, (1 + (V x - V (prev P x))) := by
  rw [abs_prod]
  exact prod_le_prod₀ (fun x _ => abs_nonneg _) fun x hx => abs_cell_le hc hP (hQ hx)

/-- A controlled grid product is dominated by the grid product of the control. -/
theorem abs_gridProd_le (hc : IsControl A V a b) {P : Finset ℝ}
    (hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b) : |gridProd A P| ≤ gridProd V P :=
  abs_prod_cells_le hc hP P subset_rfl

/-- The exact change of a grid product under an interior insertion. -/
theorem gridProd_insert_sub (A : ℝ → ℝ) {P : Finset ℝ} {p v : ℝ} (hp : p ∉ P) (hv : v ∈ P)
    (hpv : p < v) (hvmin : ∀ y ∈ P, p < y → v ≤ y) (hlow : ∃ y ∈ P, y < p) :
    gridProd A (insert p P) - gridProd A P =
      (∏ x ∈ P.erase v, (1 + (A x - A (prev P x)))) * ((A p - A (prev P p)) * (A v - A p)) := by
  have h1 := prod_cells_insert hp hv hpv hvmin hlow (fun u x => 1 + (A x - A u))
  have h2 := prod_cells_eq_erase hp hv hpv hvmin hlow (fun u x => 1 + (A x - A u))
  rw [gridProd, gridProd, h1, h2]
  ring

/-- **Majorant inequality for one insertion.** Inserting one point into a partition changes
the `A`-product by at most the change of the `V`-product. -/
theorem abs_partitionProd_insert_sub_le (hab : a ≤ b) (hc : IsControl A V a b)
    (s : Finset ℝ) (p : ℝ) :
    |partitionProd A a b (insert p s) - partitionProd A a b s| ≤
      partitionProd V a b (insert p s) - partitionProd V a b s := by
  by_cases hp : a < p ∧ p < b
  · rw [partitionProd, partitionProd, partitionProd, partitionProd,
      partitionPts_insert_of_mem hp.1 hp.2]
    set P := partitionPts a b s with hPdef
    by_cases hmem : p ∈ P
    · simp [insert_eq_of_mem hmem]
    obtain ⟨v, hv, hpv, hvmin⟩ := exists_next ⟨b, right_mem_partitionPts s, hp.2⟩
    have hlow : ∃ y ∈ P, y < p := ⟨a, left_mem_partitionPts s, hp.1⟩
    have hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b := fun x hx => mem_Icc_of_mem_partitionPts hab hx
    rw [gridProd_insert_sub A hmem hv hpv hvmin hlow, gridProd_insert_sub V hmem hv hpv hvmin hlow,
      abs_mul, abs_mul]
    obtain ⟨hu, hup, -⟩ := prev_spec hlow
    have hpI : a ≤ p ∧ p ≤ b := ⟨hp.1.le, hp.2.le⟩
    refine mul_le_mul (abs_prod_cells_le hc hP _ (erase_subset v P))
      (mul_le_mul (hc p _ (hP _ hu).1 hup.le hpI.2) (hc v p hpI.1 hpv.le (hP v hv).2)
        (abs_nonneg _) (hc.sub_nonneg (hP _ hu).1 hup.le hpI.2))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
    refine prod_nonneg fun x hx => ?_
    have hx' := mem_of_mem_erase hx
    have := hc.sub_nonneg (hP _ (prev_mem hx')).1 (prev_le P x) (hP x hx').2
    linarith
  · simp [partitionPts_insert_of_not_mem hp, partitionProd]

/-- **Majorant inequality.** Refining a partition changes the `A`-product by at most the
change of the `V`-product: for `s ⊆ t`,
`|∏_t (1 + ΔA) - ∏_s (1 + ΔA)| ≤ ∏_t (1 + ΔV) - ∏_s (1 + ΔV)`. -/
theorem abs_partitionProd_sub_le_of_subset (hab : a ≤ b) (hc : IsControl A V a b)
    {s t : Finset ℝ} (hst : s ⊆ t) :
    |partitionProd A a b t - partitionProd A a b s| ≤
      partitionProd V a b t - partitionProd V a b s := by
  have key : ∀ u : Finset ℝ, |partitionProd A a b (u ∪ s) - partitionProd A a b s| ≤
      partitionProd V a b (u ∪ s) - partitionProd V a b s := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | insert p u _ ih =>
      rw [insert_union]
      have h1 := abs_partitionProd_insert_sub_le hab hc (u ∪ s) p
      have h2 := abs_sub_le (partitionProd A a b (insert p (u ∪ s)))
        (partitionProd A a b (u ∪ s)) (partitionProd A a b s)
      linarith
  have := key (t \ s)
  rwa [sdiff_union_of_subset hst] at this

/-- The partition products of a control increase under refinement. -/
theorem monotone_partitionProd (hab : a ≤ b) (hc : IsControl A V a b) :
    Monotone (partitionProd V a b) := fun _ _ hst =>
  sub_nonneg.1 ((abs_nonneg _).trans (abs_partitionProd_sub_le_of_subset hab hc hst))

/-- The partition products of a control are bounded by `exp (V b - V a)`. -/
theorem partitionProd_le_exp (hab : a ≤ b) (hc : IsControl A V a b) (s : Finset ℝ) :
    partitionProd V a b s ≤ Real.exp (V b - V a) := by
  set P := partitionPts a b s
  have hP : ∀ x ∈ P, a ≤ x ∧ x ≤ b := fun x hx => mem_Icc_of_mem_partitionPts hab hx
  have hsum := sum_cells_partitionPts hab (fun u x => V x - V u) (sub_self _) (fun _ _ _ _ _ _ _ =>
    by ring) s
  rw [partitionProd, gridProd, ← hsum, Real.exp_sum]
  refine prod_le_prod₀ (fun x hx => ?_) fun x _ => by
    rw [add_comm]; exact Real.add_one_le_exp _
  have := hc.sub_nonneg (hP _ (prev_mem hx)).1 (prev_le P x) (hP x hx).2
  linarith

end GridProd


/-! ### Existence of the product integral -/

section Existence

variable {A V : ℝ → ℝ} {a b : ℝ}

/-- A control controls itself. -/
theorem IsControl.self (hc : IsControl A V a b) : IsControl V V a b := fun x y hy hyx hx => by
  rw [abs_of_nonneg (hc.sub_nonneg hy hyx hx)]

/-- **Existence of the product integral.** If `A` is dominated on `[a, b]` by a monotone
control `V`, the partition products of `A` converge along refinement to
`productIntegral A a b`. -/
theorem tendsto_partitionProd (hab : a ≤ b) (hc : IsControl A V a b) :
    Tendsto (partitionProd A a b) atTop (𝓝 (productIntegral A a b)) := by
  have hmono := monotone_partitionProd hab hc
  have hbdd : BddAbove (Set.range (partitionProd V a b)) :=
    ⟨Real.exp (V b - V a), by rintro _ ⟨s, rfl⟩; exact partitionProd_le_exp hab hc s⟩
  have hV := tendsto_atTop_ciSup hmono hbdd
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hV).1 _ (sub_lt_self _ (half_pos hε)))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hNN := hN N le_rfl
  have h1 := abs_partitionProd_sub_le_of_subset hab hc (show N ⊆ m from hm)
  have h2 := abs_partitionProd_sub_le_of_subset hab hc (show N ⊆ n from hn)
  have h3 := le_ciSup hbdd m
  have h4 := le_ciSup hbdd n
  rw [Real.dist_eq]
  calc |partitionProd A a b m - partitionProd A a b n|
      ≤ |partitionProd A a b m - partitionProd A a b N| +
          |partitionProd A a b n - partitionProd A a b N| := by
        rw [abs_sub_comm (partitionProd A a b n)]; exact abs_sub_le _ _ _
    _ < ε := by linarith

/-- **Existence of the product integral for integrators of bounded variation.** -/
theorem tendsto_partitionProd_of_boundedVariationOn (hab : a ≤ b)
    (h : BoundedVariationOn A (Set.Icc a b)) :
    Tendsto (partitionProd A a b) atTop (𝓝 (productIntegral A a b)) :=
  tendsto_partitionProd hab (exists_control_of_boundedVariationOn h)

/-- The product integral of a controlled integrator is approximated by every partition
product, with error at most the corresponding error for the control. -/
theorem abs_productIntegral_sub_partitionProd_le (hab : a ≤ b) (hc : IsControl A V a b)
    (s : Finset ℝ) :
    |productIntegral A a b - partitionProd A a b s| ≤
      productIntegral V a b - partitionProd V a b s := by
  refine le_of_tendsto_of_tendsto (((tendsto_partitionProd hab hc).sub_const _).abs)
    ((tendsto_partitionProd hab hc.self).sub_const _) (eventually_atTop.2 ⟨s, fun t ht => ?_⟩)
  exact abs_partitionProd_sub_le_of_subset hab hc ht

/-- **One-cell estimate**: `∏_{(a,b]} (1 + dA)` is `1 + (A b - A a)` up to the second-order
error `∏_{(a,b]} (1 + dV) - (1 + (V b - V a))` of the control. -/
theorem abs_productIntegral_sub_one_add_le (hab : a ≤ b) (hc : IsControl A V a b) :
    |productIntegral A a b - (1 + (A b - A a))| ≤ productIntegral V a b - (1 + (V b - V a)) := by
  have := abs_productIntegral_sub_partitionProd_le hab hc ∅
  rwa [partitionProd_empty A hab, partitionProd_empty V hab] at this

/-- The product integral of a control is at least `1 + (V b - V a)`. -/
theorem one_add_sub_le_productIntegral_of_control (hab : a ≤ b) (hc : IsControl A V a b) :
    1 + (V b - V a) ≤ productIntegral V a b :=
  sub_nonneg.1 ((abs_nonneg _).trans (abs_productIntegral_sub_one_add_le hab hc.self))

/-- For a monotone integrator, `1 + (A b - A a) ≤ ∏_{(a,b]} (1 + dA)`. -/
theorem one_add_sub_le_productIntegral (hab : a ≤ b) (h : MonotoneOn A (Set.Icc a b)) :
    1 + (A b - A a) ≤ productIntegral A a b :=
  one_add_sub_le_productIntegral_of_control hab (isControl_self_of_monotoneOn h)

/-- The product integral of a control is at most `exp (V b - V a)`. -/
theorem productIntegral_le_exp (hab : a ≤ b) (hc : IsControl A V a b) :
    productIntegral V a b ≤ Real.exp (V b - V a) :=
  le_of_tendsto (tendsto_partitionProd hab hc.self)
    (Eventually.of_forall fun s => partitionProd_le_exp hab hc s)

/-- **Domination**: `|∏_{(a,b]} (1 + dA)| ≤ ∏_{(a,b]} (1 + dV)` for a control `V`. -/
theorem abs_productIntegral_le (hab : a ≤ b) (hc : IsControl A V a b) :
    |productIntegral A a b| ≤ productIntegral V a b :=
  le_of_tendsto_of_tendsto (tendsto_partitionProd hab hc).abs (tendsto_partitionProd hab hc.self)
    (Eventually.of_forall fun _ =>
      abs_gridProd_le hc fun _ hx => mem_Icc_of_mem_partitionPts hab hx)

/-- **Exponential bound**: `|∏_{(a,b]} (1 + dA)| ≤ exp (V b - V a)` for a control `V`. -/
theorem abs_productIntegral_le_exp (hab : a ≤ b) (hc : IsControl A V a b) :
    |productIntegral A a b| ≤ Real.exp (V b - V a) :=
  (abs_productIntegral_le hab hc).trans (productIntegral_le_exp hab hc)

end Existence

/-! ### Elementary product integrals -/

section Elementary

variable {a b : ℝ}

/-- **Congruence**: the product integral over `[a, b]` only depends on the values of the
integrator on `[a, b]`. -/
theorem productIntegral_congr {A B : ℝ → ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, A x = B x) : productIntegral A a b = productIntegral B a b := by
  have hpp : partitionProd A a b = partitionProd B a b := by
    funext s
    refine prod_congr rfl fun x hx => ?_
    have hxI := mem_Icc_of_mem_partitionPts hab hx
    have huI := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
    rw [h x hxI, h _ huI]
  rw [productIntegral, productIntegral, hpp]

/-- If the partition products are eventually equal to `c`, the product integral is `c`. -/
theorem productIntegral_eq_of_eventually {A : ℝ → ℝ} {c : ℝ}
    (h : ∀ᶠ s in atTop, partitionProd A a b s = c) : productIntegral A a b = c :=
  (tendsto_const_nhds.congr' (h.mono fun _ hs => hs.symm)).limUnder_eq

/-- The product integral over a degenerate interval is `1`. -/
@[simp]
theorem productIntegral_self (A : ℝ → ℝ) (a : ℝ) : productIntegral A a a = 1 := by
  refine productIntegral_eq_of_eventually (Eventually.of_forall fun s => ?_)
  have hP : partitionPts a a s = {a, a} := by
    ext x
    simp only [mem_partitionPts, mem_insert, mem_singleton]
    constructor
    · rintro (h | h | ⟨-, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inl h
      · exact absurd (h1.trans h2) (lt_irrefl a)
    · rintro (h | h) <;> exact Or.inl h
  rw [partitionProd, hP, gridProd_pair A le_rfl, sub_self, add_zero]

/-- The product integral of a constant integrator is `1`. -/
@[simp]
theorem productIntegral_const (c a b : ℝ) : productIntegral (fun _ => c) a b = 1 :=
  productIntegral_eq_of_eventually (Eventually.of_forall fun _ => by
    simp [partitionProd, gridProd])

/-- The grid product of a step function with a single jump at a point `c` of `P` that is not
the minimum of `P` is `1 + (y₁ - y₀)`. -/
theorem gridProd_step {P : Finset ℝ} {c y₀ y₁ : ℝ} (hc : c ∈ P) (hlow : ∃ y ∈ P, y < c) :
    gridProd (fun t => if c ≤ t then y₁ else y₀) P = 1 + (y₁ - y₀) := by
  rw [gridProd, prod_eq_single c]
  · obtain ⟨-, h2, -⟩ := prev_spec hlow
    simp [not_le.2 h2]
  · intro x hx hxc
    rcases lt_or_gt_of_ne hxc with hlt | hgt
    · have := (prev_le P x).trans_lt hlt
      simp [not_le.2 hlt, not_le.2 this]
    · obtain ⟨-, -, h3⟩ := prev_spec ⟨c, hc, hgt⟩
      simp [hgt.le, h3 c hc hgt]
  · intro h; exact absurd hc h

/-- **Product integral of a step integrator**: a single jump of size `y₁ - y₀` at
`c ∈ (a, b]` gives `∏_{(a,b]} (1 + dA) = 1 + (y₁ - y₀)`. -/
theorem productIntegral_step {c y₀ y₁ : ℝ} (hac : a < c) (hcb : c ≤ b) :
    productIntegral (fun t => if c ≤ t then y₁ else y₀) a b = 1 + (y₁ - y₀) := by
  refine productIntegral_eq_of_eventually (eventually_atTop.2 ⟨{c}, fun s hs => ?_⟩)
  have hcP : c ∈ partitionPts a b s := by
    rcases eq_or_lt_of_le hcb with rfl | hlt
    · exact right_mem_partitionPts s
    · exact mem_partitionPts.2 (Or.inr (Or.inr ⟨hs (mem_singleton_self c), hac, hlt⟩))
  exact gridProd_step hcP ⟨a, left_mem_partitionPts s, hac⟩

end Elementary


/-! ### Multiplicativity -/

section Multiplicativity

variable {A V : ℝ → ℝ} {a b c : ℝ}

/-- Grid products are multiplicative over two finite sets meeting at a common point `c`
with `P ≤ c ≤ Q`. -/
theorem gridProd_union (A : ℝ → ℝ) {P Q : Finset ℝ} (hcP : c ∈ P) (hcQ : c ∈ Q)
    (hP : ∀ x ∈ P, x ≤ c) (hQ : ∀ y ∈ Q, c ≤ y) :
    gridProd A (P ∪ Q) = gridProd A P * gridProd A Q := by
  have hU : P ∪ Q = P ∪ Q.erase c := by
    ext x
    simp only [mem_union, mem_erase]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hx : x = c
        · exact Or.inl (hx ▸ hcP)
        · exact Or.inr ⟨hx, h⟩
    · rintro (h | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h
  have hdisj : Disjoint P (Q.erase c) := by
    rw [disjoint_left]
    intro x hxP hxQ
    have h1 := hP x hxP
    have h2 := hQ x (mem_of_mem_erase hxQ)
    exact ne_of_mem_erase hxQ (le_antisymm h1 h2)
  have hprevP : ∀ x ∈ P, prev (P ∪ Q) x = prev P x := by
    intro x hx
    have hnoQ : ∀ z ∈ Q, ¬z < x := fun z hz hzx =>
      absurd ((hQ z hz).trans_lt hzx) (not_lt.2 (hP x hx))
    by_cases h : ∃ z ∈ P, z < x
    · obtain ⟨h1, h2, h3⟩ := prev_spec h
      refine prev_eq_of (mem_union_left _ h1) h2 fun z hz hzx => ?_
      rcases mem_union.1 hz with hz | hz
      · exact h3 z hz hzx
      · exact absurd hzx (hnoQ z hz)
    · rw [prev_eq_self h]
      refine prev_eq_self ?_
      rintro ⟨z, hz, hzx⟩
      rcases mem_union.1 hz with hz | hz
      · exact h ⟨z, hz, hzx⟩
      · exact hnoQ z hz hzx
  have hprevQ : ∀ x ∈ Q.erase c, prev (P ∪ Q) x = prev Q x := by
    intro x hx
    have hcx : c < x := lt_of_le_of_ne (hQ x (mem_of_mem_erase hx)) (ne_of_mem_erase hx).symm
    obtain ⟨h1, h2, h3⟩ := prev_spec ⟨c, hcQ, hcx⟩
    refine prev_eq_of (mem_union_right _ h1) h2 fun z hz hzx => ?_
    rcases mem_union.1 hz with hz | hz
    · exact (hP z hz).trans (h3 c hcQ hcx)
    · exact h3 z hz hzx
  have hQc : prev Q c = c := prev_eq_self fun ⟨z, hz, hzc⟩ => absurd (hQ z hz) (not_le.2 hzc)
  rw [gridProd, hU, prod_union hdisj, ← hU, gridProd, gridProd, ← mul_prod_erase Q _ hcQ, hQc,
    sub_self, add_zero, one_mul]
  congr 1
  · exact prod_congr rfl fun x hx => by rw [hprevP x hx]
  · exact prod_congr rfl fun x hx => by rw [hprevQ x hx]

theorem partitionPts_insert_split (hac : a ≤ c) (hcb : c ≤ b) (s : Finset ℝ) :
    partitionPts a b (insert c s) =
      partitionPts a c (insert c s) ∪ partitionPts c b (insert c s) := by
  ext x
  simp only [mem_union, mem_partitionPts, mem_insert]
  constructor
  · rintro (h | h | ⟨h, h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases lt_trichotomy x c with hxc | rfl | hxc
      · exact Or.inl (Or.inr (Or.inr ⟨h, h1, hxc⟩))
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hxc, h2⟩))
  · rintro ((h | rfl | ⟨h, h1, h2⟩) | (rfl | h | ⟨h, h1, h2⟩))
    · exact Or.inl h
    · rcases eq_or_lt_of_le hac with rfl | hac'
      · exact Or.inl rfl
      rcases eq_or_lt_of_le hcb with rfl | hcb'
      · exact Or.inr (Or.inl rfl)
      exact Or.inr (Or.inr ⟨Or.inl rfl, hac', hcb'⟩)
    · exact Or.inr (Or.inr ⟨h, h1, h2.trans_le hcb⟩)
    · rcases eq_or_lt_of_le hac with rfl | hac'
      · exact Or.inl rfl
      rcases eq_or_lt_of_le hcb with rfl | hcb'
      · exact Or.inr (Or.inl rfl)
      exact Or.inr (Or.inr ⟨Or.inl rfl, hac', hcb'⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hac.trans_lt h1, h2⟩)

/-- **Multiplicativity** of the product integral over adjacent intervals:
`∏_{(a,b]} (1 + dA) = ∏_{(a,c]} (1 + dA) · ∏_{(c,b]} (1 + dA)` for `a ≤ c ≤ b`. -/
theorem productIntegral_mul (hac : a ≤ c) (hcb : c ≤ b) (hc : IsControl A V a b) :
    productIntegral A a b = productIntegral A a c * productIntegral A c b := by
  have hg : Tendsto (fun s : Finset ℝ => insert c s) atTop atTop :=
    tendsto_atTop_atTop.2 fun t => ⟨t, fun s hs => hs.trans (subset_insert c s)⟩
  have h1 := (tendsto_partitionProd (hac.trans hcb) hc).comp hg
  have h2 := ((tendsto_partitionProd hac (hc.mono le_rfl hcb)).mul
    (tendsto_partitionProd hcb (hc.mono hac le_rfl))).comp hg
  refine tendsto_nhds_unique h1 (h2.congr fun s => ?_)
  simp only [Function.comp, partitionProd]
  rw [partitionPts_insert_split hac hcb s]
  refine (gridProd_union A (c := c) (right_mem_partitionPts _) (left_mem_partitionPts _)
    (fun x hx => (mem_Icc_of_mem_partitionPts hac hx).2)
    (fun x hx => (mem_Icc_of_mem_partitionPts hcb hx).1)).symm

/-- The product integral of a control over consecutive cells of a partition multiplies out to
the product integral over the whole interval. -/
theorem prod_productIntegral_cells (hab : a ≤ b) (hc : IsControl A V a b) (s : Finset ℝ) :
    ∏ x ∈ partitionPts a b s,
      productIntegral A (prev (partitionPts a b s) x) x = productIntegral A a b :=
  prod_cells_partitionPts hab (productIntegral A) (productIntegral_self A a)
    (fun _ _ _ hu hup hpv hv =>
      (productIntegral_mul hup.le hpv.le (hc.mono hu hv)).symm) s

end Multiplicativity


/-! ### The Duhamel identity -/

/-- For numbers `1 ≤ Y i ≤ X i`, the sum of the differences is at most the difference of the
products. -/
theorem sum_sub_le_prod_sub {ι : Type*} (S : Finset ι) (X Y : ι → ℝ)
    (hY : ∀ i ∈ S, 1 ≤ Y i) (hXY : ∀ i ∈ S, Y i ≤ X i) :
    ∑ i ∈ S, (X i - Y i) ≤ ∏ i ∈ S, X i - ∏ i ∈ S, Y i := by
  classical
  have key : 1 ≤ ∏ i ∈ S, Y i ∧ ∏ i ∈ S, Y i ≤ ∏ i ∈ S, X i ∧
      ∑ i ∈ S, (X i - Y i) ≤ ∏ i ∈ S, X i - ∏ i ∈ S, Y i := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hY i (mem_insert_of_mem hi))
        (fun i hi => hXY i (mem_insert_of_mem hi))
      have hYj := hY j (mem_insert_self j S)
      have hXYj := hXY j (mem_insert_self j S)
      rw [prod_insert hj, prod_insert hj, sum_insert hj]
      refine ⟨one_le_mul_of_one_le_of_one_le hYj h1, ?_, ?_⟩
      · exact mul_le_mul hXYj h2 (by linarith) (by linarith)
      · nlinarith [mul_nonneg (sub_nonneg.2 hXYj) (show 0 ≤ ∏ i ∈ S, X i - 1 by linarith),
          mul_nonneg (show 0 ≤ Y j - 1 by linarith) (sub_nonneg.2 h2)]
  exact key.2.2

/-- The **Duhamel sum** of the integrators `A` and `B` over the partition generated by `s`:
the Riemann–Stieltjes sum
`∑ᵢ ∏_{(a,tᵢ₋₁]} (1 + dA) · (ΔBᵢ - ΔAᵢ) · ∏_{(tᵢ,b]} (1 + dB)`
for the Duhamel integral `∫_{(a,b]} ∏_{(a,u)} (1 + dA) d(B - A)(u) ∏_{(u,b]} (1 + dB)`. -/
noncomputable def duhamelSum (A B : ℝ → ℝ) (a b : ℝ) (s : Finset ℝ) : ℝ :=
  ∑ x ∈ partitionPts a b s,
    productIntegral A a (prev (partitionPts a b s) x) *
      ((B x - B (prev (partitionPts a b s) x)) - (A x - A (prev (partitionPts a b s) x))) *
      productIntegral B x b

section Duhamel

variable {A B V W : ℝ → ℝ} {a b : ℝ}

/-- **Exact Duhamel identity** on an arbitrary partition `a = t₀ < ⋯ < tₙ = b`:
`∏_{(a,b]} (1 + dB) - ∏_{(a,b]} (1 + dA) =
  ∑ᵢ ∏_{(a,tᵢ₋₁]} (1 + dA) · (∏_{(tᵢ₋₁,tᵢ]} (1 + dB) - ∏_{(tᵢ₋₁,tᵢ]} (1 + dA)) ·
    ∏_{(tᵢ,b]} (1 + dB)`. -/
theorem productIntegral_sub_eq_sum (hab : a ≤ b) (hA : IsControl A V a b)
    (hB : IsControl B W a b) (s : Finset ℝ) :
    productIntegral B a b - productIntegral A a b =
      ∑ x ∈ partitionPts a b s,
        productIntegral A a (prev (partitionPts a b s) x) *
          (productIntegral B (prev (partitionPts a b s) x) x -
            productIntegral A (prev (partitionPts a b s) x) x) *
          productIntegral B x b := by
  set G : ℝ → ℝ := fun t => productIntegral A a t * productIntegral B t b
  have htel := sum_cells_partitionPts hab (fun u x => G u - G x) (sub_self _)
    (fun _ _ _ _ _ _ _ => by ring) s
  have hGa : G a - G b = productIntegral B a b - productIntegral A a b := by
    simp [G]
  rw [← hGa, ← htel]
  refine sum_congr rfl fun x hx => ?_
  set P := partitionPts a b s
  have hxI := mem_Icc_of_mem_partitionPts hab hx
  have huI := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
  have hux := prev_le P x
  have e1 : productIntegral B (prev P x) b =
      productIntegral B (prev P x) x * productIntegral B x b :=
    productIntegral_mul hux hxI.2 (hB.mono huI.1 le_rfl)
  have e2 : productIntegral A a x =
      productIntegral A a (prev P x) * productIntegral A (prev P x) x :=
    productIntegral_mul huI.1 hux (hA.mono le_rfl hxI.2)
  simp only [G, e1, e2]
  ring

/-- The cellwise second-order errors of a control sum to at most the error of the partition
product: `∑ᵢ (∏_{(tᵢ₋₁,tᵢ]} (1 + dV) - (1 + ΔVᵢ)) ≤ ∏_{(a,b]} (1 + dV) - ∏ᵢ (1 + ΔVᵢ)`. -/
theorem sum_cell_errors_le (hab : a ≤ b) (hc : IsControl A V a b) (s : Finset ℝ) :
    ∑ x ∈ partitionPts a b s, (productIntegral V (prev (partitionPts a b s) x) x -
        (1 + (V x - V (prev (partitionPts a b s) x)))) ≤
      productIntegral V a b - partitionProd V a b s := by
  set P := partitionPts a b s
  rw [← prod_productIntegral_cells hab hc.self s]
  refine sum_sub_le_prod_sub P _ _ (fun x hx => ?_) fun x hx => ?_
  · have := hc.sub_nonneg (mem_Icc_of_mem_partitionPts hab (prev_mem hx)).1 (prev_le P x)
      (mem_Icc_of_mem_partitionPts hab hx).2
    linarith
  · exact one_add_sub_le_productIntegral_of_control (prev_le P x)
      (hc.mono (mem_Icc_of_mem_partitionPts hab (prev_mem hx)).1
        (mem_Icc_of_mem_partitionPts hab hx).2)

/-- The cellwise first-order errors of the product integral of `A` are dominated by the
second-order errors of the control. -/
theorem sum_abs_cell_errors_le (hab : a ≤ b) (hc : IsControl A V a b) (s : Finset ℝ) :
    ∑ x ∈ partitionPts a b s, |productIntegral A (prev (partitionPts a b s) x) x -
        (1 + (A x - A (prev (partitionPts a b s) x)))| ≤
      productIntegral V a b - partitionProd V a b s := by
  refine (sum_le_sum fun x hx => ?_).trans (sum_cell_errors_le hab hc s)
  exact abs_productIntegral_sub_one_add_le (prev_le _ x)
    (hc.mono (mem_Icc_of_mem_partitionPts hab (prev_mem hx)).1
      (mem_Icc_of_mem_partitionPts hab hx).2)

/-- **Duhamel identity**, Riemann–Stieltjes form. For integrators `A`, `B` with monotone
controls on `[a, b]`, the Duhamel sums converge along refinement to
`∏_{(a,b]} (1 + dB) - ∏_{(a,b]} (1 + dA)`; that is,
`∏(1 + dB) - ∏(1 + dA) = ∫_{(a,b]} ∏_{(a,u)} (1 + dA) d(B - A)(u) ∏_{(u,b]} (1 + dB)`. -/
theorem tendsto_duhamelSum (hab : a ≤ b) (hA : IsControl A V a b) (hB : IsControl B W a b) :
    Tendsto (duhamelSum A B a b) atTop
      (𝓝 (productIntegral B a b - productIntegral A a b)) := by
  set KA := Real.exp (V b - V a)
  set KB := Real.exp (W b - W a)
  -- the error between the exact identity and the Duhamel sum
  set E : Finset ℝ → ℝ := fun s => ∑ x ∈ partitionPts a b s,
    productIntegral A a (prev (partitionPts a b s) x) *
      ((productIntegral B (prev (partitionPts a b s) x) x -
          (1 + (B x - B (prev (partitionPts a b s) x)))) -
        (productIntegral A (prev (partitionPts a b s) x) x -
          (1 + (A x - A (prev (partitionPts a b s) x))))) *
      productIntegral B x b with hEdef
  have hsplit : ∀ s, duhamelSum A B a b s =
      (productIntegral B a b - productIntegral A a b) - E s := by
    intro s
    rw [productIntegral_sub_eq_sum hab hA hB s, duhamelSum, hEdef, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    ring
  have hbound : ∀ s, ‖E s‖ ≤ KA * KB * ((productIntegral W a b - partitionProd W a b s) +
      (productIntegral V a b - partitionProd V a b s)) := by
    intro s
    set P := partitionPts a b s
    rw [Real.norm_eq_abs, hEdef]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ x ∈ P, |productIntegral A a (prev P x) *
        ((productIntegral B (prev P x) x - (1 + (B x - B (prev P x)))) -
          (productIntegral A (prev P x) x - (1 + (A x - A (prev P x))))) *
        productIntegral B x b| ≤
        KA * KB * (|productIntegral B (prev P x) x - (1 + (B x - B (prev P x)))| +
          |productIntegral A (prev P x) x - (1 + (A x - A (prev P x)))|) := by
      intro x hx
      have hxI := mem_Icc_of_mem_partitionPts hab hx
      have huI := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
      have h1 : |productIntegral A a (prev P x)| ≤ KA :=
        (abs_productIntegral_le_exp huI.1 (hA.mono le_rfl huI.2)).trans
          (Real.exp_le_exp.2 (by linarith [hA.sub_nonneg huI.1 huI.2 le_rfl]))
      have h2 : |productIntegral B x b| ≤ KB :=
        (abs_productIntegral_le_exp hxI.2 (hB.mono hxI.1 le_rfl)).trans
          (Real.exp_le_exp.2 (by linarith [hB.sub_nonneg le_rfl hxI.1 hxI.2]))
      rw [abs_mul, abs_mul]
      calc |productIntegral A a (prev P x)| * |(productIntegral B (prev P x) x -
            (1 + (B x - B (prev P x)))) -
              (productIntegral A (prev P x) x - (1 + (A x - A (prev P x))))| *
            |productIntegral B x b|
          ≤ KA * (|productIntegral B (prev P x) x - (1 + (B x - B (prev P x)))| +
              |productIntegral A (prev P x) x - (1 + (A x - A (prev P x)))|) * KB :=
            mul_le_mul (mul_le_mul h1 (abs_sub _ _) (abs_nonneg _) (Real.exp_pos _).le) h2
              (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le
                (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        _ = KA * KB * (|productIntegral B (prev P x) x - (1 + (B x - B (prev P x)))| +
              |productIntegral A (prev P x) x - (1 + (A x - A (prev P x)))|) := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum, sum_add_distrib]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (sum_abs_cell_errors_le hab hB s) (sum_abs_cell_errors_le hab hA s))
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hlimW : Tendsto (fun s => productIntegral W a b - partitionProd W a b s) atTop (𝓝 0) := by
    simpa using (tendsto_partitionProd hab hB.self).const_sub (productIntegral W a b)
  have hlimV : Tendsto (fun s => productIntegral V a b - partitionProd V a b s) atTop (𝓝 0) := by
    simpa using (tendsto_partitionProd hab hA.self).const_sub (productIntegral V a b)
  have hE : Tendsto E atTop (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa using (hlimW.add hlimV).const_mul (KA * KB))
  have := hE.const_sub (productIntegral B a b - productIntegral A a b)
  rw [sub_zero] at this
  exact this.congr fun s => (hsplit s).symm

/-- The zero function is controlled by the zero function. -/
theorem isControl_zero : IsControl (fun _ => 0) (fun _ => 0) a b := fun _ _ _ _ _ => by simp

/-- **Forward Volterra equation**: `∏_{(a,b]} (1 + dA) = 1 + ∫_{(a,b]} ∏_{(a,u)} (1 + dA) dA(u)`,
as the limit of the left-tagged Riemann–Stieltjes sums. -/
theorem tendsto_volterra_forward (hab : a ≤ b) (hA : IsControl A V a b) :
    Tendsto (fun s => ∑ x ∈ partitionPts a b s,
        productIntegral A a (prev (partitionPts a b s) x) *
          (A x - A (prev (partitionPts a b s) x))) atTop
      (𝓝 (productIntegral A a b - 1)) := by
  have h := (tendsto_duhamelSum hab hA (isControl_zero (a := a) (b := b))).neg
  rw [productIntegral_const, neg_sub] at h
  refine h.congr fun s => ?_
  rw [duhamelSum, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [productIntegral_const]
  ring

/-- **Backward Volterra equation**: `∏_{(a,b]} (1 + dB) = 1 + ∫_{(a,b]} dB(u) ∏_{(u,b]} (1 + dB)`,
as the limit of the right-tagged Riemann–Stieltjes sums. -/
theorem tendsto_volterra_backward (hab : a ≤ b) (hB : IsControl B W a b) :
    Tendsto (fun s => ∑ x ∈ partitionPts a b s,
        (B x - B (prev (partitionPts a b s) x)) * productIntegral B x b) atTop
      (𝓝 (productIntegral B a b - 1)) := by
  have h := tendsto_duhamelSum hab (isControl_zero (a := a) (b := b)) hB
  rw [productIntegral_const] at h
  refine h.congr fun s => ?_
  rw [duhamelSum]
  refine sum_congr rfl fun x _ => ?_
  rw [productIntegral_const]
  ring

end Duhamel

end MathlibExt.Analysis.StieltjesProductIntegral
