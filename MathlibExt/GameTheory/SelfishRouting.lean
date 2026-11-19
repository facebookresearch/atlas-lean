/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Selfish routing: Wardrop equilibria and the price of anarchy

A *nonatomic routing instance* has a finite set `E` of edges, a finite set `ι` of
commodities, a finite set `P` of paths, each path `p` belonging to the commodity
`commodity p` and using the edge set `edges p`, and a latency function
`latency e : ℝ → ℝ` for every edge. A flow `f : P → ℝ` routes `f p` units of
traffic on path `p`; it is feasible for the demand vector `r : ι → ℝ` when it is
nonnegative and routes exactly `r i` units for every commodity `i`. The flow on
an edge is the total flow of the paths through it, the latency of a path is the
sum of the latencies of its edges, and the cost of a flow is its total latency
`∑ e, ℓₑ(fₑ) fₑ`.

A flow is a *Wardrop equilibrium* (a flow at Nash equilibrium) when every path
carrying flow has minimum latency among the paths of its commodity. Roughgarden
and Tardos define equilibria through infinitesimal deviations (Definition 2.1) and
show that, for continuous nondecreasing latencies, this is equivalent to the
condition used here (Lemma 2.2); we take the condition as the definition.

Modelling a path as an abstract edge set covers routing in a directed graph with
the simple `sᵢ`–`tᵢ` paths as `P`, and more generally the nonatomic congestion
games of Roughgarden and Tardos (2004), for which all results below hold.

## Main results

* `IsWardrop.smul_sum_pathLatency_mul_le`: if `f` is a Wardrop flow for `r` and `g`
  is feasible for `c • r`, then `c ∑ₚ ℓₚ(f) fₚ ≤ ∑ₚ ℓₚ(f) gₚ`
  (the cost of `f` is `∑ᵢ Lᵢ rᵢ`, Lemma 2.3, and every path has latency at least `Lᵢ`).
* `IsWardrop.cost_le_sum_latency_mul_edgeFlow`: the variational inequality
  `C(f) ≤ ∑ₑ ℓₑ(fₑ) gₑ` against every feasible flow `g` for the same demand.
* `IsWardrop.cost_eq`, `IsWardrop.latency_edgeFlow_eq`: for latencies nondecreasing on `[0, ∞)`
  any two Wardrop flows for the same demand have the same edge latencies and the
  same cost (Beckmann, McGuire and Winsten 1956).
* `IsWardrop.cost_le_of_affine`: for affine latencies `aₑ x + bₑ` with
  `aₑ, bₑ ≥ 0` the price of anarchy is at most `4/3` (Roughgarden–Tardos,
  Theorem 4.5); `pigou_*` shows that `4/3` is attained.
* `IsWardrop.mul_cost_le_of_feasible_one_add`, `IsWardrop.cost_le_of_feasible_two`:
  for nonnegative nondecreasing latencies a Wardrop flow costs at most `1/γ` times
  any flow feasible for the demand `(1 + γ) r`, in particular at most any flow routing
  twice the traffic (Roughgarden–Tardos, Theorems 3.2 and 3.1).
* `braess_paradox`: in Braess's network every Wardrop flow costs `3/2` before and `2` after a
  zero-latency link is added (Roughgarden–Tardos, Figure 1).

## References

* T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002),
  236–259: Definition 2.1, Lemmas 2.2–2.3, Theorems 3.1, 3.2 and 4.5.
* T. Roughgarden and É. Tardos, "Bounding the inefficiency of equilibria in
  nonatomic congestion games", Games Econom. Behav. 47 (2004), 389–403.
* M. Beckmann, C. B. McGuire and C. B. Winsten, *Studies in the Economics of
  Transportation*, Yale University Press, 1956.
* D. Braess, "Über ein Paradoxon aus der Verkehrsplanung", Unternehmensforschung 12 (1968),
  258–268.
* J. G. Wardrop, "Some theoretical aspects of road traffic research",
  Proc. Inst. Civil Engineers 1 (1952), 325–378.
-/

namespace MathlibExt.GameTheory.SelfishRouting

open Finset

/-- A nonatomic routing instance with edges `E`, commodities `ι` and paths `P`:
each path belongs to a commodity and uses a finite set of edges, and each edge has
a latency function of its load (Roughgarden–Tardos 2002, §2.1). -/
structure RoutingInstance (E ι P : Type*) where
  /-- The commodity (source–destination pair) served by a path. -/
  commodity : P → ι
  /-- The edges used by a path. -/
  edges : P → Finset E
  /-- The latency of an edge as a function of the flow on it. -/
  latency : E → ℝ → ℝ

namespace RoutingInstance

variable {E ι P : Type*} [Fintype E] [Fintype P] [DecidableEq E] [DecidableEq ι]
variable (N : RoutingInstance E ι P)

/-- The path flow `f` is feasible for the demand `r`: it is nonnegative and routes
exactly `r i` units of commodity `i`. -/
def IsFeasible (r : ι → ℝ) (f : P → ℝ) : Prop :=
  (∀ p, 0 ≤ f p) ∧ ∀ i, ∑ p with N.commodity p = i, f p = r i

/-- The flow on edge `e`: the total flow of the paths using `e`. -/
def edgeFlow (f : P → ℝ) (e : E) : ℝ :=
  ∑ p with e ∈ N.edges p, f p

/-- The latency of path `p` under the flow `f`: the sum of the latencies of its edges. -/
def pathLatency (f : P → ℝ) (p : P) : ℝ :=
  ∑ e ∈ N.edges p, N.latency e (N.edgeFlow f e)

/-- The cost (total latency) `∑ₑ ℓₑ(fₑ) fₑ` of the flow `f`. -/
def cost (f : P → ℝ) : ℝ :=
  ∑ e, N.latency e (N.edgeFlow f e) * N.edgeFlow f e

/-- Wardrop's principle: every path carrying flow has minimum latency among the paths
of its commodity. This is the characterisation of flows at Nash equilibrium in
Roughgarden–Tardos 2002, Lemma 2.2. -/
def IsWardrop (f : P → ℝ) : Prop :=
  ∀ p q, N.commodity p = N.commodity q → 0 < f p → N.pathLatency f p ≤ N.pathLatency f q

variable {N}

omit [Fintype E] [DecidableEq ι] in
/-- A nonnegative path flow has nonnegative edge flows. -/
theorem edgeFlow_nonneg {f : P → ℝ} (hf : ∀ p, 0 ≤ f p) (e : E) : 0 ≤ N.edgeFlow f e :=
  sum_nonneg fun p _ => hf p

omit [DecidableEq ι] in
/-- Exchanging the order of summation: weighting path latencies under `f` by a second
flow `g` gives the sum over edges of `ℓₑ(fₑ) gₑ`. -/
theorem sum_pathLatency_mul (f g : P → ℝ) :
    ∑ p, N.pathLatency f p * g p = ∑ e, N.latency e (N.edgeFlow f e) * N.edgeFlow g e := by
  unfold pathLatency
  simp_rw [sum_mul]
  rw [sum_comm' (t' := univ) (s' := fun e => univ.filter fun p => e ∈ N.edges p)
    (fun p e => by simp)]
  simp_rw [edgeFlow, mul_sum]

omit [DecidableEq ι] in
/-- The cost of a flow is the flow-weighted sum of its path latencies. -/
theorem cost_eq_sum_pathLatency_mul (f : P → ℝ) :
    N.cost f = ∑ p, N.pathLatency f p * f p :=
  (N.sum_pathLatency_mul f f).symm

omit [Fintype E] in
/-- The key inequality behind Roughgarden–Tardos, Lemma 2.3 and Theorem 3.1: if `f` is a
Wardrop flow for `r` and `g` is feasible for `c • r`, then
`c ∑ₚ ℓₚ(f) fₚ ≤ ∑ₚ ℓₚ(f) gₚ`. Each commodity `i` has a common latency `Lᵢ` on its flow
paths, the left side is `c ∑ᵢ Lᵢ rᵢ`, and every path of `i` has latency at least `Lᵢ`. -/
theorem IsWardrop.smul_sum_pathLatency_mul_le [Finite ι] {f g : P → ℝ} {r : ι → ℝ}
    {c : ℝ} (hW : N.IsWardrop f) (hf : N.IsFeasible r f) (hg : N.IsFeasible (c • r) g) :
    c * ∑ p, N.pathLatency f p * f p ≤ ∑ p, N.pathLatency f p * g p := by
  cases nonempty_fintype ι
  rw [← sum_fiberwise univ N.commodity (fun p => N.pathLatency f p * f p),
    ← sum_fiberwise univ N.commodity (fun p => N.pathLatency f p * g p), mul_sum]
  refine sum_le_sum fun i _ => ?_
  by_cases h : ∃ p₀, N.commodity p₀ = i ∧ 0 < f p₀
  · obtain ⟨p₀, hp₀, hpos⟩ := h
    set L := N.pathLatency f p₀
    have hflow : ∀ p ∈ univ.filter (fun p => N.commodity p = i),
        N.pathLatency f p * f p = L * f p := by
      intro p hp
      rw [mem_filter] at hp
      rcases (hf.1 p).lt_or_eq with hfp | hfp
      · have h1 := hW p p₀ (hp.2.trans hp₀.symm) hfp
        have h2 := hW p₀ p (hp₀.trans hp.2.symm) hpos
        rw [le_antisymm h1 h2]
      · rw [← hfp]; ring
    have hlow : ∀ p ∈ univ.filter (fun p => N.commodity p = i),
        L * g p ≤ N.pathLatency f p * g p := by
      intro p hp
      rw [mem_filter] at hp
      exact mul_le_mul_of_nonneg_right (hW p₀ p (hp₀.trans hp.2.symm) hpos) (hg.1 p)
    rw [sum_congr rfl hflow, ← mul_sum, hf.2 i]
    calc c * (L * r i) = L * ∑ p with N.commodity p = i, g p := by
          rw [hg.2 i]; simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = ∑ p with N.commodity p = i, L * g p := mul_sum _ _ _
      _ ≤ _ := sum_le_sum hlow
  · push Not at h
    have hf0 : ∀ p ∈ univ.filter (fun p => N.commodity p = i), f p = 0 := by
      intro p hp
      rw [mem_filter] at hp
      exact le_antisymm (h p hp.2) (hf.1 p)
    have hr : r i = 0 := by rw [← hf.2 i, sum_eq_zero hf0]
    have hg0 : ∀ p ∈ univ.filter (fun p => N.commodity p = i), g p = 0 := by
      have hsum : ∑ p with N.commodity p = i, g p = 0 := by
        rw [hg.2 i]; simp [hr]
      exact (sum_eq_zero_iff_of_nonneg fun p _ => hg.1 p).1 hsum
    rw [sum_eq_zero fun p hp => by rw [hf0 p hp, mul_zero],
      sum_eq_zero fun p hp => by rw [hg0 p hp, mul_zero], mul_zero]

/-- The variational inequality of a Wardrop flow: its cost is at most `∑ₑ ℓₑ(fₑ) gₑ` for
every flow `g` feasible for the same demand (the case `c = 1` of
`IsWardrop.smul_sum_pathLatency_mul_le`). -/
theorem IsWardrop.cost_le_sum_latency_mul_edgeFlow [Finite ι] {f g : P → ℝ} {r : ι → ℝ}
    (hW : N.IsWardrop f) (hf : N.IsFeasible r f) (hg : N.IsFeasible r g) :
    N.cost f ≤ ∑ e, N.latency e (N.edgeFlow f e) * N.edgeFlow g e := by
  have := hW.smul_sum_pathLatency_mul_le hf (c := 1) (by simpa using hg)
  rw [one_mul] at this
  rw [cost_eq_sum_pathLatency_mul, ← sum_pathLatency_mul]
  exact this

omit [Fintype E] in
/-- Essential uniqueness of Wardrop equilibria (Beckmann, McGuire and Winsten 1956): for
latencies nondecreasing on `[0, ∞)`, two Wardrop flows for the same demand induce the same
latency on every edge. -/
theorem IsWardrop.latency_edgeFlow_eq [Finite ι] [Finite E] {f g : P → ℝ} {r : ι → ℝ}
    (hmono : ∀ e, MonotoneOn (N.latency e) (Set.Ici 0)) (hWf : N.IsWardrop f)
    (hf : N.IsFeasible r f)
    (hWg : N.IsWardrop g) (hg : N.IsFeasible r g) (e : E) :
    N.latency e (N.edgeFlow f e) = N.latency e (N.edgeFlow g e) := by
  cases nonempty_fintype E
  set ℓf := fun e => N.latency e (N.edgeFlow f e)
  set ℓg := fun e => N.latency e (N.edgeFlow g e)
  have h1 := hWf.cost_le_sum_latency_mul_edgeFlow hf hg
  have h2 := hWg.cost_le_sum_latency_mul_edgeFlow hg hf
  have hterm : ∀ e, 0 ≤ (ℓf e - ℓg e) * (N.edgeFlow f e - N.edgeFlow g e) := by
    intro e
    have hfe : N.edgeFlow f e ∈ Set.Ici (0 : ℝ) := edgeFlow_nonneg hf.1 e
    have hge : N.edgeFlow g e ∈ Set.Ici (0 : ℝ) := edgeFlow_nonneg hg.1 e
    rcases le_total (N.edgeFlow f e) (N.edgeFlow g e) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hmono e hfe hge h)) (sub_nonpos.2 h)
    · exact mul_nonneg (sub_nonneg.2 (hmono e hge hfe h)) (sub_nonneg.2 h)
  have hsum : ∑ e, (ℓf e - ℓg e) * (N.edgeFlow f e - N.edgeFlow g e) = 0 := by
    refine le_antisymm ?_ (sum_nonneg fun e _ => hterm e)
    have : ∑ e, (ℓf e - ℓg e) * (N.edgeFlow f e - N.edgeFlow g e) =
        (N.cost f - ∑ e, ℓf e * N.edgeFlow g e) + (N.cost g - ∑ e, ℓg e * N.edgeFlow f e) := by
      simp only [cost, ℓf, ℓg, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun e _ => ?_
      ring
    rw [this]; linarith
  have he := (sum_eq_zero_iff_of_nonneg fun e _ => hterm e).1 hsum e (mem_univ e)
  rcases mul_eq_zero.1 he with h | h
  · exact sub_eq_zero.1 h
  · rw [sub_eq_zero.1 h]

/-- For latencies nondecreasing on `[0, ∞)` all Wardrop flows for a given demand have the same
cost (Beckmann, McGuire and Winsten 1956; Roughgarden–Tardos 2002, Lemma 2.9). -/
theorem IsWardrop.cost_eq [Finite ι] {f g : P → ℝ} {r : ι → ℝ}
    (hmono : ∀ e, MonotoneOn (N.latency e) (Set.Ici 0)) (hWf : N.IsWardrop f)
    (hf : N.IsFeasible r f)
    (hWg : N.IsWardrop g) (hg : N.IsFeasible r g) : N.cost f = N.cost g := by
  have hl := hWf.latency_edgeFlow_eq hmono hf hWg hg
  have h1 := hWf.cost_le_sum_latency_mul_edgeFlow hf hg
  have h2 := hWg.cost_le_sum_latency_mul_edgeFlow hg hf
  simp only [hl] at h1
  simp only [← hl] at h2
  exact le_antisymm (h1.trans_eq (by simp [cost])) (h2.trans_eq (by simp [cost]))

/-- **Price of anarchy `4/3` for affine latencies** (Roughgarden–Tardos 2002,
Theorem 4.5). If every latency is `ℓₑ(x) = aₑ x + bₑ` with `aₑ, bₑ ≥ 0`, then a
Wardrop flow costs at most `4/3` times any flow feasible for the same demand. -/
theorem IsWardrop.cost_le_of_affine [Finite ι] {f g : P → ℝ} {r : ι → ℝ} {a b : E → ℝ}
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) (hlat : ∀ e x, N.latency e x = a e * x + b e)
    (hW : N.IsWardrop f) (hf : N.IsFeasible r f) (hg : N.IsFeasible r g) :
    N.cost f ≤ 4 / 3 * N.cost g := by
  have hvi := hW.cost_le_sum_latency_mul_edgeFlow hf hg
  have hedge : ∀ e, N.latency e (N.edgeFlow f e) * N.edgeFlow g e ≤
      N.latency e (N.edgeFlow g e) * N.edgeFlow g e +
        1 / 4 * (N.latency e (N.edgeFlow f e) * N.edgeFlow f e) := by
    intro e
    have hx := edgeFlow_nonneg (N := N) hf.1 e
    have hy := edgeFlow_nonneg (N := N) hg.1 e
    rw [hlat, hlat]
    have := mul_nonneg (ha e) (sq_nonneg (N.edgeFlow g e - N.edgeFlow f e / 2))
    have := mul_nonneg (hb e) hx
    nlinarith
  have hsum := sum_le_sum fun e (_ : e ∈ univ) => hedge e
  rw [sum_add_distrib, ← mul_sum] at hsum
  change _ ≤ N.cost g + 1 / 4 * N.cost f at hsum
  linarith

/-- **Bicriteria bound** (Roughgarden–Tardos 2002, Theorem 3.2). For nonnegative
nondecreasing latencies on `[0, ∞)`, if `f` is a Wardrop flow for the demand `r` and `g`
is feasible for `(1 + γ) r`, then `γ C(f) ≤ C(g)`. The source states this for `γ > 0`
as `C(f) ≤ C(g) / γ`; the proof needs no sign condition on `γ`. -/
theorem IsWardrop.mul_cost_le_of_feasible_one_add [Finite ι] {f g : P → ℝ} {r : ι → ℝ}
    {γ : ℝ} (hmono : ∀ e, MonotoneOn (N.latency e) (Set.Ici 0))
    (hnn : ∀ e x, 0 ≤ x → 0 ≤ N.latency e x)
    (hW : N.IsWardrop f) (hf : N.IsFeasible r f) (hg : N.IsFeasible ((1 + γ) • r) g) :
    γ * N.cost f ≤ N.cost g := by
  have hkey := hW.smul_sum_pathLatency_mul_le hf hg
  rw [← cost_eq_sum_pathLatency_mul, sum_pathLatency_mul] at hkey
  have hedge : ∀ e, N.latency e (N.edgeFlow f e) * N.edgeFlow g e ≤
      N.latency e (N.edgeFlow g e) * N.edgeFlow g e +
        N.latency e (N.edgeFlow f e) * N.edgeFlow f e := by
    intro e
    set x := N.edgeFlow f e
    set y := N.edgeFlow g e
    have hx : 0 ≤ x := edgeFlow_nonneg hf.1 e
    have hy : 0 ≤ y := edgeFlow_nonneg hg.1 e
    have hlx := hnn e x hx
    have hly := hnn e y hy
    rcases le_total x y with hxy | hxy
    · have hl : N.latency e x ≤ N.latency e y := hmono e hx hy hxy
      nlinarith [mul_le_mul_of_nonneg_right hl hy, mul_nonneg hlx hx]
    · nlinarith [mul_le_mul_of_nonneg_left hxy hlx, mul_nonneg hly hy]
  have hsum := sum_le_sum fun e (_ : e ∈ univ) => hedge e
  rw [sum_add_distrib] at hsum
  change _ ≤ N.cost g + N.cost f at hsum
  linarith

/-- **Selfish routing costs no more than optimally routing twice the traffic**
(Roughgarden–Tardos 2002, Theorem 3.1): for nonnegative nondecreasing latencies on
`[0, ∞)`, a Wardrop flow for `r` costs at most any flow feasible for `2 r`. -/
theorem IsWardrop.cost_le_of_feasible_two [Finite ι] {f g : P → ℝ} {r : ι → ℝ}
    (hmono : ∀ e, MonotoneOn (N.latency e) (Set.Ici 0))
    (hnn : ∀ e x, 0 ≤ x → 0 ≤ N.latency e x)
    (hW : N.IsWardrop f) (hf : N.IsFeasible r f) (hg : N.IsFeasible ((2 : ℝ) • r) g) :
    N.cost f ≤ N.cost g := by
  have := hW.mul_cost_le_of_feasible_one_add (γ := 1) hmono hnn hf
    (by norm_num at hg ⊢; exact hg)
  linarith

end RoutingInstance

/-! ### Pigou's example: the bound `4/3` is attained -/

/-- Pigou's network: two parallel edges from `s` to `t`, one commodity, each edge is a
path; edge `0` has constant latency `1` and edge `1` has latency `x`
(Roughgarden–Tardos 2002, Figure 3 with `p = 1`). -/
def pigou : RoutingInstance (Fin 2) Unit (Fin 2) where
  commodity _ := ()
  edges p := {p}
  latency e x := if e = 0 then 1 else x

/-- The Wardrop flow of Pigou's network: all traffic on the variable-latency edge. -/
def pigouWardrop : Fin 2 → ℝ := ![0, 1]

/-- The optimal flow of Pigou's network: half the traffic on each edge. -/
noncomputable def pigouOptimal : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- In Pigou's network each edge is its own path, so edge flows equal path flows. -/
theorem pigou_edgeFlow (f : Fin 2 → ℝ) (e : Fin 2) : pigou.edgeFlow f e = f e := by
  simp [RoutingInstance.edgeFlow, pigou, Finset.sum_filter]

/-- The all-on-the-variable-edge flow routes one unit in Pigou's network. -/
theorem pigou_isFeasible_wardrop : pigou.IsFeasible (fun _ => 1) pigouWardrop := by
  refine ⟨fun p => ?_, fun _ => ?_⟩
  · fin_cases p <;> simp [pigouWardrop]
  · simp [pigou, pigouWardrop, Fin.sum_univ_two]

/-- The half-and-half flow routes one unit in Pigou's network. -/
theorem pigou_isFeasible_optimal : pigou.IsFeasible (fun _ => 1) pigouOptimal := by
  refine ⟨fun p => ?_, fun _ => ?_⟩
  · fin_cases p <;> norm_num [pigouOptimal]
  · norm_num [pigou, pigouOptimal, Fin.sum_univ_two]

/-- Routing all traffic on the edge of latency `x` is a Wardrop flow in Pigou's network:
its latency `1` equals that of the constant edge. -/
theorem pigou_isWardrop : pigou.IsWardrop pigouWardrop := by
  intro p q _ hp
  simp only [RoutingInstance.pathLatency, pigou_edgeFlow]
  fin_cases p <;> fin_cases q <;> simp_all [pigouWardrop, pigou]

/-- The Wardrop flow of Pigou's network has cost `1`. -/
theorem pigou_cost_wardrop : pigou.cost pigouWardrop = 1 := by
  simp only [RoutingInstance.cost, pigou_edgeFlow]
  simp [pigou, pigouWardrop, Fin.sum_univ_two]

/-- The half-and-half flow of Pigou's network has cost `3/4`, the minimum of
`(1 - x) + x²` over `0 ≤ x ≤ 1`. -/
theorem pigou_cost_optimal : pigou.cost pigouOptimal = 3 / 4 := by
  simp only [RoutingInstance.cost, pigou_edgeFlow]
  norm_num [pigou, pigouOptimal, Fin.sum_univ_two]

/-- In Pigou's network the Wardrop flow costs exactly `4/3` times the optimal flow, so the
constant of `RoutingInstance.IsWardrop.cost_le_of_affine` cannot be improved. -/
theorem pigou_cost_wardrop_eq : pigou.cost pigouWardrop = 4 / 3 * pigou.cost pigouOptimal := by
  rw [pigou_cost_wardrop, pigou_cost_optimal]; norm_num

/-! ### Braess's paradox -/

/-- The latencies of Braess's network on the edges `0 : s → v`, `1 : v → t`, `2 : s → w`,
`3 : w → t` and `4 : v → w`: latency `x` on edges `0` and `3`, `1` on edges `1` and `2`, and
`0` on the shortcut `4` (Roughgarden–Tardos 2002, Figure 1). -/
def braessLatency (e : Fin 5) (x : ℝ) : ℝ :=
  if e = 0 ∨ e = 3 then x else if e = 4 then 0 else 1

/-- Braess's network before the shortcut: the two paths `s → v → t` and `s → w → t`. -/
def braessBefore : RoutingInstance (Fin 5) Unit (Fin 2) where
  commodity _ := ()
  edges := ![{0, 1}, {2, 3}]
  latency := braessLatency

/-- Braess's network after adding the zero-latency shortcut `v → w`, which creates the third
path `s → v → w → t`. -/
def braessAfter : RoutingInstance (Fin 5) Unit (Fin 3) where
  commodity _ := ()
  edges := ![{0, 1}, {2, 3}, {0, 4, 3}]
  latency := braessLatency

/-- The latencies of Braess's network are nondecreasing. -/
theorem braessLatency_monotone (e : Fin 5) : Monotone (braessLatency e) := by
  fin_cases e
  · exact fun x y h => by simpa [braessLatency] using h
  · exact fun x y _ => by simp [braessLatency]
  · exact fun x y _ => by simp [braessLatency]
  · exact fun x y h => by simpa [braessLatency] using h
  · exact fun x y _ => by simp [braessLatency]

/-- Edge flows before the shortcut: edges `0, 1` carry the first path, edges `2, 3` the
second. -/
theorem braessBefore_edgeFlow (f : Fin 2 → ℝ) :
    braessBefore.edgeFlow f = ![f 0, f 0, f 1, f 1, 0] := by
  funext e
  simp only [RoutingInstance.edgeFlow]
  rw [Finset.sum_filter]
  fin_cases e <;> simp [braessBefore, Fin.sum_univ_two]

/-- Edge flows after the shortcut. -/
theorem braessAfter_edgeFlow (f : Fin 3 → ℝ) :
    braessAfter.edgeFlow f = ![f 0 + f 2, f 0, f 1, f 1 + f 2, f 2] := by
  funext e
  simp only [RoutingInstance.edgeFlow]
  rw [Finset.sum_filter]
  fin_cases e <;> simp [braessAfter, Fin.sum_univ_three]

/-- Splitting one unit equally is a Wardrop flow of Braess's network before the shortcut. -/
theorem braessBefore_isWardrop : braessBefore.IsWardrop ![1 / 2, 1 / 2] := by
  intro p q _ _
  simp only [RoutingInstance.pathLatency, braessBefore_edgeFlow]
  fin_cases p <;> fin_cases q <;> norm_num [braessBefore, braessLatency]

/-- Routing all traffic on the zigzag path is a Wardrop flow after the shortcut is added. -/
theorem braessAfter_isWardrop : braessAfter.IsWardrop ![0, 0, 1] := by
  intro p q _ hp
  simp only [RoutingInstance.pathLatency, braessAfter_edgeFlow]
  fin_cases p <;> fin_cases q <;> norm_num [braessAfter, braessLatency] at *

/-- **Braess's paradox** (Braess 1968; Roughgarden–Tardos 2002, Figure 1). In Braess's
network with one unit of traffic, every Wardrop flow costs `3/2` before the zero-latency
shortcut `v → w` is added and `2` after: adding a link makes every user worse off. -/
theorem braess_paradox :
    (∀ f, braessBefore.IsFeasible (fun _ => 1) f → braessBefore.IsWardrop f →
      braessBefore.cost f = 3 / 2) ∧
    (∀ f, braessAfter.IsFeasible (fun _ => 1) f → braessAfter.IsWardrop f →
      braessAfter.cost f = 2) := by
  have hb : braessBefore.IsFeasible (fun _ => 1) ![1 / 2, 1 / 2] := by
    refine ⟨fun p => ?_, fun _ => ?_⟩
    · fin_cases p <;> norm_num
    · norm_num [braessBefore, Fin.sum_univ_two]
  have ha : braessAfter.IsFeasible (fun _ => 1) ![0, 0, 1] := by
    refine ⟨fun p => ?_, fun _ => ?_⟩
    · fin_cases p <;> norm_num
    · norm_num [braessAfter, Fin.sum_univ_three]
  refine ⟨fun f hf hW => ?_, fun f hf hW => ?_⟩
  · rw [hW.cost_eq (fun e => (braessLatency_monotone e).monotoneOn _) hf braessBefore_isWardrop hb]
    simp only [RoutingInstance.cost, braessBefore_edgeFlow]
    norm_num [braessBefore, braessLatency, Fin.sum_univ_five]
  · rw [hW.cost_eq (fun e => (braessLatency_monotone e).monotoneOn _) hf braessAfter_isWardrop ha]
    simp only [RoutingInstance.cost, braessAfter_edgeFlow]
    norm_num [braessAfter, braessLatency, Fin.sum_univ_five]

end MathlibExt.GameTheory.SelfishRouting
