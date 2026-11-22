/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
public import PhyslibExt.FluidDynamics.Traffic.CellTransmission

/-!
# Junction turning certificates and link boundary flows

## i. Overview

Network. Finite link type `E` and node type `V` with `tail head : E → V`, the
arc-ID convention of `MathlibExt.Combinatorics.Graph.ArcNetwork`. A link is its
element of `E`: parallel links stay distinct and loops (`tail e = head e`) are
allowed. Every node is a junction without storage. Origins and destinations
enter only through the external faces of source and sink links, never through a
junction.

Commodities. A finite label type `C`: destinations or routes. All commodity
flows are in the one vehicle unit of the cell-transmission model;
passenger-car equivalents are not modeled. Under the route convention
commodity `c` follows the arc list `edges c` from `orig c` to `dest c`, a valid
walk in the sense of `IsArcWalk`, and turns only from an arc of its route to
the next arc.

Turning certificate. For one time step, `q c e e'` is the flow of commodity `c`
that leaves link `e` at its head and enters link `e'` at its tail, in the
face-flux unit of the cell-transmission model (vehicles per unit time). The
certificate `q` is data, not the output of a junction solver. Its fields, used
as hypotheses where needed: nonnegativity, `0 ≤ q c e e'`; support on
movements, `q c e e' = 0` unless `head e = tail e'`; and the junction-local
receiving constraint `IsSupplyFeasible`: at the junction `tail e'`, the turning
flows from that junction's incoming links into `e'`, summed over commodities,
are at most the receiving supply of the first cell of `e'`. No priority rule,
supply shares, flow maximization, invariance principle, first-in first-out rule
or junction solver is assumed: any certificate with these fields is admitted.

Link boundary flows. `linkOutflow q c e = ∑ e', q c e e'` is the downstream
boundary flow of commodity `c` on link `e` (into the junction at `head e`);
`linkInflow q c e' = ∑ e, q c e e'` is its upstream boundary flow on link `e'`
(out of the junction at `tail e'`). Aggregate flows are the sums over `C`. The
turning fraction of `c` from `e` to `e'` is `q c e e' / linkOutflow q c e`.

Receiving supply. Each link carries its own triangular diagram, free-flow speed
`vf e`, wave speed `w e` and jam density `kj e`, and `kFirst e` is the density
of its first cell. The receiving supply of link `e'` is
`supply (vf e') (w e') (kj e') (kFirst e')`, the cell-transmission supply
`min (w * (kj - k)) (capacity v w kj)` of
`FluidDynamics.Traffic.CellTransmission`. No statement here needs `0 < vf`,
`0 < w`, `0 ≤ kj` or `0 ≤ kFirst ≤ kj`; on that domain the supply is
nonnegative, and outside it `IsSupplyFeasible` can be unsatisfiable, which
leaves the statements true.

Sign. `MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix` has
`B v e = 1[head e = v] - 1[tail e = v]`, inflow minus outflow. On the
turning-movement network, whose nodes are links and whose arcs are ordered link
pairs `m` with tail `m.1` and head `m.2`, it gives net junction inflow minus
outflow per link.

Totalized operations. `capacity` divides by `v + w` (value `0` when
`v + w = 0`); the turning fraction divides by the link outflow (value `0` on a
link with zero outflow). No statement depends on a junk value: the fraction
identity holds on zero-outflow links because nonnegative flows then vanish.

Scope and exclusions. Aggregate junction conservation, the receiving supply
bound and spillback at a jammed first cell, the turning-fraction factorization,
the bridge to the canonical incidence transfer, and route consistency.
Aggregate conservation does not imply multi-commodity first-in first-out
behavior, and no such claim, node-priority model, junction solver, equilibrium,
sending-demand statement or cell-update admissibility is stated.

## ii. Key results

- `FluidDynamics.Traffic.JunctionBoundaryFlow.sum_linkOutflow_eq_sum_linkInflow`:
  aggregate junction conservation for movement-supported turning flows.
- `FluidDynamics.Traffic.JunctionBoundaryFlow.sum_linkInflow_le_supply`: the
  aggregate inflow of each link is at most its receiving supply.
- `FluidDynamics.Traffic.JunctionBoundaryFlow.eq_zero_of_kFirst_eq_kj`: no
  turning flow enters a link whose first cell is jammed (spillback).
- `FluidDynamics.Traffic.JunctionBoundaryFlow.turningFraction_mul_linkOutflow`:
  turning fractions factor the turning flows, zero-outflow links included.
- `FluidDynamics.Traffic.JunctionBoundaryFlow.incidenceMatrix_mulVec_turningFlow`:
  the canonical incidence transfer of the aggregate turning flows is aggregate
  inflow minus aggregate outflow per link.
- `FluidDynamics.Traffic.JunctionBoundaryFlow.eq_zero_of_route`: routing
  certificates (valid walks, flow only to the next arc) are supported on
  movements.

## iii. Table of contents

- A. Turning flows and link boundary flows
- B. Conservation, the supply bound and spillback
- C. Turning fractions, the incidence bridge and routes

## iv. References

- C. F. Daganzo, the cell transmission model, *Transp. Res. B* 28, 1994, and
  *Transp. Res. B* 29, 1995 (network junctions in the cell-transmission model).
-/

@[expose] public section

namespace FluidDynamics.Traffic.JunctionBoundaryFlow

open FluidDynamics.Traffic.CellTransmission
open MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ## A. Turning flows and link boundary flows -/

/-- Downstream boundary flow of commodity `c` on link `e`: its total turning flow from `e` into
the junction at `head e`. -/
def linkOutflow {E C : Type*} [Fintype E] (q : C → E → E → ℝ) (c : C) (e : E) : ℝ :=
  ∑ e', q c e e'

/-- Upstream boundary flow of commodity `c` on link `e`: its total turning flow from the
junction at `tail e` into `e`. -/
def linkInflow {E C : Type*} [Fintype E] (q : C → E → E → ℝ) (c : C) (e : E) : ℝ :=
  ∑ e₀, q c e₀ e

/-- Turning fraction of commodity `c` from link `e` to link `e'`: its share of the outflow of
`c` from `e`, with value `0` when that outflow is zero. -/
noncomputable def turningFraction {E C : Type*} [Fintype E] (q : C → E → E → ℝ) (c : C)
    (e e' : E) : ℝ :=
  q c e e' / linkOutflow q c e

/-- Junction-local receiving constraint: for every link `e'`, the turning flows into `e'` from
the incoming links of the junction `tail e'`, summed over commodities, are at most the
receiving supply of the first cell of `e'`. -/
def IsSupplyFeasible {V E C : Type*} [DecidableEq V] [Fintype E] [Fintype C]
    (tail head : E → V) (vf w kj kFirst : E → ℝ) (q : C → E → E → ℝ) : Prop :=
  ∀ e', ∑ c, ∑ e with head e = tail e', q c e e' ≤ supply (vf e') (w e') (kj e') (kFirst e')

/-! ## B. Conservation, the supply bound and spillback -/

/-- **Aggregate junction conservation.** If every turning flow joins a link to a link that
starts where it ends, then at every junction `v` the total boundary outflow of the links ending
at `v` equals the total boundary inflow of the links starting at `v`, summed over commodities.
Signs of the flows are not used. This is aggregate conservation only; it says nothing about
first-in first-out order between commodities. -/
theorem sum_linkOutflow_eq_sum_linkInflow {V E C : Type*} [DecidableEq V] [Fintype E]
    [Fintype C] {tail head : E → V} {q : C → E → E → ℝ}
    (hq : ∀ c e e', head e ≠ tail e' → q c e e' = 0) (v : V) :
    ∑ e with head e = v, ∑ c, linkOutflow q c e =
      ∑ e with tail e = v, ∑ c, linkInflow q c e := by
  unfold linkOutflow linkInflow
  have key : ∀ (c : C) (e : E), head e = v →
      (∑ e', q c e e') = ∑ e' with tail e' = v, q c e e' := by
    intro c e he
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e' _ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hq c e e' (fun h => hmem (h.symm.trans he))
  have key' : ∀ (c : C) (e' : E), tail e' = v →
      (∑ e₀, q c e₀ e') = ∑ e₀ with head e₀ = v, q c e₀ e' := by
    intro c e' he
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e₀ _ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hq c e₀ e' (fun h => hmem (h.trans he))
  calc ∑ e with head e = v, ∑ c, ∑ e', q c e e'
      = ∑ e with head e = v, ∑ c, ∑ e' with tail e' = v, q c e e' := by
        apply Finset.sum_congr rfl
        intro e he
        have he' : head e = v := (Finset.mem_filter.mp he).2
        exact Finset.sum_congr rfl fun c _ => key c e he'
    _ = ∑ c, ∑ e with head e = v, ∑ e' with tail e' = v, q c e e' :=
        Finset.sum_comm
    _ = ∑ c, ∑ e' with tail e' = v, ∑ e with head e = v, q c e e' :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ e' with tail e' = v, ∑ c, ∑ e with head e = v, q c e e' :=
        Finset.sum_comm
    _ = ∑ e with tail e = v, ∑ c, ∑ e₀, q c e₀ e := by
        apply Finset.sum_congr rfl
        intro e' he
        have he' : tail e' = v := (Finset.mem_filter.mp he).2
        exact Finset.sum_congr rfl fun c _ => (key' c e' he').symm

/-- **Receiving supply bound.** For a certificate supported on movements and satisfying the
junction-local receiving constraint, the aggregate upstream boundary flow of every link `e'`
is at most the receiving supply of its first cell, the face-flux supply bound of the
cell-transmission model at the junction. -/
theorem sum_linkInflow_le_supply {V E C : Type*} [DecidableEq V] [Fintype E] [Fintype C]
    {tail head : E → V} {vf w kj kFirst : E → ℝ} {q : C → E → E → ℝ}
    (hq : ∀ c e e', head e ≠ tail e' → q c e e' = 0)
    (hR : IsSupplyFeasible tail head vf w kj kFirst q) (e' : E) :
    ∑ c, linkInflow q c e' ≤ supply (vf e') (w e') (kj e') (kFirst e') := by
  unfold linkInflow
  have h : ∀ c : C, (∑ e₀, q c e₀ e') = ∑ e₀ with head e₀ = tail e', q c e₀ e' := by
    intro c
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e₀ _ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hq c e₀ e' hmem
  calc ∑ c, ∑ e₀, q c e₀ e'
      = ∑ c, ∑ e₀ with head e₀ = tail e', q c e₀ e' :=
        Finset.sum_congr rfl fun c _ => h c
    _ ≤ supply (vf e') (w e') (kj e') (kFirst e') := hR e'

/-- **Spillback.** For a nonnegative certificate supported on movements and satisfying the
junction-local receiving constraint, if the first cell of link `e'` is at jam density, then
every turning flow of every commodity into `e'` is zero: a saturated downstream link blocks all
realized turning flow into it. -/
lemma eq_zero_of_kFirst_eq_kj {V E C : Type*} [DecidableEq V] [Fintype E] [Fintype C]
    {tail head : E → V} {vf w kj kFirst : E → ℝ} {q : C → E → E → ℝ}
    (hnn : ∀ c e e', 0 ≤ q c e e') (hq : ∀ c e e', head e ≠ tail e' → q c e e' = 0)
    (hR : IsSupplyFeasible tail head vf w kj kFirst q) {e' : E}
    (hjam : kFirst e' = kj e') (c : C) (e : E) :
    q c e e' = 0 := by
  have hsup : supply (vf e') (w e') (kj e') (kFirst e') ≤ 0 := by
    unfold supply
    rw [hjam, sub_self, mul_zero]
    exact min_le_left _ _
  have hle : ∑ c, ∑ e₀ with head e₀ = tail e', q c e₀ e' ≤ 0 :=
    le_trans (hR e') hsup
  have hnnC : ∀ c ∈ (Finset.univ : Finset C),
      0 ≤ ∑ e₀ with head e₀ = tail e', q c e₀ e' := by
    intro c _
    apply Finset.sum_nonneg
    intro e₀ _
    exact hnn c e₀ e'
  have hsum0 : ∑ c, ∑ e₀ with head e₀ = tail e', q c e₀ e' = 0 :=
    le_antisymm hle (Finset.sum_nonneg hnnC)
  have hall : ∀ c ∈ (Finset.univ : Finset C),
      (∑ e₀ with head e₀ = tail e', q c e₀ e') = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnnC).mp hsum0
  by_cases he : head e = tail e'
  · have hmem : e ∈ Finset.univ.filter (fun e₀ => head e₀ = tail e') := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact he
    have h0 := hall c (Finset.mem_univ c)
    have hnnE : ∀ e₀ ∈ Finset.univ.filter (fun e₀ => head e₀ = tail e'),
        0 ≤ q c e₀ e' := fun e₀ _ => hnn c e₀ e'
    have hallE := (Finset.sum_eq_zero_iff_of_nonneg hnnE).mp h0
    exact hallE e hmem
  · exact hq c e e' he

/-! ## C. Turning fractions, the incidence bridge and routes -/

/-- **Turning fractions.** If the turning flows of commodity `c` out of link `e` are
nonnegative, each of them is its turning fraction times the outflow of `c` from `e`. On a link
with positive outflow the fractions therefore sum to one; on a link with zero outflow all its
turning flows vanish. -/
lemma turningFraction_mul_linkOutflow {E C : Type*} [Fintype E] {q : C → E → E → ℝ}
    {c : C} {e : E} (hnn : ∀ e', 0 ≤ q c e e') (e' : E) :
    turningFraction q c e e' * linkOutflow q c e = q c e e' := by
  unfold turningFraction
  by_cases h : linkOutflow q c e = 0
  · have hsum : (∑ e'', q c e e'') = 0 := h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun e'' _ => hnn e'')).mp hsum
    have h0 : q c e e' = 0 := hall e' (Finset.mem_univ e')
    rw [h0, h, div_zero, zero_mul]
  · exact div_mul_cancel₀ _ h

/-- **Physical-to-canonical bridge.** On the turning-movement network, whose nodes are links and
whose arcs are ordered link pairs, the canonical incidence transfer of the aggregate turning
flows at link `e` is the aggregate upstream boundary flow of `e` minus its aggregate downstream
boundary flow. So over a step of length `dt` the junction transfer changes link vehicle
counts by `dt` times this canonical incidence transfer, in addition to the external source
and sink faces, in the inflow-minus-outflow sign of `incidenceMatrix`. -/
lemma incidenceMatrix_mulVec_turningFlow {E C : Type*} [Fintype E] [DecidableEq E]
    [Fintype C] (q : C → E → E → ℝ) (e : E) :
    (incidenceMatrix (fun m : E × E => m.1) (fun m => m.2)).mulVec
        (fun m => ∑ c, q c m.1 m.2) e =
      ∑ c, linkInflow q c e - ∑ c, linkOutflow q c e := by
  have h1 : (∑ m : E × E, (if m.2 = e then (1 : ℝ) else 0) * (∑ c, q c m.1 m.2))
      = ∑ c, ∑ a, q c a e := by
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_prod_type, Fintype.sum_ite_eq']
    exact Finset.sum_comm
  have h2 : (∑ m : E × E, (if m.1 = e then (1 : ℝ) else 0) * (∑ c, q c m.1 m.2))
      = ∑ c, ∑ b, q c e b := by
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [Fintype.sum_ite_eq']
    exact Finset.sum_comm
  unfold linkInflow linkOutflow
  simp only [Matrix.mulVec_apply_eq_sum, incidenceMatrix, sub_mul,
    Finset.sum_sub_distrib, h1, h2]

private theorem isChain_of_mem_zip_tail {E : Type*} {R : E → E → Prop} {l : List E}
    (h : l.IsChain R) {x : E × E} (hmem : x ∈ l.zip l.tail) : R x.1 x.2 := by
  induction h generalizing x with
  | nil => simp at hmem
  | singleton a => simp at hmem
  | cons_cons hab hbc ih =>
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hab
    · exact ih hmem

/-- **Routing certificates are turning certificates.** If every commodity is a route given by a
valid walk and carries flow only from an arc of its route to the next arc, then its turning
flows are supported on movements: a flow from `e` to `e'` with `head e ≠ tail e'` is zero. -/
lemma eq_zero_of_route {V E C : Type*} {tail head : E → V} {orig dest : C → V}
    {edges : C → List E} {q : C → E → E → ℝ}
    (hwalk : ∀ c, IsArcWalk tail head (orig c) (dest c) (edges c))
    (hroute : ∀ c e e', q c e e' ≠ 0 → (e, e') ∈ (edges c).zip (edges c).tail)
    {c : C} {e e' : E} (hne : head e ≠ tail e') :
    q c e e' = 0 := by
  by_contra hne0
  have hchain := (hwalk c).2.2.1
  have hmem := hroute c e e' hne0
  have hR := isChain_of_mem_zip_tail hchain hmem
  exact hne hR

end FluidDynamics.Traffic.JunctionBoundaryFlow
