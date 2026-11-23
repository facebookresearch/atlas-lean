/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LosslessDCFlowModel
public import MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# Grounded DC load-flow solve on a connected positive-susceptance network

## i. Overview

A lossless DC network
(`PhyslibExt.Circuits.LosslessDCFlowModel`) has nodes `Fin nN`,
oriented branches `Fin nE` with tail and head maps, branch
susceptances `b`, branch flows `f = diag(b) * Bᵀ * θ`, and nodal
injections `p = B * f = L_b * θ` for the full weighted Laplacian
`L_b = B * diag(b) * Bᵀ`. The DC load-flow problem asks for angles `θ`
with `L_b * θ = p`.

Assume every susceptance is positive, the underlying undirected
network is connected, a reference node `ref` is fixed, and the
injections are balanced, `∑ v, p v = 0`. Connectivity is stated on
the arc graph of `ArcNetworkLaplacian` with every branch counted with
weight one (orientation ignored, loops dropped):
`(positiveArcGraph tail head (fun _ => 1)).Connected`. With positive
susceptances this is the `b`-weighted arc graph
(`positiveArcGraph_eq_of_pos`). Deleting the `ref` row and
column of `L_b` gives the reduced grounded matrix, which is invertible
by the grounded positive definiteness of the arc-network Laplacian
(`PhyslibExt.Circuits.LosslessDCFlowModel.grounded_weightedLaplacian_isUnit`).
Solving the non-reference equations with it and setting `θ ref = 0`
gives the grounded angles `groundedAngles`. They are the unique `θ`
with `θ ref = 0` and `L_b * θ = p`, their DC injection is `p`, every
solution of `L_b * θ = p` carries their branch flows, and the DC
model's per-line bound against the lossless AC sending-end power holds
at them.

Balance is necessary: `L_b * θ = p` forces `∑ v, p v = 0` for every
`θ` and every real `b`. The reference row of the system then follows
from the others, which is why the reduced solve also solves it.

Susceptances enter the graph results only as abstract positive arc
weights; they are not identified with physical conductances. DC
solvability says nothing about AC, voltage-magnitude, or reactive
feasibility. The bound compares two formulas at the same angles, not
two independently solved operating points, and no small-angle premise
follows from solvability.

## ii. Key results

- `l2_correct`: unique grounded solve, its DC injection, its branch
  flows, flow transfer to every solution, and the per-line bound,
  together.
- `weightedLaplacian_mulVec_groundedAngles`: existence of the grounded
  solve, reference row included.
- `eq_groundedAngles`: uniqueness among grounded solutions.
- `dcBranchFlow_eq_groundedAngles`: every solution carries the grounded
  branch flows.
- `sum_eq_zero_of_weightedLaplacian_mulVec_eq`: balance is necessary.

## iii. Table of contents

- A. Connectivity and the reduced grounded matrix
- B. The grounded solve
- C. Headline

## iv. References

- B. Stott, J. Jardim, and O. Alsaç, "DC Power Flow Revisited,"
  *IEEE Transactions on Power Systems* 24(3), 2009, 1290-1300: the
  lossless DC load flow and its reference-bus reduction.
- J. J. Grainger and W. D. Stevenson, *Power System Analysis*,
  McGraw-Hill, 1994: the reduced bus susceptance matrix and the DC
  load flow.

## A. Connectivity and the reduced grounded matrix
-/

@[expose] public section

namespace PhyslibExt.Circuits.DCFlowNetworkBridge

open Matrix PhyslibExt.Circuits.LosslessDCFlowModel
open MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
  (positiveArcGraph positiveArcGraph_eq_of_pos)

/-- Reduced grounded susceptance matrix: the full weighted Laplacian `L_b` with the reference
row and column deleted, indexed by the non-reference nodes. -/
noncomputable def groundedLaplacian (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (ref : Fin nN) : Matrix {v // v ≠ ref} {v // v ≠ ref} ℝ :=
  (weightedLaplacian nN nE tail head b).submatrix Subtype.val Subtype.val

/-- Grounded DC angles: solve the non-reference equations `L_b θ = p` with the reduced grounded
matrix and reconstruct the reference angle `θ ref = 0`. The matrix inverse is Mathlib's
`Matrix.inv`, which is the true inverse when the reduced matrix is invertible. -/
noncomputable def groundedAngles (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (ref : Fin nN) (p : Fin nN → ℝ) : Fin nN → ℝ :=
  fun v => if h : v = ref then 0 else
    ((groundedLaplacian nN nE tail head b ref)⁻¹ *ᵥ fun i => p i.1) ⟨v, h⟩

/-- The grounded angles vanish at the reference node. -/
theorem groundedAngles_ref (nN nE : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (ref : Fin nN) (p : Fin nN → ℝ) :
    groundedAngles nN nE tail head b ref p ref = 0 := by
  simp [groundedAngles]

/-- Positive susceptances on a connected network make the reduced grounded matrix invertible. -/
theorem groundedLaplacian_isUnit (nN nE : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (hb : ∀ e, 0 < b e) (ref : Fin nN)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected) :
    IsUnit (groundedLaplacian nN nE tail head b ref) :=
  grounded_weightedLaplacian_isUnit nN nE tail head b (fun e => (hb e).le) ref
    (by rw [positiveArcGraph_eq_of_pos tail head hb]; exact hconn.preconnected ref)

/-! ## B. The grounded solve -/

/-- Balance is necessary: any injection of the form `L_b θ` sums to zero, for every real `b`. -/
theorem sum_eq_zero_of_weightedLaplacian_mulVec_eq (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ p : Fin nN → ℝ) (h : weightedLaplacian nN nE tail head b *ᵥ θ = p) :
    ∑ v, p v = 0 := by
  rw [← h, ← dcInjection_eq_weightedLaplacian_mulVec]
  exact sum_dcInjection_eq_zero nN nE tail head b θ

/-- **Existence.** For positive susceptances on a connected network and balanced injections, the
grounded angles solve the full system `L_b θ = p`, the reference row included. -/
theorem weightedLaplacian_mulVec_groundedAngles (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 < b e) (ref : Fin nN)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (p : Fin nN → ℝ) (hp : ∑ v, p v = 0) :
    weightedLaplacian nN nE tail head b *ᵥ groundedAngles nN nE tail head b ref p = p := by
  have hdet : IsUnit (groundedLaplacian nN nE tail head b ref).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (groundedLaplacian_isUnit nN nE tail head b hb ref hconn)
  have hMq : groundedLaplacian nN nE tail head b ref *ᵥ
      ((groundedLaplacian nN nE tail head b ref)⁻¹ *ᵥ fun i => p i.1) = fun i => p i.1 := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hθref := groundedAngles_ref nN nE tail head b ref p
  have hθi : ∀ i : {v // v ≠ ref}, groundedAngles nN nE tail head b ref p i =
      ((groundedLaplacian nN nE tail head b ref)⁻¹ *ᵥ fun i => p i.1) i := by
    intro i
    simp [groundedAngles, i.2]
  have hrow : ∀ i : {v // v ≠ ref},
      (weightedLaplacian nN nE tail head b *ᵥ groundedAngles nN nE tail head b ref p) i = p i := by
    intro i
    have h := congrFun hMq i
    rw [← h]
    simp only [mulVec, dotProduct]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ ref, hθref, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθi j]
    rfl
  have hsum := sum_eq_zero_of_weightedLaplacian_mulVec_eq nN nE tail head b
    (groundedAngles nN nE tail head b ref p) _ rfl
  funext v
  by_cases hv : v = ref
  · subst hv
    rw [Fintype.sum_eq_add_sum_subtype_ne _ v] at hsum hp
    have h3 : ∑ i : {u // u ≠ v},
        (weightedLaplacian nN nE tail head b *ᵥ groundedAngles nN nE tail head b v p) i =
          ∑ i : {u // u ≠ v}, p i :=
      Finset.sum_congr rfl fun i _ => hrow i
    linarith
  · exact hrow ⟨v, hv⟩

/-- **Uniqueness.** For positive susceptances on a connected network, a solution of
`L_b θ = p` with `θ ref = 0` is the grounded angle vector. -/
theorem eq_groundedAngles (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 < b e) (ref : Fin nN)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (p : Fin nN → ℝ) (θ : Fin nN → ℝ) (hθref : θ ref = 0)
    (hθ : weightedLaplacian nN nE tail head b *ᵥ θ = p) :
    θ = groundedAngles nN nE tail head b ref p := by
  have hp := sum_eq_zero_of_weightedLaplacian_mulVec_eq nN nE tail head b θ p hθ
  have hsol := weightedLaplacian_mulVec_groundedAngles nN nE tail head b hb ref hconn p hp
  have hker : weightedLaplacian nN nE tail head b *ᵥ
      (θ - groundedAngles nN nE tail head b ref p) = 0 := by
    rw [mulVec_sub, hθ, hsol, sub_self]
  have hc := (weightedLaplacian_mulVec_eq_zero_iff_of_reachable nN nE tail head b
    (fun e => (hb e).le) ref
    (by rw [positiveArcGraph_eq_of_pos tail head hb]; exact hconn.preconnected ref) _).mp hker
  funext v
  have h := hc v
  simp only [Pi.sub_apply, hθref, groundedAngles_ref] at h
  linarith

/-- **Flow transfer.** For positive susceptances on a connected network, every solution of
`L_b θ = p` carries the branch flows of the grounded angles. -/
theorem dcBranchFlow_eq_groundedAngles (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 < b e) (ref : Fin nN)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (p : Fin nN → ℝ) (θ : Fin nN → ℝ)
    (hθ : weightedLaplacian nN nE tail head b *ᵥ θ = p) :
    dcBranchFlow nN nE tail head b θ =
      dcBranchFlow nN nE tail head b (groundedAngles nN nE tail head b ref p) := by
  have hp := sum_eq_zero_of_weightedLaplacian_mulVec_eq nN nE tail head b θ p hθ
  have hsol := weightedLaplacian_mulVec_groundedAngles nN nE tail head b hb ref hconn p hp
  have hker : weightedLaplacian nN nE tail head b *ᵥ
      (θ - groundedAngles nN nE tail head b ref p) = 0 := by
    rw [mulVec_sub, hθ, hsol, sub_self]
  have hc := (weightedLaplacian_mulVec_eq_zero_iff_of_reachable nN nE tail head b
    (fun e => (hb e).le) ref
    (by rw [positiveArcGraph_eq_of_pos tail head hb]; exact hconn.preconnected ref) _).mp hker
  funext e
  have h1 := hc (tail e)
  have h2 := hc (head e)
  simp only [Pi.sub_apply] at h1 h2
  rw [dcBranchFlow_apply, dcBranchFlow_apply]
  congr 1
  linarith

/-! ## C. Headline -/

/-- **Grounded DC load-flow solve and flow transfer.** For positive susceptances on a connected
network, a reference node, and balanced injections `p`:

1. the grounded angles (reduced grounded matrix solve, `θ ref = 0`) are the unique `θ` with
   `θ ref = 0` and `L_b θ = p`;
2. they vanish at the reference and solve `L_b θ = p`;
3. their DC injection `B f`, with `f = diag(b) Bᵀ θ` for the same `B` and `b`, is `p`;
4. their branch flows are `b e * (θ tail - θ head)`, and every solution of `L_b θ = p` carries the
   same flows;
5. the DC model's per-line bound holds at the grounded angles:
   `|P e - f e| ≤ b e * |θ tail - θ head| ^ 3 / 6`. -/
theorem l2_correct (nN nE : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (hb : ∀ e, 0 < b e) (ref : Fin nN)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (p : Fin nN → ℝ) (hp : ∑ v, p v = 0) :
    (∃! θ : Fin nN → ℝ, θ ref = 0 ∧ weightedLaplacian nN nE tail head b *ᵥ θ = p) ∧
      groundedAngles nN nE tail head b ref p ref = 0 ∧
      weightedLaplacian nN nE tail head b *ᵥ groundedAngles nN nE tail head b ref p = p ∧
      dcInjection nN nE tail head b (groundedAngles nN nE tail head b ref p) = p ∧
      (∀ e, dcBranchFlow nN nE tail head b (groundedAngles nN nE tail head b ref p) e =
        b e * (groundedAngles nN nE tail head b ref p (tail e) -
          groundedAngles nN nE tail head b ref p (head e))) ∧
      (∀ θ : Fin nN → ℝ, weightedLaplacian nN nE tail head b *ᵥ θ = p →
        dcBranchFlow nN nE tail head b θ =
          dcBranchFlow nN nE tail head b (groundedAngles nN nE tail head b ref p)) ∧
      (∀ e, |acBranchRealPower nN nE tail head b (groundedAngles nN nE tail head b ref p) e -
          dcBranchFlow nN nE tail head b (groundedAngles nN nE tail head b ref p) e| ≤
        b e * |groundedAngles nN nE tail head b ref p (tail e) -
          groundedAngles nN nE tail head b ref p (head e)| ^ 3 / 6) := by
  have hsol := weightedLaplacian_mulVec_groundedAngles nN nE tail head b hb ref hconn p hp
  refine ⟨⟨groundedAngles nN nE tail head b ref p, ⟨groundedAngles_ref nN nE tail head b ref p,
      hsol⟩, fun θ hθ => eq_groundedAngles nN nE tail head b hb ref hconn p θ hθ.1 hθ.2⟩,
    groundedAngles_ref nN nE tail head b ref p, hsol, ?_,
    fun e => dcBranchFlow_apply nN nE tail head b _ e,
    fun θ hθ => dcBranchFlow_eq_groundedAngles nN nE tail head b hb ref hconn p θ hθ,
    fun e => abs_acBranchRealPower_sub_dcBranchFlow_le nN nE tail head b hb _ e⟩
  rw [dcInjection_eq_weightedLaplacian_mulVec, hsol]

end PhyslibExt.Circuits.DCFlowNetworkBridge
