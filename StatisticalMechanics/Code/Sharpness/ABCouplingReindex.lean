/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.ABClusterCondition
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Finset SimpleGraph

namespace StatMech
namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abcrEndpointSum (F : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => F x + F y, fun x y => by ring⟩

@[simp] theorem abcrEndpointSum_mk (F : V → ℝ) (x y : V) :
    abcrEndpointSum F s(x, y) = F x + F y := rfl



noncomputable def abcrIncidentCoupling (J : Sym2 V → ℝ) (x : V) : ℝ :=
  ∑ d : {d : G.Dart // d.fst = x}, J d.1.edge



theorem abcr_edgeSum_eq_dartSum (J : Sym2 V → ℝ) (F : V → ℝ) :
    ∑ e ∈ G.edgeFinset, J e * abcrEndpointSum F e =
      ∑ d : G.Dart, J d.edge * F d.fst := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
    (g := fun d : G.Dart => d.edge)
    (fun d _ => by simpa only [mem_edgeFinset] using d.edge_mem)
    (fun d : G.Dart => J d.edge * F d.fst)]
  apply Finset.sum_congr rfl
  intro e he
  rw [mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : G.Adj x y := he
      let d : G.Dart := ⟨(x, y), hxy⟩
      have hfiber : (Finset.univ.filter fun d' : G.Dart => d'.edge = s(x, y)) =
          {d, d.symm} := by
        change ({d' : G.Dart | d'.edge = d.edge} : Finset G.Dart) = {d, d.symm}
        exact d.edge_fiber
      rw [hfiber, Finset.sum_insert (by simpa using d.symm_ne.symm), Finset.sum_singleton]
      simp [d, abcrEndpointSum]
      rw [Sym2.eq_swap]
      ring



theorem abcr_dartSum_eq_vertexSum (J : Sym2 V → ℝ) (F : V → ℝ) :
    ∑ d : G.Dart, J d.edge * F d.fst =
      ∑ x : V, F x * abcrIncidentCoupling G J x := by
  rw [← Fintype.sum_fiberwise (fun d : G.Dart => d.fst)
    (fun d : G.Dart => J d.edge * F d.fst)]
  apply Finset.sum_congr rfl
  intro x _
  unfold abcrIncidentCoupling
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [d.2]
  ring




theorem abcr_edgeSum_eq_rowSum (J : Sym2 V → ℝ) (F : V → ℝ) (J0 : ℝ)
    (hrow : ∀ x, abcrIncidentCoupling G J x = J0) :
    ∑ e ∈ G.edgeFinset, J e * abcrEndpointSum F e = J0 * ∑ x : V, F x := by
  rw [abcr_edgeSum_eq_dartSum G, abcr_dartSum_eq_vertexSum G]
  simp_rw [hrow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring




theorem abcr_edgeSum_le_rowSum (J : Sym2 V → ℝ) (F : V → ℝ) (J0 : ℝ)
    (hF : ∀ x, 0 ≤ F x)
    (hrow : ∀ x, abcrIncidentCoupling G J x ≤ J0) :
    ∑ e ∈ G.edgeFinset, J e * abcrEndpointSum F e ≤
      J0 * ∑ x : V, F x := by
  rw [abcr_edgeSum_eq_dartSum G, abcr_dartSum_eq_vertexSum G]
  calc
    (∑ x : V, F x * abcrIncidentCoupling G J x) ≤
        ∑ x : V, F x * J0 := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hrow x) (hF x)
    _ = J0 * ∑ x : V, F x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end Sharpness
end StatMech
