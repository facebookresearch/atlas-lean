/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Prefix-causal operators

Given bounded projections `P t` on a normed space, an operator `G`
is *prefix causal* when the prefix of its output up to any `t`
depends only on the same prefix of the input:
`P t ∘L G = P t ∘L G ∘L P t` (`IsPrefixCausal`). When every `P t`
is idempotent, the prefix-causal operators form a unital
subalgebra of the bounded operators (`prefixCausalSubalgebra`);
only pointwise idempotence is needed, and a filtration law
`P s ∘L P t = P (s ⊓ t)` is one way to obtain it. The carrier is
closed in the operator norm (`isClosed_prefixCausalCarrier`), and
the Neumann series of a prefix-causal strict contraction is again
prefix causal (`IsPrefixCausal.tsum_pow`), so inverses of the form
`(1 - G)⁻¹` given by Neumann series stay prefix causal.
-/

open ContinuousLinearMap

@[expose] public section

namespace ControlTheory

/-- A bounded operator `G` is **prefix causal** with respect to a
filtration `P` of bounded projections when every prefix of the output
of `G` depends only on the same prefix of the input: `P t ∘ G` never
reads past `P t`, i.e. `P t ∘L G = P t ∘L G ∘L P t` for all `t`. This
is a prefix law, not a commutation law: the unit delay is prefix
causal but does not commute with the `P t`. -/
def IsPrefixCausal {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] {ι : Type*}
    (P : ι → X →L[𝕜] X) (G : X →L[𝕜] X) : Prop :=
  ∀ t, (P t).comp G = ((P t).comp G).comp (P t)

/-- The prefix-causal operators form a unital subalgebra of
`X →L[𝕜] X`: each constraint `P t ∘L G ∘L (1 - P t) = 0` is linear,
and for a product the inner projection is absorbed by either factor
(`P t ∘L G ∘L P t ∘L H = P t ∘L G ∘L H` by causality of `G`, then the
right projection by causality of `H`). Only pointwise idempotence of the `P t` is used; a filtration
law `P s ∘L P t = P (s ⊓ t)` is one way to obtain it. -/
def prefixCausalSubalgebra {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {ι : Type*}
    (P : ι → X →L[𝕜] X)
    (hP : ∀ t, (P t).comp (P t) = P t) :
    Subalgebra 𝕜 (X →L[𝕜] X) where
  carrier := {G | IsPrefixCausal P G}
  mul_mem' {G H} hG hH := by
    intro t
    ext x
    simp only [comp_apply]
    have e1 : (P t) (G (H x)) = (P t) (G ((P t) (H x))) := by
      have h := DFunLike.congr_fun (hG t) (H x)
      simpa [comp_apply] using h
    have e2 : (P t) (H x) = (P t) (H ((P t) x)) := by
      have h := DFunLike.congr_fun (hH t) x
      simpa [comp_apply] using h
    have e3 : (P t) (G (H ((P t) x)))
        = (P t) (G ((P t) (H ((P t) x)))) := by
      have h := DFunLike.congr_fun (hG t) (H ((P t) x))
      simpa [comp_apply] using h
    calc (P t) (G (H x)) = (P t) (G ((P t) (H x))) := e1
      _ = (P t) (G ((P t) (H ((P t) x)))) := by rw [e2]
      _ = (P t) (G (H ((P t) x))) := e3.symm
  one_mem' := by
    intro t
    have h : (P t).comp (P t) = P t := hP t
    ext x
    simp only [comp_apply]
    have h' := DFunLike.congr_fun h x
    simpa [comp_apply] using h'.symm
  add_mem' {G H} hG hH := by
    intro t
    ext x
    simp only [comp_apply, add_apply, map_add]
    have e1 := DFunLike.congr_fun (hG t) x
    have e2 := DFunLike.congr_fun (hH t) x
    simp only [comp_apply] at e1 e2
    rw [e1, e2]
  zero_mem' := by
    intro t
    simp
  algebraMap_mem' r := by
    intro t
    have h : (P t).comp (P t) = P t := hP t
    ext x
    simp only [comp_apply, ContinuousLinearMap.algebraMap_apply, map_smul]
    congr 1
    have h' := DFunLike.congr_fun h x
    simpa [comp_apply] using h'.symm

/-- The carrier of the prefix-causal subalgebra is norm-closed: it is
an intersection of closed conditions `P t ∘L G = P t ∘L G ∘L P t`,
both sides continuous in `G` in the operator norm. -/
theorem isClosed_prefixCausalCarrier {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {ι : Type*}
    (P : ι → X →L[𝕜] X) (hP : ∀ t, (P t).comp (P t) = P t) :
    IsClosed (prefixCausalSubalgebra P hP : Set (X →L[𝕜] X)) := by
  have hcarrier : (prefixCausalSubalgebra P hP : Set (X →L[𝕜] X))
      = ⋂ t, {G : X →L[𝕜] X | (P t).comp G = ((P t).comp G).comp (P t)} := by
    ext G
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [hcarrier]
  refine isClosed_iInter fun t => isClosed_eq ?_ ?_
  · exact continuous_id.const_clm_comp (P t)
  · exact (continuous_id.const_clm_comp (P t)).clm_comp_const (P t)

/-- Neumann-series inverses stay prefix causal: if `‖G‖ < 1` and `G`
is prefix causal on a Banach space, then the Neumann series
`∑' n, G ^ n` (the inverse of `1 - G`) is prefix causal, since its
partial sums are prefix causal and the carrier is closed. -/
theorem IsPrefixCausal.tsum_pow {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] {ι : Type*}
    (P : ι → X →L[𝕜] X) (hP : ∀ t, (P t).comp (P t) = P t)
    {G : X →L[𝕜] X} (hG : IsPrefixCausal P G) (hG1 : ‖G‖ < 1) :
    IsPrefixCausal P (∑' n : ℕ, G ^ n) := by
  have hsum : Summable (fun n : ℕ => G ^ n) := summable_geometric_of_norm_lt_one hG1
  have hmem : ∀ n : ℕ, (∑ i ∈ Finset.range n, G ^ i) ∈ prefixCausalSubalgebra P hP := by
    intro n
    refine (prefixCausalSubalgebra P hP).sum_mem ?_
    intro i _
    exact (prefixCausalSubalgebra P hP).pow_mem hG i
  have hlim := (isClosed_prefixCausalCarrier P hP).mem_of_tendsto hsum.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hmem)
  exact hlim

end ControlTheory
