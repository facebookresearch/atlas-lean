/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/LinearAlgebra/Determinant.lean` (Mathlib):
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

module

public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Trace additivity for an invariant submodule

For an endomorphism `e` of a finite-dimensional vector space `V` over a field
that preserves a submodule `W`, the trace of `e` is the sum of the trace of the
restriction to `W` and the trace of the induced map on the quotient `V ⧸ W`.

This is the trace analogue of `LinearMap.det_eq_det_mul_det`; the proof follows
the same block-basis pattern via `Module.Basis.sumQuot`.

ATLAS source and scope: this module is a prerequisite stage for ATLAS item
NumberTheoryI N261 (Theorem 12.27), whose different-valuation target is
defined and stated in
`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines 1237-1324, at
revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`
(<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324>).
Those ATLAS lines define and state the different-valuation target but do not
state these generic trace-additivity lemmas. Source-to-API map:
`LinearMap.trace_eq_trace_restrict_add_trace_mapQ`,
`LinearMap.trace_eq_trace_restrict_ker_add_of_surjective` are generic
prerequisites intended for the future step of iterating the trace across the
maximal-ideal quotient filtration.
This module is a prerequisite stage only, not the full N261 theorem: it proves
no different-ideal containment and no valuation bound. The ATLAS statement
`different_valuation_exact` (lines 1269-1276 there) is unfinished and false in
general wild ramification, so it is neither copied nor used here.
-/

open Module.Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **Trace is additive over an invariant subspace.** Let $V$ be a finite-dimensional vector space
over a field $K$, let $e$ be a linear endomorphism of $V$, and let $W$ be a subspace of $V$ with
$e(W) \subseteq W$. Then the trace of $e$ equals the trace of the restriction $e|_W$ of $e$ to $W$
plus the trace of the endomorphism $\bar e$ of the quotient $V/W$ induced by $e$:
$\operatorname{tr}(e) = \operatorname{tr}(e|_W) + \operatorname{tr}(\bar e)$. -/
theorem LinearMap.trace_eq_trace_restrict_add_trace_mapQ
    (W : Submodule K V) (e : V →ₗ[K] V) (he : W ≤ W.comap e) :
    LinearMap.trace K V e =
      LinearMap.trace K W (e.restrict he) +
        LinearMap.trace K (V ⧸ W) (W.mapQ W e he) := by
  let m := Module.Free.ChooseBasisIndex K W
  let bW : Module.Basis m K W := Module.Free.chooseBasis K W
  let n := Module.Free.ChooseBasisIndex K (V ⧸ W)
  let bQ : Module.Basis n K (V ⧸ W) := Module.Free.chooseBasis K (V ⧸ W)
  let b := sumQuot bW bQ
  have := Module.Free.ChooseBasisIndex.fintype K W
  have := Module.Free.ChooseBasisIndex.fintype K (V ⧸ W)
  let A : Matrix m m K := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n K := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n K := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  have hblock : LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
          LinearMap.toMatrix_apply]
        apply sumQuot_repr_inl_of_mem
      | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        suffices W.mkQ (e (bW k)) = 0 by
          simp [LinearMap.toMatrix_apply, b, this]
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact he (Submodule.coe_mem (bW k))
      | inr l =>
        simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  have htrace : Matrix.trace (Matrix.fromBlocks A B 0 D) =
      Matrix.trace A + Matrix.trace D := by
    simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  rw [LinearMap.trace_eq_matrix_trace K b e,
    LinearMap.trace_eq_matrix_trace K bW (e.restrict he),
    LinearMap.trace_eq_matrix_trace K bQ (W.mapQ W e he), hblock, htrace]

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- **Trace splits along a surjective intertwining map.** Let $V$ be a finite-dimensional vector
space over a field $K$, let $W$ be a vector space over $K$, and let $q : V \to W$ be a surjective
linear map. If $f$ is a linear endomorphism of $V$ and $g$ a linear endomorphism of $W$ with
$q \circ f = g \circ q$, then $f$ maps $\ker q$ into itself, and the trace of $f$ equals the
trace of the restriction $f|_{\ker q}$ of $f$ to $\ker q$ plus the trace of $g$. -/
theorem LinearMap.trace_eq_trace_restrict_ker_add_of_surjective
    (q : V →ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hq : Function.Surjective q) (h : q.comp f = g.comp q) :
    LinearMap.trace K V f =
      LinearMap.trace K (LinearMap.ker q)
        (f.restrict (by
          change LinearMap.ker q ≤ (LinearMap.ker q).comap f
          rw [← LinearMap.ker_comp f q, h]
          exact LinearMap.ker_le_ker_comp q g)) +
      LinearMap.trace K W g := by
  let hi : LinearMap.ker q ≤ (LinearMap.ker q).comap f := by
    rw [← LinearMap.ker_comp f q, h]
    exact LinearMap.ker_le_ker_comp q g
  let E := q.quotKerEquivOfSurjective hq
  have hc : E.conj ((LinearMap.ker q).mapQ (LinearMap.ker q) f hi) = g := by
    ext y
    obtain ⟨x, rfl⟩ := hq y
    simp only [E, LinearEquiv.conj_apply_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply,
      Submodule.mapQ_apply,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
    exact LinearMap.congr_fun h x
  rw [LinearMap.trace_eq_trace_restrict_add_trace_mapQ
    (LinearMap.ker q) f hi,
    ← LinearMap.trace_conj'
      ((LinearMap.ker q).mapQ (LinearMap.ker q) f hi) E, hc]
