/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopy

@[expose] public section

namespace MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopyTest

open MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopy
open ContinuousLinearMap Filter Set

/-- The identity operator has index `0`. -/
private theorem index_one : (ContinuousLinearMap.id ℝ (ℝ × ℝ)).index = 0 :=
  LinearMap.index_id

/-- The scaling path `(1 + t) • id` on `ℓ² (ℕ, ℝ)`. -/
private noncomputable def scalePath (t : ℝ) :
    lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  (1 + t) • ContinuousLinearMap.id ℝ (lp (fun _ : ℕ => ℝ) 2)

/-- Each operator on the scaling path is Fredholm, since it is invertible:
`1 + t ≠ 0` for `t ∈ [0, 1]`. -/
private theorem scalePath_fredholm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (scalePath t).IsFredholm := by
  have hc : (1 + t) ≠ 0 := by linarith [ht.1]
  apply IsInvertible.isFredholm
  refine ⟨(Units.mk0 (1 + t) hc) • ContinuousLinearEquiv.refl ℝ
    (lp (fun _ : ℕ => ℝ) 2), ?_⟩
  ext x
  simp [scalePath]

/-- The scaling path is a continuous path of Fredholm operators whose index
is constant. The increment between endpoints is `id`, which is not
finite-rank on the infinite-dimensional space `ℓ² (ℕ, ℝ)`, so this genuinely
exercises the homotopy theorem rather than its finite-rank corollary. -/
example : (scalePath 0).index = (scalePath 1).index := by
  refine index_eq_of_continuous_path (γ := scalePath) ?_ ?_
  · exact (continuous_const.add continuous_id).smul continuous_const
  · intro t ht
    exact scalePath_fredholm ht

/-- The scaling path starts at the identity, whose index is `0`. -/
example : (scalePath 0).index = 0 := by
  have h0 : scalePath 0 = ContinuousLinearMap.id ℝ (lp (fun _ : ℕ => ℝ) 2) := by
    simp [scalePath]
  rw [h0]
  exact LinearMap.index_id

/-- A concrete nonzero rank-one operator on `ℝ × ℝ`: `F (a, b) = a • (0, 1)`. -/
private abbrev rankOneF : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (0, 1)

/-- The rank-one operator has finite range. -/
private theorem rankOneF_hasFiniteRange : rankOneF.toLinearMap.HasFiniteRange :=
  hasFiniteRange_smulRight

/-- The rank-one operator is nonzero: it sends `(1, 0)` to `(0, 1)`. -/
example : rankOneF (1, 0) = (0, 1) := by
  simp [rankOneF]

/-- Adding the rank-one operator to the identity does not change the index:
it stays `0`. -/
example : (ContinuousLinearMap.id ℝ (ℝ × ℝ) + rankOneF).index = 0 := by
  rw [index_add_hasFiniteRange IsFredholm.id rankOneF_hasFiniteRange]
  exact index_one

/-- Adding the rank-one operator to the identity stays Fredholm. -/
example : (ContinuousLinearMap.id ℝ (ℝ × ℝ) + rankOneF).IsFredholm :=
  IsFredholm.id.add_hasFiniteRange rankOneF_hasFiniteRange

/-- Subtracting the rank-one operator from the identity also preserves the
index `0`. -/
example : (ContinuousLinearMap.id ℝ (ℝ × ℝ) - rankOneF).index = 0 := by
  rw [index_sub_hasFiniteRange IsFredholm.id rankOneF_hasFiniteRange]
  exact index_one

/-- The `x`-axis in `ℝ × ℝ`, as a submodule. -/
private def xAxis : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ {(1, 0)}

/-- The `x`-axis is finite-dimensional. -/
private instance : FiniteDimensional ℝ xAxis :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)

/-- The `x`-axis is complemented: it is closed with finite-dimensional
quotient. -/
private theorem xAxis_closedComplemented : xAxis.ClosedComplemented :=
  Submodule.ClosedComplemented.of_finiteDimensional_quotient xAxis.closed_of_finiteDimensional

/-- The quotient map by the `x`-axis is Fredholm. -/
private theorem xAxis_mkQL_fredholm : xAxis.mkQL.IsFredholm :=
  Submodule.isFredholm_mkQL xAxis_closedComplemented

/-- The `x`-axis has rank `1`. -/
private theorem finrank_xAxis : Module.finrank ℝ xAxis = 1 := by
  rw [show xAxis = ℝ ∙ (1, 0) from rfl]
  exact finrank_span_singleton (by norm_num)

/-- The quotient map by the `x`-axis is Fredholm of index `1`
(the kernel is the one-dimensional `x`-axis). -/
private theorem index_xAxis_mkQL : (xAxis.mkQL).index = 1 := by
  rw [show xAxis.mkQL.toLinearMap = xAxis.mkQ from rfl, LinearMap.index_mkQ, finrank_xAxis]
  norm_num

/-- The embedding `(x, y) ↦ (0, (x, y))` of `ℝ × ℝ` into `ℝ × (ℝ × ℝ)`,
as a continuous linear map. Its cokernel is one-dimensional, so it has
Fredholm index `-1`. Unlike the quotient example above, every type here is
a product, so all instances are canonical. -/
private noncomputable abbrev embedInr : (ℝ × ℝ) →L[ℝ] ℝ × (ℝ × ℝ) :=
  (LinearIsometry.inr ℝ ℝ (ℝ × ℝ)).toContinuousLinearMap

/-- The embedding is Fredholm: it is a closed embedding (a linear
isometry) with finite-codimensional range. -/
private theorem embedInr_fredholm : embedInr.IsFredholm := by
  refine (Function.Injective.isFredholm_iff embedInr
    (LinearIsometry.inr ℝ ℝ (ℝ × ℝ)).injective).mpr
    ⟨(LinearIsometry.inr ℝ ℝ (ℝ × ℝ)).isometry.isClosedEmbedding,
      Submodule.CoFG.of_finite⟩

/-- The embedding has Fredholm index `-1`: its kernel is `⊥` and its
cokernel is identified with `ℝ` via the first-coordinate projection. -/
private theorem index_embedInr : embedInr.index = -1 := by
  have hinj : Function.Injective embedInr.toLinearMap :=
    (LinearIsometry.inr ℝ ℝ (ℝ × ℝ)).injective
  rw [LinearMap.index_of_injective hinj]
  have hfin : Module.finrank ℝ ((ℝ × (ℝ × ℝ)) ⧸ embedInr.toLinearMap.range) = 1 := by
    have hker : LinearMap.ker (LinearMap.fst ℝ ℝ (ℝ × ℝ)) = embedInr.toLinearMap.range := by
      rw [LinearMap.ker_fst]
      rfl
    have he : ((ℝ × (ℝ × ℝ)) ⧸ embedInr.toLinearMap.range) ≃ₗ[ℝ] ℝ := by
      rw [← hker]
      exact (LinearMap.fst ℝ ℝ (ℝ × ℝ)).quotKerEquivOfSurjective
        (fun y => ⟨(y, (0, 0)), rfl⟩)
    rw [he.finrank_eq]
    simp
  rw [hfin]
  norm_num

/-- A rank-one operator with the same domain and codomain as `embedInr`:
`(a, b) ↦ a • (1, (0, 0))`. -/
private abbrev embedRankOne : (ℝ × ℝ) →L[ℝ] ℝ × (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight ((1, (0, 0)) : ℝ × (ℝ × ℝ))

/-- The rank-one operator has finite range. -/
private theorem embedRankOne_hasFiniteRange :
    embedRankOne.toLinearMap.HasFiniteRange := hasFiniteRange_smulRight

/-- The rank-one operator is nonzero: it sends `(1, 0)` to `(1, (0, 0))`. -/
example : embedRankOne (1, 0) = ((1, (0, 0)) : ℝ × (ℝ × ℝ)) := by
  simp [embedRankOne]

/-- A rank-one perturbation of the embedding keeps the index `-1`. -/
example : (embedInr + embedRankOne).index = -1 := by
  have h : (embedInr + embedRankOne).index = embedInr.index :=
    index_add_hasFiniteRange embedInr_fredholm embedRankOne_hasFiniteRange
  rw [h, index_embedInr]

end MathlibExt.Analysis.Normed.Operator.FredholmIndexHomotopyTest
