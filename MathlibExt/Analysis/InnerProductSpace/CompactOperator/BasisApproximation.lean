/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Order.Filter.AtTopBot.Prod

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Fixed-basis approximation of compact Hilbert-space operators

The existing unconditional Schauder-basis projections of a Hilbert basis
are its finite-span orthogonal projections. Their norms are at most one,
including empty spans and zero spaces. Two independent finite-set nets
therefore sandwich an actual compact operator in the original operator norm.

The proof reuses the closure of the span of all rank-one maps. Compactness
is essential: on an infinite-dimensional space the finite projections need
not converge to identity in operator norm on all bounded operators.
-/

namespace HilbertBasis

universe u𝕜 uE uF uι uκ

open Filter
open scoped Topology InnerProductSpace

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable {ι : Type uι} {κ : Type uκ}

/-- Let `𝕜` be a real or complex scalar field and let `E` be a normed inner-product space over `𝕜`
with a specified Hilbert basis. The projected coordinate set is finite. The Hilbert-basis index
types are arbitrary, and coordinate truncations are indexed by their finite subsets.

A finite Hilbert-basis projection is the sum of its rank-one projections. The scalar is any
RCLike field; empty sets and arbitrary basis index types are included. -/
public theorem proj_eq_sum_rankOne (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    b.toUnconditionalSchauderBasis.proj s =
      ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (b i) (b i) := by
  change (∑ i ∈ s, (innerSL 𝕜 (b i)).smulRight (b i)) = _
  simp only [InnerProductSpace.rankOne_def]

private theorem rankOne_sub_norm_le (x x' : F) (y y' : E) :
    ‖InnerProductSpace.rankOne 𝕜 x' y' - InnerProductSpace.rankOne 𝕜 x y‖ ≤
      ‖x' - x‖ * ‖y'‖ + ‖x‖ * ‖y' - y‖ := by
  have hSplit :
      InnerProductSpace.rankOne 𝕜 x' y' - InnerProductSpace.rankOne 𝕜 x y =
        InnerProductSpace.rankOne 𝕜 (x' - x) y' +
          InnerProductSpace.rankOne 𝕜 x (y' - y) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [sub_apply, add_apply,
      InnerProductSpace.rankOne_apply, inner_sub_left, smul_sub, sub_smul]
    abel
  rw [hSplit]
  exact (norm_add_le _ _).trans_eq (by
    rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne])

variable [CompleteSpace E]

/-- Let `𝕜` be a real or complex scalar field and let `E` be a normed inner-product space over `𝕜`
with a specified Hilbert basis. The projected coordinate set is finite. Assume `E` is complete.
The Hilbert-basis index types are arbitrary, and coordinate truncations are indexed by their
finite subsets.

Every finite Hilbert-basis projection is contractive and self-adjoint. The adjoint type uses the
ambient completeness instance. -/
public theorem proj_bounds (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    ‖b.toUnconditionalSchauderBasis.proj s‖ ≤ 1 ∧
      (b.toUnconditionalSchauderBasis.proj s).adjoint =
        b.toUnconditionalSchauderBasis.proj s := by
  classical
  let U : Submodule 𝕜 E := Submodule.span 𝕜 (s.image b : Set E)
  let : FiniteDimensional 𝕜 U := FiniteDimensional.span_finset 𝕜 (s.image b)
  let : CompleteSpace U := FiniteDimensional.complete 𝕜 U
  have hU : U.starProjection = b.toUnconditionalSchauderBasis.proj s := by
    calc
      U.starProjection =
          ∑ i : s, InnerProductSpace.rankOne 𝕜 (b (i : ι)) (b (i : ι)) := by
        simpa only [OrthonormalBasis.span_apply] using
          (OrthonormalBasis.span b.orthonormal s).starProjection_eq_sum_rankOne
      _ = ∑ i ∈ s, InnerProductSpace.rankOne 𝕜 (b i) (b i) :=
        Finset.sum_coe_sort s (fun i : ι => InnerProductSpace.rankOne 𝕜 (b i) (b i))
      _ = b.toUnconditionalSchauderBasis.proj s := (proj_eq_sum_rankOne b s).symm
  constructor
  · rw [← hU]
    exact U.starProjection_norm_le
  · rw [← hU]
    change IsSelfAdjoint U.starProjection
    exact isSelfAdjoint_starProjection U

variable [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Let `𝕜` be a real or complex scalar field and let `E` and `F` be normed inner-product spaces
over `𝕜`, equipped with the specified Hilbert bases. The coordinate subsets are finite. The
Hilbert-basis index types are arbitrary, and coordinate truncations are indexed by their finite
subsets.

Finite projections in two independent Hilbert bases contract the operator norm. Completeness is
obtained from each Hilbert basis; no ambient completeness hypothesis or compactness of the
bounded operator is needed. -/
public theorem norm_sandwich_le
    (bE : HilbertBasis ι 𝕜 E) (bF : HilbertBasis κ 𝕜 F)
    (T : E →L[𝕜] F) (s : Finset ι) (t : Finset κ) :
    ‖(bF.toUnconditionalSchauderBasis.proj t).comp
        (T.comp (bE.toUnconditionalSchauderBasis.proj s))‖ ≤ ‖T‖ := by
  let : CompleteSpace E := bE.repr.toIsometryEquiv.completeSpace
  let : CompleteSpace F := bF.repr.toIsometryEquiv.completeSpace
  have hRight : ‖T.comp (bE.toUnconditionalSchauderBasis.proj s)‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖T‖ * ‖bE.toUnconditionalSchauderBasis.proj s‖ := T.opNorm_comp_le _
      _ ≤ ‖T‖ * 1 :=
        mul_le_mul_of_nonneg_left (proj_bounds bE s).1 (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  calc
    _ ≤ ‖bF.toUnconditionalSchauderBasis.proj t‖ *
        ‖T.comp (bE.toUnconditionalSchauderBasis.proj s)‖ :=
      (bF.toUnconditionalSchauderBasis.proj t).opNorm_comp_le _
    _ ≤ 1 * ‖T‖ :=
      mul_le_mul (proj_bounds bF t).1 hRight (norm_nonneg _) zero_le_one
    _ = ‖T‖ := one_mul _

omit [CompleteSpace F] in
private theorem tendsto_rankOne_sandwich
    (bE : HilbertBasis ι 𝕜 E) (bF : HilbertBasis κ 𝕜 F) (x : F) (y : E) :
    Tendsto (fun st : Finset ι × Finset κ =>
      (bF.toUnconditionalSchauderBasis.proj st.2).comp
        ((InnerProductSpace.rankOne 𝕜 x y).comp
          (bE.toUnconditionalSchauderBasis.proj st.1)))
      atTop (𝓝 (InnerProductSpace.rankOne 𝕜 x y)) := by
  have hFst : Tendsto (Prod.fst : Finset ι × Finset κ → Finset ι) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hSnd : Tendsto (Prod.snd : Finset ι × Finset κ → Finset κ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hqx : Tendsto (fun st : Finset ι × Finset κ =>
      bF.toUnconditionalSchauderBasis.proj st.2 x) atTop (𝓝 x) :=
    (bF.toUnconditionalSchauderBasis.tendsto_proj x).comp hSnd
  have hpy : Tendsto (fun st : Finset ι × Finset κ =>
      bE.toUnconditionalSchauderBasis.proj st.1 y) atTop (𝓝 y) :=
    (bE.toUnconditionalSchauderBasis.tendsto_proj y).comp hFst
  have hxError : Tendsto (fun st : Finset ι × Finset κ =>
      ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖) atTop (𝓝 0) := by
    have hxConst : Tendsto (fun _ : Finset ι × Finset κ => x) atTop (𝓝 x) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hqx.sub hxConst).norm
  have hyError : Tendsto (fun st : Finset ι × Finset κ =>
      ‖bE.toUnconditionalSchauderBasis.proj st.1 y - y‖) atTop (𝓝 0) := by
    have hyConst : Tendsto (fun _ : Finset ι × Finset κ => y) atTop (𝓝 y) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hpy.sub hyConst).norm
  have hBound : ∀ st : Finset ι × Finset κ,
      ‖InnerProductSpace.rankOne 𝕜
          (bF.toUnconditionalSchauderBasis.proj st.2 x)
          (bE.toUnconditionalSchauderBasis.proj st.1 y) -
        InnerProductSpace.rankOne 𝕜 x y‖ ≤
      ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖ * ‖y‖ +
        ‖x‖ * ‖bE.toUnconditionalSchauderBasis.proj st.1 y - y‖ := by
    intro st
    have hpyNorm : ‖bE.toUnconditionalSchauderBasis.proj st.1 y‖ ≤ ‖y‖ := by
      calc
        _ ≤ ‖bE.toUnconditionalSchauderBasis.proj st.1‖ * ‖y‖ :=
          (bE.toUnconditionalSchauderBasis.proj st.1).le_opNorm y
        _ ≤ 1 * ‖y‖ :=
          mul_le_mul_of_nonneg_right (proj_bounds bE st.1).1 (norm_nonneg y)
        _ = ‖y‖ := one_mul _
    have hProduct :
        ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖ *
            ‖bE.toUnconditionalSchauderBasis.proj st.1 y‖ ≤
          ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖ * ‖y‖ :=
      mul_le_mul_of_nonneg_left hpyNorm
        (norm_nonneg (bF.toUnconditionalSchauderBasis.proj st.2 x - x))
    have hAdd :
        ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖ *
            ‖bE.toUnconditionalSchauderBasis.proj st.1 y‖ +
          ‖x‖ * ‖bE.toUnconditionalSchauderBasis.proj st.1 y - y‖ ≤
        ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖ * ‖y‖ +
          ‖x‖ * ‖bE.toUnconditionalSchauderBasis.proj st.1 y - y‖ :=
      add_le_add hProduct
        (le_refl (‖x‖ * ‖bE.toUnconditionalSchauderBasis.proj st.1 y - y‖))
    exact (rankOne_sub_norm_le (𝕜 := 𝕜) x
      (bF.toUnconditionalSchauderBasis.proj st.2 x) y
      (bE.toUnconditionalSchauderBasis.proj st.1 y)).trans hAdd
  have hBoundLimit : Tendsto (fun st : Finset ι × Finset κ =>
      ‖bF.toUnconditionalSchauderBasis.proj st.2 x - x‖ * ‖y‖ +
        ‖x‖ * ‖bE.toUnconditionalSchauderBasis.proj st.1 y - y‖)
      atTop (𝓝 0) := by
    have hY : Tendsto (fun _ : Finset ι × Finset κ => ‖y‖) atTop (𝓝 ‖y‖) :=
      tendsto_const_nhds
    have hX : Tendsto (fun _ : Finset ι × Finset κ => ‖x‖) atTop (𝓝 ‖x‖) :=
      tendsto_const_nhds
    simpa only [zero_mul, mul_zero, zero_add] using
      (hxError.mul hY).add (hX.mul hyError)
  have hNormLimit := squeeze_zero (fun _ => norm_nonneg _) hBound hBoundLimit
  have hRankLimit : Tendsto (fun st : Finset ι × Finset κ =>
      InnerProductSpace.rankOne 𝕜
        (bF.toUnconditionalSchauderBasis.proj st.2 x)
        (bE.toUnconditionalSchauderBasis.proj st.1 y))
      atTop (𝓝 (InnerProductSpace.rankOne 𝕜 x y)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    simpa only [dist_eq_norm] using hNormLimit.eventually_lt_const hε
  have hSandwich (st : Finset ι × Finset κ) :
      (bF.toUnconditionalSchauderBasis.proj st.2).comp
        ((InnerProductSpace.rankOne 𝕜 x y).comp
          (bE.toUnconditionalSchauderBasis.proj st.1)) =
      InnerProductSpace.rankOne 𝕜
        (bF.toUnconditionalSchauderBasis.proj st.2 x)
        (bE.toUnconditionalSchauderBasis.proj st.1 y) := by
    rw [InnerProductSpace.rankOne_comp, (proj_bounds bE st.1).2,
      InnerProductSpace.comp_rankOne]
  simpa only [hSandwich] using hRankLimit

omit [CompleteSpace F] in
private theorem tendsto_sandwich_of_mem_finiteRankSubmodule
    (bE : HilbertBasis ι 𝕜 E) (bF : HilbertBasis κ 𝕜 F)
    {T : E →L[𝕜] F}
    (hT : T ∈ InnerProductSpace.finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F)) :
    Tendsto (fun st : Finset ι × Finset κ =>
      (bF.toUnconditionalSchauderBasis.proj st.2).comp
        (T.comp (bE.toUnconditionalSchauderBasis.proj st.1))) atTop (𝓝 T) := by
  change T ∈ Submodule.span 𝕜
    (Set.range fun p : F × E => InnerProductSpace.rankOne 𝕜 p.1 p.2) at hT
  refine Submodule.span_induction
    (p := fun (S : E →L[𝕜] F) _ =>
      Tendsto (fun st : Finset ι × Finset κ =>
        (bF.toUnconditionalSchauderBasis.proj st.2).comp
          (S.comp (bE.toUnconditionalSchauderBasis.proj st.1))) atTop (𝓝 S))
    ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact tendsto_rankOne_sandwich bE bF x y
  · simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : Finset ι × Finset κ => (0 : E →L[𝕜] F)) atTop (𝓝 0))
  · intro S T _ _ hS hT
    simpa only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using hS.add hT
  · intro c S _ hS
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
      hS.const_smul c

@[expose] public section

omit [CompleteSpace E] [CompleteSpace F] in
/-- Let `𝕜` be a real or complex scalar field and let `E` and `F` be normed inner-product spaces
over `𝕜`, equipped with the specified Hilbert bases. The coordinate subsets are finite. Assume
the continuous linear map `T : E →L[𝕜] F` is compact. The Hilbert-basis index types are
arbitrary, and coordinate truncations are indexed by their finite subsets.

For independent Hilbert bases, their finite-span projections sandwich a compact map to itself in
the operator norm. Both index types are arbitrary; no separability, nonzero-space or
approximation-property assumption is needed. Completeness is derived from the supplied basis
representations; callers need no separate completeness instances. The existing basis projections
are reused. -/
theorem tendsto_compact_sandwich
    (bE : HilbertBasis ι 𝕜 E) (bF : HilbertBasis κ 𝕜 F)
    {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    Tendsto (fun st : Finset ι × Finset κ =>
      (bF.toUnconditionalSchauderBasis.proj st.2).comp
        (T.comp (bE.toUnconditionalSchauderBasis.proj st.1))) atTop (𝓝 T) := by
  let : CompleteSpace E := bE.repr.toIsometryEquiv.completeSpace
  let : CompleteSpace F := bF.repr.toIsometryEquiv.completeSpace
  have hClosure := hT.mem_topologicalClosure_finiteRankSubmodule
  change T ∈ closure
    (InnerProductSpace.finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F) :
      Set (E →L[𝕜] F)) at hClosure
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hThird : 0 < ε / 3 := div_pos hε (by linarith)
  obtain ⟨A, hA, hClose⟩ := Metric.mem_closure_iff.mp hClosure (ε / 3) hThird
  have hAEvent := Metric.tendsto_nhds.mp
    (tendsto_sandwich_of_mem_finiteRankSubmodule bE bF hA) (ε / 3) hThird
  have hDifference (st : Finset ι × Finset κ) :
      dist ((bF.toUnconditionalSchauderBasis.proj st.2).comp
          (T.comp (bE.toUnconditionalSchauderBasis.proj st.1)))
        ((bF.toUnconditionalSchauderBasis.proj st.2).comp
          (A.comp (bE.toUnconditionalSchauderBasis.proj st.1))) ≤ dist T A := by
    rw [dist_eq_norm, dist_eq_norm]
    simpa only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub] using
      norm_sandwich_le bE bF (T - A) st.1 st.2
  filter_upwards [hAEvent] with st hst
  have hTriangle := dist_triangle4
    ((bF.toUnconditionalSchauderBasis.proj st.2).comp
      (T.comp (bE.toUnconditionalSchauderBasis.proj st.1)))
    ((bF.toUnconditionalSchauderBasis.proj st.2).comp
      (A.comp (bE.toUnconditionalSchauderBasis.proj st.1))) A T
  rw [dist_comm A T] at hTriangle
  linarith [hDifference st]

end

end HilbertBasis
