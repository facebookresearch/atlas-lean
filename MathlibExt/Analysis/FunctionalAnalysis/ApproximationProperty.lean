/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The approximation property

A normed space has the *approximation property* if the identity operator can
be approximated, uniformly on compact sets, by finite-rank continuous linear
operators. This is the classical notion going back to Grothendieck: every
Banach space with a Schauder basis has the approximation property (the
partial-sum projections are finite-rank and converge pointwise, hence
uniformly on compact sets since they are uniformly bounded), and the
property passes to isomorphic spaces. We prove these two facts, the
finite-dimensional case, and the Hilbert-space case via a Hilbert basis
indexed by `ℕ`.

This is a companion to the Banach-space / basis material of
`v1/Atlas/IntroductionToFunctionalAnalysis` (in particular the Hamel-basis
definition and the Hilbert-space / orthonormal-basis material), not one of
the 72 v1 targets. Mathlib contains Schauder bases and Hilbert bases, but no
approximation-property statement. The converse is false in general: Enflo
constructed a Banach space without the approximation property.

## Main declarations

* `HasApproximationProperty` : the approximation property for a normed space.
* `hasApproximationProperty_of_finiteDimensional` : finite-dimensional spaces
  have the approximation property (the identity is finite-rank).
* `hasApproximationProperty_of_schauderBasis` : a Banach space with a
  Schauder basis has the approximation property.
* `HasApproximationProperty.of_continuousLinearEquiv` : the property is
  preserved under continuous linear equivalence.
* `HasApproximationProperty.of_complemented` : the property passes to
  complemented subspaces.
* `hasApproximationProperty_of_hilbertBasis` : a Hilbert space with a
  Hilbert basis indexed by `ℕ` has the approximation property.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ApproximationProperty

open scoped ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A normed space has the **approximation property** if, on every compact
set, the identity operator is a uniform limit of finite-rank continuous
linear operators. -/
def HasApproximationProperty (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] : Prop :=
  ∀ (K : Set E), IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ T : E →L[𝕜] E, FiniteDimensional 𝕜 ↥(LinearMap.range T.toLinearMap) ∧
      ∀ x ∈ K, ‖T x - x‖ < ε

/-- Finite-dimensional spaces have the approximation property: the identity
operator is itself finite-rank. -/
theorem hasApproximationProperty_of_finiteDimensional (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    HasApproximationProperty 𝕜 E := by
  intro K _ ε hε
  refine ⟨1, ?_, fun x _ => ?_⟩
  · have hrange : LinearMap.range (1 : E →L[𝕜] E).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr fun y => ⟨y, by simp⟩
    rw [hrange]
    infer_instance
  · simp [sub_self, hε]

/-- A Banach space with a Schauder basis has the approximation property.
The partial-sum projections are finite-rank, converge pointwise to the
identity, and are uniformly bounded by the Banach–Steinhaus theorem
(`SchauderBasis.exists_norm_proj_le`); pointwise convergence plus uniform
boundedness gives uniform convergence on compact sets via a finite
`ε`-net argument. -/
theorem hasApproximationProperty_of_schauderBasis {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (b : SchauderBasis 𝕜 E) :
    HasApproximationProperty 𝕜 E := by
  intro K hK ε hε
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    rw [SchauderBasis.proj_zero] at h0
    simpa using h0
  have hC1 : (0 : ℝ) < 2 * (C + 1) := by linarith
  have hδ : (0 : ℝ) < ε / (2 * (C + 1)) := div_pos hε hC1
  -- For each `y`, the projections approximate `y` eventually.
  have hstep : ∀ y : E, ∃ N : ℕ, ∀ n ≥ N, ‖b.proj n y - y‖ < ε / 2 := by
    intro y
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (b.tendsto_proj y) (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rwa [dist_eq_norm] at h
  choose N hN using hstep
  -- Cover `K` by finitely many balls of radius `ε / (2 * (C + 1))`.
  obtain ⟨t, htfin, ht⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded _ hδ
  set tf := htfin.toFinset with htf
  refine ⟨b.proj (tf.sup N), ?_, ?_⟩
  · -- The projection is finite-rank: its range is the span of the first
    -- `tf.sup N` basis vectors.
    rw [SchauderBasis.range_proj_eq_span]
    exact FiniteDimensional.span_of_finite _ (Set.Finite.image _ (Finset.finite_toSet _))
  · intro x hx
    obtain ⟨y, hyt, hyx⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hytf : y ∈ tf := (htfin.mem_toFinset).mpr hyt
    have hyN : N y ≤ tf.sup N := Finset.le_sup hytf
    have happrox : ‖b.proj (tf.sup N) y - y‖ < ε / 2 := hN y _ hyN
    have hdist : ‖x - y‖ < ε / (2 * (C + 1)) := by
      have h : dist x y < ε / (2 * (C + 1)) := Metric.mem_ball.mp hyx
      rwa [dist_eq_norm] at h
    calc ‖b.proj (tf.sup N) x - x‖
        = ‖b.proj (tf.sup N) (x - y) + (b.proj (tf.sup N) y - y) + (y - x)‖ := by
          congr 1
          rw [map_sub]
          abel
      _ ≤ ‖b.proj (tf.sup N) (x - y)‖ + ‖b.proj (tf.sup N) y - y‖ + ‖y - x‖ := by
          calc ‖b.proj (tf.sup N) (x - y) + (b.proj (tf.sup N) y - y) + (y - x)‖
              ≤ ‖b.proj (tf.sup N) (x - y) + (b.proj (tf.sup N) y - y)‖ + ‖y - x‖ :=
                norm_add_le _ _
            _ ≤ (‖b.proj (tf.sup N) (x - y)‖ + ‖b.proj (tf.sup N) y - y‖) + ‖y - x‖ := by
                gcongr
                exact norm_add_le _ _
            _ = ‖b.proj (tf.sup N) (x - y)‖ + ‖b.proj (tf.sup N) y - y‖ + ‖y - x‖ := by
                abel
      _ < C * (ε / (2 * (C + 1))) + ε / 2 + ε / (2 * (C + 1)) := by
          apply add_lt_add_of_lt_of_le
            (add_lt_add_of_le_of_lt ?_ happrox) ?_
          · calc ‖b.proj (tf.sup N) (x - y)‖
                ≤ ‖b.proj (tf.sup N)‖ * ‖x - y‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ C * (ε / (2 * (C + 1))) :=
                  mul_le_mul (hC _) hdist.le (norm_nonneg _) hC0
          · rw [norm_sub_rev]
            exact hdist.le
      _ = ε := by
          have hne : (2 : ℝ) * (C + 1) ≠ 0 := ne_of_gt hC1
          field_simp
          ring

/-- The approximation property is preserved under continuous linear
equivalence: conjugate a finite-rank approximant by the equivalence. -/
theorem HasApproximationProperty.of_continuousLinearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (h : HasApproximationProperty 𝕜 E) (e : E ≃L[𝕜] F) :
    HasApproximationProperty 𝕜 F := by
  intro K hK ε hε
  have hnorm : (0 : ℝ) ≤ ‖e.toContinuousLinearMap‖ := norm_nonneg _
  have hne : (‖e.toContinuousLinearMap‖ : ℝ) + 1 ≠ 0 :=
    ne_of_gt (by linarith)
  have hε' : (0 : ℝ) < ε / (‖e.toContinuousLinearMap‖ + 1) :=
    div_pos hε (by linarith)
  obtain ⟨S, hSfin, hS⟩ := h (e.symm '' K) (hK.image e.symm.continuous)
    (ε / (‖e.toContinuousLinearMap‖ + 1)) hε'
  refine ⟨e.toContinuousLinearMap ∘L S ∘L e.symm.toContinuousLinearMap, ?_, ?_⟩
  · -- The conjugate has finite rank: its range is contained in the image
    -- under `e` of the range of `S`.
    have hle : LinearMap.range
        (e.toContinuousLinearMap ∘L S ∘L e.symm.toContinuousLinearMap).toLinearMap ≤
        Submodule.map e.toContinuousLinearMap.toLinearMap (LinearMap.range S.toLinearMap) := by
      rintro z ⟨y, rfl⟩
      refine Submodule.mem_map.mpr ⟨S (e.symm y), LinearMap.mem_range_self _ _, ?_⟩
      simp
    have hfin : FiniteDimensional 𝕜
        ↥(Submodule.map e.toContinuousLinearMap.toLinearMap (LinearMap.range S.toLinearMap)) :=
      inferInstance
    exact Submodule.finiteDimensional_of_le hle
  · intro y hy
    have hmem : e.symm y ∈ e.symm '' K := ⟨y, hy, rfl⟩
    have hS' := hS (e.symm y) hmem
    have happ : e.toContinuousLinearMap (e.symm y) = y := by simp
    have hEq : (e.toContinuousLinearMap ∘L S ∘L e.symm.toContinuousLinearMap) y - y
        = e.toContinuousLinearMap (S (e.symm y) - e.symm y) := by
      have hT : (e.toContinuousLinearMap ∘L S ∘L e.symm.toContinuousLinearMap) y
          = e.toContinuousLinearMap (S (e.symm y)) := by
        simp [ContinuousLinearMap.comp_apply]
      calc (e.toContinuousLinearMap ∘L S ∘L e.symm.toContinuousLinearMap) y - y
          = e.toContinuousLinearMap (S (e.symm y))
              - e.toContinuousLinearMap (e.symm y) := by rw [hT, happ]
        _ = e.toContinuousLinearMap (S (e.symm y) - e.symm y) := by rw [map_sub]
    calc ‖(e.toContinuousLinearMap ∘L S ∘L e.symm.toContinuousLinearMap) y - y‖
        = ‖e.toContinuousLinearMap (S (e.symm y) - e.symm y)‖ := by rw [hEq]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖S (e.symm y) - e.symm y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖e.toContinuousLinearMap‖ * (ε / (‖e.toContinuousLinearMap‖ + 1)) :=
          mul_le_mul_of_nonneg_left hS'.le hnorm
      _ < (‖e.toContinuousLinearMap‖ + 1) * (ε / (‖e.toContinuousLinearMap‖ + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one _) hε'
      _ = ε := by field_simp

/-- The approximation property passes to complemented subspaces: if `P` is a
continuous projection onto the submodule `F`, restrict a finite-rank
approximant on the ambient space via `P`. The key point is that `P` fixes
every point of `F`, so `P (S x) - x = P (S x - x)` for `x ∈ F`. -/
theorem HasApproximationProperty.of_complemented {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (h : HasApproximationProperty 𝕜 E) {F : Submodule 𝕜 E}
    (P : E →L[𝕜] E) (hPid : ∀ x, P (P x) = P x)
    (hPrange : LinearMap.range P.toLinearMap = F) :
    HasApproximationProperty 𝕜 ↥F := by
  intro K hK ε hε
  have hnorm : (0 : ℝ) ≤ ‖P‖ := norm_nonneg _
  have hne : (‖P‖ : ℝ) + 1 ≠ 0 := ne_of_gt (by linarith)
  have hε' : (0 : ℝ) < ε / (‖P‖ + 1) := div_pos hε (by linarith)
  obtain ⟨S, hSfin, hS⟩ := h (Subtype.val '' K) (hK.image continuous_subtype_val)
    (ε / (‖P‖ + 1)) hε'
  -- The restricted approximant: `P ∘L S ∘L subtype`, corestricted to `F`.
  have hmemF : ∀ x : ↥F, (P ∘L S ∘L F.subtypeL) x ∈ F := by
    intro x
    have hval : (P ∘L S ∘L F.subtypeL) x = P (S (x : E)) := by
      simp [ContinuousLinearMap.comp_apply]
    rw [hval]
    have hmem : P (S (x : E)) ∈ LinearMap.range P.toLinearMap :=
      LinearMap.mem_range_self _ _
    rwa [hPrange] at hmem
  set T : ↥F →L[𝕜] ↥F := (P ∘L S ∘L F.subtypeL).codRestrict F hmemF with hTdef
  refine ⟨T, ?_, ?_⟩
  · -- Finite rank: the range of `T` is contained in the preimage, under the
    -- inclusion of `F`, of the image under `P` of the range of `S`.
    have hle : LinearMap.range T.toLinearMap ≤
        Submodule.comap F.subtype
          (Submodule.map P.toLinearMap (LinearMap.range S.toLinearMap)) := by
      rintro y ⟨x, rfl⟩
      have hcoe : ((T x : ↥F) : E) = P (S (x : E)) := by
        rw [ContinuousLinearMap.coe_codRestrict_apply]
        simp [ContinuousLinearMap.comp_apply]
      rw [Submodule.mem_comap]
      show ((T x : ↥F) : E) ∈ Submodule.map P.toLinearMap (LinearMap.range S.toLinearMap)
      rw [hcoe]
      exact Submodule.mem_map.mpr ⟨S (x : E), LinearMap.mem_range_self _ _, rfl⟩
    have hfin : FiniteDimensional 𝕜 ↥(Submodule.comap F.subtype
        (Submodule.map P.toLinearMap (LinearMap.range S.toLinearMap))) := by
      have hkerfin : FiniteDimensional 𝕜 ↥(LinearMap.ker F.subtype) := by
        rw [Submodule.ker_subtype]
        infer_instance
      infer_instance
    exact Submodule.finiteDimensional_of_le hle
  · intro x hx
    have hTx : ((T x : ↥F) : E) = P (S (x : E)) := by
      rw [ContinuousLinearMap.coe_codRestrict_apply]
      simp [ContinuousLinearMap.comp_apply]
    have hPx : P (x : E) = (x : E) := by
      have hxF : (x : E) ∈ LinearMap.range P.toLinearMap := by
        rw [hPrange]
        exact x.2
      obtain ⟨z, hz⟩ := hxF
      rw [← hz]
      exact hPid z
    have hS' : ‖S (x : E) - (x : E)‖ < ε / (‖P‖ + 1) :=
      hS (x : E) ⟨x, hx, rfl⟩
    calc ‖T x - x‖
        = ‖((T x : ↥F) : E) - (x : E)‖ := by
          rw [← Submodule.norm_coe, Submodule.coe_sub]
      _ = ‖P (S (x : E)) - P (x : E)‖ := by rw [hTx, hPx]
      _ = ‖P (S (x : E) - (x : E))‖ := by rw [map_sub]
      _ ≤ ‖P‖ * ‖S (x : E) - (x : E)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖P‖ * (ε / (‖P‖ + 1)) :=
          mul_le_mul_of_nonneg_left hS'.le hnorm
      _ < (‖P‖ + 1) * (ε / (‖P‖ + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one _) hε'
      _ = ε := by field_simp

/-- A Hilbert space with a Hilbert basis indexed by `ℕ` has the approximation
property, via the associated Schauder basis
(`HilbertBasis.toSchauderBasis`). -/
theorem hasApproximationProperty_of_hilbertBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (b : HilbertBasis ℕ 𝕜 E) :
    HasApproximationProperty 𝕜 E :=
  hasApproximationProperty_of_schauderBasis b.toSchauderBasis

end MathlibExt.Analysis.FunctionalAnalysis.ApproximationProperty
