/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

open scoped LinearMap.FiniteRangeSetoid

open ContinuousLinearMap Set

namespace MathlibExt.Analysis.InnerProductSpace.DirectSumOperators

/-!
# Direct sum operators

For bounded operators `T : E →L[𝕜] E'` and `S : F →L[𝕜] F'`, the direct sum
operator `T.prodMap S : E × F →L[𝕜] E' × F'` acts componentwise. This file
collects its basic properties: the algebra laws, the operator norm, the
kernel and range, invertibility, the spectrum, compactness, and Fredholmness
with its index.

This is a companion to the v1 book's operator material
(`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`SpectralTheory.lean`): the book treats single operators, and none of its
72 targets states anything about direct sums of operators. The results here
are the standard "block-diagonal" facts used throughout spectral theory; in
particular the spectrum of a direct sum is the union of the spectra, and
the Fredholm index is additive.

Main results:

* `norm_prodMap`: `‖T.prodMap S‖ = max ‖T‖ ‖S‖`.
* `ker_prodMap` / `range_prodMap`: kernel and range are componentwise.
* `isUnit_prodMap_iff`: a direct sum is a unit iff both summands are.
* `spectrum_prodMap`: `spectrum 𝕜 (T.prodMap S) = spectrum 𝕜 T ∪ spectrum 𝕜 S`,
  plus `resolventSet_prodMap`.
* `isCompactOperator_prodMap_iff`: a direct sum is compact iff both summands are.
* `isFredholm_prodMap_iff`: a direct sum is Fredholm iff both summands are,
  plus `index_prodMap`: the Fredholm index is additive.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Composing direct sums is componentwise. -/
theorem prodMap_comp {E'' F'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
    (T : E' →L[𝕜] E'') (S : F' →L[𝕜] F'') (T' : E →L[𝕜] E') (S' : F →L[𝕜] F') :
    (T.prodMap S) ∘L (T'.prodMap S') = (T ∘L T').prodMap (S ∘L S') := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => rfl

/-- The identity direct sum is the identity. -/
theorem prodMap_one : (1 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) = 1 := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => rfl

/-- The zero direct sum is zero. -/
theorem prodMap_zero : (0 : E →L[𝕜] E').prodMap (0 : F →L[𝕜] F') = 0 := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => rfl

/-- Scaling a direct sum scales both summands by the same factor. -/
theorem prodMap_smul (c : 𝕜) (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (c • T).prodMap (c • S) = c • (T.prodMap S) := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => rfl

/-- The first projection commutes with direct sums. -/
private theorem fst_comp_prodMap (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (fst 𝕜 E' F') ∘L (T.prodMap S) = T ∘L (fst 𝕜 E F) := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => rfl

/-- The second projection commutes with direct sums. -/
private theorem snd_comp_prodMap (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (snd 𝕜 E' F') ∘L (T.prodMap S) = S ∘L (snd 𝕜 E F) := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => rfl

/-- A direct sum followed by the first inclusion is the first inclusion
followed by the first summand. -/
private theorem prodMap_comp_inl (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (T.prodMap S) ∘L (inl 𝕜 E F) = (inl 𝕜 E' F') ∘L T := by
  refine ContinuousLinearMap.ext fun x => Prod.ext rfl (map_zero S)

/-- A direct sum followed by the second inclusion is the second inclusion
followed by the second summand. -/
private theorem prodMap_comp_inr (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (T.prodMap S) ∘L (inr 𝕜 E F) = (inr 𝕜 E' F') ∘L S := by
  refine ContinuousLinearMap.ext fun y => Prod.ext (map_zero T) rfl

/-- The operator norm of a direct sum is the maximum of the operator norms. -/
theorem norm_prodMap (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    ‖T.prodMap S‖ = max ‖T‖ ‖S‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (M := max ‖T‖ ‖S‖)
      (le_trans (norm_nonneg _) (le_max_left _ _)) ?_
    intro ⟨x, y⟩
    simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply, Prod.norm_mk]
    refine max_le ?_ ?_
    · calc ‖T x‖ ≤ ‖T‖ * ‖x‖ := le_opNorm T x
        _ ≤ max ‖T‖ ‖S‖ * max ‖x‖ ‖y‖ :=
          mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _)
            (le_trans (norm_nonneg _) (le_max_left _ _))
    · calc ‖S y‖ ≤ ‖S‖ * ‖y‖ := le_opNorm S y
        _ ≤ max ‖T‖ ‖S‖ * max ‖x‖ ‖y‖ :=
          mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _)
            (le_trans (norm_nonneg _) (le_max_right _ _))
  · refine max_le ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (M := ‖T.prodMap S‖) (norm_nonneg _) ?_
      intro x
      have h := (T.prodMap S).le_opNorm (x, (0 : F))
      simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply, map_zero, Prod.norm_mk,
        norm_zero, max_eq_left (norm_nonneg (T x)), max_eq_left (norm_nonneg x)] at h
      exact h
    · refine ContinuousLinearMap.opNorm_le_bound _ (M := ‖T.prodMap S‖) (norm_nonneg _) ?_
      intro y
      have h := (T.prodMap S).le_opNorm ((0 : E), y)
      simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply, map_zero, Prod.norm_mk,
        norm_zero, max_eq_right (norm_nonneg (S y)), max_eq_right (norm_nonneg y)] at h
      exact h

/-- The kernel of a direct sum is the product of the kernels. -/
theorem ker_prodMap (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (T.prodMap S).ker = T.ker.prod S.ker := by
  show LinearMap.ker (T.prodMap S : (E × F) →ₗ[𝕜] (E' × F')) = _
  rw [ContinuousLinearMap.coe_prodMap, LinearMap.ker_prodMap]

/-- The range of a direct sum is the product of the ranges. -/
theorem range_prodMap (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (T.prodMap S).range = T.range.prod S.range := by
  show LinearMap.range (T.prodMap S : (E × F) →ₗ[𝕜] (E' × F')) = _
  rw [ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap]

/-- Bijectivity of a product map is componentwise. -/
private theorem bijective_prodMap_iff {f : E → E'} {g : F → F'} :
    Function.Bijective (Prod.map f g) ↔ Function.Bijective f ∧ Function.Bijective g := by
  constructor
  · intro h
    constructor
    · constructor
      · intro x₁ x₂ h12
        have hmap : Prod.map f g (x₁, (0 : F)) = Prod.map f g (x₂, (0 : F)) := by
          simp only [Prod.map_apply, h12]
        exact (Prod.mk.injEq ..).mp (h.1 hmap) |>.1
      · intro y
        obtain ⟨⟨x, _⟩, hx⟩ := h.2 (y, (0 : F'))
        simp only [Prod.map_apply, Prod.mk.injEq] at hx
        exact ⟨x, hx.1⟩
    · constructor
      · intro y₁ y₂ h12
        have hmap : Prod.map f g ((0 : E), y₁) = Prod.map f g ((0 : E), y₂) := by
          simp only [Prod.map_apply, h12]
        exact (Prod.mk.injEq ..).mp (h.1 hmap) |>.2
      · intro y
        obtain ⟨⟨_, x⟩, hx⟩ := h.2 ((0 : E'), y)
        simp only [Prod.map_apply, Prod.mk.injEq] at hx
        exact ⟨x, hx.2⟩
  · intro ⟨hf, hg⟩
    exact hf.prodMap hg

/-- A direct sum is a unit iff both summands are units. -/
theorem isUnit_prodMap_iff [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) :
    IsUnit (T.prodMap S) ↔ IsUnit T ∧ IsUnit S := by
  simp only [ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.coe_prodMap']
  exact bijective_prodMap_iff

/-- Subtracting a direct sum from a scalar is a direct sum of the
componentwise differences. -/
private theorem algebraMap_sub_prodMap (z : 𝕜) (T : E →L[𝕜] E) (S : F →L[𝕜] F) :
    algebraMap 𝕜 (E × F →L[𝕜] E × F) z - T.prodMap S
      = (algebraMap 𝕜 (E →L[𝕜] E) z - T).prodMap
        (algebraMap 𝕜 (F →L[𝕜] F) z - S) := by
  refine ContinuousLinearMap.ext fun ⟨x, y⟩ => ?_
  simp [ContinuousLinearMap.coe_prodMap', Prod.map, Algebra.algebraMap_eq_smul_one]

/-- The spectrum of a direct sum is the union of the spectra. -/
theorem spectrum_prodMap [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) :
    spectrum 𝕜 (T.prodMap S) = spectrum 𝕜 T ∪ spectrum 𝕜 S := by
  ext z
  simp only [spectrum.mem_iff, Set.mem_union]
  rw [algebraMap_sub_prodMap, isUnit_prodMap_iff]
  exact not_and_or

/-- The resolvent set of a direct sum is the intersection of the resolvent sets. -/
theorem resolventSet_prodMap [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] E) (S : F →L[𝕜] F) :
    resolventSet 𝕜 (T.prodMap S) = resolventSet 𝕜 T ∩ resolventSet 𝕜 S := by
  ext z
  simp only [spectrum.mem_resolventSet_iff, Set.mem_inter_iff]
  rw [algebraMap_sub_prodMap, isUnit_prodMap_iff]

/-- A direct sum is compact iff both summands are compact. -/
theorem isCompactOperator_prodMap_iff (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    IsCompactOperator (T.prodMap S) ↔ IsCompactOperator T ∧ IsCompactOperator S := by
  constructor
  · intro h
    have hT : IsCompactOperator ((fst 𝕜 E' F') ∘L (T.prodMap S) ∘L (inl 𝕜 E F)) := by
      have h1 : IsCompactOperator (⇑(T.prodMap S) ∘ ⇑(inl 𝕜 E F)) := h.comp_clm _
      have h2 : IsCompactOperator (⇑(fst 𝕜 E' F') ∘ (⇑(T.prodMap S) ∘ ⇑(inl 𝕜 E F))) :=
        h1.clm_comp _
      rw [← ContinuousLinearMap.coe_comp, ← ContinuousLinearMap.coe_comp] at h2
      exact h2
    have hcompT : (fst 𝕜 E' F') ∘L (T.prodMap S) ∘L (inl 𝕜 E F) = T := by
      rw [← ContinuousLinearMap.comp_assoc, fst_comp_prodMap, ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.fst_comp_inl, ContinuousLinearMap.comp_id]
    have hS : IsCompactOperator ((snd 𝕜 E' F') ∘L (T.prodMap S) ∘L (inr 𝕜 E F)) := by
      have h1 : IsCompactOperator (⇑(T.prodMap S) ∘ ⇑(inr 𝕜 E F)) := h.comp_clm _
      have h2 : IsCompactOperator (⇑(snd 𝕜 E' F') ∘ (⇑(T.prodMap S) ∘ ⇑(inr 𝕜 E F))) :=
        h1.clm_comp _
      rw [← ContinuousLinearMap.coe_comp, ← ContinuousLinearMap.coe_comp] at h2
      exact h2
    have hcompS : (snd 𝕜 E' F') ∘L (T.prodMap S) ∘L (inr 𝕜 E F) = S := by
      rw [← ContinuousLinearMap.comp_assoc, snd_comp_prodMap, ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.snd_comp_inr, ContinuousLinearMap.comp_id]
    rw [hcompT] at hT
    rw [hcompS] at hS
    exact ⟨hT, hS⟩
  · rintro ⟨hT, hS⟩
    refine (isCompactOperator_iff_image_ball_subset_compact
      (T.prodMap S : (E × F) →ₗ[𝕜] (E' × F')) one_pos).mpr ?_
    obtain ⟨KT, hKT, hKTsub⟩ := hT.image_ball_subset_compact 1
    obtain ⟨KS, hKS, hKSsub⟩ := hS.image_ball_subset_compact 1
    refine ⟨KT ×ˢ KS, hKT.prod hKS, ?_⟩
    rw [Set.image_subset_iff]
    intro ⟨x, y⟩ hxy
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def] at hxy
    have hx : x ∈ Metric.ball (0 : E) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (le_max_left _ _) hxy
    have hy : y ∈ Metric.ball (0 : F) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (le_max_right _ _) hxy
    have hTx := hKTsub (Set.mem_image_of_mem T hx)
    have hSy := hKSsub (Set.mem_image_of_mem S hy)
    change (T x, S y) ∈ KT ×ˢ KS
    exact ⟨hTx, hSy⟩

/-- The first-component extraction of a quasi-inverse of a direct sum is a
quasi-inverse of the first summand. -/
private theorem isQuasiInverse_fst_of_prodMap
    {W : E' × F' →L[𝕜] E × F} {T : E →L[𝕜] E'} {S : F →L[𝕜] F'}
    (hW : W.IsQuasiInverse (T.prodMap S)) :
    ((fst 𝕜 E F) ∘L W ∘L (inl 𝕜 E' F')).IsQuasiInverse T := by
  have hWleft : ((↑W : (E' × F') →ₗ[𝕜] (E × F)) ∘ₗ
        (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')))
      ≈ (LinearMap.id : (E × F) →ₗ[𝕜] (E × F)) := hW.1.equiv
  have hWright : ((↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) ∘ₗ
        (↑W : (E' × F') →ₗ[𝕜] (E × F)))
      ≈ (LinearMap.id : (E' × F') →ₗ[𝕜] (E' × F')) := hW.2.equiv
  have h2 := LinearMap.FiniteRangeSetoid.equiv_comp_right
    (u := (↑(inl 𝕜 E F) : E →ₗ[𝕜] E × F)) hWleft
  have h3 := LinearMap.FiniteRangeSetoid.equiv_comp_left
    (u' := (↑(fst 𝕜 E F) : (E × F) →ₗ[𝕜] E)) h2
  have eid : (↑(fst 𝕜 E F) : (E × F) →ₗ[𝕜] E) ∘ₗ
      (LinearMap.id ∘ₗ (↑(inl 𝕜 E F) : E →ₗ[𝕜] E × F)) = LinearMap.id := by
    ext x
    rfl
  have h2' := LinearMap.FiniteRangeSetoid.equiv_comp_left
    (u' := (↑(fst 𝕜 E' F') : (E' × F') →ₗ[𝕜] E')) hWright
  have h3' := LinearMap.FiniteRangeSetoid.equiv_comp_right
    (u := (↑(inl 𝕜 E' F') : E' →ₗ[𝕜] E' × F')) h2'
  have eid' : ((↑(fst 𝕜 E' F') : (E' × F') →ₗ[𝕜] E') ∘ₗ LinearMap.id) ∘ₗ
      (↑(inl 𝕜 E' F') : E' →ₗ[𝕜] E' × F') = LinearMap.id := by
    ext x
    rfl
  refine ⟨?_, ?_⟩
  · show (↑((fst 𝕜 E F) ∘L W ∘L (inl 𝕜 E' F')) : E' →ₗ[𝕜] E) ∘ₗ
        (↑T : E →ₗ[𝕜] E') ≈ LinearMap.id
    have e : (↑((fst 𝕜 E F) ∘L W ∘L (inl 𝕜 E' F')) : E' →ₗ[𝕜] E) ∘ₗ
        (↑T : E →ₗ[𝕜] E')
        = (↑(fst 𝕜 E F) : (E × F) →ₗ[𝕜] E) ∘ₗ
          (((↑W : (E' × F') →ₗ[𝕜] (E × F)) ∘ₗ (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F'))) ∘ₗ (↑(inl 𝕜 E F) : E →ₗ[𝕜] E × F)) := by
      ext x
      simp [map_zero]
    rw [e]
    rwa [eid] at h3
  · show (↑T : E →ₗ[𝕜] E') ∘ₗ
        (↑((fst 𝕜 E F) ∘L W ∘L (inl 𝕜 E' F')) : E' →ₗ[𝕜] E) ≈ LinearMap.id
    have e : (↑T : E →ₗ[𝕜] E') ∘ₗ
        (↑((fst 𝕜 E F) ∘L W ∘L (inl 𝕜 E' F')) : E' →ₗ[𝕜] E)
        = ((↑(fst 𝕜 E' F') : (E' × F') →ₗ[𝕜] E') ∘ₗ ((↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) ∘ₗ (↑W : (E' × F') →ₗ[𝕜] (E × F)))) ∘ₗ
          (↑(inl 𝕜 E' F') : E' →ₗ[𝕜] E' × F') := by
      ext x
      simp
    rw [e]
    rwa [eid'] at h3'

/-- The second-component extraction of a quasi-inverse of a direct sum is a
quasi-inverse of the second summand. -/
private theorem isQuasiInverse_snd_of_prodMap
    {W : E' × F' →L[𝕜] E × F} {T : E →L[𝕜] E'} {S : F →L[𝕜] F'}
    (hW : W.IsQuasiInverse (T.prodMap S)) :
    ((snd 𝕜 E F) ∘L W ∘L (inr 𝕜 E' F')).IsQuasiInverse S := by
  have hWleft : ((↑W : (E' × F') →ₗ[𝕜] (E × F)) ∘ₗ
        (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')))
      ≈ (LinearMap.id : (E × F) →ₗ[𝕜] (E × F)) := hW.1.equiv
  have hWright : ((↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) ∘ₗ
        (↑W : (E' × F') →ₗ[𝕜] (E × F)))
      ≈ (LinearMap.id : (E' × F') →ₗ[𝕜] (E' × F')) := hW.2.equiv
  have h2 := LinearMap.FiniteRangeSetoid.equiv_comp_right
    (u := (↑(inr 𝕜 E F) : F →ₗ[𝕜] E × F)) hWleft
  have h3 := LinearMap.FiniteRangeSetoid.equiv_comp_left
    (u' := (↑(snd 𝕜 E F) : (E × F) →ₗ[𝕜] F)) h2
  have eid : (↑(snd 𝕜 E F) : (E × F) →ₗ[𝕜] F) ∘ₗ
      (LinearMap.id ∘ₗ (↑(inr 𝕜 E F) : F →ₗ[𝕜] E × F)) = LinearMap.id := by
    ext x
    rfl
  have h2' := LinearMap.FiniteRangeSetoid.equiv_comp_left
    (u' := (↑(snd 𝕜 E' F') : (E' × F') →ₗ[𝕜] F')) hWright
  have h3' := LinearMap.FiniteRangeSetoid.equiv_comp_right
    (u := (↑(inr 𝕜 E' F') : F' →ₗ[𝕜] E' × F')) h2'
  have eid' : ((↑(snd 𝕜 E' F') : (E' × F') →ₗ[𝕜] F') ∘ₗ LinearMap.id) ∘ₗ
      (↑(inr 𝕜 E' F') : F' →ₗ[𝕜] E' × F') = LinearMap.id := by
    ext x
    rfl
  refine ⟨?_, ?_⟩
  · show (↑((snd 𝕜 E F) ∘L W ∘L (inr 𝕜 E' F')) : F' →ₗ[𝕜] F) ∘ₗ
        (↑S : F →ₗ[𝕜] F') ≈ LinearMap.id
    have e : (↑((snd 𝕜 E F) ∘L W ∘L (inr 𝕜 E' F')) : F' →ₗ[𝕜] F) ∘ₗ
        (↑S : F →ₗ[𝕜] F')
        = (↑(snd 𝕜 E F) : (E × F) →ₗ[𝕜] F) ∘ₗ
          (((↑W : (E' × F') →ₗ[𝕜] (E × F)) ∘ₗ (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F'))) ∘ₗ (↑(inr 𝕜 E F) : F →ₗ[𝕜] E × F)) := by
      ext x
      simp [map_zero]
    rw [e]
    rwa [eid] at h3
  · show (↑S : F →ₗ[𝕜] F') ∘ₗ
        (↑((snd 𝕜 E F) ∘L W ∘L (inr 𝕜 E' F')) : F' →ₗ[𝕜] F) ≈ LinearMap.id
    have e : (↑S : F →ₗ[𝕜] F') ∘ₗ
        (↑((snd 𝕜 E F) ∘L W ∘L (inr 𝕜 E' F')) : F' →ₗ[𝕜] F)
        = ((↑(snd 𝕜 E' F') : (E' × F') →ₗ[𝕜] F') ∘ₗ ((↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) ∘ₗ (↑W : (E' × F') →ₗ[𝕜] (E × F)))) ∘ₗ
          (↑(inr 𝕜 E' F') : F' →ₗ[𝕜] E' × F') := by
      ext x
      simp
    rw [e]
    rwa [eid'] at h3'

/-- A direct sum is Fredholm iff both summands are Fredholm. -/
theorem isFredholm_prodMap_iff [CompleteSpace 𝕜] (T : E →L[𝕜] E') (S : F →L[𝕜] F') :
    (T.prodMap S).IsFredholm ↔ T.IsFredholm ∧ S.IsFredholm := by
  simp only [ContinuousLinearMap.isFredholm_iff_exists_isQuasiInverse]
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨⟨(fst 𝕜 E F) ∘L W ∘L (inl 𝕜 E' F'), isQuasiInverse_fst_of_prodMap hW⟩,
      ⟨(snd 𝕜 E F) ∘L W ∘L (inr 𝕜 E' F'), isQuasiInverse_snd_of_prodMap hW⟩⟩
  · rintro ⟨⟨VT, hVT⟩, ⟨VS, hVS⟩⟩
    refine ⟨VT.prodMap VS, ?_, ?_⟩
    · show (↑(VT.prodMap VS) : (E' × F') →ₗ[𝕜] (E × F)) ∘ₗ (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F'))
          ≈ LinearMap.id
      have e : (↑(VT.prodMap VS) : (E' × F') →ₗ[𝕜] (E × F)) ∘ₗ (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F'))
          - LinearMap.id
          = LinearMap.prodMap (((↑VT : E' →ₗ[𝕜] E) ∘ₗ (↑T : E →ₗ[𝕜] E')) - LinearMap.id) (((↑VS : F' →ₗ[𝕜] F) ∘ₗ (↑S : F →ₗ[𝕜] F')) - LinearMap.id) := by
        refine LinearMap.ext fun ⟨x, y⟩ => ?_
        simp [ContinuousLinearMap.coe_prodMap]
      rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange, e,
        LinearMap.hasFiniteRange_iff_range, LinearMap.range_prodMap]
      exact (LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hVT.1).fg_range.prod
        (LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hVS.1).fg_range
    · show (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) ∘ₗ (↑(VT.prodMap VS) : (E' × F') →ₗ[𝕜] (E × F))
          ≈ LinearMap.id
      have e : (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) ∘ₗ (↑(VT.prodMap VS) : (E' × F') →ₗ[𝕜] (E × F))
          - LinearMap.id
          = LinearMap.prodMap (((↑T : E →ₗ[𝕜] E') ∘ₗ (↑VT : E' →ₗ[𝕜] E)) - LinearMap.id) (((↑S : F →ₗ[𝕜] F') ∘ₗ (↑VS : F' →ₗ[𝕜] F)) - LinearMap.id) := by
        refine LinearMap.ext fun ⟨x, y⟩ => ?_
        simp [ContinuousLinearMap.coe_prodMap]
      rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange, e,
        LinearMap.hasFiniteRange_iff_range, LinearMap.range_prodMap]
      exact (LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hVT.2).fg_range.prod
        (LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hVS.2).fg_range

set_option linter.style.haveILetI false in
/-- The Fredholm index of a direct sum is the sum of the Fredholm indices. -/
theorem index_prodMap [CompleteSpace 𝕜] (T : E →L[𝕜] E') (S : F →L[𝕜] F')
    (hT : T.IsFredholm) (hS : S.IsFredholm) :
    (T.prodMap S).index = T.index + S.index := by
  have hker : LinearMap.ker (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F'))
      = (↑T : E →ₗ[𝕜] E').ker.prod (↑S : F →ₗ[𝕜] F').ker := by
    rw [ContinuousLinearMap.coe_prodMap, LinearMap.ker_prodMap]
  haveI : Module.Finite 𝕜 (↑T : E →ₗ[𝕜] E').ker := hT.finite_ker
  haveI : Module.Finite 𝕜 (↑S : F →ₗ[𝕜] F').ker := hS.finite_ker
  haveI : Module.Finite 𝕜 (E' ⧸ LinearMap.range (↑T : E →ₗ[𝕜] E')) := hT.finite_coker
  haveI : Module.Finite 𝕜 (F' ⧸ LinearMap.range (↑S : F →ₗ[𝕜] F')) := hS.finite_coker
  have hfin_ker : Module.finrank 𝕜
      ((↑T : E →ₗ[𝕜] E').ker.prod (↑S : F →ₗ[𝕜] F').ker)
      = Module.finrank 𝕜 (↑T : E →ₗ[𝕜] E').ker
        + Module.finrank 𝕜 (↑S : F →ₗ[𝕜] F').ker := by
    rw [(Submodule.prodEquiv (↑T : E →ₗ[𝕜] E').ker (↑S : F →ₗ[𝕜] F').ker).finrank_eq]
    exact Module.finrank_prod
  have hker_map : LinearMap.ker
      (LinearMap.prodMap (LinearMap.range (↑T : E →ₗ[𝕜] E')).mkQ
        (LinearMap.range (↑S : F →ₗ[𝕜] F')).mkQ)
      = LinearMap.range (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')) := by
    rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ,
      ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap]
  have hsurj : Function.Surjective
      (LinearMap.prodMap (LinearMap.range (↑T : E →ₗ[𝕜] E')).mkQ
        (LinearMap.range (↑S : F →ₗ[𝕜] F')).mkQ) :=
    (Submodule.mkQ_surjective _).prodMap (Submodule.mkQ_surjective _)
  have hquot : ((E' × F') ⧸ LinearMap.range (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')))
      ≃ₗ[𝕜] (E' ⧸ LinearMap.range (↑T : E →ₗ[𝕜] E'))
        × (F' ⧸ LinearMap.range (↑S : F →ₗ[𝕜] F')) :=
    hker_map ▸ LinearMap.quotKerEquivOfSurjective _ hsurj
  have hfin_coker : Module.finrank 𝕜
      ((E' × F') ⧸ LinearMap.range (↑(T.prodMap S) : (E × F) →ₗ[𝕜] (E' × F')))
      = Module.finrank 𝕜 (E' ⧸ LinearMap.range (↑T : E →ₗ[𝕜] E'))
        + Module.finrank 𝕜 (F' ⧸ LinearMap.range (↑S : F →ₗ[𝕜] F')) := by
    rw [hquot.finrank_eq]
    exact Module.finrank_prod
  simp only [LinearMap.index_eq_finrank_sub]
  rw [hker, hfin_ker, hfin_coker]
  push_cast
  ring

end MathlibExt.Analysis.InnerProductSpace.DirectSumOperators
