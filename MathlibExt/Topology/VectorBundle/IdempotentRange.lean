/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported from `TauCeti/Topology/VectorBundle/IdempotentRange.lean` in TauCetiProject/TauCeti
(https://github.com/TauCetiProject/TauCeti) at revision
62bbc0596dc3539d488232e4e924a338548ea0a9; the copyright and license notice above are the
source's. Modification: imports of the coupled ports point to `MathlibExt`; declarations and
proofs are unchanged.
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic
public import MathlibExt.Analysis.Normed.Operator.IdempotentRange

/-!
# The image bundle of a continuous family of projections

Let `p : B → F →L[𝕜] F` be a continuous family of idempotent operators on a Banach space `F`.
The ranges `(p x).range` form a subbundle of the trivial bundle `B × F`: this file gives
their total space the topology of a subspace of `B × F`
(`TauCeti.isEmbedding_totalSpace_range`) and shows that it is a topological vector bundle, with
any model fibre `F'` that is isomorphic to every range (`TauCeti.rangeFiberBundle` and
`TauCeti.rangeVectorBundle`). Complementary projections `p` and `1 - p` give complementary
subbundles, whose direct sum is the trivial bundle (`TauCeti.rangeProdRangeOneSubHomeomorph`).
These image bundles are the bundle side of the correspondence between vector bundles and
projections used in topological K-theory: classically, over a compact Hausdorff base every
finite-rank vector bundle is isomorphic to one of them, a fact not proved here.

The local trivialization at `x₀` uses the intertwining operator
`U x = p x * p x₀ + (1 - p x) * (1 - p x₀)`, which equals `1` at `x₀`. Where `U x` is
invertible, which is an open condition containing `x₀`, it carries the range of `p x₀`
isomorphically onto the range of `p x` (`ContinuousLinearMap.IsIdempotentElem.rangeEquiv`), and
this gives the trivialization (`TauCeti.rangeTrivialization`). The resulting local constancy of
the rank of a continuous family of projections is `TauCeti.isLocallyConstant_finrank_range`, in
`TauCeti/Analysis/Normed/Operator/IdempotentRange.lean`. No compactness, separation or
finite-dimensionality is assumed of the base or the fibres.

## Main definitions

* `TauCeti.instTopologicalSpaceTotalSpaceRange`: the subspace topology on the total space of the
  ranges of a family of operators.
* `TauCeti.rangeTrivialization`: the local trivialization at `x₀` given by the intertwining
  operator, read through an isomorphism of the model fibre with the range of `p x₀`.
* `TauCeti.rangeFiberBundle`: the fibre bundle structure on the ranges of a continuous family of
  projections.
* `TauCeti.rangeProdRangeOneSubHomeomorph`: the direct sum of the ranges of `p` and `1 - p` is
  homeomorphic to `B × F`, linearly on each fibre.

## Main results

* `TauCeti.rangeVectorBundle`: the ranges of a continuous family of projections form a
  topological vector bundle.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6, for the
  intertwining operator of a pair of projections.
* M. F. Atiyah, *K-Theory*, Benjamin (1967), Chapter I, for sub-bundles of trivial bundles and
  their complements.
* The subspace topology, the chart and atlas, and the vector-bundle packaging follow the
  subbundles of distributions in `TauCeti/Geometry/Manifold/Distribution/VectorBundle.lean`:
  `TauCeti.instTopologicalSpaceTotalSpaceDistribution`,
  `TauCeti.IsDistributionFrameOn.trivialization`, `TauCeti.IsContMDiffDistribution.fiberBundle`
  and `TauCeti.IsContMDiffDistribution.vectorBundle`.
-/

public section

open Bundle Set Topology
open scoped Ring
open ContinuousLinearMap.IsIdempotentElem (apply_coe_range coe_rangeEquiv_apply
  coe_rangeEquiv_symm_apply isUnit_mul_self_add_one_sub_mul_one_sub
  mul_self_add_one_sub_mul_one_sub)

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

section Topology

/-- The total space of the ranges of a family `p` of operators on `F`, the pairs `(x, v)` with
`v ∈ (p x).range`, carries the topology of a subspace of `B × F`. The model-fibre
parameter `F'` of `Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceRange (F' : Type*) (p : B → F →L[𝕜] F) :
    TopologicalSpace (TotalSpace F' fun x ↦ (p x).range) :=
  .induced (fun v ↦ (v.proj, (v.2 : F))) inferInstance

/-- The total space of the ranges of a family of operators on `F` is embedded in `B × F`. -/
theorem isEmbedding_totalSpace_range (F' : Type*) (p : B → F →L[𝕜] F) :
    IsEmbedding fun v : TotalSpace F' (fun x ↦ (p x).range) ↦ (v.proj, (v.2 : F)) := by
  refine ⟨⟨rfl⟩, fun ⟨x, v⟩ ⟨y, w⟩ h ↦ ?_⟩
  obtain rfl : x = y := congrArg Prod.fst h
  exact congrArg (TotalSpace.mk x) (Subtype.ext (congrArg Prod.snd h))

/-- The projection of the total space of the ranges of a family of operators is continuous. -/
theorem continuous_proj_totalSpace_range (F' : Type*) (p : B → F →L[𝕜] F) :
    Continuous (TotalSpace.proj : TotalSpace F' (fun x ↦ (p x).range) → B) :=
  continuous_fst.comp (isEmbedding_totalSpace_range F' p).continuous

end Topology

section Trivialization

variable [CompleteSpace F] {p : B → F →L[𝕜] F}

variable (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x)) (x₀ : B)
  (φ : F' ≃L[𝕜] (p x₀).range)

/-- The local trivialization at `x₀` of the ranges of a continuous family `p` of projections.
Over the open set where the intertwiner `U x = p x * p x₀ + (1 - p x) * (1 - p x₀)` is
invertible, a vector `w` in the range of `p x` is sent to `φ.symm (U x)⁻¹ w`, using an
isomorphism `φ` of the model fibre with the range of `p x₀`. -/
noncomputable def rangeTrivialization :
    Trivialization F' (π F' fun x ↦ (p x).range) where
  toFun v := (v.proj, φ.symm ((p x₀).rangeRestrict
    ((p v.proj * p x₀ + (1 - p v.proj) * (1 - p x₀))⁻¹ʳ v.2)))
  invFun q := TotalSpace.mk' F' (E := fun x ↦ (p x).range) q.1
    ((p q.1).rangeRestrict ((p q.1 * p x₀ + (1 - p q.1) * (1 - p x₀)) (φ q.2)))
  source := π F' (fun x ↦ (p x).range) ⁻¹' {x | IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀))}
  target := {x | IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀))} ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' := by
    rintro ⟨x, w⟩ (hx : IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀)))
    refine congrArg (TotalSpace.mk x) (Subtype.ext ?_)
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_codRestrict_apply]
    rw [← coe_rangeEquiv_symm_apply (hidem x₀) (hidem x) hx, apply_coe_range (hidem x₀),
      ← coe_rangeEquiv_apply (hidem x₀) (hidem x) hx, apply_coe_range (hidem x),
      ContinuousLinearEquiv.apply_symm_apply]
  right_inv' := by
    rintro ⟨x, v⟩ ⟨hx : IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀)), -⟩
    simp only [TotalSpace.mk', ContinuousLinearMap.coe_codRestrict_apply]
    refine Prod.ext rfl ((φ.symm_apply_eq).mpr (Subtype.ext ?_))
    rw [← coe_rangeEquiv_apply (hidem x₀) (hidem x) hx, apply_coe_range (hidem x),
      ← coe_rangeEquiv_symm_apply (hidem x₀) (hidem x) hx, ContinuousLinearEquiv.symm_apply_apply]
    exact apply_coe_range (hidem x₀) (φ v)
  open_source := (isOpen_setOf_isUnit_intertwiner hp x₀).preimage
    (continuous_proj_totalSpace_range F' p)
  open_target := (isOpen_setOf_isUnit_intertwiner hp x₀).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_proj_totalSpace_range F' p).continuousOn.prodMk ?_
    refine (φ.symm.continuous.comp ((p x₀).rangeRestrict).continuous).comp_continuousOn ?_
    exact ((continuousOn_inverse_intertwiner hp x₀).comp
      (continuous_proj_totalSpace_range F' p).continuousOn fun _ hv ↦ hv).clm_apply
      (continuous_snd.comp (isEmbedding_totalSpace_range F' p).continuous).continuousOn
  continuousOn_invFun := by
    refine Continuous.continuousOn ((isEmbedding_totalSpace_range F' p).continuous_iff.mpr ?_)
    exact continuous_fst.prodMk ((hp.comp continuous_fst).clm_apply
      ((continuous_intertwiner hp x₀ |>.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp (φ.continuous.comp continuous_snd))))
  baseSet := {x | IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀))}
  open_baseSet := isOpen_setOf_isUnit_intertwiner hp x₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The trivialization at `x₀` is defined over a neighbourhood of `x₀`. -/
theorem mem_baseSet_rangeTrivialization :
    x₀ ∈ (rangeTrivialization hp hidem x₀ φ).baseSet :=
  isUnit_mul_self_add_one_sub_mul_one_sub (hidem x₀)

/-- A point lies in the base set of the trivialization at `x₀` exactly when the intertwiner
`p x * p x₀ + (1 - p x) * (1 - p x₀)` is invertible. -/
theorem mem_baseSet_rangeTrivialization_iff {x : B} :
    x ∈ (rangeTrivialization hp hidem x₀ φ).baseSet ↔
      IsUnit (p x * p x₀ + (1 - p x) * (1 - p x₀)) :=
  Iff.rfl

/- The two evaluation lemmas below are not `simp` lemmas, so that the evaluations at the base point
`x₀` stay in simp normal form. -/

/-- The trivialization at `x₀` sends a vector `w` of the range of `p x` to `φ.symm (U x)⁻¹ w`,
where `U x = p x * p x₀ + (1 - p x) * (1 - p x₀)`. -/
theorem rangeTrivialization_apply (v : TotalSpace F' fun x ↦ (p x).range) :
    rangeTrivialization hp hidem x₀ φ v = (v.proj, φ.symm ((p x₀).rangeRestrict
      ((p v.proj * p x₀ + (1 - p v.proj) * (1 - p x₀))⁻¹ʳ v.2))) :=
  (rfl)

/-- The inverse of the trivialization at `x₀` sends `(x, v)` to `U x (φ v)` in the range of `p x`,
where `U x = p x * p x₀ + (1 - p x) * (1 - p x₀)`. -/
theorem rangeTrivialization_symm_apply (x : B) (v : F') :
    (rangeTrivialization hp hidem x₀ φ).toOpenPartialHomeomorph.symm (x, v) =
      ⟨x, (p x).rangeRestrict ((p x * p x₀ + (1 - p x) * (1 - p x₀)) (φ v))⟩ :=
  (rfl)

/-- At the base point `x₀`, the trivialization reads a vector of the range of `p x₀` through `φ`. -/
@[simp]
theorem rangeTrivialization_apply_self (w : (p x₀).range) :
    rangeTrivialization hp hidem x₀ φ ⟨x₀, w⟩ = (x₀, φ.symm w) := by
  refine Prod.ext rfl (congrArg φ.symm (Subtype.ext ?_))
  simp [mul_self_add_one_sub_mul_one_sub (hidem x₀), apply_coe_range (hidem x₀)]

/-- At the base point `x₀`, the inverse of the trivialization is `φ`. -/
@[simp]
theorem rangeTrivialization_symm_apply_self (v : F') :
    (rangeTrivialization hp hidem x₀ φ).toOpenPartialHomeomorph.symm (x₀, v) = ⟨x₀, φ v⟩ := by
  refine congrArg (TotalSpace.mk x₀) (Subtype.ext ?_)
  simp [mul_self_add_one_sub_mul_one_sub (hidem x₀), apply_coe_range (hidem x₀)]

/-- The trivialization at `x₀` is linear on every fibre. -/
instance isLinear_rangeTrivialization : (rangeTrivialization hp hidem x₀ φ).IsLinear 𝕜 where
  linear x _ := (φ.symm.toLinearMap ∘ₗ ((p x₀).rangeRestrict).toLinearMap ∘ₗ
    ((p x * p x₀ + (1 - p x) * (1 - p x₀))⁻¹ʳ).toLinearMap ∘ₗ ((p x).range).subtype).isLinear

/-- The coordinate changes between two trivializations given by intertwiners are continuous on
the intersection of their base sets. -/
theorem continuousOn_coordChangeL_rangeTrivialization (x₁ : B)
    (φ₁ : F' ≃L[𝕜] (p x₁).range) :
    ContinuousOn (fun x ↦ ((rangeTrivialization hp hidem x₀ φ).coordChangeL 𝕜
      (rangeTrivialization hp hidem x₁ φ₁) x : F' →L[𝕜] F'))
      ((rangeTrivialization hp hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp hidem x₁ φ₁).baseSet) := by
  -- On the overlap the coordinate change is an explicit composite of continuous operator families.
  have hc : ContinuousOn (fun x ↦ (φ₁.symm : (p x₁).range →L[𝕜] F') ∘L
      (p x₁).rangeRestrict ∘L (p x * p x₁ + (1 - p x) * (1 - p x₁))⁻¹ʳ ∘L
      p x ∘L (p x * p x₀ + (1 - p x) * (1 - p x₀)) ∘L ((p x₀).range).subtypeL ∘L
      (φ : F' →L[𝕜] (p x₀).range))
      ((rangeTrivialization hp hidem x₀ φ).baseSet ∩
        (rangeTrivialization hp hidem x₁ φ₁).baseSet) :=
    continuousOn_const.clm_comp (continuousOn_const.clm_comp
      (((continuousOn_inverse_intertwiner hp x₁).mono inter_subset_right).clm_comp
      (hp.continuousOn.clm_comp ((continuous_intertwiner hp x₀).continuousOn.clm_comp
      continuousOn_const))))
  refine hc.congr fun x hx ↦ ContinuousLinearMap.ext fun v ↦ ?_
  exact (rangeTrivialization hp hidem x₀ φ).coordChangeL_apply' (R := 𝕜) _ hx v

end Trivialization

section FiberBundle

variable [CompleteSpace F] {p : B → F →L[𝕜] F}

/-- **The ranges of a continuous family of projections form a fibre bundle**, the topology of
its total space being that of a subspace of `B × F`, with any model fibre `F'` isomorphic to all
the ranges. The trivializations are those of `TauCeti.rangeTrivialization`. Use this definition
as a local instance. -/
@[instance_reducible]
noncomputable def rangeFiberBundle (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜] (p x).range)) :
    FiberBundle F' fun x ↦ (p x).range where
  totalSpaceMk_isInducing' x := by
    rw [← (isEmbedding_totalSpace_range F' p).isInducing.of_comp_iff]
    exact (isInducing_prodMkRight x).comp IsInducing.subtypeVal
  trivializationAtlas' :=
    {e | ∃ (x₀ : B) (φ : F' ≃L[𝕜] (p x₀).range), rangeTrivialization hp hidem x₀ φ = e}
  trivializationAt' x := rangeTrivialization hp hidem x (hF' x).some
  mem_baseSet_trivializationAt' x := mem_baseSet_rangeTrivialization hp hidem x _
  trivialization_mem_atlas' x := ⟨x, _, rfl⟩

/-- The trivializations of `rangeFiberBundle` are the intertwiner trivializations. -/
theorem mem_trivializationAtlas_rangeFiberBundle_iff (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) (hF' : ∀ x, Nonempty (F' ≃L[𝕜] (p x).range))
    (e : Trivialization F' (π F' fun x ↦ (p x).range)) :
    letI := rangeFiberBundle hp hidem hF'
    e ∈ trivializationAtlas F' (fun x ↦ (p x).range) ↔
      ∃ (x₀ : B) (φ : F' ≃L[𝕜] (p x₀).range), rangeTrivialization hp hidem x₀ φ = e :=
  Iff.rfl

/-- **The ranges of a continuous family of projections form a vector bundle**: with the subspace
topology of `B × F`, the intertwiner trivializations are linear, with continuous coordinate
changes. -/
theorem rangeVectorBundle (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x))
    (hF' : ∀ x, Nonempty (F' ≃L[𝕜] (p x).range)) :
    letI := rangeFiberBundle hp hidem hF'
    VectorBundle 𝕜 F' fun x ↦ (p x).range := by
  let := rangeFiberBundle hp hidem hF'
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro e he
    obtain ⟨x₀, φ, rfl⟩ := (mem_trivializationAtlas_rangeFiberBundle_iff hp hidem hF' e).mp he.out
    infer_instance
  · intro e e' he he'
    obtain ⟨x₀, φ, rfl⟩ := (mem_trivializationAtlas_rangeFiberBundle_iff hp hidem hF' e).mp he.out
    obtain ⟨x₁, φ₁, rfl⟩ :=
      (mem_trivializationAtlas_rangeFiberBundle_iff hp hidem hF' e').mp he'.out
    exact continuousOn_coordChangeL_rangeTrivialization hp hidem x₀ φ x₁ φ₁

end FiberBundle

section Complement

variable {p : B → F →L[𝕜] F}

/-- **Complementary projections give complementary subbundles of the trivial bundle.** For a
continuous family of projections `p`, adding the components is a homeomorphism from the total
space of the direct sum of the ranges of `p x` and of `1 - p x` onto `B × F`, over the identity of
`B` and linear on each fibre. The model-fibre parameters `F'` and `F''` play no role. -/
def rangeProdRangeOneSubHomeomorph (F' F'' : Type*) (hp : Continuous p)
    (hidem : ∀ x, IsIdempotentElem (p x)) :
    TotalSpace (F' × F'') ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range) ≃ₜ B × F where
  toFun v := (v.proj, (v.2.1 : F) + v.2.2)
  invFun q := ⟨q.1, ((p q.1).rangeRestrict q.2, (1 - p q.1).rangeRestrict q.2)⟩
  left_inv := by
    rintro ⟨x, w₁, w₂⟩
    have h₂ : (1 - p x) w₂ = w₂ := apply_coe_range (hidem x).one_sub w₂
    have h₂' := congr($((hidem x).mul_one_sub_self) (w₂ : F))
    rw [mul_apply_eq_comp, h₂, zero_apply] at h₂'
    refine congrArg (TotalSpace.mk x) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · simp only [map_add, Submodule.coe_add, ContinuousLinearMap.coe_codRestrict_apply,
        apply_coe_range (hidem x) w₁, h₂', add_zero]
    · simp only [map_add, Submodule.coe_add, ContinuousLinearMap.coe_codRestrict_apply,
        sub_apply, one_apply_eq_self, apply_coe_range (hidem x) w₁, h₂']
      abel
  right_inv := by
    rintro ⟨x, v⟩
    simp only [ContinuousLinearMap.coe_codRestrict_apply, sub_apply,
      one_apply_eq_self, add_sub_cancel]
  continuous_toFun := by
    have hD := (FiberBundle.Prod.isInducing_diag F' (fun x ↦ (p x).range) F''
      fun x ↦ (1 - p x).range).continuous
    have h₁ := (isEmbedding_totalSpace_range F' p).continuous.comp (continuous_fst.comp hD)
    have h₂ := (isEmbedding_totalSpace_range F'' (fun x ↦ 1 - p x)).continuous.comp
      (continuous_snd.comp hD)
    exact (continuous_fst.comp h₁).prodMk ((continuous_snd.comp h₁).add (continuous_snd.comp h₂))
  continuous_invFun := by
    refine (FiberBundle.Prod.isInducing_diag F' (fun x ↦ (p x).range) F''
      fun x ↦ (1 - p x).range).continuous_iff.mpr (Continuous.prodMk ?_ ?_)
    · exact (isEmbedding_totalSpace_range F' p).continuous_iff.mpr
        (continuous_fst.prodMk ((hp.comp continuous_fst).clm_apply continuous_snd))
    · exact (isEmbedding_totalSpace_range F'' (fun x ↦ 1 - p x)).continuous_iff.mpr
        (continuous_fst.prodMk (((continuous_const.sub hp).comp continuous_fst).clm_apply
          continuous_snd))

variable (F' F'' : Type*) (hp : Continuous p) (hidem : ∀ x, IsIdempotentElem (p x))

/- The two evaluation lemmas are not `simp` lemmas: `simp` would rewrite the coercion of `1 - p x`
inside the type of the total space, so their left-hand sides are not in simp normal form. -/

/-- The homeomorphism adds the two components of a vector of the direct sum. -/
theorem rangeProdRangeOneSubHomeomorph_apply
    (v : TotalSpace (F' × F'') ((fun x ↦ (p x).range) ×ᵇ fun x ↦ (1 - p x).range)) :
    rangeProdRangeOneSubHomeomorph F' F'' hp hidem v = (v.proj, (v.2.1 : F) + v.2.2) :=
  (rfl)

/-- The inverse homeomorphism splits a vector of `F` by the projections `p x` and `1 - p x`. -/
theorem rangeProdRangeOneSubHomeomorph_symm_apply (q : B × F) :
    (rangeProdRangeOneSubHomeomorph F' F'' hp hidem).symm q =
      ⟨q.1, ((p q.1).rangeRestrict q.2, (1 - p q.1).rangeRestrict q.2)⟩ :=
  (rfl)

end Complement

end TauCeti
