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

public import MathlibExt.Analysis.Normed.Group.DirectLimit
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Normed-space dictionaries and bounded stages for directed limits

Over any normed field, the norm-preserving family equips the original algebraic
directed limit with its stock scalar action and an explicit normed-space
structure. Its coefficient maps are linear isometries for the original norms.

For an eventually bounded system, the scalar norm inequality holds for the
real-limsup seminorm. The module structure descends to the same separated
`NormedLimit` and retains its constructed additive-group metric. The raw and
separated coefficient maps are bounded linear maps with public application
and original stage-limsup norm laws.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DirectLimit

universe uK uI uG uT

variable {𝕜 : Type uK} [NormedField 𝕜]
  {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {G : I → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), LinearMapClass (T h) 𝕜 (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)
  [DirectedSystem G (f · · ·)]
  (hNorm : ∀ i j (h : i ≤ j) (x : G i), ‖f i j h x‖ = ‖x‖)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. Every transition preserves norms exactly. The transition maps are
`𝕜`-linear.

The normed-space structure over any normed field, using the existing group metric and the
direct-limit module over the supplied maps. -/
@[instance_reducible]
noncomputable def normedSpaceOfNormPreserving :
    letI : NormedAddCommGroup (_root_.DirectLimit G f) :=
      normedAddCommGroupOfNormPreserving f hNorm;
    NormedSpace 𝕜 (_root_.DirectLimit G f) := by
  let md : Module 𝕜 (_root_.DirectLimit G f) := inferInstance
  letI : NormedAddCommGroup (_root_.DirectLimit G f) :=
    normedAddCommGroupOfNormPreserving f hNorm
  letI : Module 𝕜 (_root_.DirectLimit G f) := md
  refine { md with norm_smul_le := ?_ }
  intro c z
  refine _root_.DirectLimit.induction (f := f) (fun i x => ?_) z
  rw [_root_.DirectLimit.smul_def]
  change ‖c • x‖ ≤ ‖c‖ * ‖x‖
  exact norm_smul_le c x

namespace Module

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. Every transition preserves norms exactly. The transition maps are
`𝕜`-linear.

The coefficient map bundled as a linear isometry, using exactly the constructed direct-limit
group and normed-space structures. -/
noncomputable def ofₗᵢ (i : I) :
    letI : NormedAddCommGroup (_root_.DirectLimit G f) :=
      DirectLimit.normedAddCommGroupOfNormPreserving f hNorm;
    letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
      DirectLimit.normedSpaceOfNormPreserving (𝕜 := 𝕜) f hNorm;
    G i →ₗᵢ[𝕜] _root_.DirectLimit G f := by
  let coefficient : G i →ₗ[𝕜] _root_.DirectLimit G f :=
    _root_.DirectLimit.Module.of 𝕜 I G f i
  let _ : NormedAddCommGroup (_root_.DirectLimit G f) :=
    DirectLimit.normedAddCommGroupOfNormPreserving f hNorm
  let _ : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    DirectLimit.normedSpaceOfNormPreserving (𝕜 := 𝕜) f hNorm
  refine { coefficient with norm_map' := ?_ }
  intro x
  change ‖(⟦⟨i, x⟩⟧ : _root_.DirectLimit G f)‖ = ‖x‖
  exact DirectLimit.normedAddCommGroupOfNormPreserving_norm_mk f hNorm i x

end Module

end DirectLimit

namespace DirectLimit

open Filter

universe uK uI uG uT

variable {𝕜 : Type uK} [NormedField 𝕜]
  {I : Type uI} [Preorder I]
  {G : I → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), LinearMapClass (T h) 𝕜 (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Specify a transition map for every ordered pair of indices. The transition
maps are `𝕜`-linear.

The linear transitions give the scalar norm formula for every value of the representative norm
net. -/
theorem stageTailNorm_smul (i : I) (c : 𝕜) (x : G i) :
    stageTailNorm f i (c • x) = (fun _ : I => ‖c‖) * stageTailNorm f i x := by
  classical
  funext j
  by_cases h : i ≤ j
  · simp only [stageTailNorm, dite_eq_left h, Pi.mul_apply, map_smul, norm_smul]
  · simp only [stageTailNorm, dite_eq_right h, Pi.mul_apply, mul_zero]

variable [IsDirectedOrder I] [Nonempty I]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. Specify a transition map for every
ordered pair of indices. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The finite real limsups satisfy the scalar norm bound. -/
theorem stageTailNorm_limsup_smul_le
    (hBound : IsEventuallyNormBounded f) (i : I) (c : 𝕜) (x : G i) :
    limsup (stageTailNorm f i (c • x)) atTop ≤
      ‖c‖ * limsup (stageTailNorm f i x) atTop := by
  rw [stageTailNorm_smul]
  have hc : IsBoundedUnder (· ≤ ·) atTop (fun _ : I => ‖c‖) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun _ => le_rfl))
  have hx0 : ∀ᶠ j in atTop, 0 ≤ stageTailNorm f i x j :=
    Eventually.of_forall (stageTailNorm_nonneg f i x)
  simpa only [limsup_const] using
    (limsup_mul_le (Frequently.of_forall (fun _ : I => norm_nonneg c)) hc hx0
      (stageTailNorm_boundedAbove f hBound i x))

variable [DirectedSystem G (f · · ·)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The raw direct-limit module becomes a normed space for the constructed limsup seminorm, using
exactly its existing module laws. -/
@[instance_reducible]
noncomputable def normedSpaceOfEventuallyBounded
    (hBound : IsEventuallyNormBounded f) :
    letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
      seminormedAddCommGroupOfEventuallyBounded f hBound;
    NormedSpace 𝕜 (_root_.DirectLimit G f) := by
  let md : Module 𝕜 (_root_.DirectLimit G f) := inferInstance
  letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  letI : Module 𝕜 (_root_.DirectLimit G f) := md
  refine { md with norm_smul_le := ?_ }
  intro c z
  refine _root_.DirectLimit.induction (f := f) (fun i x => ?_) z
  rw [_root_.DirectLimit.smul_def]
  change limsup (stageTailNorm f i (c • x)) atTop ≤
    ‖c‖ * limsup (stageTailNorm f i x) atTop
  exact stageTailNorm_limsup_smul_le f hBound i c x

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The normed-space structure on the zero-seminorm quotient, preserving its already constructed
normed-group structure. -/
@[instance_reducible]
noncomputable def normedSpaceNormedLimit
    (hBound : IsEventuallyNormBounded f) :
    letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    NormedSpace 𝕜 (NormedLimit f hBound) := by
  letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  exact SeparationQuotient.instNormedSpace (𝕜 := 𝕜) (E := _root_.DirectLimit G f)

namespace Module

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The raw coefficient map is bounded for the limsup seminorm by the common map bound on a tail
from its source stage. -/
noncomputable def ofRawCLM (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
      seminormedAddCommGroupOfEventuallyBounded f hBound;
    letI : AddCommMonoid (_root_.DirectLimit G f) :=
      (seminormedAddCommGroupOfEventuallyBounded f hBound).toAddCommMonoid;
    letI : TopologicalSpace (_root_.DirectLimit G f) :=
      (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
      normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound;
    G i →L[𝕜] _root_.DirectLimit G f := by
  letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  letI : AddCommMonoid (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toAddCommMonoid
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  let coefficient : G i →ₗ[𝕜] _root_.DirectLimit G f :=
    { toFun := fun x => (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f)
      map_add' := fun x y => (_root_.DirectLimit.add_def i x y).symm
      map_smul' := fun c x => (_root_.DirectLimit.smul_def i x c).symm }
  refine coefficient.mkContinuousOfExistsBound ?_
  obtain ⟨C, _, hC⟩ := hBound i
  refine ⟨C, fun x => ?_⟩
  change limsup (stageTailNorm f i x) atTop ≤ C * ‖x‖
  apply limsup_le_of_le (stageTailNorm_boundedBelow f i x).isCoboundedUnder_le
  filter_upwards [hC, eventually_ge_atTop i] with j hj hij
  rw [stageTailNorm, dite_eq_left hij]
  exact hj hij x

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The bounded raw map retains the exact algebraic coefficient value under the explicitly induced
raw seminorm topology. -/
theorem ofRawCLM_apply (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
      seminormedAddCommGroupOfEventuallyBounded f hBound;
    letI : AddCommMonoid (_root_.DirectLimit G f) :=
      (seminormedAddCommGroupOfEventuallyBounded f hBound).toAddCommMonoid;
    letI : TopologicalSpace (_root_.DirectLimit G f) :=
      (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
      normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound;
    ofRawCLM (𝕜 := 𝕜) f hBound i x = (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f) := by
  let : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  let : AddCommMonoid (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toAddCommMonoid
  let : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  simp only [ofRawCLM, LinearMap.mkContinuousOfExistsBound_apply]
  rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The bounded stage map to the zero-seminorm quotient. -/
noncomputable def ofCLM (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    G i →L[𝕜] NormedLimit f hBound := by
  letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  letI : AddCommMonoid (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toAddCommMonoid
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  exact (SeparationQuotient.mkCLM 𝕜 (_root_.DirectLimit G f)).comp (ofRawCLM f hBound i)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The bounded stage map has the same quotient coefficient value. -/
theorem ofCLM_apply (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    ofCLM (𝕜 := 𝕜) f hBound i x =
      normedLimitMk f hBound (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f) := by
  let : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  let : AddCommMonoid (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toAddCommMonoid
  let : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  simp only [ofCLM, normedLimitMk]
  rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed vector spaces over a
normed field `𝕜`. Assume `I` is nonempty and directed. The transition homomorphisms form a
compatible directed system. For each starting stage there is a nonnegative common operator-norm
bound on a tail of its transition maps. The transition maps are `𝕜`-linear.

The bounded stages retain the real limsup norm law. -/
theorem ofCLM_norm (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    ‖ofCLM (𝕜 := 𝕜) f hBound i x‖ = limsup (stageTailNorm f i x) atTop := by
  let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  rw [ofCLM_apply]
  exact normedLimitMk_norm_mk f hBound i x

end Module

end DirectLimit
