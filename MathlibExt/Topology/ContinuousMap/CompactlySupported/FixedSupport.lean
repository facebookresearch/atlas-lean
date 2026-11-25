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

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The actual Banach carrier of functions with one fixed compact support

The closed submodule of stock bounded continuous functions vanishing outside
K retains its norm, metric and scalar operations. For compact closed K, its
values are the original compactly supported functions. Restriction to K is a
linear isometry, so joint continuity of a supported family gives continuity
in this actual sup norm. No completed-function model is supplied as an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped CompactlySupported

namespace BoundedContinuousFunction

noncomputable section

universe uX uE u𝕜 uY

variable {X : Type uX} [TopologicalSpace X]
variable (𝕜 : Type u𝕜) [NormedField 𝕜]
variable (E : Type uE) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (K : Set X)

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.

The bounded continuous functions that vanish outside the given set. -/
def supportedSubmodule : Submodule 𝕜 (X →ᵇ E) where
  carrier := {f : X →ᵇ E | ∀ x : X, x ∉ K → f x = 0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by
    intro f g hf hg x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, zero_add]
  smul_mem' := by
    intro c f hf x hx
    change c • f x = 0
    rw [hf x hx, smul_zero]

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.

The fixed-support carrier has exactly the bounded-function norm. -/
abbrev Supported := ↥(supportedSubmodule 𝕜 E K)

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.

Point evaluations show that vanishing outside any set is a closed condition. -/
theorem isClosed_supportedSubmodule : IsClosed (supportedSubmodule 𝕜 E K : Set (X →ᵇ E)) := by
  have hset : (supportedSubmodule 𝕜 E K : Set (X →ᵇ E)) =
      ⋂ x : X, ⋂ _ : x ∉ K, {f : X →ᵇ E | f x = 0} := by
    ext f
    change (∀ x : X, x ∉ K → f x = 0) ↔ _
    simp only [mem_iInter, mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (lipschitz_eval_const x).continuous continuous_const

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `E` is complete.

The closed subtype of the complete bounded-function space is complete. -/
theorem completeSpace_supported [CompleteSpace E] : CompleteSpace (Supported 𝕜 E K) :=
  (isClosed_supportedSubmodule 𝕜 E K).isComplete.completeSpace_coe

instance instCompleteSpaceSupported [CompleteSpace E] : CompleteSpace (Supported 𝕜 E K) :=
  completeSpace_supported 𝕜 E K

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact. Assume `K` is closed.

Read a fixed compactly supported value as the same C_c function. -/
def supportedToCc (hK : IsCompact K) (hKclosed : IsClosed K) :
    Supported 𝕜 E K →ₗ[𝕜] C_c(X, E) where
  toFun f :=
    { toFun := f.1
      continuous_toFun := f.1.continuous
      hasCompactSupport' := HasCompactSupport.intro' hK hKclosed f.2 }
  map_add' f g := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    rfl
  map_smul' c f := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    rfl

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact. Assume `K` is closed.

The fixed-support coercion preserves every coefficient value. -/
@[simp]
theorem supportedToCc_apply (hK : IsCompact K) (hKclosed : IsClosed K)
    (f : Supported 𝕜 E K) (x : X) : supportedToCc 𝕜 E K hK hKclosed f x = f.1 x :=
  rfl

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact. Assume `K` is closed.

The function's topological support lies in the fixed closed set. -/
theorem tsupport_supportedToCc_subset (hK : IsCompact K) (hKclosed : IsClosed K)
    (f : Supported 𝕜 E K) : tsupport (supportedToCc 𝕜 E K hK hKclosed f) ⊆ K := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (f.2 x hnot)
  · exact hKclosed

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
The given compactly supported function has topological support contained in `K`.

Put an compact-support function into the bounded-function subtype. -/
def ccToSupported (f : C_c(X, E)) (hSupport : tsupport f ⊆ K) : Supported 𝕜 E K :=
  ⟨f.toBoundedContinuousFunction, fun x hx =>
    show f x = 0 from image_eq_zero_of_notMem_tsupport (fun hfx => hx (hSupport hfx))⟩

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
The given compactly supported function has topological support contained in `K`.

The bounded subtype retains every C_c coefficient value. -/
@[simp]
theorem ccToSupported_apply (f : C_c(X, E)) (hSupport : tsupport f ⊆ K) (x : X) :
    (ccToSupported 𝕜 E K f hSupport).1 x = f x :=
  rfl

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact. Assume `K` is closed. The given compactly supported function has
topological support contained in `K`.

The two function views agree on every compact-support value. -/
@[simp]
theorem supportedToCc_ccToSupported (hK : IsCompact K) (hKclosed : IsClosed K)
    (f : C_c(X, E)) (hSupport : tsupport f ⊆ K) :
    supportedToCc 𝕜 E K hK hKclosed (ccToSupported 𝕜 E K f hSupport) = f := by
  apply CompactlySupportedContinuousMap.ext
  intro x
  rfl

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.

The bounded point evaluation restricted to the same fixed-support subspace. -/
def supportedEvalCLM (x : X) : Supported 𝕜 E K →L[𝕜] E :=
  (evalCLM 𝕜 x).comp (supportedSubmodule 𝕜 E K).subtypeL

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.

Evaluation through the bounded linear map is the function value. -/
@[simp]
theorem supportedEvalCLM_apply (x : X) (f : Supported 𝕜 E K) :
    supportedEvalCLM 𝕜 E K x f = f.1 x :=
  rfl

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact.

Restriction to the same compact set is an linear isometry, including empty K. -/
def restrictSupportedLI (hK : IsCompact K) :
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    Supported 𝕜 E K →ₗᵢ[𝕜] C(K, E) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R : Supported 𝕜 E K →ₗ[𝕜] C(K, E) :=
    { toFun f := ⟨fun x : K => f.1 x, f.1.continuous.comp continuous_subtype_val⟩
      map_add' f g := by ext x; rfl
      map_smul' c f := by ext x; rfl }
  refine { R with norm_map' := ?_ }
  intro f
  apply le_antisymm
  · apply (ContinuousMap.norm_le (R f) (norm_nonneg f)).mpr
    intro x
    exact norm_coe_le_norm f.1 x
  · change ‖f.1‖ ≤ ‖R f‖
    apply (BoundedContinuousFunction.norm_le (norm_nonneg (R f))).mpr
    intro x
    by_cases hx : x ∈ K
    · exact ContinuousMap.norm_coe_le_norm (R f) ⟨x, hx⟩
    · rw [f.2 x hx, norm_zero]
      exact norm_nonneg (R f)

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact.

The restriction has the same coefficient values on the compact set. -/
@[simp]
theorem restrictSupportedLI_apply (hK : IsCompact K) (f : Supported 𝕜 E K) (x : K) :
    let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
    restrictSupportedLI 𝕜 E K hK f x = f.1 x :=
  rfl

/-- Let `X` be a topological space, let `𝕜` be a normed field, let `E` be a normed `𝕜`-vector space,
and let `K ⊆ X`. Supported functions are bounded continuous functions which vanish outside `K`.
Assume `K` is compact. A topological parameter space `Y` and a jointly continuous family of
these supported functions are given.

Joint coefficient continuity gives continuity in the fixed-support sup norm. -/
theorem continuous_supported_of_joint {Y : Type uY} [TopologicalSpace Y]
    (hK : IsCompact K) (F : Y → Supported 𝕜 E K)
    (hF : Continuous (fun p : Y × X => (F p.1).1 p.2)) : Continuous F := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R : Supported 𝕜 E K →ₗᵢ[𝕜] C(K, E) := restrictSupportedLI 𝕜 E K hK
  have hc : Continuous (fun y : Y => R (F y)) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  exact R.comp_continuous_iff.mp hc

end

end BoundedContinuousFunction
