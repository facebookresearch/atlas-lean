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
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import MathlibExt.Analysis.Normed.Module.DirectLimit

/-!
# Normed ring and algebra dictionaries on directed limits

The norm-preserving family combines the stock algebraic direct-limit product
with its descended stage norm to give an explicit nonunital normed ring.

For an eventually bounded system, the stage-norm limsup is submultiplicative.
The raw algebraic carrier and its stock separated `NormedLimit` receive
compatible nonunital and unital ring dictionaries. The zero-seminorm two-sided
ideal is the kernel of the actual quotient ring map.

The algebra layers preserve the original scalar action, scalar-tower and
commuting-action laws, and the unital algebra map where supplied by the stages.
Their canonical coefficient maps expose application, transition-compatibility
and bounded-linear-map equations on the same original carriers and norms.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DirectLimit

universe uI uG uT

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {G : I → Type uG} [∀ i, NonUnitalNormedRing (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), NonUnitalRingHomClass (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)
  [DirectedSystem G (f · · ·)]
  (hNorm : ∀ i j (h : i ≤ j) (x : G i), ‖f i j h x‖ = ‖x‖)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. Every transition preserves norms exactly.

The nonunital normed-ring structure with the multiplication and exactly the previously
constructed additive-group norm and metric. -/
@[instance_reducible]
noncomputable def nonUnitalNormedRingOfNormPreserving :
    NonUnitalNormedRing (_root_.DirectLimit G f) := by
  let rawRing : NonUnitalRing (_root_.DirectLimit G f) := inferInstance
  let normedGroup : NormedAddCommGroup (_root_.DirectLimit G f) :=
    normedAddCommGroupOfNormPreserving f hNorm
  let _ : NormedAddCommGroup (_root_.DirectLimit G f) := normedGroup
  refine { rawRing, normedGroup with norm_mul_le := ?_ }
  intro z w
  refine _root_.DirectLimit.induction₂ (f := f) (fun i x y => ?_) z w
  rw [_root_.DirectLimit.mul_def]
  change ‖x * y‖ ≤ ‖x‖ * ‖y‖
  exact norm_mul_le x y

end DirectLimit

namespace DirectLimit

open Filter

universe uK uI uG uT

variable {I : Type uI} [Preorder I]
  {G : I → Type uG} [∀ i, NonUnitalNormedRing (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), NonUnitalRingHomClass (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Specify a transition map for every ordered pair of indices.

The ring transitions give the pointwise product norm bound for the representative norm nets. -/
theorem stageTailNorm_mul_le (i : I) (x y : G i) (j : I) :
    stageTailNorm f i (x * y) j ≤ stageTailNorm f i x j * stageTailNorm f i y j := by
  classical
  by_cases h : i ≤ j
  · rw [stageTailNorm, dite_eq_left h, stageTailNorm, dite_eq_left h,
      stageTailNorm, dite_eq_left h, map_mul]
    exact norm_mul_le _ _
  · rw [stageTailNorm, dite_eq_right h, stageTailNorm, dite_eq_right h,
      stageTailNorm, dite_eq_right h, zero_mul]

variable [IsDirectedOrder I] [Nonempty I]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. Specify a transition map for every ordered pair of
indices. For each starting stage there is a nonnegative common operator-norm bound on a tail of
its transition maps.

The finite real limsups of the norms are submultiplicative. -/
theorem stageTailNorm_limsup_mul_le
    (hBound : IsEventuallyNormBounded f) (i : I) (x y : G i) :
    limsup (stageTailNorm f i (x * y)) atTop ≤
      limsup (stageTailNorm f i x) atTop * limsup (stageTailNorm f i y) atTop := by
  have hx := stageTailNorm_boundedAbove f hBound i x
  have hy := stageTailNorm_boundedAbove f hBound i y
  have hx0 : ∀ᶠ j in atTop, 0 ≤ stageTailNorm f i x j :=
    Eventually.of_forall (stageTailNorm_nonneg f i x)
  have hy0 : ∀ᶠ j in atTop, 0 ≤ stageTailNorm f i y j :=
    Eventually.of_forall (stageTailNorm_nonneg f i y)
  have hxy0 := stageTailNorm_boundedBelow f i (x * y)
  exact (limsup_le_limsup (Eventually.of_forall (stageTailNorm_mul_le f i x y))
    hxy0.isCoboundedUnder_le
    (isBoundedUnder_le_mul_of_nonneg hx0.frequently hx hy0 hy)).trans
      (limsup_mul_le hx0.frequently hx hy0 hy)

variable [DirectedSystem G (f · · ·)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The algebraic limit has the nonunital seminormed-ring structure given by its multiplication and
constructed limsup additive seminorm. -/
@[instance_reducible]
noncomputable def nonUnitalSeminormedRingOfEventuallyBounded
    (hBound : IsEventuallyNormBounded f) : NonUnitalSeminormedRing (_root_.DirectLimit G f) := by
  let rawRing : NonUnitalRing (_root_.DirectLimit G f) := inferInstance
  let rawGroup : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  letI : SeminormedAddCommGroup (_root_.DirectLimit G f) := rawGroup
  refine { rawRing, rawGroup with norm_mul_le := ?_ }
  intro z w
  refine _root_.DirectLimit.induction₂ (f := f) (fun i x y => ?_) z w
  rw [_root_.DirectLimit.mul_def]
  change limsup (stageTailNorm f i (x * y)) atTop ≤
    limsup (stageTailNorm f i x) atTop * limsup (stageTailNorm f i y) atTop
  exact stageTailNorm_limsup_mul_le f hBound i x y

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The nonunital normed ring on the zero-seminorm quotient, using exactly its previously
constructed additive norm and metric. -/
@[instance_reducible]
noncomputable def nonUnitalNormedRingNormedLimit
    (hBound : IsEventuallyNormBounded f) : NonUnitalNormedRing (NormedLimit f hBound) :=
  @SeparationQuotient.instNonUnitalNormedRing (_root_.DirectLimit G f)
    (nonUnitalSeminormedRingOfEventuallyBounded f hBound)

namespace NonUnitalRing

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The ring homomorphism that quotients the algebraic limit by its zero seminorm. -/
noncomputable def normedLimitMk (hBound : IsEventuallyNormBounded f) :
    letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    _root_.DirectLimit G f →ₙ+* NormedLimit f hBound := by
  letI : NonUnitalSeminormedRing (_root_.DirectLimit G f) :=
    nonUnitalSeminormedRingOfEventuallyBounded f hBound
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  exact
    { toFun := fun z : _root_.DirectLimit G f => SeparationQuotient.mk z
      map_zero' := SeparationQuotient.mk_zero
      map_add' := SeparationQuotient.mk_add
      map_mul' := SeparationQuotient.mk_mul }

end NonUnitalRing

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The zero-seminorm two-sided ideal in the nonunital algebraic direct limit. Its congruence is the
kernel of the constructed quotient. -/
noncomputable def zeroSeminormIdeal (hBound : IsEventuallyNormBounded f) :
    TwoSidedIdeal (_root_.DirectLimit G f) := by
  letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  exact TwoSidedIdeal.ker (NonUnitalRing.normedLimitMk f hBound)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

Membership in that two-sided ideal is exactly zero of the real limsup seminorm. -/
theorem mem_zeroSeminormIdeal_iff (hBound : IsEventuallyNormBounded f)
    (z : _root_.DirectLimit G f) :
    z ∈ zeroSeminormIdeal f hBound ↔ addGroupSeminormOfEventuallyBounded f hBound z = 0 := by
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  change z ∈ TwoSidedIdeal.ker (NonUnitalRing.normedLimitMk f hBound) ↔ _
  rw [TwoSidedIdeal.mem_ker]
  exact normedLimitMk_eq_zero_iff f hBound z

end DirectLimit

namespace DirectLimit

universe uK uI uG uT

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {G : I → Type uG} [∀ i, NonUnitalNormedRing (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)
  [DirectedSystem G (f · · ·)]

section NonUnitalAlgebra

variable {𝕜 : Type uK} [NormedField 𝕜]
  [∀ i, NormedSpace 𝕜 (G i)]
  [∀ i j (h : i ≤ j), NonUnitalAlgHomClass (T h) 𝕜 (G i) (G j)]

section ScalarTower

variable [∀ i, IsScalarTower 𝕜 (G i) (G i)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action. Assume
scalar action commutes with left multiplication at each stage.

Scalar multiplication on the constructed quotient has the left multiplication compatibility from
the stage algebras. -/
theorem isScalarTowerNormedLimit (hBound : IsEventuallyNormBounded f) :
    let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    IsScalarTower 𝕜 (NormedLimit f hBound) (NormedLimit f hBound) := by
  let : NonUnitalSeminormedRing (_root_.DirectLimit G f) :=
    nonUnitalSeminormedRingOfEventuallyBounded f hBound
  let : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  let : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  constructor
  intro c z w
  refine Quotient.inductionOn₂ z w (fun x y => ?_)
  change SeparationQuotient.mk ((c • x) * y) = SeparationQuotient.mk (c • (x * y))
  exact congrArg SeparationQuotient.mk (smul_mul_assoc c x y)

end ScalarTower

section CommScalar

variable [∀ i, SMulCommClass 𝕜 (G i) (G i)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action. Assume
scalar action commutes with right multiplication at each stage.

Scalar multiplication on the same quotient retains the right multiplication compatibility of the
stage algebras. -/
theorem smulCommClassNormedLimit (hBound : IsEventuallyNormBounded f) :
    let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    SMulCommClass 𝕜 (NormedLimit f hBound) (NormedLimit f hBound) := by
  let : NonUnitalSeminormedRing (_root_.DirectLimit G f) :=
    nonUnitalSeminormedRingOfEventuallyBounded f hBound
  let : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  let : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  constructor
  intro c z w
  refine Quotient.inductionOn₂ z w (fun x y => ?_)
  change SeparationQuotient.mk (c • (x * y)) = SeparationQuotient.mk (x * (c • y))
  exact congrArg SeparationQuotient.mk (smul_comm c x y)

end CommScalar

namespace NonUnitalAlgebra

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action.

The nonunital algebra quotient map, with the multiplication and scalar action from the
previously constructed quotient structures. -/
noncomputable def normedLimitMk (hBound : IsEventuallyNormBounded f) :
    letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    _root_.DirectLimit G f →ₙₐ[𝕜] NormedLimit f hBound := by
  letI : NonUnitalSeminormedRing (_root_.DirectLimit G f) :=
    nonUnitalSeminormedRingOfEventuallyBounded f hBound
  letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  exact
    { toFun := fun z : _root_.DirectLimit G f => SeparationQuotient.mk z
      map_zero' := SeparationQuotient.mk_zero
      map_add' := SeparationQuotient.mk_add
      map_mul' := SeparationQuotient.mk_mul
      map_smul' := SeparationQuotient.mk_smul }

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action.

The nonunital algebra stage map followed by the zero-seminorm quotient. -/
noncomputable def ofNormed (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    G i →ₙₐ[𝕜] NormedLimit f hBound := by
  letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  exact (normedLimitMk f hBound).comp (_root_.DirectLimit.NonUnitalAlgebra.of G f i)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action.

The nonunital normed algebra stage has its quotient coefficient value. -/
@[simp]
theorem ofNormed_apply (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    ofNormed (𝕜 := 𝕜) f hBound i x =
      DirectLimit.normedLimitMk f hBound (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f) := by
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action.

Every transition leaves the nonunital normed algebra stage value unchanged. -/
theorem ofNormed_of_f (hBound : IsEventuallyNormBounded f)
    {i j : I} (hij : i ≤ j) (x : G i) :
    letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    ofNormed (𝕜 := 𝕜) f hBound j (f i j hij x) = ofNormed (𝕜 := 𝕜) f hBound i x := by
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  rw [ofNormed_apply, ofNormed_apply]
  exact congrArg (DirectLimit.normedLimitMk f hBound)
    (_root_.DirectLimit.mk_apply (f := f) i j x hij)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action.

The nonunital algebra stage and bounded linear stage have the same entire function. -/
theorem ofNormed_eq_ofCLM (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    letI : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    (ofNormed (𝕜 := 𝕜) f hBound i : G i → NormedLimit f hBound) =
      (Module.ofCLM (𝕜 := 𝕜) f hBound i : G i → NormedLimit f hBound) := by
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  funext x
  rw [ofNormed_apply, Module.ofCLM_apply]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of possibly nonunital normed
rings. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps. The scalars `𝕜` form a normed field; each stage is a normed
`𝕜`-algebra and the transition maps preserve the algebra operations and scalar action.

The algebra stage map is the previously proved bounded linear stage map on the same carrier with
the same norms and scalar action. -/
theorem ofNormed_continuous (hBound : IsEventuallyNormBounded f) (i : I) :
    let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound;
    let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound;
    Continuous (ofNormed (𝕜 := 𝕜) f hBound i) := by
  let : NonUnitalNormedRing (NormedLimit f hBound) := nonUnitalNormedRingNormedLimit f hBound
  let : NormedSpace 𝕜 (NormedLimit f hBound) := normedSpaceNormedLimit (𝕜 := 𝕜) f hBound
  exact (Module.ofCLM (𝕜 := 𝕜) f hBound i).continuous

end NonUnitalAlgebra

end NonUnitalAlgebra

end DirectLimit

namespace DirectLimit

universe uK uI uG uT

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {G : I → Type uG} [∀ i, NormedRing (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), RingHomClass (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)
  [DirectedSystem G (f · · ·)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps.

The unital raw ring retains the direct-limit unit and the same constructed limsup seminorm and
multiplication. -/
@[instance_reducible]
noncomputable def seminormedRingOfEventuallyBounded (hBound : IsEventuallyNormBounded f) :
    SeminormedRing (_root_.DirectLimit G f) := by
  let rawRing : Ring (_root_.DirectLimit G f) := inferInstance
  let rawNormedRing : NonUnitalSeminormedRing (_root_.DirectLimit G f) :=
    nonUnitalSeminormedRingOfEventuallyBounded f hBound
  exact { rawRing, rawNormedRing with }

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps.

The unital normed ring on the same zero-seminorm quotient of the unital algebraic limit. -/
@[instance_reducible]
noncomputable def normedRingNormedLimit (hBound : IsEventuallyNormBounded f) :
    NormedRing (NormedLimit f hBound) :=
  @SeparationQuotient.instNormedRing (_root_.DirectLimit G f)
    (seminormedRingOfEventuallyBounded f hBound)

end DirectLimit

namespace DirectLimit

universe uK uI uG uT

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {G : I → Type uG} [∀ i, NormedRing (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)
  [DirectedSystem G (f · · ·)]

section Algebra

variable {𝕜 : Type uK} [NormedField 𝕜]
  [∀ i, NormedAlgebra 𝕜 (G i)]
  [∀ i j (h : i ≤ j), AlgHomClass (T h) 𝕜 (G i) (G j)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The raw algebra, equipped with the constructed limsup seminorm and the existing scalar action of
its algebraic directed limit. -/
@[instance_reducible]
noncomputable def normedAlgebraOfEventuallyBounded (hBound : IsEventuallyNormBounded f) :
    letI : SeminormedRing (_root_.DirectLimit G f) := seminormedRingOfEventuallyBounded f hBound;
    NormedAlgebra 𝕜 (_root_.DirectLimit G f) := by
  letI : SeminormedRing (_root_.DirectLimit G f) := seminormedRingOfEventuallyBounded f hBound
  letI : NormedSpace 𝕜 (_root_.DirectLimit G f) :=
    normedSpaceOfEventuallyBounded (𝕜 := 𝕜) f hBound
  exact { norm_smul_le := norm_smul_le }

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The quotient's unital normed-algebra structure, preserving the same quotient norm, unit,
product, and scalar action. -/
@[instance_reducible]
noncomputable def normedAlgebraNormedLimit (hBound : IsEventuallyNormBounded f) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    NormedAlgebra 𝕜 (NormedLimit f hBound) := by
  letI : SeminormedRing (_root_.DirectLimit G f) := seminormedRingOfEventuallyBounded f hBound
  letI : NormedAlgebra 𝕜 (_root_.DirectLimit G f) :=
    normedAlgebraOfEventuallyBounded (𝕜 := 𝕜) f hBound
  letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  exact SeparationQuotient.instNormedAlgebra (𝕜 := 𝕜) (E := _root_.DirectLimit G f)

namespace Algebra

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The unital algebra quotient map to the zero-seminorm quotient. -/
noncomputable def normedLimitMk (hBound : IsEventuallyNormBounded f) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound;
    _root_.DirectLimit G f →ₐ[𝕜] NormedLimit f hBound := by
  letI : SeminormedRing (_root_.DirectLimit G f) := seminormedRingOfEventuallyBounded f hBound
  letI : NormedAlgebra 𝕜 (_root_.DirectLimit G f) :=
    normedAlgebraOfEventuallyBounded (𝕜 := 𝕜) f hBound
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound
  exact
    { toFun := SeparationQuotient.mk
      map_one' := SeparationQuotient.mk_one
      map_zero' := SeparationQuotient.mk_zero
      map_add' := SeparationQuotient.mk_add
      map_mul' := SeparationQuotient.mk_mul
      commutes' := SeparationQuotient.mk_algebraMap }

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The unital algebraic coefficient map followed by the zero-seminorm algebra quotient. -/
noncomputable def ofNormed (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound;
    G i →ₐ[𝕜] NormedLimit f hBound := by
  letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound
  exact (normedLimitMk f hBound).comp (_root_.DirectLimit.Algebra.of G f i)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The unital normed algebra stage has its quotient coefficient value. -/
@[simp]
theorem ofNormed_apply (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound;
    ofNormed (𝕜 := 𝕜) f hBound i x =
      DirectLimit.normedLimitMk f hBound (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f) := by
  let : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  let : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound
  rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

Every transition leaves the unital normed algebra stage value unchanged. -/
theorem ofNormed_of_f (hBound : IsEventuallyNormBounded f)
    {i j : I} (hij : i ≤ j) (x : G i) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound;
    ofNormed (𝕜 := 𝕜) f hBound j (f i j hij x) = ofNormed (𝕜 := 𝕜) f hBound i x := by
  let : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  let : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound
  rw [ofNormed_apply, ofNormed_apply]
  exact congrArg (DirectLimit.normedLimitMk f hBound)
    (_root_.DirectLimit.mk_apply (f := f) i j x hij)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The unital algebra stage and bounded linear stage have the same entire function. -/
theorem ofNormed_eq_ofCLM (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound;
    (ofNormed (𝕜 := 𝕜) f hBound i : G i → NormedLimit f hBound) =
      (Module.ofCLM (𝕜 := 𝕜) f hBound i : G i → NormedLimit f hBound) := by
  let : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  let : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound
  funext x
  rw [ofNormed_apply, Module.ofCLM_apply]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed rings. Assume `I` is
nonempty and directed. The transition homomorphisms form a compatible directed system. For each
starting stage there is a nonnegative common operator-norm bound on a tail of its transition
maps. The scalars `𝕜` form a normed field; each stage is a normed `𝕜`-algebra and the transition
maps preserve the algebra operations and scalar action.

The unital algebra stage is the already constructed bounded linear coefficient map, on the same
carrier and norm structures. -/
theorem ofNormed_continuous (hBound : IsEventuallyNormBounded f) (i : I) :
    letI : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound;
    letI : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound;
    Continuous (ofNormed (𝕜 := 𝕜) f hBound i) := by
  let : NormedRing (NormedLimit f hBound) := normedRingNormedLimit f hBound
  let : NormedAlgebra 𝕜 (NormedLimit f hBound) := normedAlgebraNormedLimit (𝕜 := 𝕜) f hBound
  exact (Module.ofCLM (𝕜 := 𝕜) f hBound i).continuous

end Algebra

end Algebra

end DirectLimit
