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

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Normed additive groups and separated directed limits

For norm-preserving transition maps, the actual stage norms descend to a norm
on the stock algebraic directed limit. The explicit normed-group dictionary
retains every original stage norm.

For a common element-norm bound on a tail at each source stage, the finite real
limsup of the stage norms defines an additive-group seminorm on the same
algebraic carrier. Its seminormed-group dictionary supplies the topology used
by the stock separation quotient. The resulting `NormedLimit` has the descended
norm, quotient map, zero-seminorm criterion and stage-representative norm laws.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DirectLimit

universe uI uG uT

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {G : I → Type uG} [∀ i, NormedAddCommGroup (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  [∀ i j (h : i ≤ j), AddMonoidHomClass (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)
  [DirectedSystem G (f · · ·)]
  (hNorm : ∀ i j (h : i ≤ j) (x : G i), ‖f i j h x‖ = ‖x‖)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. Every transition preserves norms exactly.

The additive-group norm induced by the norm-preserving transition maps on the existing
directed-system quotient. -/
noncomputable def addGroupNormOfNormPreserving : AddGroupNorm (_root_.DirectLimit G f) where
  toFun := _root_.DirectLimit.lift f (fun i x => ‖x‖)
    (fun i j h x => (hNorm i j h x).symm)
  map_zero' := by
    obtain ⟨i⟩ := ‹Nonempty I›
    rw [_root_.DirectLimit.zero_def (f := f) i, _root_.DirectLimit.lift_def]
    exact norm_zero
  add_le' z w := by
    refine _root_.DirectLimit.induction₂ (f := f) (fun i x y => ?_) z w
    simpa only [_root_.DirectLimit.add_def, _root_.DirectLimit.lift_def]
      using norm_add_le x y
  neg' z := by
    refine _root_.DirectLimit.induction (f := f) (fun i x => ?_) z
    simpa only [_root_.DirectLimit.neg_def, _root_.DirectLimit.lift_def]
      using norm_neg x
  eq_zero_of_map_eq_zero' := by
    intro z
    refine _root_.DirectLimit.induction (f := f) (fun i x => ?_) z
    intro hx
    change ‖x‖ = 0 at hx
    have hx0 : x = 0 := norm_eq_zero.mp hx
    subst x
    exact (_root_.DirectLimit.zero_def (f := f) i).symm

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. Every transition preserves norms exactly.

The normed additive-commutative-group structure on the same raw direct limit, using the standard
group-norm metric construction. -/
@[instance_reducible]
noncomputable def normedAddCommGroupOfNormPreserving :
    NormedAddCommGroup (_root_.DirectLimit G f) :=
  (addGroupNormOfNormPreserving f hNorm).toNormedAddCommGroup

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. Every transition preserves norms exactly.

Under the constructed structure, every stage representative has exactly its norm. -/
theorem normedAddCommGroupOfNormPreserving_norm_mk (i : I) (x : G i) :
    letI : NormedAddCommGroup (_root_.DirectLimit G f) :=
      normedAddCommGroupOfNormPreserving f hNorm;
    ‖(⟦⟨i, x⟩⟧ : _root_.DirectLimit G f)‖ = ‖x‖ := by
  let : NormedAddCommGroup (_root_.DirectLimit G f) :=
    normedAddCommGroupOfNormPreserving f hNorm
  rfl

end DirectLimit

namespace DirectLimit

open Filter

universe uI uG uT

variable {I : Type uI} [Preorder I]
  {G : I → Type uG} [∀ i, NormedAddCommGroup (G i)]
  {T : ∀ ⦃i j : I⦄, i ≤ j → Type uT}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]
  (f : ∀ i j (h : i ≤ j), T h)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices. For each starting stage
there is a nonnegative common operator-norm bound on a tail of its transition maps.

A common element-norm bound on a tail for each fixed source stage. The tail and bound may depend
on that stage. -/
def IsEventuallyNormBounded : Prop :=
  ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j in atTop,
    ∀ (h : i ≤ j) (x : G i), ‖f i j h x‖ ≤ C * ‖x‖

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices.

The norm net of a stage representative, extended by zero outside its cofinal upper cone. -/
noncomputable def stageTailNorm (i : I) (x : G i) (j : I) : ℝ := by
  classical
  exact if h : i ≤ j then ‖f i j h x‖ else 0

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices.

Every value of the stage-norm net is nonnegative. -/
theorem stageTailNorm_nonneg (i : I) (x : G i) (j : I) :
    0 ≤ stageTailNorm f i x j := by
  classical
  unfold stageTailNorm
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices. For each starting stage
there is a nonnegative common operator-norm bound on a tail of its transition maps.

An eventual common map bound supplies the upper bound for each representative's real limsup. -/
theorem stageTailNorm_boundedAbove
    (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    IsBoundedUnder (· ≤ ·) atTop (stageTailNorm f i x) := by
  classical
  obtain ⟨C, _, hC⟩ := hBound i
  refine isBoundedUnder_of_eventually_le (a := C * ‖x‖) ?_
  filter_upwards [hC, eventually_ge_atTop i] with j hj hij
  rw [stageTailNorm, dite_eq_left hij]
  exact hj hij x

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices.

Nonnegativity supplies the lower bound independently of the eventual common-map bound. -/
theorem stageTailNorm_boundedBelow (i : I) (x : G i) :
    IsBoundedUnder (· ≥ ·) atTop (stageTailNorm f i x) :=
  isBoundedUnder_of_eventually_ge
    (Eventually.of_forall (stageTailNorm_nonneg f i x))

section Additive

variable [∀ i j (h : i ≤ j), AddMonoidHomClass (T h) (G i) (G j)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices.

The zero representative has the constant zero stage-norm net. -/
theorem stageTailNorm_zero (i : I) :
    stageTailNorm f i (0 : G i) = fun _ => (0 : ℝ) := by
  classical
  funext j
  by_cases h : i ≤ j
  · rw [stageTailNorm, dite_eq_left h, map_zero, norm_zero]
  · rw [stageTailNorm, dite_eq_right h]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices.

Negation preserves the stage-norm net pointwise. -/
theorem stageTailNorm_neg (i : I) (x : G i) :
    stageTailNorm f i (-x) = stageTailNorm f i x := by
  classical
  funext j
  by_cases h : i ≤ j
  · rw [stageTailNorm, dite_eq_left h, stageTailNorm, dite_eq_left h, map_neg, norm_neg]
  · rw [stageTailNorm, dite_eq_right h, stageTailNorm, dite_eq_right h]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Specify a transition map for every ordered pair of indices.

The transition maps give the pointwise triangle inequality for representative norm nets. -/
theorem stageTailNorm_add_le (i : I) (x y : G i) (j : I) :
    stageTailNorm f i (x + y) j ≤
      stageTailNorm f i x j + stageTailNorm f i y j := by
  classical
  by_cases h : i ≤ j
  · rw [stageTailNorm, dite_eq_left h, stageTailNorm, dite_eq_left h,
      stageTailNorm, dite_eq_left h, map_add]
    exact norm_add_le _ _
  · rw [stageTailNorm, dite_eq_right h, stageTailNorm, dite_eq_right h,
      stageTailNorm, dite_eq_right h, zero_add]

variable [IsDirectedOrder I] [Nonempty I]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. Specify a transition map for every ordered pair of
indices. For each starting stage there is a nonnegative common operator-norm bound on a tail of
its transition maps.

The finite real limsups satisfy the triangle inequality under the eventual common-map bound. -/
theorem stageTailNorm_limsup_add_le
    (hBound : IsEventuallyNormBounded f) (i : I) (x y : G i) :
    limsup (stageTailNorm f i (x + y)) atTop ≤
      limsup (stageTailNorm f i x) atTop + limsup (stageTailNorm f i y) atTop := by
  have hx := stageTailNorm_boundedAbove f hBound i x
  have hy := stageTailNorm_boundedAbove f hBound i y
  have hx0 := stageTailNorm_boundedBelow f i x
  have hy0 := stageTailNorm_boundedBelow f i y
  have hxy0 := stageTailNorm_boundedBelow f i (x + y)
  exact (limsup_le_limsup (Eventually.of_forall (stageTailNorm_add_le f i x y))
    hxy0.isCoboundedUnder_le (isBoundedUnder_le_add hx hy)).trans
      (limsup_add_le hx0 hx hy0.isCoboundedUnder_le hy)

end Additive

section Coherent

variable [DirectedSystem G (f · · ·)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. The transition homomorphisms form a compatible directed system.

Coherence makes the two stage-norm nets agree above the later stage. -/
theorem stageTailNorm_map_eventuallyEq
    {i j : I} (h : i ≤ j) (x : G i) :
    stageTailNorm f i x =ᶠ[atTop] stageTailNorm f j (f i j h x) := by
  classical
  filter_upwards [eventually_ge_atTop j] with k hjk
  rw [stageTailNorm, dite_eq_left (h.trans hjk), stageTailNorm, dite_eq_left hjk]
  have hmap : f j k hjk (f i j h x) = f i k (h.trans hjk) x :=
    DirectedSystem.map_map (f := (f · · ·)) h hjk x
  exact congrArg (fun y : G k => ‖y‖) hmap.symm

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. The transition homomorphisms form a compatible directed system.

The real limsup is independent of moving a representative along an transition. -/
theorem stageTailNorm_limsup_map
    {i j : I} (h : i ≤ j) (x : G i) :
    limsup (stageTailNorm f i x) atTop =
      limsup (stageTailNorm f j (f i j h x)) atTop :=
  limsup_congr (stageTailNorm_map_eventuallyEq f h x)

end Coherent

variable [IsDirectedOrder I] [Nonempty I]
  [∀ i j (h : i ≤ j), AddMonoidHomClass (T h) (G i) (G j)]
  [DirectedSystem G (f · · ·)]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The additive-group seminorm on the algebraic direct limit, obtained by descending the finite
real limsup of the stage norms. -/
noncomputable def addGroupSeminormOfEventuallyBounded
    (hBound : IsEventuallyNormBounded f) : AddGroupSeminorm (_root_.DirectLimit G f) where
  toFun := _root_.DirectLimit.lift f
    (fun i x => limsup (stageTailNorm f i x) atTop)
    (fun i j h x => stageTailNorm_limsup_map f h x)
  map_zero' := by
    obtain ⟨i⟩ := ‹Nonempty I›
    rw [_root_.DirectLimit.zero_def (f := f) i, _root_.DirectLimit.lift_def,
      stageTailNorm_zero, limsup_const]
  add_le' z w := by
    refine _root_.DirectLimit.induction₂ (f := f) (fun i x y => ?_) z w
    simpa only [_root_.DirectLimit.add_def, _root_.DirectLimit.lift_def]
      using stageTailNorm_limsup_add_le f hBound i x y
  neg' z := by
    refine _root_.DirectLimit.induction (f := f) (fun i x => ?_) z
    simp only [_root_.DirectLimit.neg_def, _root_.DirectLimit.lift_def, stageTailNorm_neg]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The seminormed additive-group structure on the same algebraic carrier, with the direct-limit
addition and subtraction. -/
@[instance_reducible]
noncomputable def seminormedAddCommGroupOfEventuallyBounded
    (hBound : IsEventuallyNormBounded f) : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
  (addGroupSeminormOfEventuallyBounded f hBound).toSeminormedAddCommGroup

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The constructed raw seminorm has exactly the real stage-limsup formula. -/
theorem seminormedAddCommGroupOfEventuallyBounded_norm_mk
    (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    letI : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
      seminormedAddCommGroupOfEventuallyBounded f hBound;
    ‖(⟦⟨i, x⟩⟧ : _root_.DirectLimit G f)‖ = limsup (stageTailNorm f i x) atTop := by
  let : SeminormedAddCommGroup (_root_.DirectLimit G f) :=
    seminormedAddCommGroupOfEventuallyBounded f hBound
  rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The separated quotient of the algebraic direct limit by the zero-seminorm relation. No
completion is taken in this carrier. -/
noncomputable def NormedLimit (hBound : IsEventuallyNormBounded f) : Type (max uI uG) :=
  @SeparationQuotient (_root_.DirectLimit G f)
    (seminormedAddCommGroupOfEventuallyBounded f hBound).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The normed-group structure on the zero-seminorm quotient, with its separated addition, metric
and descended norm. -/
@[instance_reducible]
noncomputable def normedAddCommGroupNormedLimit
    (hBound : IsEventuallyNormBounded f) : NormedAddCommGroup (NormedLimit f hBound) :=
  @SeparationQuotient.instNormedAddCommGroup (_root_.DirectLimit G f)
    (seminormedAddCommGroupOfEventuallyBounded f hBound)

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The additive quotient map from the algebraic limit. -/
noncomputable def normedLimitMk (hBound : IsEventuallyNormBounded f) :
    letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    _root_.DirectLimit G f →+ NormedLimit f hBound := by
  let s := seminormedAddCommGroupOfEventuallyBounded f hBound
  letI : SeminormedAddCommGroup (_root_.DirectLimit G f) := s
  letI : AddCommGroup (_root_.DirectLimit G f) := s.toAddCommGroup
  letI : TopologicalSpace (_root_.DirectLimit G f) :=
    s.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  exact
    { toFun := fun z : _root_.DirectLimit G f => SeparationQuotient.mk z
      map_zero' := SeparationQuotient.mk_zero
      map_add' := fun x y => SeparationQuotient.mk_add x y }

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

Quotienting preserves precisely the constructed raw seminorm value. -/
theorem normedLimitMk_norm (hBound : IsEventuallyNormBounded f)
    (z : _root_.DirectLimit G f) :
    letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    ‖normedLimitMk f hBound z‖ = addGroupSeminormOfEventuallyBounded f hBound z := by
  let s := seminormedAddCommGroupOfEventuallyBounded f hBound
  let : SeminormedAddCommGroup (_root_.DirectLimit G f) := s
  let : AddCommGroup (_root_.DirectLimit G f) := s.toAddCommGroup
  let : TopologicalSpace (_root_.DirectLimit G f) :=
    s.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  exact @SeparationQuotient.norm_mk (_root_.DirectLimit G f) s z

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The quotient's norm is the real stage-norm limsup. -/
theorem normedLimitMk_norm_mk (hBound : IsEventuallyNormBounded f) (i : I) (x : G i) :
    letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    ‖normedLimitMk f hBound (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f)‖ =
      limsup (stageTailNorm f i x) atTop := by
  let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  rw [normedLimitMk_norm]
  rfl

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

The elements killed by the quotient map are exactly those with zero seminorm. -/
theorem normedLimitMk_eq_zero_iff (hBound : IsEventuallyNormBounded f)
    (z : _root_.DirectLimit G f) :
    letI : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound;
    normedLimitMk f hBound z = 0 ↔ addGroupSeminormOfEventuallyBounded f hBound z = 0 := by
  let : NormedAddCommGroup (NormedLimit f hBound) := normedAddCommGroupNormedLimit f hBound
  rw [← norm_eq_zero, normedLimitMk_norm]

/-- Let `I` be a preordered index type and let `(Gᵢ)` be a family of normed additive commutative
groups. Assume `I` is nonempty and directed. The transition homomorphisms form a compatible
directed system. For each starting stage there is a nonnegative common operator-norm bound on a
tail of its transition maps.

Every element of the zero-seminorm quotient still has an finite-stage representative. -/
theorem normedLimit_exists_stage (hBound : IsEventuallyNormBounded f)
    (z : NormedLimit f hBound) :
    ∃ i, ∃ x : G i,
      normedLimitMk f hBound (⟦⟨i, x⟩⟧ : _root_.DirectLimit G f) = z := by
  let s := seminormedAddCommGroupOfEventuallyBounded f hBound
  let : SeminormedAddCommGroup (_root_.DirectLimit G f) := s
  let : AddCommGroup (_root_.DirectLimit G f) := s.toAddCommGroup
  let : TopologicalSpace (_root_.DirectLimit G f) :=
    s.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨y, hy⟩ := SeparationQuotient.surjective_mk z
  obtain ⟨i, x, hx⟩ := _root_.DirectLimit.exists_eq_mk f y
  refine ⟨i, x, ?_⟩
  rw [← hx]
  exact hy

end DirectLimit
