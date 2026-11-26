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

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Unilateral shift, backward shift and the coordinate defect

For a real or complex normed inner-product space `G`, the unilateral shift on `ℓ²(ℕ,G)` is
`S(x_0,x_1,…)=(0,x_0,x_1,…)`. It is a linear isometry. When `G` is complete, its adjoint is the
backward shift `B(x)_n=x_(n+1)`, satisfying `BS=I`.

The defect `P=I-SB` projects onto the zeroth-coordinate copy of `G`. It is compact when `G` is
finite-dimensional. The shift is Fredholm exactly in that finite-dimensional case; its algebraic
index is `-finrank_𝕜(G)`. For infinite-dimensional multiplicity this totalized index value is
zero and does not imply Fredholmness.
-/

@[expose] public section

noncomputable section

namespace lp

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [hG : CompleteSpace G]

/-- **Coordinate function of a right unilateral shift.** Let `G` be a normed additive
commutative group and `x ∈ ℓ²(ℕ,G)`. `unilateralShiftSeq x` has zeroth value zero and
successor value `x_n` at `n+1`. -/
def unilateralShiftSeq (x : lp (fun _ : ℕ ↦ G) 2) : ℕ → G
  | 0 => 0
  | n + 1 => x n

omit hG in
@[simp]
theorem unilateralShiftSeq_zero (x : lp (fun _ : ℕ ↦ G) 2) :
    unilateralShiftSeq x 0 = 0 :=
  rfl

omit hG in
@[simp]
theorem unilateralShiftSeq_succ (x : lp (fun _ : ℕ ↦ G) 2) (n : ℕ) :
    unilateralShiftSeq x (n + 1) = x n :=
  rfl

omit hG in
theorem unilateralShiftSeq_mem (x : lp (fun _ : ℕ ↦ G) 2) :
    Memℓp (unilateralShiftSeq x) 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hx : Summable (fun n => ‖x n‖ ^ (2 : ENNReal).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp x)
  have hshift :
      (fun n => ‖unilateralShiftSeq x (n + 1)‖ ^ (2 : ENNReal).toReal) =
        fun n => ‖x n‖ ^ (2 : ENNReal).toReal := by
    funext n
    rfl
  have htail :
      Summable (fun n => ‖unilateralShiftSeq x (n + 1)‖ ^ (2 : ENNReal).toReal) := by
    rw [hshift]
    exact hx
  exact memℓp_gen ((summable_nat_add_iff 1).mp htail)

omit hG in
private theorem unilateralShiftSeq_norm (x : lp (fun _ : ℕ ↦ G) 2) :
    ‖(⟨unilateralShiftSeq x, unilateralShiftSeq_mem x⟩ :
        lp (fun _ : ℕ ↦ G) 2)‖ = ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hx : Summable (fun n => ‖x n‖ ^ (2 : ENNReal).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp x)
  have hshift :
      (fun n => ‖unilateralShiftSeq x (n + 1)‖ ^ (2 : ENNReal).toReal) =
        fun n => ‖x n‖ ^ (2 : ENNReal).toReal := by
    funext n
    rfl
  have htail :
      Summable (fun n => ‖unilateralShiftSeq x (n + 1)‖ ^ (2 : ENNReal).toReal) := by
    rw [hshift]
    exact hx
  have hsum : Summable (fun n => ‖unilateralShiftSeq x n‖ ^ (2 : ENNReal).toReal) :=
    (summable_nat_add_iff 1).mp htail
  have hzero : ‖unilateralShiftSeq x 0‖ ^ (2 : ENNReal).toReal = 0 := by
    calc
      ‖unilateralShiftSeq x 0‖ ^ (2 : ENNReal).toReal =
          ‖(0 : G)‖ ^ (2 : ENNReal).toReal := by rw [unilateralShiftSeq_zero]
      _ = (0 : ℝ) ^ (2 : ENNReal).toReal := by
        have hnorm : ‖(0 : G)‖ = 0 := _root_.norm_zero
        rw [hnorm]
      _ = 0 := Real.zero_rpow (ne_of_gt hp)
  have hrange :
      ∑ n ∈ Finset.range 1,
          ‖unilateralShiftSeq x n‖ ^ (2 : ENNReal).toReal = 0 := by
    rw [Finset.sum_range_one]
    exact hzero
  have hadd := Summable.sum_add_tsum_nat_add 1 hsum
  rw [hrange, zero_add] at hadd
  have htailSum :
      (∑' n, ‖unilateralShiftSeq x (n + 1)‖ ^ (2 : ENNReal).toReal) =
        ∑' n, ‖x n‖ ^ (2 : ENNReal).toReal := by
    rw [hshift]
  have hsumEq :
      (∑' n, ‖unilateralShiftSeq x n‖ ^ (2 : ENNReal).toReal) =
        ∑' n, ‖x n‖ ^ (2 : ENNReal).toReal := by
    rw [← hadd, htailSum]
  have hnormShift :
      ‖(⟨unilateralShiftSeq x, unilateralShiftSeq_mem x⟩ :
          lp (fun _ : ℕ ↦ G) 2)‖ =
        ((∑' n, ‖unilateralShiftSeq x n‖ ^ (2 : ENNReal).toReal) ^
          ((1 : ℝ) / (2 : ENNReal).toReal)) := by
    rw [lp.norm_eq_tsum_rpow hp]
  have hnormInput :
      ‖x‖ = ((∑' n, ‖x n‖ ^ (2 : ENNReal).toReal) ^
        ((1 : ℝ) / (2 : ENNReal).toReal)) := by
    rw [lp.norm_eq_tsum_rpow hp]
  rw [hnormShift, hnormInput, hsumEq]

/-- **Linear unilateral coordinate shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
`unilateralShiftLinear : L →ₗ[𝕜] L` has zeroth coordinate zero and `(Sx)_(n+1)=x_n`. -/
def unilateralShiftLinear :
    lp (fun _ : ℕ ↦ G) 2 →ₗ[𝕜] lp (fun _ : ℕ ↦ G) 2 where
  toFun x := ⟨unilateralShiftSeq x, unilateralShiftSeq_mem x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    cases n with
    | zero =>
      simp only [unilateralShiftSeq_zero, lp.coeFn_add, Pi.add_apply, add_zero]
    | succ n =>
      simp only [unilateralShiftSeq_succ, lp.coeFn_add, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext n
    cases n with
    | zero =>
      simp only [unilateralShiftSeq_zero, lp.coeFn_smul, Pi.smul_apply, smul_zero]
    | succ n =>
      simp only [unilateralShiftSeq_succ, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

omit hG in
theorem unilateralShiftLinear_norm (x : lp (fun _ : ℕ ↦ G) 2) :
    ‖unilateralShiftLinear (𝕜 := 𝕜) x‖ = ‖x‖ := by
  have h : unilateralShiftLinear (𝕜 := 𝕜) x =
      (⟨unilateralShiftSeq x, unilateralShiftSeq_mem x⟩ :
        lp (fun _ : ℕ ↦ G) 2) := rfl
  rw [h]
  exact unilateralShiftSeq_norm x

/-- **Bounded forward unilateral shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
`unilateralShift : L →L[𝕜] L` is the norm-preserving operator `S`; completeness is not
needed for this bounded shift. -/
noncomputable def unilateralShift :
    lp (fun _ : ℕ ↦ G) 2 →L[𝕜] lp (fun _ : ℕ ↦ G) 2 :=
  unilateralShiftLinear.mkContinuous 1 fun x ↦ by
    rw [unilateralShiftLinear_norm, one_mul]

omit hG in
/-- **Zero initial coordinate of the unilateral shift.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
for every `x ∈ L`, `(unilateralShift x)_0=0`. -/
@[simp]
theorem unilateralShift_apply_zero (x : lp (fun _ : ℕ ↦ G) 2) :
    unilateralShift (𝕜 := 𝕜) x 0 = 0 := by
  have h : unilateralShift (𝕜 := 𝕜) x =
      unilateralShiftLinear (𝕜 := 𝕜) x := rfl
  rw [h]
  exact unilateralShiftSeq_zero x

omit hG in
/-- **Successor coordinate of the unilateral shift.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
for `x ∈ L` and `n : ℕ`, `(unilateralShift x)_(n+1)=x_n`. -/
@[simp]
theorem unilateralShift_apply_succ (x : lp (fun _ : ℕ ↦ G) 2) (n : ℕ) :
    unilateralShift (𝕜 := 𝕜) x (n + 1) = x n := by
  have h : unilateralShift (𝕜 := 𝕜) x =
      unilateralShiftLinear (𝕜 := 𝕜) x := rfl
  rw [h]
  exact unilateralShiftSeq_succ x n

omit hG in
/-- **Unilateral shift of a scalar-multiplicity singleton.** Let `𝕜` be real or complex and
`G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. for `n : ℕ` and `g ∈ G`, `S(single_n g)=single_(n+1) g`. -/
@[simp]
theorem unilateralShift_single (n : ℕ) (g : G) :
    unilateralShift (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ ↦ G) 2 n g) =
      lp.single (E := fun _ : ℕ ↦ G) 2 (n + 1) g := by
  apply lp.ext
  funext j
  cases j with
  | zero =>
    rw [unilateralShift_apply_zero]
    rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 (n + 1) g
      (Nat.zero_ne_add_one n)]
  | succ j =>
    rw [unilateralShift_apply_succ]
    by_cases h : j = n
    · subst h
      rw [lp.single_apply_self, lp.single_apply_self]
    · have h' : j + 1 ≠ n + 1 := Nat.succ_ne_succ_iff.mpr h
      rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 n g h]
      rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 (n + 1) g h']

omit hG in
/-- **Norm preservation of the unilateral shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. for every
`x ∈ L`, `‖Sx‖₂=‖x‖₂`. -/
theorem unilateralShift_norm (x : lp (fun _ : ℕ ↦ G) 2) :
    ‖unilateralShift (𝕜 := 𝕜) x‖ = ‖x‖ := by
  have h : unilateralShift (𝕜 := 𝕜) x =
      unilateralShiftLinear (𝕜 := 𝕜) x := rfl
  rw [h]
  exact unilateralShiftLinear_norm x

omit hG in
/-- **Metric isometry of the unilateral shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. `S` is an
isometry for the square-summable norm metric. -/
theorem unilateralShift_isometry :
    Isometry (unilateralShift (𝕜 := 𝕜) (G := G)) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr unilateralShift_norm

omit hG in
/-- **Injectivity of the unilateral shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. the
bounded shift `S : L → L` is injective, including the zero-multiplicity case. -/
theorem unilateralShift_injective :
    Function.Injective (unilateralShift (𝕜 := 𝕜) (G := G)) :=
  (unilateralShift_isometry (𝕜 := 𝕜) (G := G)).injective

/-- **Closed range of the complete-multiplicity unilateral shift.** Let `𝕜` be real or complex
and `G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. the range of `S` is norm-closed in `L`. -/
theorem unilateralShift_isClosed_range :
    IsClosed (Set.range (unilateralShift (𝕜 := 𝕜) (G := G))) :=
  (unilateralShift_isometry (𝕜 := 𝕜) (G := G)).isClosedEmbedding.isClosed_range

omit hG in
/-- **Nonsurjectivity for nonzero unilateral multiplicity.** Let `𝕜` be real or complex and
`G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. if `G` is nontrivial, `S : L → L` is not surjective because every
shifted vector has zeroth coordinate zero. -/
theorem unilateralShift_not_surjective [Nontrivial G] :
    ¬ Function.Surjective (unilateralShift (𝕜 := 𝕜) (G := G)) := by
  intro hsurj
  obtain ⟨g, hg⟩ := exists_ne (0 : G)
  obtain ⟨x, hx⟩ :=
    hsurj (lp.single (E := fun _ : ℕ ↦ G) 2 0 g)
  apply hg
  simpa using (congrArg (fun y => y 0) hx).symm

/-- **Backward shift as the Hilbert adjoint.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. Assume
`G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. `backwardShift : L →L[𝕜]
L` is `B=S*`, with `(Bx)_n=x_(n+1)`. -/
noncomputable abbrev backwardShift :
    lp (fun _ : ℕ ↦ G) 2 →L[𝕜] lp (fun _ : ℕ ↦ G) 2 :=
  ContinuousLinearMap.adjoint (unilateralShift (𝕜 := 𝕜) (G := G))

/-- **Coordinate formula of the backward shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. Assume
`G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. for `x ∈ L` and `n : ℕ`,
`backwardShift x n=x_(n+1)`. -/
@[simp]
theorem backwardShift_apply (x : lp (fun _ : ℕ ↦ G) 2) (n : ℕ) :
    backwardShift (𝕜 := 𝕜) x n = x (n + 1) := by
  apply ext_inner_left 𝕜
  intro g
  calc
    inner 𝕜 g (backwardShift (𝕜 := 𝕜) x n) =
        inner 𝕜 (lp.single (E := fun _ : ℕ ↦ G) 2 n g)
          (backwardShift (𝕜 := 𝕜) x) :=
      (lp.inner_single_left (𝕜 := 𝕜) n g
        (backwardShift (𝕜 := 𝕜) x)).symm
    _ = inner 𝕜 (unilateralShift (𝕜 := 𝕜)
        (lp.single (E := fun _ : ℕ ↦ G) 2 n g)) x :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner 𝕜 (lp.single (E := fun _ : ℕ ↦ G) 2 (n + 1) g) x := by
      rw [unilateralShift_single]
    _ = inner 𝕜 g (x (n + 1)) :=
      lp.inner_single_left (𝕜 := 𝕜) (n + 1) g x

/-- **Backward shift kills the initial singleton.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. for `g ∈ G`,
`B(single_0 g)=0`. -/
@[simp]
theorem backwardShift_single_zero (g : G) :
    backwardShift (𝕜 := 𝕜)
        (lp.single (E := fun _ : ℕ ↦ G) 2 0 g) = 0 := by
  apply lp.ext
  funext j
  rw [backwardShift_apply]
  rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 0 g
    (Nat.succ_ne_zero j)]
  rfl

/-- **Backward shift of a successor singleton.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. Assume
`G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. for `n : ℕ`, `g ∈ G`,
`B(single_(n+1) g)=single_n g`. -/
@[simp]
theorem backwardShift_single_succ (n : ℕ) (g : G) :
    backwardShift (𝕜 := 𝕜)
        (lp.single (E := fun _ : ℕ ↦ G) 2 (n + 1) g) =
      lp.single (E := fun _ : ℕ ↦ G) 2 n g := by
  apply lp.ext
  funext j
  rw [backwardShift_apply]
  by_cases h : j = n
  · subst h
    rw [lp.single_apply_self, lp.single_apply_self]
  · have h' : j + 1 ≠ n + 1 := Nat.succ_ne_succ_iff.mpr h
    rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 (n + 1) g h']
    rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 n g h]

/-- **Backward shift is a left inverse.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. Assume
`G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. `B∘S=I_L`. -/
@[simp]
theorem backwardShift_comp_unilateralShift :
    backwardShift (𝕜 := 𝕜) (G := G) ∘L
      unilateralShift (𝕜 := 𝕜) (G := G) = 1 :=
  (unilateralShift (𝕜 := 𝕜) (G := G)).norm_map_iff_adjoint_comp_self.mp
    unilateralShift_norm

/-- **Surjectivity of the backward shift.** Let `𝕜` be real or complex and `G` a normed
inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`. Assume
`G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. `B : L → L` is
surjective, with `S` providing a right inverse. -/
theorem backwardShift_surjective :
    Function.Surjective (backwardShift (𝕜 := 𝕜) (G := G)) := by
  intro x
  refine ⟨unilateralShift (𝕜 := 𝕜) x, ?_⟩
  have h := congrArg
    (fun T : lp (fun _ : ℕ ↦ G) 2 →L[𝕜] lp (fun _ : ℕ ↦ G) 2 ↦ T x)
    (backwardShift_comp_unilateralShift (𝕜 := 𝕜) (G := G))
  change backwardShift (𝕜 := 𝕜)
      (unilateralShift (𝕜 := 𝕜) x) = x at h
  exact h

/-- **Projection onto the unilateral shift's initial-coordinate defect.** Let `𝕜` be real or
complex and `G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. `unilateralShiftDefectProjection=P=I-SB`, retaining the zeroth coordinate of a
vector and setting every successor coordinate to zero. -/
noncomputable def unilateralShiftDefectProjection :
    lp (fun _ : ℕ ↦ G) 2 →L[𝕜] lp (fun _ : ℕ ↦ G) 2 :=
  1 - unilateralShift (𝕜 := 𝕜) (G := G) ∘L
    backwardShift (𝕜 := 𝕜) (G := G)

/-- **Initial coordinate retained by the defect projection.** Let `𝕜` be real or complex and
`G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. for `x ∈ L`, `(Px)_0=x_0`. -/
@[simp]
theorem unilateralShiftDefectProjection_apply_zero
    (x : lp (fun _ : ℕ ↦ G) 2) :
    unilateralShiftDefectProjection (𝕜 := 𝕜) x 0 = x 0 := by
  simp [unilateralShiftDefectProjection, ContinuousLinearMap.comp_apply]

/-- **Successor coordinates killed by the defect projection.** Let `𝕜` be real or complex and
`G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. for `x ∈ L` and `n : ℕ`, `(Px)_(n+1)=0`. -/
@[simp]
theorem unilateralShiftDefectProjection_apply_succ
    (x : lp (fun _ : ℕ ↦ G) 2) (n : ℕ) :
    unilateralShiftDefectProjection (𝕜 := 𝕜) x (n + 1) = 0 := by
  simp [unilateralShiftDefectProjection, ContinuousLinearMap.comp_apply]

/-- **Shift and backward shift give the complement of the defect.** Let `𝕜` be real or complex
and `G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. `S∘B=I_L-P`. -/
@[simp]
theorem unilateralShift_comp_backwardShift :
    unilateralShift (𝕜 := 𝕜) (G := G) ∘L
      backwardShift (𝕜 := 𝕜) (G := G) =
        1 - unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G) := by
  simp [unilateralShiftDefectProjection]

/-- **Range of the zeroth-coordinate defect projection.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. for `x ∈ L`,
`x∈range P` exactly when `x_(n+1)=0` for every `n : ℕ`. -/
theorem mem_unilateralShiftDefectProjection_range_iff
    (x : lp (fun _ : ℕ ↦ G) 2) :
    x ∈ (unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G)).range ↔
      ∀ n : ℕ, x (n + 1) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ n
    simp
  · intro hx
    refine ⟨x, ?_⟩
    apply lp.ext
    funext n
    cases n with
    | zero => simp
    | succ n => simpa using (hx n).symm

/-- **Defect kernel is the unilateral shift range.** Let `𝕜` be real or complex and `G` a
normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. `ker P=range S`. -/
theorem unilateralShiftDefectProjection_ker :
    (unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G)).ker =
      (unilateralShift (𝕜 := 𝕜) (G := G)).range := by
  ext x
  constructor
  · intro hx
    change unilateralShiftDefectProjection (𝕜 := 𝕜) x = 0 at hx
    refine ⟨backwardShift (𝕜 := 𝕜) x, ?_⟩
    have h := congrArg
      (fun T : lp (fun _ : ℕ ↦ G) 2 →L[𝕜] lp (fun _ : ℕ ↦ G) 2 ↦ T x)
      (unilateralShift_comp_backwardShift (𝕜 := 𝕜) (G := G))
    change unilateralShift (𝕜 := 𝕜)
        (backwardShift (𝕜 := 𝕜) x) =
      x - unilateralShiftDefectProjection (𝕜 := 𝕜) x at h
    rw [hx, sub_zero] at h
    exact h
  · rintro ⟨y, rfl⟩
    change unilateralShiftDefectProjection (𝕜 := 𝕜)
      (unilateralShift (𝕜 := 𝕜) y) = 0
    apply lp.ext
    funext n
    cases n <;> simp

/-- **Self-adjoint idempotence of the unilateral defect.** Let `𝕜` be real or complex and `G`
a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`. `P²=P` and `P*=P`. -/
theorem unilateralShiftDefectProjection_isStarProjection :
    IsStarProjection
      (unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G)) where
  isIdempotentElem := by
    change unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G) *
        unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G) =
      unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G)
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext n
    cases n <;> simp [mul_apply_eq_comp]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff]
    have hP : unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G) =
        1 - unilateralShift (𝕜 := 𝕜) (G := G) *
          star (unilateralShift (𝕜 := 𝕜) (G := G)) := by
      rw [unilateralShiftDefectProjection,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
    rw [hP]
    change ContinuousLinearMap.adjoint
        (1 - unilateralShift (𝕜 := 𝕜) (G := G) *
          star (unilateralShift (𝕜 := 𝕜) (G := G))) =
      1 - unilateralShift (𝕜 := 𝕜) (G := G) *
        star (unilateralShift (𝕜 := 𝕜) (G := G))
    calc
      ContinuousLinearMap.adjoint
          (1 - unilateralShift (𝕜 := 𝕜) (G := G) *
          star (unilateralShift (𝕜 := 𝕜) (G := G))) =
          ContinuousLinearMap.adjoint (1 : lp (fun _ : ℕ ↦ G) 2 →L[𝕜]
            lp (fun _ : ℕ ↦ G) 2) -
            ContinuousLinearMap.adjoint
              (unilateralShift (𝕜 := 𝕜) (G := G) *
                star (unilateralShift (𝕜 := 𝕜) (G := G))) :=
        map_sub ContinuousLinearMap.adjoint _ _
      _ = 1 - ContinuousLinearMap.adjoint
          (star (unilateralShift (𝕜 := 𝕜) (G := G))) ∘L
          ContinuousLinearMap.adjoint
            (unilateralShift (𝕜 := 𝕜) (G := G)) := by
        rw [ContinuousLinearMap.adjoint_one, ContinuousLinearMap.mul_def,
          ContinuousLinearMap.adjoint_comp]
      _ = 1 - unilateralShift (𝕜 := 𝕜) (G := G) *
          star (unilateralShift (𝕜 := 𝕜) (G := G)) := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.mul_def]

private theorem unilateralShiftDefectProjection_eq_single_comp_eval :
    unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G) =
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ G) 2 0).comp
        (lp.evalCLM 𝕜 (fun _ : ℕ ↦ G) 2 0) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  cases n with
  | zero =>
      rw [unilateralShiftDefectProjection_apply_zero, ContinuousLinearMap.comp_apply,
        lp.singleContinuousLinearMap_apply, lp.single_apply_self]
      rfl
  | succ n =>
      rw [unilateralShiftDefectProjection_apply_succ, ContinuousLinearMap.comp_apply,
        lp.singleContinuousLinearMap_apply]
      rw [lp.single_apply_ne (E := fun _ : ℕ ↦ G) 2 0
        ((lp.evalCLM 𝕜 (fun _ : ℕ ↦ G) 2 0) x)
        (Nat.succ_ne_zero n)]

/-- **Compact initial defect for finite-dimensional multiplicity.** Let `𝕜` be real or complex
and `G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. if `G` is finite-dimensional over `𝕜`, the operator `P` is compact. -/
theorem unilateralShiftDefectProjection_isCompact [FiniteDimensional 𝕜 G] :
    IsCompactOperator
      (unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G)) := by
  let _ : ProperSpace G := FiniteDimensional.proper_rclike 𝕜 G
  rw [unilateralShiftDefectProjection_eq_single_comp_eval]
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ ↦ G) 2 0)).comp_clm _

/-- **Adjoint product equation of the unilateral isometry.** Let `𝕜` be real or complex and
`G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. `S* S=I_L`. -/
@[simp]
theorem star_unilateralShift_mul_unilateralShift :
    star (unilateralShift (𝕜 := 𝕜) (G := G)) *
      unilateralShift (𝕜 := 𝕜) (G := G) = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  exact backwardShift_comp_unilateralShift (𝕜 := 𝕜) (G := G)

/-- **Unilateral adjoint product equals the defect complement.** Let `𝕜` be real or complex
and `G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. `S S*=I_L-P`. -/
theorem unilateralShift_mul_star_unilateralShift :
    unilateralShift (𝕜 := 𝕜) (G := G) *
      star (unilateralShift (𝕜 := 𝕜) (G := G)) =
        1 - unilateralShiftDefectProjection (𝕜 := 𝕜) (G := G) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  exact unilateralShift_comp_backwardShift (𝕜 := 𝕜) (G := G)

omit hG in
private theorem unilateralShift_evalZero_surjective :
    Function.Surjective
      (lp.evalCLM 𝕜 (fun _ : ℕ ↦ G) 2 0) := by
  intro g
  refine ⟨lp.single (E := fun _ : ℕ ↦ G) 2 0 g, ?_⟩
  change lp.single (E := fun _ : ℕ ↦ G) 2 0 g 0 = g
  rw [lp.single_apply_self]

private theorem unilateralShift_range_eq_ker_evalZero :
    (unilateralShift (𝕜 := 𝕜) (G := G)).range =
      (lp.evalCLM 𝕜 (fun _ : ℕ ↦ G) 2 0).ker := by
  rw [← unilateralShiftDefectProjection_ker (𝕜 := 𝕜) (G := G)]
  ext x
  constructor
  · intro hx
    change unilateralShiftDefectProjection (𝕜 := 𝕜) x = 0 at hx
    change x 0 = 0
    simpa using congrArg (fun y => y 0) hx
  · intro hx
    change x 0 = 0 at hx
    change unilateralShiftDefectProjection (𝕜 := 𝕜) x = 0
    apply lp.ext
    funext n
    cases n with
    | zero => simp [hx]
    | succ n => simp

private noncomputable def unilateralShiftCokerEquiv :
    (lp (fun _ : ℕ ↦ G) 2 ⧸
      (unilateralShift (𝕜 := 𝕜) (G := G)).range) ≃ₗ[𝕜] G :=
  (Submodule.quotEquivOfEq _ _
      (unilateralShift_range_eq_ker_evalZero (𝕜 := 𝕜) (G := G))).trans
    ((lp.evalCLM 𝕜 (fun _ : ℕ ↦ G) 2 0).toLinearMap.quotKerEquivOfSurjective
      (unilateralShift_evalZero_surjective (𝕜 := 𝕜) (G := G)))

/-- **Fredholmness exactly for finite-dimensional shift multiplicity.** Let `𝕜` be real or
complex and `G` a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write
`Sx=(0,x_0,x_1,…)`. Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and
`P=I-SB`. `S` is Fredholm exactly when `FiniteDimensional 𝕜 G`. -/
theorem unilateralShift_isFredholm_iff :
    (unilateralShift (𝕜 := 𝕜) (G := G)).IsFredholm ↔
      FiniteDimensional 𝕜 G := by
  constructor
  · intro hS
    let _ : (unilateralShift (𝕜 := 𝕜) (G := G)).range.CoFG :=
      hS.finite_coker
    let e := unilateralShiftCokerEquiv (𝕜 := 𝕜) (G := G)
    exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  · intro hG
    let _ : FiniteDimensional 𝕜 G := hG
    let e := unilateralShiftCokerEquiv (𝕜 := 𝕜) (G := G)
    have hcofg : (unilateralShift (𝕜 := 𝕜) (G := G)).range.CoFG :=
      FiniteDimensional.of_injective e.toLinearMap e.injective
    exact (unilateralShift_isometry (𝕜 := 𝕜) (G := G)).isClosedEmbedding.isFredholm hcofg

/-- **Totalized algebraic index of the unilateral shift.** Let `𝕜` be real or complex and `G`
a normed inner-product `𝕜`-space. On `L=lp (fun _ : ℕ => G) 2`, write `Sx=(0,x_0,x_1,…)`.
Assume `G` is complete, and put `B=S*`, `(Bx)_n=x_(n+1)`, and `P=I-SB`.
`S.index=-(finrank_𝕜 G : ℤ)`. For infinite-dimensional `G`, `finrank` and this totalized
index value are zero; the formula does not assert Fredholmness in that case. -/
theorem unilateralShift_index :
    (unilateralShift (𝕜 := 𝕜) (G := G)).index =
      -(Module.finrank 𝕜 G : ℤ) := by
  rw [LinearMap.index_of_injective
    (unilateralShift_injective (𝕜 := 𝕜) (G := G))]
  rw [(unilateralShiftCokerEquiv (𝕜 := 𝕜) (G := G)).finrank_eq]

end lp
