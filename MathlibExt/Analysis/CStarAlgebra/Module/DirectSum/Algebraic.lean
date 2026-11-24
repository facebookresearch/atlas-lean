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

public import MathlibExt.Analysis.CStarAlgebra.Module.Right
public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Algebraic direct sums of right C-star modules

For an arbitrary family `E i` of right pre-Hilbert modules over one
coefficient C-star algebra `B`, this file equips the finite-support dependent
sum with the coefficient inner product

`<x,y> = ∑ i, <x i,y i>`.

The norm is the norm induced by that inner product, not a pre-existing
`DFinsupp` norm.  The construction needs neither component completeness nor a
nonempty index type.  Completion is performed separately.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators RightActions

namespace CStarModule.DirectSum

universe uB uI uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ]
variable {I : Type uI} {E : I → Type uE}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]

/-- The finite-support algebraic direct sum, kept in a coefficient-indexed
synonym so its inner-product norm cannot be confused with another `DFinsupp`
norm. -/
abbrev Algebraic (B : Type uB) {I : Type uI} (E : I → Type uE)
    [∀ i, NormedAddCommGroup (E i)] :=
  WithCStarModule Bᵐᵒᵖ (Π₀ i, E i)

/-- The underlying dependent finite-support function. -/
def toDFinsupp : Algebraic B E ≃ₗ[ℂ] (Π₀ i, E i) :=
  WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (Π₀ i, E i)

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
@[simp]
theorem toDFinsupp_apply (x : Algebraic B E) (i : I) :
    toDFinsupp x i = (WithCStarModule.equiv Bᵐᵒᵖ (Π₀ i, E i) x) i :=
  rfl

/-- The underlying classical finite-support coordinate vector.  Classical
decidable equality is an implementation detail, not an API hypothesis. -/
def rawSingle (i : I) (x : E i) : Π₀ i, E i := by
  classical
  exact DFinsupp.single i x

/-- The finite support of an algebraic direct-sum vector. -/
def support (x : Algebraic B E) : Finset I := by
  classical
  exact (toDFinsupp x).support

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
theorem mem_support_iff (x : Algebraic B E) (i : I) :
    i ∈ support x ↔ toDFinsupp x i ≠ 0 := by
  classical
  simp only [support, DFinsupp.mem_support_toFun]

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
theorem not_mem_support_iff (x : Algebraic B E) (i : I) :
    i ∉ support x ↔ toDFinsupp x i = 0 := by
  rw [mem_support_iff]
  exact not_ne_iff

/-- The algebraic coordinate inclusion as a complex-linear map. -/
def singleLinear (i : I) : E i →ₗ[ℂ] Algebraic B E := by
  classical
  exact
    (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (Π₀ i, E i)).symm.toLinearMap.comp
      (DFinsupp.lsingle i)

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
@[simp]
theorem toDFinsupp_singleLinear (i : I) (x : E i) :
    toDFinsupp (singleLinear (B := B) (E := E) i x) = rawSingle i x :=
  by
    classical
    rfl

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
@[simp, nolint simpNF]
theorem singleLinear_apply_same (i : I) (x : E i) :
    toDFinsupp (singleLinear (B := B) (E := E) i x) i = x := by
  classical
  change rawSingle i x i = x
  simp only [rawSingle, DFinsupp.single_eq_same]

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
@[simp, nolint simpNF]
theorem singleLinear_apply_ne {i j : I} (h : j ≠ i) (x : E i) :
    toDFinsupp (singleLinear (B := B) (E := E) i x) j = 0 := by
  classical
  change rawSingle i x j = 0
  simp only [rawSingle, DFinsupp.single_eq_of_ne h]

omit [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [(i : I) → SMul Bᵐᵒᵖ (E i)]
  [(i : I) → CStarModule Bᵐᵒᵖ (E i)] in
/-- Induction on algebraic direct sums, expressed through the public
coefficient-indexed carrier rather than exposing raw `DFinsupp`. -/
protected theorem induction {p : Algebraic B E → Prop} (x : Algebraic B E)
    (h0 : p 0)
    (ha : ∀ (i : I) (b : E i) (y : Algebraic B E),
      toDFinsupp y i = 0 → b ≠ 0 → p y →
        p (singleLinear (B := B) (E := E) i b + y)) : p x := by
  classical
  let q : (Π₀ i, E i) → Prop := fun f ↦ p (toDFinsupp.symm f)
  have hq0 : q 0 := by simpa [q] using h0
  have hqa : ∀ (i : I) (b : E i) (f : Π₀ i, E i),
      f i = 0 → b ≠ 0 → q f → q (DFinsupp.single i b + f) := by
    intro i b f hfi hb hf
    let y : Algebraic B E := toDFinsupp.symm f
    have hyi : toDFinsupp y i = 0 := by simpa [y] using hfi
    have hpy : p y := by simpa [q, y] using hf
    have hp := ha i b y hyi hb hpy
    have heq : toDFinsupp.symm (DFinsupp.single i b + f) =
        singleLinear (B := B) (E := E) i b + y := by
      apply toDFinsupp.injective
      simp [map_add, toDFinsupp_singleLinear, rawSingle, y]
    simpa [q, heq]
  have hx := DFinsupp.induction (toDFinsupp x) hq0 hqa
  simpa [q] using hx

/-- The coefficient-valued inner product, as a complex-linear map in its
second variable. -/
def algebraicInnerSL (x : Algebraic B E) : Algebraic B E →ₗ[ℂ] Bᵐᵒᵖ := by
  classical
  exact
    (DFinsupp.lsum ℂ fun i ↦
        CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := E i) (toDFinsupp x i)).comp
      (toDFinsupp (B := B) (E := E)).toLinearMap

/-- The literal finite sum of component inner products. -/
def algebraicInner (x y : Algebraic B E) : Bᵐᵒᵖ :=
  algebraicInnerSL x y

@[simp]
theorem algebraicInner_zero_right (x : Algebraic B E) :
    algebraicInner x 0 = 0 :=
  (algebraicInnerSL x).map_zero

@[simp]
theorem algebraicInner_add_right (x y z : Algebraic B E) :
    algebraicInner x (y + z) = algebraicInner x y + algebraicInner x z :=
  (algebraicInnerSL x).map_add y z

@[simp]
theorem algebraicInner_smul_right (c : ℂ) (x y : Algebraic B E) :
    algebraicInner x (c • y) = c • algebraicInner x y :=
  (algebraicInnerSL x).map_smul c y

@[simp]
theorem algebraicInner_single_right (x : Algebraic B E) (i : I) (y : E i) :
    algebraicInner x (singleLinear (B := B) (E := E) i y) =
      inner Bᵐᵒᵖ (toDFinsupp x i) y := by
  classical
  change (DFinsupp.lsum ℂ fun j ↦
      CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := E j) (toDFinsupp x j))
        (toDFinsupp (singleLinear (B := B) (E := E) i y)) = _
  rw [toDFinsupp_singleLinear]
  simp [rawSingle, CStarModule.innerₛₗ_apply]

/-- Evaluation as the finite sum over the support of the second vector. -/
theorem algebraicInner_eq_sum (x y : Algebraic B E) :
    algebraicInner x y =
      ∑ i ∈ support y,
        inner Bᵐᵒᵖ (toDFinsupp x i) (toDFinsupp y i) := by
  classical
  change algebraicInner x y =
    ∑ i ∈ (toDFinsupp y).support,
      inner Bᵐᵒᵖ (toDFinsupp x i) (toDFinsupp y i)
  change (DFinsupp.lsum ℂ fun i ↦
      CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := E i) (toDFinsupp x i))
        (toDFinsupp y) = _
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  rfl

@[simp]
theorem algebraicInner_zero_left (y : Algebraic B E) :
    algebraicInner (0 : Algebraic B E) y = 0 := by
  rw [algebraicInner_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact CStarModule.inner_zero_left

@[simp]
theorem algebraicInner_add_left (x y z : Algebraic B E) :
    algebraicInner (x + y) z = algebraicInner x z + algebraicInner y z := by
  classical
  rw [algebraicInner_eq_sum, algebraicInner_eq_sum, algebraicInner_eq_sum]
  simp only [map_add, DFinsupp.add_apply, CStarModule.inner_add_left,
    Finset.sum_add_distrib]

@[simp]
theorem algebraicInner_smul_left (c : ℂ) (x y : Algebraic B E) :
    algebraicInner (c • x) y = star c • algebraicInner x y := by
  classical
  rw [algebraicInner_eq_sum, algebraicInner_eq_sum]
  simp only [map_smul, DFinsupp.smul_apply, CStarModule.inner_smul_left_complex,
    Finset.smul_sum]

@[simp]
theorem algebraicInner_single_left (i : I) (x : E i) (y : Algebraic B E) :
    algebraicInner (singleLinear (B := B) (E := E) i x) y =
      inner Bᵐᵒᵖ x (toDFinsupp y i) := by
  classical
  induction y using CStarModule.DirectSum.induction with
  | h0 => simp
  | ha j z y hj hz ih =>
      rw [algebraicInner_add_right, map_add]
      by_cases hji : j = i
      · subst j
        rw [algebraicInner_single_right, ih]
        rw [singleLinear_apply_same, DFinsupp.add_apply,
          singleLinear_apply_same, CStarModule.inner_add_right]
      · rw [algebraicInner_single_right, ih]
        rw [singleLinear_apply_ne hji, CStarModule.inner_zero_left, zero_add,
          DFinsupp.add_apply, singleLinear_apply_ne (Ne.symm hji), zero_add]

@[simp, nolint simpNF]
theorem algebraicInner_single_single (i : I) (x y : E i) :
    algebraicInner (singleLinear (B := B) (E := E) i x)
        (singleLinear (B := B) (E := E) i y) = inner Bᵐᵒᵖ x y := by
  rw [algebraicInner_single_right, singleLinear_apply_same]

/-- Conjugate symmetry of the finite-sum inner product. -/
theorem star_algebraicInner (x y : Algebraic B E) :
    star (algebraicInner x y) = algebraicInner y x := by
  classical
  induction x using CStarModule.DirectSum.induction with
  | h0 => simp
  | ha i z x hi hz ih =>
      rw [algebraicInner_add_left, star_add, ih, algebraicInner_add_right,
        algebraicInner_single_left, algebraicInner_single_right,
        CStarModule.star_inner]

/-- Pointwise right multiplication as a complex-linear endomorphism of the
algebraic direct sum. -/
def algebraicRightSMul (b : B) : Algebraic B E →ₗ[ℂ] Algebraic B E := by
  classical
  exact
    (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (Π₀ i, E i)).symm.toLinearMap.comp
      ((DFinsupp.mapRange.linearMap fun i ↦
        (CStarModule.rightSMulLinear (B := B) (E := E i)).flip b).comp
          (toDFinsupp (B := B) (E := E)).toLinearMap)

@[simp, nolint simpNF]
theorem toDFinsupp_algebraicRightSMul (b : B) (x : Algebraic B E) (i : I) :
    toDFinsupp (algebraicRightSMul (E := E) b x) i = toDFinsupp x i <• b := by
  classical
  let e := WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (Π₀ i, E i)
  let z := DFinsupp.mapRange (fun i x ↦ x <• b)
    (fun i ↦ CStarModule.zero_right_smul b) (toDFinsupp x)
  have hz : e (e.symm z) = z := e.apply_symm_apply z
  exact DFunLike.congr_fun hz i

/-- The exact pointwise right coefficient action. -/
instance algebraicSMul : SMul Bᵐᵒᵖ (Algebraic B E) where
  smul b x := algebraicRightSMul (E := E) b.unop x

@[simp, nolint simpNF]
theorem toDFinsupp_right_smul (x : Algebraic B E) (b : B) (i : I) :
    toDFinsupp (x <• b) i = toDFinsupp x i <• b :=
  toDFinsupp_algebraicRightSMul b x i

@[simp]
theorem singleLinear_right_smul (i : I) (x : E i) (b : B) :
    singleLinear (B := B) (E := E) i (x <• b) =
      singleLinear (B := B) (E := E) i x <• b := by
  classical
  apply (toDFinsupp (B := B) (E := E)).injective
  ext j
  by_cases hji : j = i
  · subst j
    rw [singleLinear_apply_same, toDFinsupp_right_smul, singleLinear_apply_same]
  · rw [singleLinear_apply_ne hji, toDFinsupp_right_smul,
      singleLinear_apply_ne hji, CStarModule.zero_right_smul]

/-- The finite-sum inner product is right coefficient-linear. -/
theorem algebraicInner_right_smul (x y : Algebraic B E) (b : Bᵐᵒᵖ) :
    algebraicInner x (b • y) = b * algebraicInner x y := by
  classical
  induction y using CStarModule.DirectSum.induction with
  | h0 =>
      change algebraicInner x (algebraicRightSMul (E := E) b.unop 0) = _
      rw [map_zero, algebraicInner_zero_right]
      simp
  | ha i z y hi hz ih =>
      change algebraicInner x
          (algebraicRightSMul (E := E) b.unop
            (singleLinear (B := B) (E := E) i z + y)) = _
      rw [map_add, algebraicInner_add_right]
      change algebraicInner x
          (algebraicRightSMul (E := E) b.unop (singleLinear (B := B) (E := E) i z)) +
        algebraicInner x (b • y) =
          b * algebraicInner x (singleLinear (B := B) (E := E) i z + y)
      have hs : algebraicRightSMul (E := E) b.unop
          (singleLinear (B := B) (E := E) i z) =
          singleLinear (B := B) (E := E) i (z <• b.unop) :=
        (singleLinear_right_smul (B := B) (E := E) i z b.unop).symm
      rw [ih, algebraicInner_add_right, mul_add, hs,
        algebraicInner_single_right, algebraicInner_single_right,
        CStarModule.inner_op_smul_right]
      simp only [MulOpposite.op_unop]

/-- The direct-sum norm before completion. -/
@[instance_reducible]
def algebraicNorm : Norm (Algebraic B E) where
  norm x := Real.sqrt ‖algebraicInner x x‖

variable [StarOrderedRing Bᵐᵒᵖ]

/-- The literal finite-support pre-Hilbert module. -/
@[instance_reducible]
def algebraicCStarModule :
    letI : Norm (Algebraic B E) := algebraicNorm (B := B) (E := E)
    CStarModule Bᵐᵒᵖ (Algebraic B E) := by
  letI : Norm (Algebraic B E) := algebraicNorm (B := B) (E := E)
  refine
    { inner := algebraicInner
      inner_add_right := by
        intro x y z
        exact algebraicInner_add_right (B := B) (E := E) x y z
      inner_self_nonneg := ?_
      inner_self := ?_
      inner_op_smul_right := by
        intro b x y
        exact algebraicInner_right_smul (B := B) (E := E) x y b
      inner_smul_right_complex := by
        intro c x y
        exact algebraicInner_smul_right (B := B) (E := E) c x y
      star_inner := by
        intro x y
        exact star_algebraicInner (B := B) (E := E) x y
      norm_eq_sqrt_norm_inner_self := ?_ }
  · intro x
    rw [algebraicInner_eq_sum]
    exact Finset.sum_nonneg fun i _ ↦ CStarModule.inner_self_nonneg
  · intro x
    constructor
    · intro hx
      rw [algebraicInner_eq_sum] at hx
      have hz : ∀ i ∈ support x,
          inner Bᵐᵒᵖ (toDFinsupp x i) (toDFinsupp x i) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ ↦ CStarModule.inner_self_nonneg)).mp hx
      apply (toDFinsupp (B := B) (E := E)).injective
      ext i
      by_cases hi : i ∈ support x
      · exact (CStarModule.inner_self (A := Bᵐᵒᵖ)
          (x := toDFinsupp x i)).mp (hz i hi)
      · exact (not_mem_support_iff x i).mp hi
    · rintro rfl
      exact algebraicInner_zero_left 0
  · intro x
    rfl

/-- The stock C-star-module core derives the normed group and complex normed
space laws from the constructed inner product. -/
theorem algebraicNormedSpaceCore :
    letI : Norm (Algebraic B E) := algebraicNorm (B := B) (E := E)
    NormedSpace.Core ℂ (Algebraic B E) := by
  let : Norm (Algebraic B E) := algebraicNorm (B := B) (E := E)
  let : CStarModule Bᵐᵒᵖ (Algebraic B E) :=
    algebraicCStarModule (B := B) (E := E)
  exact CStarModule.normedSpaceCore Bᵐᵒᵖ (E := Algebraic B E)

@[instance_reducible]
noncomputable instance algebraicNormedAddCommGroup :
    NormedAddCommGroup (Algebraic B E) := by
  letI : Norm (Algebraic B E) := algebraicNorm (B := B) (E := E)
  exact NormedAddCommGroup.ofCore (algebraicNormedSpaceCore (B := B) (E := E))

@[instance_reducible]
noncomputable instance algebraicNormedSpace : NormedSpace ℂ (Algebraic B E) :=
  NormedSpace.ofCore (algebraicNormedSpaceCore (B := B) (E := E))

@[instance_reducible]
noncomputable instance algebraicCStarModuleInstance :
    CStarModule Bᵐᵒᵖ (Algebraic B E) :=
  algebraicCStarModule (B := B) (E := E)

@[simp]
theorem inner_eq_algebraicInner (x y : Algebraic B E) :
    inner Bᵐᵒᵖ x y = algebraicInner x y :=
  rfl

@[simp]
theorem norm_algebraic (x : Algebraic B E) :
    ‖x‖ = Real.sqrt ‖algebraicInner x x‖ :=
  rfl

/-- Coordinate inclusion into the algebraic sum as a complex-linear isometry. -/
def single (i : I) : E i →ₗᵢ[ℂ] Algebraic B E where
  toLinearMap := singleLinear (B := B) (E := E) i
  norm_map' x := by
    rw [norm_algebraic, algebraicInner_single_single]
    exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm

@[simp]
theorem single_apply_eq_singleLinear (i : I) (x : E i) :
    single (B := B) (E := E) i x = singleLinear (B := B) (E := E) i x :=
  rfl

@[simp, nolint simpNF]
theorem single_apply_same (i : I) (x : E i) :
    toDFinsupp (single (B := B) (E := E) i x) i = x :=
  singleLinear_apply_same i x

@[simp, nolint simpNF]
theorem single_apply_ne {i j : I} (h : j ≠ i) (x : E i) :
    toDFinsupp (single (B := B) (E := E) i x) j = 0 :=
  singleLinear_apply_ne h x

@[simp, nolint simpNF]
theorem inner_single_same (i : I) (x y : E i) :
    inner Bᵐᵒᵖ (single (B := B) (E := E) i x)
        (single (B := B) (E := E) i y) = inner Bᵐᵒᵖ x y :=
  by
    rw [inner_eq_algebraicInner, single_apply_eq_singleLinear,
      single_apply_eq_singleLinear]
    exact algebraicInner_single_single i x y

@[simp, nolint simpNF]
theorem inner_single_ne {i j : I} (h : i ≠ j) (x : E i) (y : E j) :
    inner Bᵐᵒᵖ (single (B := B) (E := E) i x)
        (single (B := B) (E := E) j y) = 0 := by
  rw [inner_eq_algebraicInner, single_apply_eq_singleLinear,
    single_apply_eq_singleLinear]
  rw [algebraicInner_single_right, singleLinear_apply_ne (Ne.symm h)]
  exact CStarModule.inner_zero_left

/-- Every algebraic direct-sum vector belongs to the complex linear span of
the coordinate singles. -/
theorem span_range_single_eq_top :
    Submodule.span ℂ
        (Set.range fun p : Σ i, E i ↦ single (B := B) (E := E) p.1 p.2) = ⊤ := by
  classical
  apply top_unique
  intro x _
  induction x using CStarModule.DirectSum.induction with
  | h0 => exact Submodule.zero_mem _
  | ha i z x hi hz ih =>
      exact Submodule.add_mem _
        (Submodule.subset_span ⟨⟨i, z⟩, rfl⟩) (ih trivial)

end CStarModule.DirectSum
