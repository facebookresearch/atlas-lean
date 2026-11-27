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

public import MathlibExt.Analysis.CStarAlgebra.Module.Support
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Standard right Hilbert C-star modules

This file constructs the finite and algebraic finite-support standard right
C-star modules. Their uniform completion is the standard Hilbert module.
-/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped RightActions CStarModule.Right

namespace CStarModule.Right

universe uB uι

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. The
finite standard right Hilbert module. -/
abbrev FiniteStandard
    (B : Type uB) (ι : Type uι) : Type (max uB uι) :=
  WithCStarModule Bᵐᵒᵖ (ι → B)

section Finite

variable {B : Type uB} {ι : Type uι} [Fintype ι]
variable [NonUnitalCStarAlgebra B]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. The
opposite coefficient algebra has the C-star-positive order determined by its self-adjoint
spectrum. -/
local instance spectralOrderBop : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder _
local instance : @StarOrderedRing Bᵐᵒᵖ _ spectralOrderBop _ :=
  CStarAlgebra.spectralOrderedRing _

@[simp]
theorem finite_rightInner (x y : FiniteStandard B ι) :
    CStarModule.rightInner (B := B) x y = ∑ i, star (x i) * y i := by
  rw [CStarModule.rightInner, WithCStarModule.pi_inner]
  calc
    MulOpposite.unop (∑ i, inner Bᵐᵒᵖ (x i) (y i)) =
        ∑ i, MulOpposite.unop (inner Bᵐᵒᵖ (x i) (y i)) :=
      map_sum MulOpposite.opAddEquiv.symm _ _
    _ = ∑ i, star (x i) * y i := by rfl

theorem finite_norm (x : FiniteStandard B ι) :
    ‖x‖ = √‖∑ i, star (x i) * x i‖ := by
  rw [WithCStarModule.pi_norm]
  have h := finite_rightInner (B := B) x x
  change MulOpposite.unop (∑ i, inner Bᵐᵒᵖ (x i) (x i)) = _ at h
  calc
    √‖∑ i, inner Bᵐᵒᵖ (x i) (x i)‖ =
        √‖MulOpposite.unop (∑ i, inner Bᵐᵒᵖ (x i) (x i))‖ := by
      rw [MulOpposite.norm_unop]
    _ = _ := by rw [h]

theorem finite_norm_sq (x : FiniteStandard B ι) :
    ‖x‖ ^ 2 = ‖∑ i, star (x i) * x i‖ := by
  rw [WithCStarModule.pi_norm_sq]
  have h := finite_rightInner (B := B) x x
  change MulOpposite.unop (∑ i, inner Bᵐᵒᵖ (x i) (x i)) = _ at h
  calc
    ‖∑ i, inner Bᵐᵒᵖ (x i) (x i)‖ =
        ‖MulOpposite.unop (∑ i, inner Bᵐᵒᵖ (x i) (x i))‖ := by
      rw [MulOpposite.norm_unop]
    _ = _ := by rw [h]

theorem finite_norm_apply_le_norm (x : FiniteStandard B ι) (i : ι) :
    ‖x i‖ ≤ ‖x‖ :=
  WithCStarModule.norm_apply_le_norm x i

omit [Fintype ι] in
/-- Let B be a possibly nonunital complex C-star algebra and I any index type. On coefficient
families B to the power I, right multiplication is coordinatewise. The finite standard-module
right action is coordinatewise right-action multiplication. -/
@[simp]
theorem finite_right_smul_apply (x : FiniteStandard B ι) (b : B) (i : ι) :
    (x <• b) i = x i * b := by
  change (x i) <• b = x i * b
  exact CStarModule.Right.right_smul_self (x i) b

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product.
Coordinate evaluation on a finite standard module. -/
def finiteCoord (i : ι) : FiniteStandard B ι →L[ℂ] B := by
  let f : FiniteStandard B ι →ₗ[ℂ] B :=
    { toFun := fun x ↦ x i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact f.mkContinuous 1 fun x ↦ by
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using finite_norm_apply_le_norm x i

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. Insert
one coefficient into a finite standard module. -/
noncomputable def finiteSingle (i : ι) : B →L[ℂ] FiniteStandard B ι := by
  classical
  let f : B →ₗ[ℂ] FiniteStandard B ι :=
    { toFun := fun b ↦
        (WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).symm (Pi.single i b)
      map_add' := by
        intro x y
        apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).injective
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      map_smul' := by
        intro c x
        apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).injective
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji] }
  exact f.mkContinuous 1 fun b ↦ by
    change ‖(WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).symm (Pi.single i b)‖ ≤ 1 * ‖b‖
    simpa only [one_mul] using
      (WithCStarModule.norm_single (A := Bᵐᵒᵖ)
        (E := fun _ : ι ↦ B) i b).le

@[simp low]
theorem finiteCoord_apply (i : ι) (x : FiniteStandard B ι) :
    finiteCoord i x = x i := by
  change x i = x i
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. The
selected coordinate of a finite coefficient single is its coefficient. -/
@[simp]
theorem finiteCoord_single_self (i : ι) (b : B) :
    finiteCoord i (finiteSingle i b) = b := by
  classical
  change (@Pi.single ι (fun _ ↦ B) (fun _ ↦ inferInstance)
    (Classical.decEq ι) i b) i = b
  simp

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. Every
other coordinate of a finite coefficient single vanishes. -/
@[simp]
theorem finiteCoord_single_ne {i j : ι} (h : j ≠ i) (b : B) :
    finiteCoord j (finiteSingle i b) = 0 := by
  classical
  change (@Pi.single ι (fun _ ↦ B) (fun _ ↦ inferInstance)
    (Classical.decEq ι) i b) j = 0
  simp [h]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. Finite
coefficient singles intertwine right-action right multiplication. -/
@[simp]
theorem finiteSingle_right_smul (i : ι) (b c : B) :
    finiteSingle i b <• c = finiteSingle i (b * c) := by
  classical
  ext j
  rw [finite_right_smul_apply]
  by_cases hji : j = i
  · subst j
    have hb : finiteSingle i b i = b := by
      simpa only [finiteCoord_apply] using
        (finiteCoord_single_self (B := B) i b)
    have hbc : finiteSingle i (b * c) i = b * c := by
      simpa only [finiteCoord_apply] using
        (finiteCoord_single_self (B := B) i (b * c))
    rw [hb, hbc]
  · have hb : finiteSingle i b j = 0 := by
      simpa only [finiteCoord_apply] using
        (finiteCoord_single_ne (B := B) hji b)
    have hbc : finiteSingle i (b * c) j = 0 := by
      simpa only [finiteCoord_apply] using
        (finiteCoord_single_ne (B := B) hji (b * c))
    rw [hb, hbc, zero_mul]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. Finite
coefficient singles reconstruct every finite standard-module vector. -/
theorem finite_sum_single (x : FiniteStandard B ι) :
    ∑ i, finiteSingle i (x i) = x := by
  classical
  apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).injective
  change ∑ i, Pi.single i (x i) = fun i ↦ x i
  exact Finset.univ_sum_single (fun i ↦ x i)

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The finite standard right module has the coefficient-valued sum inner product. The norm
on a finite standard module is bounded by the sum of its coordinate norms. -/
theorem finite_norm_le_sum (x : FiniteStandard B ι) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  classical
  calc
    ‖x‖ = ‖∑ i, finiteSingle i (x i)‖ :=
      congrArg (fun y : FiniteStandard B ι ↦ ‖y‖)
        (finite_sum_single x).symm
    _ ≤ ∑ i, ‖finiteSingle i (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).symm
        (Pi.single i (x i))‖ ≤ ‖x i‖
      exact (WithCStarModule.norm_single (A := Bᵐᵒᵖ)
        (E := fun _ : ι ↦ B) i (x i)).le

end Finite

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The algebraic finite-
support standard pre-Hilbert module. -/
@[nolint unusedArguments]
def StandardPre
    (B : Type uB) (ι : Type uι)
    [NonUnitalCStarAlgebra B] : Type (max uB uι) :=
  ι →₀ B

namespace StandardPre

variable {B : Type uB} {ι : Type uι}
variable [NonUnitalCStarAlgebra B]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The canonical equivalence
with finitely supported coefficient families. -/
def toFinsupp : StandardPre B ι ≃ (ι →₀ B) := Equiv.refl _

instance : AddCommGroup (StandardPre B ι) :=
  Equiv.addCommGroup (toFinsupp (B := B) (ι := ι))

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The additive equivalence
underlying toFinsupp. -/
def toFinsuppAddEquiv : StandardPre B ι ≃+ (ι →₀ B) where
  toEquiv := toFinsupp
  map_add' _ _ := rfl

instance : Module ℂ (StandardPre B ι) :=
  (toFinsuppAddEquiv (B := B) (ι := ι)).module ℂ

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The complex-linear
equivalence underlying toFinsupp. -/
def toFinsuppLinearEquiv : StandardPre B ι ≃ₗ[ℂ] (ι →₀ B) where
  toAddEquiv := toFinsuppAddEquiv
  map_smul' _ _ := rfl

instance : SMul Bᵐᵒᵖ (StandardPre B ι) where
  smul b x := toFinsupp.symm (b • toFinsupp x : ι →₀ B)

instance : CoeFun (StandardPre B ι) fun _ ↦ ι → B where
  coe x := toFinsupp x

@[simp] theorem toFinsupp_zero : toFinsupp (0 : StandardPre B ι) = 0 := rfl
@[simp] theorem toFinsupp_add (x y : StandardPre B ι) :
    toFinsupp (x + y) = toFinsupp x + toFinsupp y := rfl
@[simp] theorem toFinsupp_smul (c : ℂ) (x : StandardPre B ι) :
    toFinsupp (c • x) = c • toFinsupp x :=
  (toFinsuppLinearEquiv (B := B) (ι := ι)).map_smul c x
@[simp] theorem toFinsupp_op_smul (b : Bᵐᵒᵖ) (x : StandardPre B ι) :
    toFinsupp (b • x) = b • toFinsupp x :=
  (toFinsupp (B := B) (ι := ι)).apply_symm_apply _
@[simp] theorem coe_zero (i : ι) : (0 : StandardPre B ι) i = 0 := rfl
@[simp] theorem coe_add (x y : StandardPre B ι) (i : ι) :
    (x + y) i = x i + y i := rfl
theorem coe_smul (c : ℂ) (x : StandardPre B ι) (i : ι) :
    (c • x) i = c • x i := by
  exact DFunLike.congr_fun (toFinsupp_smul c x) i
theorem coe_op_smul (b : Bᵐᵒᵖ) (x : StandardPre B ι) (i : ι) :
    (b • x) i = b • x i := by
  exact DFunLike.congr_fun (toFinsupp_op_smul b x) i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The opposite coefficient
algebra has the C-star-positive order determined by its self-adjoint spectrum. -/
local instance spectralOrderBop : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder _
local instance : @StarOrderedRing Bᵐᵒᵖ _ spectralOrderBop _ :=
  CStarAlgebra.spectralOrderedRing _

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The opposite-coefficient
inner product of finite-support families, summed over the first family's support. -/
def innerOp (x y : StandardPre B ι) : Bᵐᵒᵖ :=
  (toFinsupp x).sum fun i xi ↦ inner Bᵐᵒᵖ xi (y i)

noncomputable instance : Norm (StandardPre B ι) where
  norm x := √‖innerOp x x‖

theorem innerOp_add_right (x y z : StandardPre B ι) :
    innerOp x (y + z) = innerOp x y + innerOp x z := by
  classical
  simp [innerOp]

theorem star_innerOp (x y : StandardPre B ι) :
    star (innerOp x y) = innerOp y x := by
  classical
  simp only [innerOp, star_finsuppSum, Pi.star_apply, star_inner]
  rw [Finsupp.sum_of_support_subset (toFinsupp x)
      (s := (toFinsupp x).support ∪ (toFinsupp y).support)
      Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset (toFinsupp y)
      (s := (toFinsupp x).support ∪ (toFinsupp y).support)
      Finset.subset_union_right _ (by simp)]

theorem innerOp_self_nonneg (x : StandardPre B ι) :
    0 ≤ innerOp x x := by
  classical
  change 0 ≤ ∑ i ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x i) (x i)
  exact Finset.sum_nonneg fun i _ ↦
    CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x i)

theorem innerOp_self_eq_zero (x : StandardPre B ι) :
    innerOp x x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro h
    apply (toFinsupp (B := B) (ι := ι)).injective
    apply Finsupp.ext
    intro i
    by_cases hi : i ∈ (toFinsupp x).support
    · have hle : inner Bᵐᵒᵖ (x i) (x i) ≤ innerOp x x := by
        change inner Bᵐᵒᵖ (x i) (x i) ≤
          ∑ j ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x j) (x j)
        exact Finset.single_le_sum
          (fun j _ ↦ CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x j)) hi
      have hz : inner Bᵐᵒᵖ (x i) (x i) = 0 :=
        le_antisymm (by simpa [h] using hle)
          (CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ))
      simpa using (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp hz
    · simpa using (Finsupp.notMem_support_iff.mp hi)
  · rintro rfl
    simp [innerOp]

noncomputable instance : CStarModule Bᵐᵒᵖ (StandardPre B ι) where
  inner := innerOp
  inner_add_right := innerOp_add_right (B := B) (ι := ι) _ _ _
  inner_self_nonneg := innerOp_self_nonneg (B := B) (ι := ι) _
  inner_self := innerOp_self_eq_zero (B := B) (ι := ι) _
  inner_op_smul_right := by
    classical
    intro a x y
    change (∑ i ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x i) (a • y i)) =
      a * ∑ i ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x i) (y i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact CStarModule.inner_op_smul_right
  inner_smul_right_complex := by
    classical
    intro c x y
    change (∑ i ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x i) (c • y i)) =
      c • ∑ i ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x i) (y i)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact CStarModule.inner_smul_right_complex
  star_inner := star_innerOp (B := B) (ι := ι)
  norm_eq_sqrt_norm_inner_self := fun _ ↦ rfl

noncomputable instance : NormedAddCommGroup (StandardPre B ι) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore Bᵐᵒᵖ)

noncomputable instance : NormedSpace ℂ (StandardPre B ι) :=
  NormedSpace.ofCore (CStarModule.normedSpaceCore Bᵐᵒᵖ)

theorem rightInner_apply (x y : StandardPre B ι) :
    CStarModule.rightInner (B := B) x y =
      (toFinsupp x).sum fun i xi ↦ star xi * y i := by
  change MulOpposite.unop (innerOp x y) = _
  rw [show innerOp x y =
      (toFinsupp x).sum (fun i xi ↦ inner Bᵐᵒᵖ xi (y i)) by rfl]
  rw [Finsupp.sum]
  calc
    MulOpposite.unop
        (∑ i ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x i) (y i)) =
      ∑ i ∈ (toFinsupp x).support,
        MulOpposite.unop (inner Bᵐᵒᵖ (x i) (y i)) :=
      map_sum MulOpposite.opAddEquiv.symm _ _
    _ = _ := by rfl

theorem norm_apply (x : StandardPre B ι) :
    ‖x‖ = √‖(toFinsupp x).sum fun i xi ↦ star xi * x i‖ := by
  change √‖innerOp x x‖ = _
  congr 1
  calc
    ‖innerOp x x‖ = ‖MulOpposite.unop (innerOp x x)‖ :=
      (MulOpposite.norm_unop _).symm
    _ = ‖(toFinsupp x).sum fun i xi ↦ star xi * x i‖ :=
      congrArg (fun b : B ↦ ‖b‖) (by
        exact rightInner_apply x x)

theorem norm_coord_le (x : StandardPre B ι) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc
    ‖x i‖ ^ 2 = ‖inner Bᵐᵒᵖ (x i) (x i)‖ :=
      CStarModule.norm_sq_eq (A := Bᵐᵒᵖ)
    _ ≤ ‖innerOp x x‖ := by
      have hle : inner Bᵐᵒᵖ (x i) (x i) ≤ innerOp x x := by
        change inner Bᵐᵒᵖ (x i) (x i) ≤
          ∑ j ∈ (toFinsupp x).support, inner Bᵐᵒᵖ (x j) (x j)
        by_cases hi : i ∈ (toFinsupp x).support
        · exact Finset.single_le_sum
            (fun j _ ↦ CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x j)) hi
        · simpa [Finsupp.notMem_support_iff.mp hi] using
            (show 0 ≤ ∑ j ∈ (toFinsupp x).support,
              inner Bᵐᵒᵖ (x j) (x j) by
                have hn := innerOp_self_nonneg x
                change 0 ≤ ∑ j ∈ (toFinsupp x).support,
                  inner Bᵐᵒᵖ (x j) (x j) at hn
                exact hn)
      exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
        (CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x i))
    _ = ‖x‖ ^ 2 := (CStarModule.norm_sq_eq (A := Bᵐᵒᵖ) (x := x)).symm

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Coordinate evaluation on
the finite-support premodule. -/
def coord (i : ι) : StandardPre B ι →L[ℂ] B := by
  let f : StandardPre B ι →ₗ[ℂ] B :=
    { toFun := fun x ↦ x i
      map_add' := fun x y ↦ coe_add x y i
      map_smul' := fun c x ↦ coe_smul c x i }
  exact f.mkContinuous 1 fun x ↦ by
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_coord_le x i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. A vector supported at one
coordinate has the coefficient norm. -/
theorem norm_single (i : ι) (b : B) :
    ‖(toFinsupp.symm (Finsupp.single i b) : StandardPre B ι)‖ = ‖b‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [CStarModule.norm_sq_eq (A := Bᵐᵒᵖ)
    (x := (toFinsupp.symm (Finsupp.single i b) : StandardPre B ι))]
  rw [CStarModule.norm_sq_eq (A := Bᵐᵒᵖ) (x := b)]
  change ‖innerOp (toFinsupp.symm (Finsupp.single i b))
    (toFinsupp.symm (Finsupp.single i b))‖ = ‖inner Bᵐᵒᵖ b b‖
  simp [innerOp]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Insert one coefficient at
a selected coordinate. -/
def single (i : ι) : B →L[ℂ] StandardPre B ι := by
  let f : B →ₗ[ℂ] StandardPre B ι :=
    { toFun := fun b ↦ toFinsupp.symm (Finsupp.single i b)
      map_add' := by
        intro x y
        apply toFinsupp.injective
        simp
      map_smul' := by
        intro c x
        apply toFinsupp.injective
        simp }
  exact f.mkContinuous 1 fun b ↦ by
    change ‖(toFinsupp.symm (Finsupp.single i b) : StandardPre B ι)‖ ≤ 1 * ‖b‖
    simpa only [one_mul] using (norm_single (B := B) (ι := ι) i b).le

@[simp]
theorem coord_apply (i : ι) (x : StandardPre B ι) : coord i x = x i := by
  change (toFinsupp x) i = (toFinsupp x) i
  rfl

@[simp]
theorem single_apply (i : ι) (b : B) :
    single i b = toFinsupp.symm (Finsupp.single i b) := by
  change toFinsupp.symm (Finsupp.single i b) = _
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The right inner product
of two coefficient singles at the same index. -/
@[simp↓]
theorem rightInner_single (i : ι) (b c : B) :
    CStarModule.rightInner (B := B) (single i b) (single i c) = star b * c := by
  classical
  rw [single_apply, single_apply, rightInner_apply]
  simp

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Coefficient singles
intertwine right-action right multiplication. -/
@[simp↓]
theorem single_right_smul (i : ι) (b c : B) :
    single i b <• c = single i (b * c) := by
  apply toFinsupp.injective
  rw [toFinsupp_op_smul, single_apply, single_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Finsupp.smul_single, CStarModule.Right.right_smul_self]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Coefficient singles at
distinct indices are orthogonal. -/
@[simp↓]
theorem rightInner_single_ne {i j : ι} (h : i ≠ j) (b c : B) :
    CStarModule.rightInner (B := B) (single i b) (single j c) = 0 := by
  classical
  simp [rightInner_apply, single_apply, h]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The coefficient singles
over the support reconstruct a finite-support vector. -/
theorem sum_single_support (x : StandardPre B ι) :
    ∑ i ∈ (toFinsupp x).support, single i (x i) = x := by
  classical
  apply toFinsupp.injective
  change ∑ i ∈ (toFinsupp x).support, Finsupp.single i (x i) = toFinsupp x
  exact Finsupp.sum_single (toFinsupp x)

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The norm of xb is at most
the norm of x times the norm of b. -/
theorem norm_right_smul_le (x : StandardPre B ι) (b : B) :
    ‖x <• b‖ ≤ ‖x‖ * ‖b‖ :=
  CStarModule.norm_right_smul_le x b

private theorem norm_filter_le [DecidableEq ι]
    (s : Finset ι) (x : StandardPre B ι) :
    ‖toFinsupp.symm ((toFinsupp x).filter (· ∈ s))‖ ≤ ‖x‖ := by
  classical
  let y : StandardPre B ι :=
    toFinsupp.symm ((toFinsupp x).filter (· ∈ s))
  have hy : toFinsupp y = (toFinsupp x).filter (· ∈ s) :=
    (toFinsupp (B := B) (ι := ι)).apply_symm_apply _
  have hsum :
      ((toFinsupp x).filter (· ∈ s)).sum
          (fun i xi ↦ inner Bᵐᵒᵖ xi (((toFinsupp x).filter (· ∈ s)) i)) =
        ∑ i ∈ (toFinsupp x).support.filter (· ∈ s),
          inner Bᵐᵒᵖ (x i) (x i) := by
    rw [Finsupp.sum, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).2
    simp only [Finsupp.filter_apply_pos (f := toFinsupp x)
      (p := fun j ↦ j ∈ s) his]
  have hinner : innerOp y y ≤ innerOp x x := by
    change (toFinsupp y).sum (fun i xi ↦ inner Bᵐᵒᵖ xi (y i)) ≤
      (toFinsupp x).sum (fun i xi ↦ inner Bᵐᵒᵖ xi (x i))
    rw [hy]
    change ((toFinsupp x).filter (· ∈ s)).sum
        (fun i xi ↦ inner Bᵐᵒᵖ xi (((toFinsupp x).filter (· ∈ s)) i)) ≤ _
    rw [hsum, Finsupp.sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ ↦ CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (x := x i)
  change ‖y‖ ≤ ‖x‖
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [CStarModule.norm_sq_eq (A := Bᵐᵒᵖ),
    CStarModule.norm_sq_eq (A := Bᵐᵒᵖ)]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hinner (innerOp_self_nonneg y)

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Restriction to a finite
coordinate set on the finite-support premodule. -/
noncomputable def truncate (s : Finset ι) :
    StandardPre B ι →L[ℂ] StandardPre B ι := by
  classical
  exact
    ({ toFun := fun x ↦ toFinsupp.symm ((toFinsupp x).filter (· ∈ s))
       map_add' := by
         intro x y
         apply toFinsupp.injective
         ext i
         simp only [toFinsupp_add, Equiv.apply_symm_apply,
           Finsupp.filter_apply, Finsupp.add_apply]
         split <;> simp_all
       map_smul' := by
         intro c x
         apply toFinsupp.injective
         ext i
         simp only [toFinsupp_smul, Equiv.apply_symm_apply,
           Finsupp.filter_apply, Finsupp.smul_apply]
         split <;> simp_all } : StandardPre B ι →ₗ[ℂ] StandardPre B ι).mkContinuous 1 fun x ↦ by
    change ‖toFinsupp.symm ((toFinsupp x).filter (· ∈ s))‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_filter_le s x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Premodule truncation
keeps exactly the selected coordinates. -/
@[simp↓]
theorem truncate_apply [DecidableEq ι]
    (s : Finset ι) (x : StandardPre B ι) (i : ι) :
    truncate s x i = if i ∈ s then x i else 0 := by
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    unfold truncate
    rw [LinearMap.mkContinuous_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [(toFinsupp (B := B) (ι := ι)).apply_symm_apply]
    rw [Finsupp.filter_apply]
    simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte]
    unfold truncate
    rw [LinearMap.mkContinuous_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [(toFinsupp (B := B) (ι := ι)).apply_symm_apply]
    rw [Finsupp.filter_apply]
    simp only [hi, ↓reduceIte]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The underlying finitely
supported family of a truncation is its filtered family. -/
@[simp]
theorem toFinsupp_truncate [DecidableEq ι] (s : Finset ι)
    (x : StandardPre B ι) :
    toFinsupp (truncate s x) = (toFinsupp x).filter (· ∈ s) := by
  ext i
  change truncate s x i = _
  rw [truncate_apply, Finsupp.filter_apply]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Truncation fixes a
finite-support vector once the truncation set contains its support. -/
theorem truncate_eq_self_of_support_subset (s : Finset ι)
    (x : StandardPre B ι) (h : (toFinsupp x).support ⊆ s) :
    truncate s x = x := by
  classical
  apply toFinsupp.injective
  ext i
  change truncate s x i = x i
  rw [truncate_apply]
  split_ifs with hi
  · rfl
  · exact (Finsupp.notMem_support_iff.mp (fun his ↦ hi (h his))).symm

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. A premodule truncation is
the finite sum of its coefficient singles. -/
theorem truncate_eq_sum_single (s : Finset ι) (x : StandardPre B ι) :
    truncate s x = ∑ i ∈ s, single i (x i) := by
  classical
  apply toFinsupp.injective
  rw [toFinsupp_truncate]
  change (toFinsupp x).filter (· ∈ s) =
    (toFinsuppAddEquiv (B := B) (ι := ι))
      (∑ i ∈ s, single i (x i))
  rw [map_sum]
  have hsingle (i : ι) :
      (toFinsuppAddEquiv (B := B) (ι := ι)) (single i (x i)) =
        Finsupp.single i (x i) := by
    change toFinsupp (single i (x i)) = _
    rw [single_apply, Equiv.apply_symm_apply]
  simp_rw [hsingle]
  ext j
  rw [Finsupp.filter_apply, Finset.sum_apply']
  by_cases hj : j ∈ s
  · simp only [hj, ↓reduceIte]
    rw [Finset.sum_eq_single j]
    all_goals simp_all
  · simp only [hj, ↓reduceIte]
    exact (Finset.sum_eq_zero fun i hi ↦ by
      apply Finsupp.single_eq_of_ne
      intro hji
      subst i
      exact hj hi).symm

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. The right inner product
of two premodule truncations is the corresponding finite coordinate sum. -/
theorem rightInner_truncate (s : Finset ι) (x y : StandardPre B ι) :
    CStarModule.rightInner (B := B) (truncate s x) (truncate s y) =
      ∑ i ∈ s, star (x i) * y i := by
  classical
  have hsupp : (toFinsupp (truncate s x)).support ⊆ s := by
    intro i hi
    rw [toFinsupp_truncate, Finsupp.support_filter] at hi
    exact (Finset.mem_filter.mp hi).2
  rw [rightInner_apply,
    Finsupp.sum_of_support_subset (toFinsupp (truncate s x))
      (s := s) hsupp
      (fun i xi ↦ star xi * (toFinsupp (truncate s y)) i) (by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  change star (truncate s x i) * truncate s y i = _
  simp only [truncate_apply, hi, ↓reduceIte]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Premodule truncation
commutes with the opposite-algebra right action. -/
@[simp]
theorem truncate_op_smul (s : Finset ι) (b : Bᵐᵒᵖ) (x : StandardPre B ι) :
    truncate s (b • x) = b • truncate s x := by
  apply toFinsupp.injective
  ext i
  classical
  simp only [truncate_apply, coe_op_smul]
  split <;> simp_all

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Premodule truncation
commutes with right-action right multiplication. -/
theorem truncate_right_smul (s : Finset ι) (x : StandardPre B ι) (b : B) :
    truncate s (x <• b) = truncate s x <• b :=
  truncate_op_smul s (MulOpposite.op b) x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard
premodule consists of finitely supported B-valued families, with inner product given by the
finite sum of conjugated first coordinates times second coordinates. Premodule truncation is
contractive. -/
theorem norm_truncate_le (s : Finset ι) (x : StandardPre B ι) :
    ‖truncate s x‖ ≤ ‖x‖ := by
  classical
  unfold truncate
  change ‖toFinsupp.symm ((toFinsupp x).filter (· ∈ s))‖ ≤ ‖x‖
  exact norm_filter_le s x

end StandardPre

/-! ## The completed standard module -/

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The standard
right Hilbert C-star module is the uniform completion of the algebraic finite-support module. -/
def Standard
    (B : Type uB) (ι : Type uι)
    [NonUnitalCStarAlgebra B] : Type (max uB uι) :=
  UniformSpace.Completion (StandardPre B ι)

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The countably
indexed standard right Hilbert C-star module. -/
abbrev H (B : Type uB) [NonUnitalCStarAlgebra B] := Standard B ℕ

namespace Standard

variable {B : Type uB} {ι : Type uι}
variable [NonUnitalCStarAlgebra B]

noncomputable instance : NormedAddCommGroup (Standard B ι) := by
  change NormedAddCommGroup (UniformSpace.Completion (StandardPre B ι))
  infer_instance

noncomputable instance : NormedSpace ℂ (Standard B ι) := by
  change NormedSpace ℂ (UniformSpace.Completion (StandardPre B ι))
  infer_instance

instance : CompleteSpace (Standard B ι) := by
  change CompleteSpace (UniformSpace.Completion (StandardPre B ι))
  infer_instance

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The opposite
coefficient algebra has the C-star-positive order determined by its self-adjoint spectrum. -/
local instance spectralOrderBop : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder _
local instance : @StarOrderedRing Bᵐᵒᵖ _ spectralOrderBop _ :=
  CStarAlgebra.spectralOrderedRing _

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The canonical
isometric inclusion of finite-support vectors. -/
def ofPre : StandardPre B ι →ₗᵢ[ℂ] Standard B ι :=
  UniformSpace.Completion.toComplₗᵢ

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Finite-support
vectors have dense range in the standard module. -/
theorem denseRange_ofPre :
    DenseRange (ofPre : StandardPre B ι → Standard B ι) :=
  UniformSpace.Completion.denseRange_coe

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Right
multiplication by a fixed coefficient on finite-support vectors. -/
def rightMulPre (b : B) :
    StandardPre B ι →L[ℂ] StandardPre B ι :=
  (CStarModule.rightSMulCLM (B := B)).flip b

instance : UniformContinuousConstSMul Bᵐᵒᵖ (StandardPre B ι) where
  uniformContinuous_const_smul b :=
    (rightMulPre (B := B) (ι := ι) b.unop).uniformContinuous

noncomputable instance : SMul Bᵐᵒᵖ (Standard B ι) := by
  change SMul Bᵐᵒᵖ (UniformSpace.Completion (StandardPre B ι))
  infer_instance

instance : UniformContinuousConstSMul Bᵐᵒᵖ (Standard B ι) := by
  change UniformContinuousConstSMul Bᵐᵒᵖ
    (UniformSpace.Completion (StandardPre B ι))
  infer_instance

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
right action extends the finite-support action. -/
@[simp]
theorem ofPre_op_smul (b : Bᵐᵒᵖ) (x : StandardPre B ι) :
    ofPre (b • x) = b • (ofPre x : Standard B ι) := by
  change (↑(b • x) : UniformSpace.Completion (StandardPre B ι)) =
    b • (↑x : UniformSpace.Completion (StandardPre B ι))
  exact UniformSpace.Completion.coe_smul b x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
right action extends right-action right multiplication. -/
theorem ofPre_right_smul (x : StandardPre B ι) (b : B) :
    ofPre (x <• b) = (ofPre x : Standard B ι) <• b :=
  ofPre_op_smul (MulOpposite.op b) x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Coordinate
evaluation on the completed standard module. -/
def coord (i : ι) : Standard B ι →L[ℂ] B :=
  (StandardPre.coord (B := B) i).fromCompletion

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Coordinate
evaluation agrees with the finite-support inclusion. -/
@[simp]
theorem coord_ofPre (i : ι) (x : StandardPre B ι) :
    coord i (ofPre x) = x i := by
  change (StandardPre.coord i).fromCompletion
      (↑x : UniformSpace.Completion (StandardPre B ι)) = x i
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  exact StandardPre.coord_apply i x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Every completed
coordinate is contractive. -/
theorem norm_coord_le (x : Standard B ι) (i : ι) :
    ‖coord i x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (continuous_norm.comp (coord i).continuous) continuous_norm) ?_
  intro x
  change ‖coord i (ofPre x : Standard B ι)‖ ≤
    ‖(ofPre x : Standard B ι)‖
  rw [coord_ofPre, (ofPre (B := B) (ι := ι)).norm_map]
  exact StandardPre.norm_coord_le x i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The two-stage
continuous extension of the finite-support inner product. The linear variable is completed
first, followed by the conjugate-linear variable. -/
noncomputable def innerOp :
    Standard B ι →L⋆[ℂ] Standard B ι →L[ℂ] Bᵐᵒᵖ := by
  change UniformSpace.Completion (StandardPre B ι) →L⋆[ℂ]
    UniformSpace.Completion (StandardPre B ι) →L[ℂ] Bᵐᵒᵖ
  exact ((((CStarModule.innerSL
    (A := Bᵐᵒᵖ) (E := StandardPre B ι)).flip).fromCompletion).flip).fromCompletion

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
inner product agrees with the finite-support inner product on the dense canonical image. -/
@[simp]
theorem innerOp_ofPre_ofPre (x y : StandardPre B ι) :
    innerOp (ofPre x) (ofPre y) = StandardPre.innerOp x y := by
  change (((((CStarModule.innerSL
      (A := Bᵐᵒᵖ) (E := StandardPre B ι)).flip).fromCompletion).flip).fromCompletion
      (↑x : UniformSpace.Completion (StandardPre B ι)))
      (↑y : UniformSpace.Completion (StandardPre B ι)) =
    StandardPre.innerOp x y
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  change (((CStarModule.innerSL
      (A := Bᵐᵒᵖ) (E := StandardPre B ι)).flip).fromCompletion
      (↑y : UniformSpace.Completion (StandardPre B ι))) x =
    StandardPre.innerOp x y
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
inner product is jointly continuous. -/
@[continuity, fun_prop]
theorem continuous_innerOp :
    Continuous fun p : Standard B ι × Standard B ι ↦ innerOp p.1 p.2 := by
  unfold innerOp
  fun_prop

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
inner product is conjugate symmetric. -/
theorem innerOp_star (x y : Standard B ι) :
    star (innerOp x y) = innerOp y x := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  refine UniformSpace.Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro y
  change star (innerOp (ofPre x) (ofPre y)) = innerOp (ofPre y) (ofPre x)
  rw [innerOp_ofPre_ofPre, innerOp_ofPre_ofPre]
  exact StandardPre.star_innerOp x y

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
diagonal inner product is positive. -/
theorem innerOp_self_nonneg (x : Standard B ι) : 0 ≤ innerOp x x := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro x
  change 0 ≤ innerOp (ofPre x) (ofPre x)
  rw [innerOp_ofPre_ofPre]
  exact StandardPre.innerOp_self_nonneg x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completion
norm is recovered from the completed inner product. -/
theorem norm_eq_sqrt_norm_innerOp_self (x : Standard B ι) :
    ‖x‖ = √‖innerOp x x‖ := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro x
  change ‖(ofPre x : Standard B ι)‖ = √‖innerOp (ofPre x) (ofPre x)‖
  rw [innerOp_ofPre_ofPre]
  exact (ofPre (B := B) (ι := ι)).norm_map x ▸
    (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x)

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
diagonal inner product vanishes exactly at zero. -/
theorem innerOp_self_eq_zero (x : Standard B ι) : innerOp x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [norm_eq_sqrt_norm_innerOp_self, h, norm_zero, Real.sqrt_zero]
  · rintro rfl
    simp [innerOp]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
inner product is compatible with the right coefficient action in its second variable. -/
theorem innerOp_op_smul_right (a : Bᵐᵒᵖ) (x y : Standard B ι) :
    innerOp x (a • y) = a * innerOp x y := by
  have hleft : Continuous fun p : Standard B ι × Standard B ι ↦
      innerOp p.1 (a • p.2) :=
    continuous_innerOp.comp
      (continuous_fst.prodMk ((continuous_const_smul a).comp continuous_snd))
  have hright : Continuous fun p : Standard B ι × Standard B ι ↦
      a * innerOp p.1 p.2 :=
    continuous_const.mul continuous_innerOp
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq hleft hright) ?_
  intro x y
  change innerOp (ofPre x) (a • ofPre y) = a * innerOp (ofPre x) (ofPre y)
  rw [← ofPre_op_smul]
  rw [innerOp_ofPre_ofPre, innerOp_ofPre_ofPre]
  change inner Bᵐᵒᵖ x (a • y) = a * inner Bᵐᵒᵖ x y
  exact CStarModule.inner_op_smul_right

@[instance_reducible]
noncomputable instance : CStarModule Bᵐᵒᵖ (Standard B ι) where
  inner := fun x y ↦ innerOp x y
  inner_add_right := by
    intro x y z
    exact (innerOp x).map_add y z
  inner_self_nonneg := by
    intro x
    exact innerOp_self_nonneg x
  inner_self := by
    intro x
    exact innerOp_self_eq_zero x
  inner_op_smul_right := by
    intro a x y
    exact innerOp_op_smul_right a x y
  inner_smul_right_complex := by
    intro c x y
    exact (innerOp x).map_smul c y
  star_inner := by
    intro x y
    exact innerOp_star x y
  norm_eq_sqrt_norm_inner_self := by
    intro x
    exact norm_eq_sqrt_norm_innerOp_self x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The bundled
C-star-module inner product is the two-stage completion of the finite-support inner product. -/
@[simp]
theorem inner_eq_innerOp (x y : Standard B ι) : inner Bᵐᵒᵖ x y = innerOp x y :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The completed
inner product agrees with the finite-support right inner product on the dense canonical image. -/
@[simp]
theorem rightInner_ofPre_ofPre (x y : StandardPre B ι) :
    CStarModule.rightInner (B := B) (ofPre x) (ofPre y) =
      CStarModule.rightInner (B := B) x y := by
  rw [CStarModule.rightInner, CStarModule.rightInner, inner_eq_innerOp]
  change MulOpposite.unop (innerOp (ofPre x) (ofPre y)) =
    MulOpposite.unop (StandardPre.innerOp x y)
  rw [innerOp_ofPre_ofPre]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
coordinate evaluation intertwines the opposite-algebra coefficient action. -/
@[simp]
theorem coord_op_smul (i : ι) (b : Bᵐᵒᵖ) (x : Standard B ι) :
    coord i (b • x) = b • coord i x := by
  have hleft : Continuous fun x : Standard B ι ↦ coord i (b • x) :=
    (coord i).continuous.comp (continuous_const_smul b)
  have hright : Continuous fun x : Standard B ι ↦ b • coord i x :=
    (continuous_const_smul b).comp (coord i).continuous
  refine UniformSpace.Completion.induction_on x (isClosed_eq hleft hright) ?_
  intro x
  change coord i (b • (ofPre x : Standard B ι)) = b • coord i (ofPre x)
  rw [← ofPre_op_smul, coord_ofPre, coord_ofPre]
  exact StandardPre.coe_op_smul b x i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
coordinate evaluation intertwines right-action right multiplication. -/
theorem coord_right_smul (i : ι) (x : Standard B ι) (b : B) :
    coord i (x <• b) = coord i x * b := by
  rw [coord_op_smul]
  exact CStarModule.Right.right_smul_self (coord i x) b

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Restriction to
a finite coordinate set on the completed standard module. -/
noncomputable def truncate (s : Finset ι) : Standard B ι →L[ℂ] Standard B ι := by
  change UniformSpace.Completion (StandardPre B ι) →L[ℂ]
    UniformSpace.Completion (StandardPre B ι)
  exact (StandardPre.truncate (B := B) s).completion

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
truncation extends finite-support truncation. -/
@[simp]
theorem truncate_ofPre (s : Finset ι) (x : StandardPre B ι) :
    truncate s (ofPre x) = ofPre (StandardPre.truncate s x) := by
  change (StandardPre.truncate s).completion
      (↑x : UniformSpace.Completion (StandardPre B ι)) =
    (↑(StandardPre.truncate s x) : UniformSpace.Completion (StandardPre B ι))
  exact ContinuousLinearMap.completion_apply_coe _ _

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
truncation keeps exactly the selected coordinates. -/
@[simp]
theorem coord_truncate [DecidableEq ι]
    (s : Finset ι) (x : Standard B ι) (i : ι) :
    coord i (truncate s x) = if i ∈ s then coord i x else 0 := by
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq ((coord i).continuous.comp (truncate s).continuous)
        (coord i).continuous) ?_
    intro x
    change coord i (truncate s (ofPre x : Standard B ι)) = coord i (ofPre x)
    rw [truncate_ofPre, coord_ofPre, coord_ofPre, StandardPre.truncate_apply]
    simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte]
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq ((coord i).continuous.comp (truncate s).continuous)
        continuous_const) ?_
    intro x
    change coord i (truncate s (ofPre x : Standard B ι)) = 0
    rw [truncate_ofPre, coord_ofPre, StandardPre.truncate_apply]
    simp only [hi, ↓reduceIte]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
truncation commutes with the opposite-algebra right action. -/
@[simp]
theorem truncate_op_smul (s : Finset ι) (b : Bᵐᵒᵖ) (x : Standard B ι) :
    truncate s (b • x) = b • truncate s x := by
  have hleft : Continuous fun x : Standard B ι ↦ truncate s (b • x) :=
    (truncate s).continuous.comp (continuous_const_smul b)
  have hright : Continuous fun x : Standard B ι ↦ b • truncate s x :=
    (continuous_const_smul b).comp (truncate s).continuous
  refine UniformSpace.Completion.induction_on x (isClosed_eq hleft hright) ?_
  intro x
  change truncate s (b • (ofPre x : Standard B ι)) = b • truncate s (ofPre x)
  rw [← ofPre_op_smul, truncate_ofPre, truncate_ofPre,
    StandardPre.truncate_op_smul, ofPre_op_smul]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
truncation commutes with right-action right multiplication. -/
theorem truncate_right_smul (s : Finset ι) (x : Standard B ι) (b : B) :
    truncate s (x <• b) = truncate s x <• b :=
  truncate_op_smul s (MulOpposite.op b) x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
truncation is contractive. -/
theorem norm_truncate_le (s : Finset ι) (x : Standard B ι) :
    ‖truncate s x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (continuous_norm.comp (truncate s).continuous) continuous_norm) ?_
  intro x
  change ‖truncate s (ofPre x : Standard B ι)‖ ≤ ‖(ofPre x : Standard B ι)‖
  rw [truncate_ofPre, (ofPre (B := B) (ι := ι)).norm_map,
    (ofPre (B := B) (ι := ι)).norm_map]
  exact StandardPre.norm_truncate_le s x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Finite-
coordinate truncations converge to every standard-module vector. -/
theorem tendsto_truncate (x : Standard B ι) :
    Tendsto (fun s : Finset ι ↦ truncate s x) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy⟩ :=
    (denseRange_ofPre (B := B) (ι := ι)).exists_dist_lt x (half_pos hε)
  filter_upwards [eventually_ge_atTop (StandardPre.toFinsupp y).support] with s hs
  have hfix : truncate s (ofPre y : Standard B ι) = ofPre y := by
    rw [truncate_ofPre,
      StandardPre.truncate_eq_self_of_support_subset _ _ hs]
  rw [dist_eq_norm] at hy ⊢
  calc
    ‖truncate s x - x‖ =
        ‖truncate s (x - ofPre y) - (x - ofPre y)‖ := by
      congr 1
      rw [map_sub, hfix]
      abel
    _ ≤ ‖truncate s (x - ofPre y)‖ + ‖x - ofPre y‖ := norm_sub_le _ _
    _ ≤ ‖x - ofPre y‖ + ‖x - ofPre y‖ :=
      add_le_add (norm_truncate_le s (x - ofPre y)) le_rfl
    _ < ε := by linarith

private theorem continuous_rightInner :
    Continuous fun p : Standard B ι × Standard B ι ↦
      CStarModule.rightInner (B := B) p.1 p.2 :=
  MulOpposite.continuous_unop.comp CStarModule.continuous_inner

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The right inner
product of two completed truncations is the corresponding finite coordinate sum. -/
theorem rightInner_truncate (s : Finset ι) (x y : Standard B ι) :
    CStarModule.rightInner (B := B) (truncate s x) (truncate s y) =
      ∑ i ∈ s, star (coord i x) * coord i y := by
  have hleft : Continuous fun p : Standard B ι × Standard B ι ↦
      CStarModule.rightInner (B := B) (truncate s p.1) (truncate s p.2) :=
    (continuous_rightInner (B := B) (ι := ι)).comp
      (((truncate s).continuous.comp continuous_fst).prodMk
        ((truncate s).continuous.comp continuous_snd))
  have hright : Continuous fun p : Standard B ι × Standard B ι ↦
      ∑ i ∈ s, star (coord i p.1) * coord i p.2 := by
    fun_prop
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq hleft hright) ?_
  intro x y
  change CStarModule.rightInner (B := B)
      (truncate s (ofPre x : Standard B ι))
      (truncate s (ofPre y : Standard B ι)) =
    ∑ i ∈ s, star (coord i (ofPre x : Standard B ι)) *
      coord i (ofPre y : Standard B ι)
  rw [truncate_ofPre, truncate_ofPre, rightInner_ofPre_ofPre,
    StandardPre.rightInner_truncate]
  simp only [coord_ofPre]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Insert one
coefficient at a selected coordinate of the standard module. -/
def single (i : ι) : B →L[ℂ] Standard B ι :=
  (ofPre (B := B) (ι := ι)).toContinuousLinearMap.comp
    (StandardPre.single (B := B) i)

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A completed
single is represented by the corresponding finite-support vector. -/
theorem single_apply (i : ι) (b : B) :
    single i b = ofPre (StandardPre.single i b) :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The selected
coordinate of a coefficient single is its coefficient. -/
@[simp]
theorem coord_single_self (i : ι) (b : B) : coord i (single i b) = b := by
  rw [single_apply, coord_ofPre, StandardPre.single_apply]
  exact Finsupp.single_eq_same

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Every other
coordinate of a coefficient single vanishes. -/
@[simp]
theorem coord_single_ne {i j : ι} (h : j ≠ i) (b : B) :
    coord j (single i b) = 0 := by
  rw [single_apply, coord_ofPre, StandardPre.single_apply]
  exact Finsupp.single_eq_of_ne h

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The right inner
product of two completed coefficient singles at the same index. -/
@[simp]
theorem rightInner_single (i : ι) (b c : B) :
    CStarModule.rightInner (B := B) (single i b) (single i c) = star b * c := by
  rw [single_apply, single_apply, rightInner_ofPre_ofPre,
    StandardPre.rightInner_single]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
coefficient singles intertwine right-action right multiplication. -/
@[simp]
theorem single_right_smul (i : ι) (b c : B) :
    single i b <• c = single i (b * c) := by
  rw [single_apply, ← ofPre_right_smul,
    StandardPre.single_right_smul, single_apply]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A completed
coefficient single has the norm of its coefficient. -/
theorem norm_single (i : ι) (b : B) : ‖single i b‖ = ‖b‖ := by
  rw [single_apply, (ofPre (B := B) (ι := ι)).norm_map,
    StandardPre.single_apply, StandardPre.norm_single]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Completed
coefficient singles at distinct indices are orthogonal. -/
@[simp]
theorem rightInner_single_ne {i j : ι} (h : i ≠ j) (b c : B) :
    CStarModule.rightInner (B := B) (single i b) (single j c) = 0 := by
  rw [single_apply, single_apply, rightInner_ofPre_ofPre,
    StandardPre.rightInner_single_ne h]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The complex
span of all coefficient singles is dense in the standard module. -/
theorem dense_span_single :
    Dense (Submodule.span ℂ
      (Set.range fun p : ι × B ↦ single p.1 p.2) : Set (Standard B ι)) := by
  refine (denseRange_ofPre (B := B) (ι := ι)).mono ?_
  rintro _ ⟨x, rfl⟩
  have hx : (ofPre x : Standard B ι) =
      ∑ i ∈ (StandardPre.toFinsupp x).support, single i (x i) := by
    have hpre := congrArg
      (fun z : StandardPre B ι ↦ (ofPre z : Standard B ι))
      (StandardPre.sum_single_support x)
    simpa only [map_sum, single_apply] using hpre.symm
  rw [hx]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.subset_span (Set.mem_range_self (i, x i))

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A completed
truncation is the finite sum of its coordinate singles. -/
theorem truncate_eq_sum_single (s : Finset ι) (x : Standard B ι) :
    truncate s x = ∑ i ∈ s, single i (coord i x) := by
  have hleft : Continuous fun x : Standard B ι ↦ truncate s x :=
    (truncate s).continuous
  have hright : Continuous fun x : Standard B ι ↦
      ∑ i ∈ s, single i (coord i x) := by
    fun_prop
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq hleft hright) ?_
  intro x
  change truncate s (ofPre x : Standard B ι) =
    ∑ i ∈ s, single i (coord i (ofPre x : Standard B ι))
  rw [truncate_ofPre, StandardPre.truncate_eq_sum_single]
  simp only [coord_ofPre, single_apply, map_sum]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The coordinate
singles of a standard-module vector sum to that vector. -/
theorem hasSum_single_coord (x : Standard B ι) :
    HasSum (fun i ↦ single i (coord i x)) x := by
  change Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, single i (coord i x))
    atTop (𝓝 x)
  simpa only [← truncate_eq_sum_single] using tendsto_truncate x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Standard-module
vectors are determined by their coordinates. -/
@[ext]
theorem coord_ext {x y : Standard B ι}
    (h : ∀ i, coord i x = coord i y) : x = y := by
  have hf : (fun i ↦ single i (coord i x)) =
      fun i ↦ single i (coord i y) :=
    funext fun i ↦ congrArg (single i) (h i)
  apply (hasSum_single_coord x).unique
  simpa only [hf] using hasSum_single_coord y

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The coordinate
cross terms sum to the right inner product. -/
theorem hasSum_coord_star_mul_coord (x y : Standard B ι) :
    HasSum (fun i ↦ star (coord i x) * coord i y)
      (CStarModule.rightInner (B := B) x y) := by
  have hpair : Tendsto (fun s : Finset ι ↦ (truncate s x, truncate s y))
      atTop (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact (tendsto_truncate x).prodMk (tendsto_truncate y)
  have hinner :=
    ((continuous_rightInner (B := B) (ι := ι)).tendsto (x, y)).comp hpair
  have hfun :
      (fun s : Finset ι ↦ CStarModule.rightInner (B := B)
        (truncate s x) (truncate s y)) =
      (fun s : Finset ι ↦ ∑ i ∈ s, star (coord i x) * coord i y) := by
    funext s
    exact rightInner_truncate s x y
  change Tendsto (fun s : Finset ι ↦
      ∑ i ∈ s, star (coord i x) * coord i y) atTop
      (𝓝 (CStarModule.rightInner (B := B) x y))
  rw [← hfun]
  change Tendsto
    ((fun p : Standard B ι × Standard B ι ↦
      CStarModule.rightInner (B := B) p.1 p.2) ∘
        fun s : Finset ι ↦ (truncate s x, truncate s y))
      atTop (𝓝 (CStarModule.rightInner (B := B) x y))
  exact hinner

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Coordinate
cross terms are summable. -/
theorem summable_coord_star_mul_coord (x y : Standard B ι) :
    Summable (fun i ↦ star (coord i x) * coord i y) :=
  (hasSum_coord_star_mul_coord x y).summable

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The right inner
product is the sum of the coordinate cross terms. -/
theorem rightInner_eq_tsum_coord (x y : Standard B ι) :
    CStarModule.rightInner (B := B) x y =
      ∑' i, star (coord i x) * coord i y :=
  (hasSum_coord_star_mul_coord x y).tsum_eq.symm

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The squared
norm is the norm of the diagonal coordinate sum. -/
theorem norm_sq_eq_norm_tsum_coord (x : Standard B ι) :
    ‖x‖ ^ 2 = ‖∑' i, star (coord i x) * coord i x‖ := by
  rw [← CStarModule.norm_rightInner_self (B := B) x,
    rightInner_eq_tsum_coord]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A coefficient
family is square summable when its positive diagonal series is summable in the coefficient
algebra. -/
def IsSquareSummable (a : ι → B) : Prop :=
  Summable (fun i ↦ star (a i) * a i)

private def finitePartial (a : ι → B) (s : Finset ι) : Standard B ι :=
  ∑ i ∈ s, single i (a i)

@[simp]
private theorem coord_finitePartial [DecidableEq ι]
    (a : ι → B) (s : Finset ι) (i : ι) :
    coord i (finitePartial a s) = if i ∈ s then a i else 0 := by
  classical
  unfold finitePartial
  rw [map_sum]
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    rw [Finset.sum_eq_single i]
    · exact coord_single_self i (a i)
    · intro j _ hji
      exact coord_single_ne (Ne.symm hji) (a j)
    · exact fun hnot => (hnot hi).elim
  · simp only [hi, ↓reduceIte]
    exact Finset.sum_eq_zero fun j hj ↦ coord_single_ne (fun hji ↦ by
      subst j
      exact hi hj) _

private theorem finitePartial_sub_of_subset [DecidableEq ι]
    (a : ι → B) {N s : Finset ι}
    (hNs : N ⊆ s) :
    finitePartial a s - finitePartial a N = finitePartial a (s \ N) := by
  classical
  apply coord_ext
  intro i
  simp only [map_sub, coord_finitePartial]
  by_cases hiN : i ∈ N
  · have his : i ∈ s := hNs hiN
    simp [hiN, his, Finset.mem_sdiff]
  · by_cases his : i ∈ s <;> simp [hiN, his, Finset.mem_sdiff]

private theorem truncate_finitePartial (a : ι → B) (s : Finset ι) :
    truncate s (finitePartial a s) = finitePartial a s := by
  classical
  rw [truncate_eq_sum_single]
  change (∑ i ∈ s, single i (coord i (finitePartial a s))) =
    ∑ i ∈ s, single i (a i)
  apply Finset.sum_congr rfl
  intro i hi
  rw [coord_finitePartial]
  simp only [hi, ↓reduceIte]

private theorem norm_finitePartial_sq (a : ι → B) (s : Finset ι) :
    ‖finitePartial a s‖ ^ 2 = ‖∑ i ∈ s, star (a i) * a i‖ := by
  classical
  calc
    ‖finitePartial a s‖ ^ 2 =
        ‖CStarModule.rightInner (B := B) (finitePartial a s)
          (finitePartial a s)‖ :=
      (CStarModule.norm_rightInner_self (B := B) (finitePartial a s)).symm
    _ = ‖CStarModule.rightInner (B := B)
          (truncate s (finitePartial a s))
          (truncate s (finitePartial a s))‖ := by
      rw [truncate_finitePartial]
    _ = ‖∑ i ∈ s, star (coord i (finitePartial a s)) *
          coord i (finitePartial a s)‖ :=
      congrArg (fun b : B ↦ ‖b‖)
        (rightInner_truncate s (finitePartial a s) (finitePartial a s))
    _ = ‖∑ i ∈ s, star (a i) * a i‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [coord_finitePartial]
      simp only [hi, ↓reduceIte]

private theorem cauchySeq_finitePartial {a : ι → B}
    (ha : IsSquareSummable a) :
    CauchySeq (fun s : Finset ι ↦ finitePartial a s) := by
  classical
  rw [Metric.cauchySeq_iff']
  intro ε hε
  change Summable (fun i ↦ star (a i) * a i) at ha
  rcases (summable_iff_vanishing_norm.mp ha) (ε ^ 2)
    (sq_pos_of_pos hε) with ⟨N, hN⟩
  refine ⟨N, fun s hs ↦ ?_⟩
  rw [dist_eq_norm, finitePartial_sub_of_subset a hs,
    ← sq_lt_sq₀ (norm_nonneg _) hε.le, norm_finitePartial_sq]
  exact hN (s \ N) Finset.sdiff_disjoint

private theorem exists_coord_eq_of_isSquareSummable {a : ι → B}
    (ha : IsSquareSummable a) :
    ∃ x : Standard B ι, ∀ i, coord i x = a i := by
  classical
  obtain ⟨x, hx⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_finitePartial ha)
  refine ⟨x, fun i ↦ ?_⟩
  have hcoord : Tendsto (fun s : Finset ι ↦ coord i (finitePartial a s))
      atTop (𝓝 (coord i x)) := ((coord i).continuous.tendsto x).comp hx
  have hevent : ∀ᶠ s : Finset ι in atTop,
      coord i (finitePartial a s) = a i :=
    (eventually_ge_atTop {i}).mono fun s hs ↦ by
      rw [coord_finitePartial]
      simp only [Finset.singleton_subset_iff.mp hs, ↓reduceIte]
  have haLim : Tendsto (fun s : Finset ι ↦ coord i (finitePartial a s))
      atTop (𝓝 (a i)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)
  exact tendsto_nhds_unique hcoord haLim

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A square-
summable coefficient family is represented by a unique standard-module vector. -/
theorem exists_standard_of_isSquareSummable {a : ι → B}
    (ha : IsSquareSummable a) :
    ∃! x : Standard B ι, ∀ i, coord i x = a i := by
  obtain ⟨x, hx⟩ := exists_coord_eq_of_isSquareSummable ha
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact coord_ext fun i ↦ (hy i).trans (hx i).symm

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The standard-
module vector represented by a square-summable coefficient family. -/
noncomputable def ofSquareSummable
    (a : {a : ι → B // IsSquareSummable a}) : Standard B ι :=
  Classical.choose (exists_standard_of_isSquareSummable a.property)

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The chosen
vector represented by a square-summable family has the given coordinates. -/
@[simp]
theorem coord_ofSquareSummable
    (a : {a : ι → B // IsSquareSummable a}) (i : ι) :
    coord i (ofSquareSummable a) = a.1 i :=
  (Classical.choose_spec
    (exists_standard_of_isSquareSummable a.property)).1 i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The coordinate
family of every standard-module vector is square summable. -/
theorem isSquareSummable_coord (x : Standard B ι) :
    IsSquareSummable (fun i ↦ coord i x) :=
  summable_coord_star_mul_coord x x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. Coordinate
evaluation identifies the standard module with the coefficient families whose series of
conjugate-coordinate products with themselves is summable in B. -/
noncomputable def summableSequenceEquiv :
    Standard B ι ≃ {a : ι → B // IsSquareSummable a} where
  toFun x := ⟨fun i ↦ coord i x, isSquareSummable_coord x⟩
  invFun := ofSquareSummable
  left_inv x := coord_ext
    (x := ofSquareSummable
      (⟨fun i ↦ coord i x, isSquareSummable_coord x⟩ :
        {a : ι → B // IsSquareSummable a}))
    (y := x) fun i ↦ coord_ofSquareSummable _ i
  right_inv a := Subtype.ext <| funext fun i ↦ coord_ofSquareSummable a i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The forward
square-summable view is coordinate evaluation. -/
@[simp]
theorem summableSequenceEquiv_apply_coord (x : Standard B ι) (i : ι) :
    (summableSequenceEquiv (B := B) (ι := ι) x).1 i = coord i x :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The inverse
square-summable view has the prescribed coordinates. -/
@[simp]
theorem coord_summableSequenceEquiv_symm
    (a : {a : ι → B // IsSquareSummable a}) (i : ι) :
    coord i ((summableSequenceEquiv (B := B) (ι := ι)).symm a) = a.1 i :=
  coord_ofSquareSummable a i

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The square-
summable view preserves addition pointwise. -/
theorem summableSequenceEquiv_add (x y : Standard B ι) :
    (summableSequenceEquiv (B := B) (ι := ι) (x + y)).1 =
      fun i ↦ (summableSequenceEquiv (B := B) (ι := ι) x).1 i +
        (summableSequenceEquiv (B := B) (ι := ι) y).1 i := by
  funext i
  simp [summableSequenceEquiv_apply_coord]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The square-
summable view preserves complex scalar multiplication pointwise. -/
theorem summableSequenceEquiv_smul (c : ℂ) (x : Standard B ι) :
    (summableSequenceEquiv (B := B) (ι := ι) (c • x)).1 =
      fun i ↦ c • (summableSequenceEquiv (B := B) (ι := ι) x).1 i := by
  funext i
  simp [summableSequenceEquiv_apply_coord]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The square-
summable view preserves the opposite-algebra right action pointwise. -/
theorem summableSequenceEquiv_op_smul (b : Bᵐᵒᵖ) (x : Standard B ι) :
    (summableSequenceEquiv (B := B) (ι := ι) (b • x)).1 =
      fun i ↦ b • (summableSequenceEquiv (B := B) (ι := ι) x).1 i := by
  funext i
  simp [summableSequenceEquiv_apply_coord]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The square-
summable view preserves right-action right multiplication pointwise. -/
theorem summableSequenceEquiv_right_smul (x : Standard B ι) (b : B) :
    (summableSequenceEquiv (B := B) (ι := ι) (x <• b)).1 =
      fun i ↦ (summableSequenceEquiv (B := B) (ι := ι) x).1 i * b := by
  funext i
  simp [summableSequenceEquiv_apply_coord]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The right inner
product is the coordinate cross sum in the square-summable view. -/
theorem summableSequenceEquiv_rightInner (x y : Standard B ι) :
    CStarModule.rightInner (B := B) x y =
      ∑' i, star ((summableSequenceEquiv (B := B) (ι := ι) x).1 i) *
        (summableSequenceEquiv (B := B) (ι := ι) y).1 i := by
  simpa only [summableSequenceEquiv_apply_coord] using
    rightInner_eq_tsum_coord x y

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The squared
norm is the diagonal sum norm in the square-summable view. -/
theorem summableSequenceEquiv_norm_sq (x : Standard B ι) :
    ‖x‖ ^ 2 = ‖∑' i,
      star ((summableSequenceEquiv (B := B) (ι := ι) x).1 i) *
        (summableSequenceEquiv (B := B) (ι := ι) x).1 i‖ := by
  simpa only [summableSequenceEquiv_apply_coord] using
    norm_sq_eq_norm_tsum_coord x

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The norm is the
square root of the diagonal sum norm in the square-summable view. -/
theorem summableSequenceEquiv_norm (x : Standard B ι) :
    ‖x‖ = √‖∑' i,
      star ((summableSequenceEquiv (B := B) (ι := ι) x).1 i) *
        (summableSequenceEquiv (B := B) (ι := ι) x).1 i‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) (x := x)]
  congr 1
  rw [← MulOpposite.norm_unop]
  change ‖CStarModule.rightInner (B := B) x x‖ = _
  rw [summableSequenceEquiv_rightInner]

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A standard
module with a chosen coordinate is full. -/
theorem isFull_of_index (i : ι) : CStarModule.IsFull B (Standard B ι) := by
  apply CStarModule.isFull_of_innerPreserving
    (fun b : B ↦ single i b) (hE := CStarModule.isFull_self (B := B))
  intro b c
  exact rightInner_single i b c

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A standard
module over a nonempty index type is full. -/
theorem isFull_of_nonempty [Nonempty ι] : CStarModule.IsFull B (Standard B ι) :=
  isFull_of_index (Classical.choice (inferInstance : Nonempty ι))

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The standard
countably indexed module is full. -/
theorem isFull_H : CStarModule.IsFull B (Standard B ℕ) :=
  isFull_of_nonempty

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. A standard
module over an empty index type is a subsingleton. -/
theorem subsingleton_of_isEmpty [IsEmpty ι] : Subsingleton (Standard B ι) := by
  constructor
  intro x y
  have hx : x = 0 := by
    apply norm_eq_zero.mp
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq continuous_norm continuous_const) ?_
    intro z
    have hz : z = 0 := by
      apply StandardPre.toFinsupp.injective
      ext i
      exact isEmptyElim i
    subst z
    change ‖(ofPre 0 : Standard B ι)‖ = 0
    simp
  have hy : y = 0 := by
    apply norm_eq_zero.mp
    refine UniformSpace.Completion.induction_on y
      (isClosed_eq continuous_norm continuous_const) ?_
    intro z
    have hz : z = 0 := by
      apply StandardPre.toFinsupp.injective
      ext i
      exact isEmptyElim i
    subst z
    change ‖(ofPre 0 : Standard B ι)‖ = 0
    simp
  exact hx.trans hy.symm

noncomputable instance [IsEmpty ι] : Subsingleton (Standard B ι) :=
  subsingleton_of_isEmpty

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The support
ideal of an empty-index standard module is bottom. -/
theorem supportIdeal_eq_bot_of_isEmpty [IsEmpty ι] :
    CStarModule.supportIdeal B (Standard B ι) = ClosedStarIdeal.bot B := by
  apply CStarModule.supportIdeal_eq_bot_iff_subsingleton.mpr
  exact subsingleton_of_isEmpty

/-- Let B be a possibly nonunital complex C-star algebra and I any index type. The standard right
Hilbert B-module is the completion of the finite-support coefficient families. The standard
module is full exactly when I is nonempty or B consists only of zero. -/
theorem isFull_iff_nonempty_or_subsingleton :
    CStarModule.IsFull B (Standard B ι) ↔ Nonempty ι ∨ Subsingleton B := by
  constructor
  · intro hfull
    cases isEmpty_or_nonempty ι
    · right
      exact (CStarModule.isFull_subsingleton_iff
        (B := B) (E := Standard B ι)).mp hfull
    · exact Or.inl inferInstance
  · rintro (hι | hB)
    · exact isFull_of_index (Classical.choice hι)
    · cases isEmpty_or_nonempty ι
      · exact (CStarModule.isFull_subsingleton_iff
          (B := B) (E := Standard B ι)).mpr hB
      · exact isFull_of_nonempty

section FiniteComparison

variable [Fintype ι]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. Coefficient evaluation identifies the finite-support premodule with the finite
standard module when the index type is finite. -/
noncomputable def preFiniteLinearEquiv :
    StandardPre B ι ≃ₗ[ℂ] FiniteStandard B ι :=
  (StandardPre.toFinsuppLinearEquiv (B := B) (ι := ι)).trans
    ((Finsupp.linearEquivFunOnFinite ℂ B ι).trans
      (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ (ι → B)).symm)

@[simp]
theorem preFiniteLinearEquiv_apply (x : StandardPre B ι) (i : ι) :
    preFiniteLinearEquiv x i = x i :=
  rfl

@[simp]
theorem preFiniteLinearEquiv_symm_apply (x : FiniteStandard B ι) (i : ι) :
    (preFiniteLinearEquiv (B := B) (ι := ι)).symm x i = x i :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The algebraic finite comparison is isometric. -/
theorem norm_preFiniteLinearEquiv (x : StandardPre B ι) :
    ‖preFiniteLinearEquiv x‖ = ‖x‖ := by
  rw [finite_norm, StandardPre.norm_apply]
  congr 2
  rw [Finsupp.sum_fintype _ _ (by intro; simp)]
  rfl

private theorem finiteComparison_norm (x : StandardPre B ι) :
    ‖(LinearMap.id : FiniteStandard B ι →ₗ[ℂ] FiniteStandard B ι)
        (preFiniteLinearEquiv x)‖ =
      ‖(ofPre (B := B) (ι := ι)).toLinearMap x‖ := by
  change ‖preFiniteLinearEquiv x‖ = ‖ofPre (B := B) (ι := ι) x‖
  exact (norm_preFiniteLinearEquiv x).trans
    ((ofPre (B := B) (ι := ι)).norm_map x).symm

private noncomputable def finiteLinearIsometryEquiv :
    Standard B ι ≃ₗᵢ[ℂ] FiniteStandard B ι :=
  (preFiniteLinearEquiv (B := B) (ι := ι)).extendOfIsometry
    (ofPre (B := B) (ι := ι)).toLinearMap
    (LinearMap.id : FiniteStandard B ι →ₗ[ℂ] FiniteStandard B ι)
    (denseRange_ofPre (B := B) (ι := ι)) denseRange_id
    (finiteComparison_norm (B := B) (ι := ι))

@[simp]
private theorem finiteLinearIsometryEquiv_ofPre (x : StandardPre B ι) :
    (finiteLinearIsometryEquiv (B := B) (ι := ι)) (ofPre x) =
      preFiniteLinearEquiv x := by
  unfold finiteLinearIsometryEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _
    (finiteComparison_norm (B := B) (ι := ι)) x

@[simp]
private theorem finiteLinearIsometryEquiv_symm_apply (x : FiniteStandard B ι) :
    (finiteLinearIsometryEquiv (B := B) (ι := ι)).symm x =
      (ofPre (B := B) (ι := ι)).toLinearMap
        ((preFiniteLinearEquiv (B := B) (ι := ι)).symm x) := by
  unfold finiteLinearIsometryEquiv
  exact LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _
    (finiteComparison_norm (B := B) (ι := ι)) x

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. For finite I, coefficient evaluation gives an isometric complex-linear equivalence
between the completed standard module and the finite standard module. -/
-- Exposed definitions cannot depend on private declarations, so this public
-- body repeats the private isometry's constructor while the characteristic
-- proofs below use the private name.
noncomputable def finiteEquiv :
    Standard B ι ≃L[ℂ] FiniteStandard B ι :=
  ((preFiniteLinearEquiv (B := B) (ι := ι)).extendOfIsometry
    (ofPre (B := B) (ι := ι)).toLinearMap
    (LinearMap.id : FiniteStandard B ι →ₗ[ℂ] FiniteStandard B ι)
    (denseRange_ofPre (B := B) (ι := ι)) denseRange_id
    (fun x ↦ (norm_preFiniteLinearEquiv x).trans
      ((ofPre (B := B) (ι := ι)).norm_map x).symm)).toContinuousLinearEquiv

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison preserves norms. -/
@[simp]
theorem norm_finiteEquiv (x : Standard B ι) :
    ‖(finiteEquiv (B := B) (ι := ι)) x‖ = ‖x‖ := by
  change ‖finiteLinearIsometryEquiv (B := B) (ι := ι) x‖ = ‖x‖
  exact (finiteLinearIsometryEquiv (B := B) (ι := ι)).norm_map x

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison extends the algebraic coefficient equivalence. -/
@[simp]
theorem finiteEquiv_ofPre (x : StandardPre B ι) :
    (finiteEquiv (B := B) (ι := ι)) (ofPre x) = preFiniteLinearEquiv x := by
  change finiteLinearIsometryEquiv (B := B) (ι := ι) (ofPre x) = _
  exact finiteLinearIsometryEquiv_ofPre (B := B) (ι := ι) x

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The inverse finite comparison sends a finite vector to its canonical finite-support
representative. -/
@[simp]
theorem finiteEquiv_symm_apply (x : FiniteStandard B ι) :
    (finiteEquiv (B := B) (ι := ι)).symm x =
      ofPre ((preFiniteLinearEquiv (B := B) (ι := ι)).symm x) := by
  change (finiteLinearIsometryEquiv (B := B) (ι := ι)).symm x =
    (ofPre (B := B) (ι := ι)).toLinearMap
      ((preFiniteLinearEquiv (B := B) (ι := ι)).symm x)
  exact finiteLinearIsometryEquiv_symm_apply (B := B) (ι := ι) x

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison is pinned by completed coordinates. -/
@[simp]
theorem finiteEquiv_apply_coord (x : Standard B ι) (i : ι) :
    (finiteEquiv (B := B) (ι := ι)) x i = coord i x := by
  have hleft : Continuous fun x : Standard B ι ↦
      finiteCoord i ((finiteEquiv (B := B) (ι := ι)) x) :=
    (finiteCoord i).continuous.comp (finiteEquiv (B := B) (ι := ι)).continuous
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq hleft (coord i).continuous) ?_
  intro x
  change (finiteEquiv (B := B) (ι := ι)) (ofPre x) i = coord i (ofPre x)
  rw [finiteEquiv_ofPre, preFiniteLinearEquiv_apply, coord_ofPre]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. Coordinates also pin the inverse finite comparison. -/
theorem finiteEquiv_symm_coord (x : FiniteStandard B ι) (i : ι) :
    coord i ((finiteEquiv (B := B) (ι := ι)).symm x) = x i := by
  have h := finiteEquiv_apply_coord
    ((finiteEquiv (B := B) (ι := ι)).symm x) i
  calc
    coord i ((finiteEquiv (B := B) (ι := ι)).symm x) =
        (finiteEquiv (B := B) (ι := ι))
          ((finiteEquiv (B := B) (ι := ι)).symm x) i := h.symm
    _ = x i := congrFun ((finiteEquiv (B := B) (ι := ι)).apply_symm_apply x) i

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison preserves the canonical opposite-algebra action. -/
@[simp]
theorem finiteEquiv_op_smul (a : Bᵐᵒᵖ) (x : Standard B ι) :
    (finiteEquiv (B := B) (ι := ι)) (a • x) =
      a • (finiteEquiv (B := B) (ι := ι)) x := by
  ext i
  rw [finiteEquiv_apply_coord, coord_op_smul]
  change a • coord i x = a • ((finiteEquiv (B := B) (ι := ι)) x) i
  rw [finiteEquiv_apply_coord]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison preserves right-action right multiplication. -/
theorem finiteEquiv_right_smul (x : Standard B ι) (b : B) :
    (finiteEquiv (B := B) (ι := ι)) (x <• b) =
      (finiteEquiv (B := B) (ι := ι)) x <• b := by
  exact finiteEquiv_op_smul (MulOpposite.op b) x

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison preserves the C-star-module inner product. -/
theorem finiteEquiv_inner (x y : Standard B ι) :
    inner Bᵐᵒᵖ ((finiteEquiv (B := B) (ι := ι)) x)
      ((finiteEquiv (B := B) (ι := ι)) y) = inner Bᵐᵒᵖ x y := by
  have hleft : Continuous fun p : Standard B ι × Standard B ι ↦
      inner Bᵐᵒᵖ ((finiteEquiv (B := B) (ι := ι)) p.1)
        ((finiteEquiv (B := B) (ι := ι)) p.2) :=
    CStarModule.continuous_inner.comp
      (((finiteEquiv (B := B) (ι := ι)).continuous.comp continuous_fst).prodMk
        ((finiteEquiv (B := B) (ι := ι)).continuous.comp continuous_snd))
  have hright : Continuous fun p : Standard B ι × Standard B ι ↦
      inner Bᵐᵒᵖ p.1 p.2 :=
    CStarModule.continuous_inner
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq hleft hright) ?_
  intro x y
  apply MulOpposite.unop_injective
  change CStarModule.rightInner (B := B)
      ((finiteEquiv (B := B) (ι := ι)) (ofPre x))
      ((finiteEquiv (B := B) (ι := ι)) (ofPre y)) =
    CStarModule.rightInner (B := B) (ofPre x) (ofPre y)
  rw [finiteEquiv_ofPre, finiteEquiv_ofPre, finite_rightInner,
    rightInner_ofPre_ofPre, StandardPre.rightInner_apply]
  rw [Finsupp.sum_fintype _ _ (by intro; simp)]
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. The standard right Hilbert B-module is the completion of the finite-support coefficient
families. The finite comparison preserves the right-action right inner product. -/
theorem finiteEquiv_rightInner (x y : Standard B ι) :
    CStarModule.rightInner (B := B) ((finiteEquiv (B := B) (ι := ι)) x)
      ((finiteEquiv (B := B) (ι := ι)) y) =
      CStarModule.rightInner (B := B) x y :=
  congrArg MulOpposite.unop (finiteEquiv_inner x y)

end FiniteComparison

end Standard

namespace Standard

section Unital

variable {B : Type uB} {ι : Type uι} [CStarAlgebra B]

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. The opposite
coefficient algebra has the C-star-positive order determined by its self-adjoint spectrum. -/
local instance spectralOrderBopUnital : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder _
local instance : @StarOrderedRing Bᵐᵒᵖ _ spectralOrderBopUnital _ :=
  CStarAlgebra.spectralOrderedRing _

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. The canonical
coordinate vector in the standard module. -/
def basisVector (i : ι) : Standard B ι := single i 1

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. The selected coordinate
of its canonical coordinate vector is one. -/
@[simp]
theorem coord_basisVector_self (i : ι) :
    coord i (basisVector (B := B) i) = 1 := by
  simp [basisVector]

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. Every other coordinate
of a canonical coordinate vector vanishes. -/
@[simp]
theorem coord_basisVector_ne {i j : ι} (h : j ≠ i) :
    coord j (basisVector (B := B) i) = 0 := by
  simp [basisVector, h]

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. A canonical coordinate
vector has right inner square one. -/
@[simp]
theorem rightInner_basisVector_self (i : ι) :
    CStarModule.rightInner (B := B) (basisVector (B := B) i)
      (basisVector (B := B) i) = 1 := by
  rw [basisVector, rightInner_single]
  simp

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. Distinct canonical
coordinate vectors are orthogonal. -/
@[simp]
theorem rightInner_basisVector_ne {i j : ι} (h : i ≠ j) :
    CStarModule.rightInner (B := B) (basisVector (B := B) i)
      (basisVector (B := B) j) = 0 := by
  simpa [basisVector] using
    rightInner_single_ne (B := B) (ι := ι) h (1 : B) (1 : B)

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. A canonical coordinate
vector has the norm of the coefficient unit. -/
theorem norm_basisVector (i : ι) :
    ‖basisVector (B := B) i‖ = ‖(1 : B)‖ := by
  change ‖single i (1 : B)‖ = ‖(1 : B)‖
  exact norm_single i 1

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. If B is nontrivial,
each coordinate vector obtained by inserting its unit has norm one. -/
@[simp]
theorem norm_basisVector_eq_one [Nontrivial B] (i : ι) :
    ‖basisVector (B := B) i‖ = 1 := by
  rw [norm_basisVector, CStarRing.norm_one]

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. Right multiplying a
canonical coordinate vector inserts that coefficient. -/
@[simp]
theorem basisVector_right_smul (i : ι) (b : B) :
    basisVector (B := B) i <• b = single i b := by
  simp [basisVector]

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. Canonical coordinate
vectors reconstruct every finite-support vector. -/
theorem sum_basisVector_right_smul_support (x : StandardPre B ι) :
    ∑ i ∈ (StandardPre.toFinsupp x).support,
      basisVector (B := B) i <• x i = ofPre x := by
  calc
    _ = ∑ i ∈ (StandardPre.toFinsupp x).support, single i (x i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact basisVector_right_smul i (x i)
    _ = ofPre (∑ i ∈ (StandardPre.toFinsupp x).support,
        StandardPre.single i (x i)) := by
      simp only [single_apply, map_sum]
    _ = ofPre x := by rw [StandardPre.sum_single_support]

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. For a finite index
type, canonical coordinate vectors reconstruct every completed vector exactly. -/
theorem sum_basisVector_right_smul [Fintype ι] (x : Standard B ι) :
    ∑ i, basisVector (B := B) i <• coord i x = x := by
  classical
  apply (finiteEquiv (B := B) (ι := ι)).injective
  ext j
  simp only [basisVector_right_smul, single_apply, StandardPre.single_apply,
    finiteEquiv_apply_coord, map_sum, coord_ofPre, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. The complex span of all
coefficient multiples of canonical coordinate vectors. -/
def basisVectorRightSpan : Submodule ℂ (Standard B ι) :=
  Submodule.span ℂ (Set.range fun p : ι × B ↦
    basisVector (B := B) p.1 <• p.2)

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. The right-generated
coordinate span is invariant under coefficient multiplication. -/
theorem basisVectorRightSpan_right_smul {x : Standard B ι}
    (hx : x ∈ basisVectorRightSpan (B := B) (ι := ι)) (b : B) :
    x <• b ∈ basisVectorRightSpan (B := B) (ι := ι) := by
  let S : Set (Standard B ι) := Set.range fun p : ι × B ↦
    basisVector (B := B) p.1 <• p.2
  change x ∈ Submodule.span ℂ S at hx
  change x <• b ∈ Submodule.span ℂ S
  refine Submodule.span_induction
    (p := fun y _ ↦ y <• b ∈ Submodule.span ℂ S) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨i, c⟩, rfl⟩
    rw [CStarModule.right_smul_mul]
    exact Submodule.subset_span (Set.mem_range_self (i, c * b))
  · rw [CStarModule.zero_right_smul]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [CStarModule.add_right_smul]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [CStarModule.smul_right_smul]
    exact Submodule.smul_mem _ c hy

/-- Let B be a unital complex C-star algebra and I any index type. The standard right Hilbert
B-module is the completion of the finite-support coefficient families. The right-generated
coordinate span is dense in the standard module. -/
theorem dense_basisVectorRightSpan :
    Dense (basisVectorRightSpan (B := B) (ι := ι) : Set (Standard B ι)) := by
  refine (denseRange_ofPre (B := B) (ι := ι)).mono ?_
  rintro _ ⟨x, rfl⟩
  rw [← sum_basisVector_right_smul_support x]
  unfold basisVectorRightSpan
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.subset_span (Set.mem_range_self (i, x i))

end Unital

end Standard

section FiniteFullness

variable {B : Type uB} {ι : Type uι} [Fintype ι]
variable [NonUnitalCStarAlgebra B]

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. The opposite coefficient algebra has the C-star-positive order determined by its
self-adjoint spectrum. -/
local instance spectralOrderBopFiniteFullness : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder _
local instance : @StarOrderedRing Bᵐᵒᵖ _ spectralOrderBopFiniteFullness _ :=
  CStarAlgebra.spectralOrderedRing _

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. The right inner product of two finite coefficient singles at the same index. -/
@[simp↓]
theorem finite_rightInner_single (i : ι) (b c : B) :
    CStarModule.rightInner (B := B) (finiteSingle i b) (finiteSingle i c) =
      star b * c := by
  classical
  rw [finite_rightInner]
  rw [Finset.sum_eq_single i]
  · simp [finiteSingle]
  · intro j _ hji
    simp [finiteSingle, hji]
  · simp

private theorem isFull_standard_iff_finite :
    CStarModule.IsFull B (Standard B ι) ↔
      CStarModule.IsFull B (FiniteStandard B ι) :=
  CStarModule.isFull_iff_of_innerPreserving_surjective
    (Standard.finiteEquiv (B := B) (ι := ι))
    (Standard.finiteEquiv (B := B) (ι := ι)).surjective
    (Standard.finiteEquiv_rightInner (B := B) (ι := ι))

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. A finite standard module with a chosen coordinate is full. -/
theorem finite_isFull_of_index (i : ι) :
    CStarModule.IsFull B (FiniteStandard B ι) :=
  isFull_standard_iff_finite.mp (Standard.isFull_of_index i)

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. A finite standard module over a nonempty index type is full. -/
theorem finite_isFull_of_nonempty [Nonempty ι] :
    CStarModule.IsFull B (FiniteStandard B ι) :=
  isFull_standard_iff_finite.mp Standard.isFull_of_nonempty

omit [Fintype ι] [NonUnitalCStarAlgebra B] in
/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. A finite standard module over an empty index type is a subsingleton. -/
theorem finite_subsingleton_of_isEmpty [IsEmpty ι] :
    Subsingleton (FiniteStandard B ι) := by
  constructor
  intro x y
  apply (WithCStarModule.equiv Bᵐᵒᵖ (ι → B)).injective
  funext i
  exact isEmptyElim i

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. The support ideal of an empty-index finite standard module is bottom. -/
theorem finite_supportIdeal_eq_bot_of_isEmpty [IsEmpty ι] :
    CStarModule.supportIdeal B (FiniteStandard B ι) = ClosedStarIdeal.bot B := by
  apply CStarModule.supportIdeal_eq_bot_iff_subsingleton.mpr
  exact finite_subsingleton_of_isEmpty

/-- Let B be a possibly nonunital complex C-star algebra and I a finite index type, possibly
empty. Consider the finite standard right B-module with its coefficient-valued sum inner
product. The finite standard module is full exactly when I is nonempty or B consists only of
zero. -/
theorem finite_isFull_iff_nonempty_or_subsingleton :
    CStarModule.IsFull B (FiniteStandard B ι) ↔
      Nonempty ι ∨ Subsingleton B :=
  isFull_standard_iff_finite.symm.trans
    Standard.isFull_iff_nonempty_or_subsingleton

end FiniteFullness

end CStarModule.Right
