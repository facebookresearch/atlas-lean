/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Matrix.Positivity
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Finite Hilbert-module columns and canonical Gram matrices

The column and its adjoint are actual bounded maps on the existing finite
Hilbert-module norm. The input opposite-order dictionaries are retained.
The coefficient order used internally by the stock matrix norm and the
matrix/endomorphism orders are canonical for positivity.

The Gram matrix is reflected through the existing faithful nonunital matrix
representation. No coefficient unit, matrix positivity assumption, tensor
model or new module norm is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators CStarModule.Right RightActions

namespace CStarModule.AdjointableOperator

universe uB uI uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {I : Type uI} [Fintype I]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- Let B be a possibly nonunital complex C-star algebra, E a normed right C-star module over B,
and I a finite index type, possibly empty. For a finite vector family x indexed by I, the
column map sends a coefficient family b to the sum of x(i)b(i); its adjoint sends a vector e
to the family of inner products of x(i) with e. -/
@[no_expose]
def finiteColumn (x : I → E) :
    AdjointableOperator B (CStarModule.Right.FiniteStandard B I) E := by
  let P := CStarModule.Right.FiniteStandard B I
  let C : ℝ := ∑ i, ‖x i‖
  let L₀ : P →ₗ[ℂ] E :=
    { toFun := fun b => ∑ i, x i <• b i
      map_add' := by
        intro b c
        calc
          (∑ i, x i <• (b + c) i) =
              ∑ i, (x i <• b i + x i <• c i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [WithCStarModule.add_apply, CStarModule.right_smul_add]
          _ = (∑ i, x i <• b i) + ∑ i, x i <• c i :=
            Finset.sum_add_distrib
      map_smul' := by
        intro c b
        simp only [RingHom.id_apply]
        calc
          (∑ i, x i <• (c • b) i) = ∑ i, c • (x i <• b i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [WithCStarModule.smul_apply, CStarModule.right_smul_smul]
          _ = c • ∑ i, x i <• b i := Finset.smul_sum.symm }
  have hL (b : P) : ‖L₀ b‖ ≤ C * ‖b‖ := by
    change ‖∑ i, x i <• b i‖ ≤ C * ‖b‖
    calc
      _ ≤ ∑ i, ‖x i <• b i‖ := _root_.norm_sum_le _ _
      _ ≤ ∑ i, ‖x i‖ * ‖b i‖ :=
        Finset.sum_le_sum fun i _ => CStarModule.norm_right_smul_le (x i) (b i)
      _ ≤ ∑ i, ‖x i‖ * ‖b‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (WithCStarModule.norm_apply_le_norm
            (A := Bᵐᵒᵖ) (E := fun _ : I => B) b i) (_root_.norm_nonneg (x i))
      _ = C * ‖b‖ := by rw [← Finset.sum_mul]
  let L : P →L[ℂ] E := L₀.mkContinuous C hL
  let R₀ : E →ₗ[ℂ] P :=
    { toFun := fun e =>
        (WithCStarModule.equiv Bᵐᵒᵖ (I → B)).symm
          (fun i => CStarModule.rightInner (B := B) (x i) e)
      map_add' := by
        intro e f
        apply (WithCStarModule.equiv Bᵐᵒᵖ (I → B)).injective
        ext i
        change CStarModule.rightInner (B := B) (x i) (e + f) =
          CStarModule.rightInner (B := B) (x i) e +
            CStarModule.rightInner (B := B) (x i) f
        exact CStarModule.rightInner_add_right (x i) e f
      map_smul' := by
        intro c e
        apply (WithCStarModule.equiv Bᵐᵒᵖ (I → B)).injective
        ext i
        change CStarModule.rightInner (B := B) (x i) (c • e) =
          c • CStarModule.rightInner (B := B) (x i) e
        exact CStarModule.rightInner_smul_right c (x i) e }
  have hR (e : E) : ‖R₀ e‖ ≤ (4 * C) * ‖e‖ := by
    calc
      _ ≤ ∑ i, ‖R₀ e i‖ :=
        WithCStarModule.pi_norm_le_sum_norm
          (A := Bᵐᵒᵖ) (E := fun _ : I => B) (R₀ e)
      _ = ∑ i, ‖CStarModule.rightInner (B := B) (x i) e‖ := by rfl
      _ ≤ ∑ i, 4 * ‖x i‖ * ‖e‖ :=
        Finset.sum_le_sum fun i _ => CStarModule.norm_rightInner_le_four_mul (x i) e
      _ = (4 * C) * ‖e‖ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  let R : E →L[ℂ] P := R₀.mkContinuous (4 * C) hR
  have hLval (b : P) : L b = ∑ i, x i <• b i := by rfl
  have hRval (e : E) (i : I) :
      R e i = CStarModule.rightInner (B := B) (x i) e := by rfl
  have hPinner (b c : P) :
      CStarModule.rightInner (B := B) b c = ∑ i, star (b i) * c i := by
    rw [CStarModule.rightInner, WithCStarModule.pi_inner]
    calc
      MulOpposite.unop (∑ i, inner Bᵐᵒᵖ (b i) (c i)) =
          ∑ i, MulOpposite.unop (inner Bᵐᵒᵖ (b i) (c i)) :=
        map_sum MulOpposite.opAddEquiv.symm _ _
      _ = ∑ i, star (b i) * c i := by rfl
  exact
    { toContinuousLinearMap := L
      adjoint := R
      isAdjointPair' := (isAdjointPair_iff_adjoint_inner L R).2 <| by
        intro b e
        let H : E →+ B :=
          { toFun := fun z => CStarModule.rightInner (B := B) z e
            map_zero' := CStarModule.rightInner_zero_left e
            map_add' := fun z w => CStarModule.rightInner_add_left z w e }
        calc
          CStarModule.rightInner (B := B) (L b) e =
              CStarModule.rightInner (B := B) (∑ i, x i <• b i) e :=
            congrArg (fun z : E => CStarModule.rightInner (B := B) z e) (hLval b)
          _ = ∑ i, CStarModule.rightInner (B := B) (x i <• b i) e :=
            map_sum H (fun i => x i <• b i) Finset.univ
          _ = ∑ i, star (b i) * CStarModule.rightInner (B := B) (x i) e := by
            simp only [CStarModule.rightInner_left_smul]
          _ = CStarModule.rightInner (B := B) b (R e) := by
            rw [hPinner]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hRval] }

/-- Let B be a possibly nonunital complex C-star algebra, E a normed right C-star module over B,
and I a finite index type, possibly empty. The column value at a coefficient vector b is the
finite sum of x(i)b(i). -/
@[simp]
theorem finiteColumn_apply (x : I → E)
    (b : CStarModule.Right.FiniteStandard B I) :
    finiteColumn (B := B) x b = ∑ i, x i <• b i := by
  rfl

/-- Let B be a possibly nonunital complex C-star algebra, E a normed right C-star module over B,
and I a finite index type, possibly empty. The i-th coordinate of the adjoint column map is
the B-valued inner product of x(i) with the input vector. -/
@[simp]
theorem finiteColumn_adjoint_apply (x : I → E) (e : E) (i : I) :
    (finiteColumn (B := B) x).adjoint e i =
      CStarModule.rightInner (B := B) (x i) e := by
  rfl

/-- Let B be a possibly nonunital complex C-star algebra, E a normed right C-star module over B,
and I a finite index type, possibly empty. The matrix representation of the Gram matrix of x
is the adjoint column map composed with the column map. -/
theorem rightMatrixHom_gram (x : I → E) :
    rightMatrixHom
        (CStarMatrix.ofMatrix fun i j =>
          CStarModule.rightInner (B := B) (x i) (x j)) =
      (finiteColumn (B := B) x).adjointOperator.comp (finiteColumn (B := B) x) := by
  apply AdjointableOperator.ext
  intro b
  apply (WithCStarModule.equiv Bᵐᵒᵖ (I → B)).injective
  ext i
  change rightMatrixHom
      (CStarMatrix.ofMatrix fun k j =>
        CStarModule.rightInner (B := B) (x k) (x j)) b i =
    (finiteColumn (B := B) x).adjoint
      (finiteColumn (B := B) x b) i
  simp only [rightMatrixHom_apply, rightMatrix_apply,
    finiteColumn_adjoint_apply, finiteColumn_apply]
  let H : E →+ B :=
    { toFun := fun e => CStarModule.rightInner (B := B) (x i) e
      map_zero' := CStarModule.rightInner_zero_right (x i)
      map_add' := fun e f => CStarModule.rightInner_add_right (x i) e f }
  have hsum : (∑ j, CStarModule.rightInner (B := B) (x i) (x j) * b j) =
      CStarModule.rightInner (B := B) (x i) (∑ j, x j <• b j) := by
    simpa only [H, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      CStarModule.rightInner_right_smul] using
      (map_sum H (fun j => x j <• b j) Finset.univ).symm
  calc
    (∑ j, CStarMatrix.ofMatrix (fun k j =>
        CStarModule.rightInner (B := B) (x k) (x j)) i j * b j) =
        ∑ j, CStarModule.rightInner (B := B) (x i) (x j) * b j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact congrArg (fun q : B => q * b j)
        (congrFun (CStarMatrix.ofMatrix_apply
          (M := fun k j => CStarModule.rightInner (B := B) (x k) (x j)) (i := i)) j)
    _ = CStarModule.rightInner (B := B) (x i) (∑ j, x j <• b j) := hsum

/-- Let B be a possibly nonunital complex C-star algebra, E a normed right C-star module over B,
and I a finite index type, possibly empty. If E is complete, the coefficient Gram matrix of
any finite vector family in E is nonnegative in the C-star matrix order. -/
theorem gramMatrix_nonneg [CompleteSpace E] (x : I → E) :
    (letI : PartialOrder B := CStarAlgebra.spectralOrder B
     letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
     @LE.le (CStarMatrix I I B)
       (CStarAlgebra.spectralOrder (CStarMatrix I I B)).toLE
       0 (CStarMatrix.ofMatrix fun i j =>
         CStarModule.rightInner (B := B) (x i) (x j))) := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let P := CStarModule.Right.FiniteStandard B I
  let : PartialOrder (CStarMatrix I I B) :=
    CStarAlgebra.spectralOrder (CStarMatrix I I B)
  let : StarOrderedRing (CStarMatrix I I B) :=
    CStarAlgebra.spectralOrderedRing (CStarMatrix I I B)
  let : PartialOrder (End B P) := CStarAlgebra.spectralOrder (End B P)
  let : StarOrderedRing (End B P) := CStarAlgebra.spectralOrderedRing (End B P)
  have hpos : (0 : End B P) ≤ rightMatrixHom
      (CStarMatrix.ofMatrix fun i j =>
        CStarModule.rightInner (B := B) (x i) (x j)) := by
    rw [rightMatrixHom_gram]
    exact adjoint_comp_self_nonneg (finiteColumn (B := B) x)
  exact (NonUnitalStarAlgHom.map_le_map_iff
    (rightMatrixHom (B := B) (ι := I)) rightMatrixHom_injective).mp
      (by simpa only [map_zero] using hpos)

end CStarModule.AdjointableOperator
