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

public import MathlibExt.Analysis.CStarAlgebra.Module.Matrix
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Standard.FiniteCoordinateAdjoints

/-!
# Compact matrix actions on finite standard modules

For a nonunital C-star algebra `B` and finite index type `I`, a matrix `M ∈ M_I(B)` acts on the
finite standard right module by `(M x)_i = ∑ j, M_ij * x_j`. This is an adjointable
module-compact operator. The resulting nonunital star homomorphism has target `K_B(B^I)`.

The finite standard-module norm is its coefficient inner-product norm, and the matrix entries
act by left multiplication in the stated order. The construction permits empty indices and zero
coefficients; it requires no unit-valued coordinate vector.
-/

@[expose] public section

noncomputable section

namespace CStarModule.AdjointableOperator

open CStarModule.Right
open scoped BigOperators

universe uB uι

variable {B : Type uB} [NonUnitalCStarAlgebra B] {ι : Type uι} [Fintype ι]

/-- **Compact finite-matrix representation.** For a nonunital complex C-star algebra `B` and
finite index type `I`, the nonunital star homomorphism `M_I(B) → K_B(FiniteStandard B I)` is
the column action `(M x)_i = ∑ j, M_ij*x_j`. -/
noncomputable def rightMatrixCompactHom :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    CStarMatrix ι ι B →⋆ₙₐ[ℂ]
      compactStarSubalgebra (B := B) (E := FiniteStandard B ι) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  let E := FiniteStandard B ι
  change CStarMatrix ι ι B →⋆ₙₐ[ℂ] compactStarSubalgebra (B := B) (E := E)
  refine NonUnitalStarAlgHom.codRestrict
    (rightMatrixHom (B := B) (ι := ι))
    (compactStarSubalgebra (B := B) (E := E)) ?_
  intro M
  change (rightMatrixHom (B := B) (ι := ι) M : End B E) ∈
    compactSubmodule (B := B) (E := E) (F := E)
  classical
  let S (i : ι) : AdjointableOperator B B E :=
    finiteSingleAdjointable (B := B) (I := ι) i
  let P (i : ι) : AdjointableOperator B E B := (S i).adjointOperator
  have hS (i : ι) (b : B) : S i b = finiteSingle i b :=
    congrArg (fun L : B →L[ℂ] E => L b)
      (finiteSingleAdjointable_toContinuousLinearMap (B := B) (I := ι) i)
  have hP (i : ι) (y : E) : P i y = finiteCoord i y :=
    congrArg (fun L : E →L[ℂ] B => L y)
      (finiteSingleAdjointable_adjoint (B := B) (I := ι) i)
  let R : End B E := rightMatrixHom (B := B) (ι := ι) M
  have hR (y : E) : R y = rightMatrix (B := B) M y :=
    rightMatrixHom_apply M y
  have hBlock (i j : ι) :
      (P i).comp (R.comp (S j)) = leftMul (B := B) (M i j) := by
    apply AdjointableOperator.ext
    intro b
    calc
      ((P i).comp (R.comp (S j))) b =
          finiteCoord i (rightMatrix (B := B) M (finiteSingle j b)) := by
        rw [comp_apply, comp_apply, hP, hS, hR]
      _ = M i j * b :=
        (finiteCoord_apply i _).trans (rightMatrix_finiteSingle M j b i)
      _ = leftMul (B := B) (M i j) b := (leftMul_apply _ _).symm
  have hReconstruct (y : E) : ∑ i, S i (P i y) = y := by
    calc
      ∑ i, S i (P i y) = ∑ i, finiteSingle i (y i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hS, hP, finiteCoord_apply]
      _ = y := finite_sum_single y
  let block (i j : ι) : End B E :=
    (S i).comp ((leftMul (B := B) (M i j)).comp (P j))
  have hEval (f : ι → End B E) (y : E) :
      (∑ i, f i) y = ∑ i, f i y := by
    let ev : End B E →+ E :=
      { toFun := fun T => T y
        map_zero' := zero_apply y
        map_add' := fun T U => add_apply T U y }
    exact _root_.map_sum ev f Finset.univ
  have hMatrix : R = ∑ i, ∑ j, block i j := by
    apply AdjointableOperator.ext
    intro y
    calc
      R y = ∑ i, S i (P i (R y)) := (hReconstruct (R y)).symm
      _ = ∑ i, ∑ j, S i (P i (R (S j (P j y)))) := by
        apply Finset.sum_congr rfl
        intro i _
        let U : End B E := (S i).comp ((P i).comp R)
        have hInput : U y = U (∑ j, S j (P j y)) :=
          congrArg U (hReconstruct y).symm
        calc
          S i (P i (R y)) = U (∑ j, S j (P j y)) := hInput
          _ = ∑ j, U (S j (P j y)) :=
            _root_.map_sum U.toContinuousLinearMap
              (fun j => S j (P j y)) Finset.univ
          _ = ∑ j, S i (P i (R (S j (P j y)))) := rfl
      _ = ∑ i, ∑ j, S i (leftMul (B := B) (M i j) (P j y)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have h := congrArg (fun T : End B B => T (P j y)) (hBlock i j)
        change P i (R (S j (P j y))) =
          leftMul (B := B) (M i j) (P j y) at h
        exact congrArg (S i) h
      _ = (∑ i, ∑ j, block i j) y := by
        symm
        calc
          (∑ i, ∑ j, block i j) y = ∑ i, (∑ j, block i j) y :=
            hEval (fun i => ∑ j, block i j) y
          _ = ∑ i, ∑ j, block i j y := by
            apply Finset.sum_congr rfl
            intro i _
            exact hEval (fun j => block i j) y
          _ = ∑ i, ∑ j, S i (leftMul (B := B) (M i j) (P j y)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rfl
  have hCompact (i j : ι) :
      block i j ∈ compactSubmodule (B := B) (E := E) (F := E) := by
    have hLP : (leftMul (B := B) (M i j)).comp (P j) ∈
        compactSubmodule (B := B) (E := E) (F := B) :=
      comp_mem_compact_left (B := B) (E := E) (F := B) (G := B)
        (leftMul_mem_compact (B := B) (M i j)) (P j)
    exact comp_mem_compact_right (B := B) (E := E) (F := B) (G := E) (S i) hLP
  have hSum : (∑ i, ∑ j, block i j) ∈
      compactSubmodule (B := B) (E := E) (F := E) :=
    (compactSubmodule (B := B) (E := E) (F := E)).sum_mem fun i _ =>
      (compactSubmodule (B := B) (E := E) (F := E)).sum_mem fun j _ => hCompact i j
  change R ∈ compactSubmodule (B := B) (E := E) (F := E)
  rw [hMatrix]
  exact hSum

/-- **Endomorphism underlying the compact matrix action.** For a nonunital complex C-star algebra
`B` and finite index type `I`, the compact-ideal inclusion of `rightMatrixCompactHom M` equals
`rightMatrixHom M`, the finite standard-module column operator. -/
@[simp]
theorem rightMatrixCompactHom_coe (M : CStarMatrix ι ι B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (rightMatrixCompactHom (B := B) (ι := ι) M : End B (FiniteStandard B ι)) =
      rightMatrixHom M := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- **Coordinate formula for a compact matrix action.** For nonunital complex C-star `B`, finite
`I`, `M : CStarMatrix I I B`, `x : FiniteStandard B I` and `i : I`, `(rightMatrixCompactHom M)
x i = ∑ j, M i j * x j`. -/
theorem rightMatrixCompactHom_apply (M : CStarMatrix ι ι B)
    (x : FiniteStandard B ι) (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (rightMatrixCompactHom (B := B) (ι := ι) M : End B (FiniteStandard B ι)) x i =
      ∑ j, M i j * x j := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rw [rightMatrixCompactHom_coe, rightMatrixHom_apply]
  exact rightMatrix_apply M x i

end CStarModule.AdjointableOperator

end

end
