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

public import MathlibExt.Algebra.Homology.MixedComplex.LodayBCTotalComponents
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.MixedBicomplex
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.NormNum

/-!
# Integer matrix coordinates of signed and unsigned cyclic columns

The algebra is `M₂(ℤ)` with matrix units `E₀₁,E₁₀`, whose products differ.
For the degree-two word `2I ⊗ (E₀₁,E₁₀)`, the coefficient-entry-01 and
tail-entry-10 probe evaluates the Hochschild boundary to `2`. The canonical
stored column-one differential has value `-2`, while the unsigned column has
value `2` under its cell coordinates.

The column isomorphism satisfies the degree-three to degree-two chain square,
so the comparison retains the complete signed-column coordinate law.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Preadditive
open ModuleCat.Algebra.Hochschild.NonUnital
open scoped TensorProduct

namespace MathlibExtTest.LodayBCIntegerMatrices

/--
The algebra of two-by-two matrices over `ℤ`.
-/
abbrev A := Matrix (Fin 2) (Fin 2) ℤ
/--
The Connes mixed-complex model for the integer matrix algebra.
-/
abbrev M : MixedComplex (ModuleCat ℤ) := connesMixedComplexModel ℤ A

/--
The matrix unit `E₀₁` over `ℤ`.
-/
def e01 : A := Matrix.single 0 1 1
/--
The matrix unit `E₁₀` over `ℤ`.
-/
def e10 : A := Matrix.single 1 0 1

/--
The `ℤ`-linear functional reading matrix entry `(i,j)`.
-/
def entry (i j : Fin 2) : A →ₗ[ℤ] ℤ where
  toFun a := a i j
  map_add' a b := rfl
  map_smul' a b := rfl

/--
The linear functional reading entry `(1,0)` of the single matrix in a
tensor-power-one tail.
-/
def tailEntry10 : TensorPower ℤ 1 A →ₗ[ℤ] ℤ :=
  (entry 1 0).comp
    (PiTensorProduct.subsingletonEquiv (R := ℤ) (s := fun _ : Fin 1 => A) (0 : Fin 1)).toLinearMap

/--
The tensor functional multiplying entry `(0,1)` of the coefficient matrix
by entry `(1,0)` of the tail matrix.
-/
def probe : A ⊗[ℤ] TensorPower ℤ 1 A →ₗ[ℤ] ℤ :=
  (TensorProduct.lid ℤ ℤ).toLinearMap.comp (TensorProduct.map (entry 0 1) tailEntry10)

/--
The probe on `a ⊗ b` in tensor degree one is `a₀₁ * b₁₀`.
-/
@[simp]
theorem probe_tmul_tprod (a : A) (b : Fin 1 → A) :
    probe (a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ b) = a 0 1 * (b 0) 1 0 := by
  change (TensorProduct.lid ℤ ℤ)
      ((TensorProduct.map (entry 0 1) tailEntry10) (a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ b)) = _
  rw [TensorProduct.map_tmul]
  change a 0 1 * ((PiTensorProduct.subsingletonEquiv
    (R := ℤ) (s := fun _ : Fin 1 => A) (0 : Fin 1)) (PiTensorProduct.tprod ℤ b)) 1 0 = _
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod]

/--
The Hochschild word with coefficient `2I` and ordered tail factors
`E₀₁,E₁₀`.
-/
def word : A ⊗[ℤ] TensorPower ℤ 2 A :=
  (2 • (1 : A)) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (Fin.cons e01 (fun _ : Fin 1 => e10))

/--
The `(0,0)` entries of `E₀₁E₁₀` and `E₁₀E₀₁` are one and zero,
respectively.
-/
theorem ordered_multiplication : (e01 * e10) 0 0 = 1 ∧ (e10 * e01) 0 0 = 0 := by
  norm_num [e01, e10, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

/--
The ordered probe evaluates the Hochschild degree-two boundary of the
specified word to `2`.
-/
theorem b_two_value : probe (((bComplex ℤ A).d 2 1).hom word) = 2 := by
  unfold word
  rw [bComplex_d ℤ A 1, ModuleCat.hom_sum, LinearMap.sum_apply, Fin.sum_univ_succ,
    Fin.sum_univ_two]
  have hmid : (0 : Fin 1).castSucc.succ = (0 : Fin 2).succ := by apply Fin.ext; rfl
  simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_one, pow_two, one_smul, neg_one_smul]
  simp only [LinearMap.smul_apply, zero_add, pow_one, Fin.val_one, one_add_one_eq_two,
    pow_two, neg_one_smul, one_smul]
  simp only [LinearMap.neg_apply, LinearMap.smul_apply, neg_mul_neg, one_mul, one_smul]
  erw [← hmid, regularFace_first_tprod, regularFace_inner_tprod, regularFace_last_tprod]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, pow_one, pow_two, one_smul,
    neg_one_zsmul, map_add, map_neg, probe_tmul_tprod]
  norm_num [word, e01, e10, Matrix.mul_apply, Fin.sum_univ_two,
    ModuleCat.Algebra.Hochschild.hochschildDropFirst,
    ModuleCat.Algebra.Hochschild.hochschildDropLast,
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, Matrix.single]
  rfl

private theorem canonical_column_one_linear :
    ((M.connesBicomplexCellIso 1 3 (by omega)).inv ≫
      (M.connesBicomplex.X 1).d 3 2 ≫ (M.connesBicomplexCellIso 1 2 (by omega)).hom).hom =
      -((bComplex ℤ A).d 2 1).hom := by
  erw [M.connesDoubleData.vertical_eq 1 2 (by omega)]
  dsimp only [MixedComplex.connesDoubleData] at ⊢
  simp only [CategoryTheory.Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    CategoryTheory.Category.comp_id, eqToHom_refl, CategoryTheory.Category.id_comp,
    ModuleCat.hom_zsmul, pow_one, neg_one_smul]
  rw [ModuleCat.hom_neg]
  congr 1

/--
Under the canonical cell coordinates, the column-one differential from
chain degree three to two evaluates on the specified word to `-2`.
-/
theorem canonical_column_one_degree_two_value :
    probe (((M.connesBicomplexCellIso 1 3 (by omega)).inv ≫
      (M.connesBicomplex.X 1).d 3 2 ≫ (M.connesBicomplexCellIso 1 2 (by omega)).hom).hom word) = -2 := by
  have h : ((M.connesBicomplexCellIso 1 3 (by omega)).inv ≫
      (M.connesBicomplex.X 1).d 3 2 ≫ (M.connesBicomplexCellIso 1 2 (by omega)).hom).hom word =
      -(((bComplex ℤ A).d 2 1).hom word) :=
    LinearMap.congr_fun canonical_column_one_linear word
  exact (congrArg (fun y : A ⊗[ℤ] TensorPower ℤ 1 A => probe y) h).trans
    ((probe.map_neg _).trans (congrArg Neg.neg b_two_value))

private theorem printed_column_one_map :
    (M.lodayBCCellIso 1 3 (by omega)).inv ≫
      (M.lodayBCColumn 1).d 3 2 ≫ (M.lodayBCCellIso 1 2 (by omega)).hom =
      M.underlying.d 2 1 := by
  have h := M.lodayBC_vertical_coordinate 1 1
  simpa only [eqToHom_refl, CategoryTheory.Category.id_comp,
    CategoryTheory.Category.comp_id] using h

/--
Under the unsigned column cell coordinates, the same vertical differential
and word have probe value `2`.
-/
theorem printed_column_one_degree_two_value :
    probe (((M.lodayBCCellIso 1 3 (by omega)).inv ≫
      (M.lodayBCColumn 1).d 3 2 ≫ (M.lodayBCCellIso 1 2 (by omega)).hom).hom word) = 2 := by
  have h : ((M.lodayBCCellIso 1 3 (by omega)).inv ≫
      (M.lodayBCColumn 1).d 3 2 ≫ (M.lodayBCCellIso 1 2 (by omega)).hom).hom =
      ((bComplex ℤ A).d 2 1).hom :=
    congrArg (fun f : M.underlying.X 2 ⟶ M.underlying.X 1 => f.hom) printed_column_one_map
  rw [h]
  exact b_two_value

/--
The two integer values `2` and `-2` are unequal.
-/
theorem positive_not_negative : (2 : ℤ) ≠ -2 := by norm_num

/--
In column one, the unsigned-to-canonical column isomorphism commutes with
the vertical boundary from degree three to degree two.
-/
example :
    (M.lodayBCColumnIso 1).hom.f 3 ≫ (M.connesBicomplex.X 1).d 3 2 =
      (M.lodayBCColumn 1).d 3 2 ≫ (M.lodayBCColumnIso 1).hom.f 2 :=
  (M.lodayBCColumnIso 1).hom.comm 3 2

end MathlibExtTest.LodayBCIntegerMatrices
