/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.Hochschild.Normalized
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.MixedBicomplex

/-!
# Normalized Connes boundary and mixed bicomplex

For a commutative ring `k` and a unital ring `A` with compatible
central ground action, let `Ā=A/(k·1)` be the ground-module quotient.
The normalized regular chain level is `C̄_n=A ⊗[k] Ā^⊗n`, and
projection `p_n` keeps the coefficient while quotienting each tail
factor. The composite `p_(n+1)B_n` annihilates unit degeneracies and
therefore defines `B̄_n : C̄_n → C̄_(n+1)`.

On representatives, `B̄` is computed from unit insertion after the
full-word norm. Its cyclic sum has sign `(-1)^(nj)` and forward
cyclic order in the quotient tail. In low degrees,
`B̄₀(a)=1 ⊗ ā` and
`B̄₁(a ⊗ b̄)=1 ⊗ [ā,b̄]-1 ⊗ [b̄,ā]`.
The equations `B̄²=0` and `b̄B̄+B̄b̄=0` give the normalized mixed
complex and its first-quadrant bicomplex. The canonical homology
comparison with cyclic homology is natural for nonunital algebra
maps that explicitly preserve `1`.

## References

* J.-L. Loday, *Cyclic Homology*, second edition, 2.1.9–2.1.11, for normalization and the Connes mixed complex.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits CategoryTheory.Preadditive AlgebraicTopology
open scoped TensorProduct BigOperators

universe u v w z t s

namespace ModuleCat.Algebra.Hochschild.NonUnital

section GroundQuotient

variable (k : Type u) (A : Type v) [CommRing k] [AddCommGroup A] [Module k A] [One A]

/-- Let `k` be a commutative ring and `A` a `k`-module with
distinguished element `1`. Put `Ā=A/(k·1)`, `q : A → Ā`,
`C_n=A ⊗[k] A^⊗n`, and `C̄_n=A ⊗[k] Ā^⊗n`.
Let `p_n=id_A ⊗ q^⊗n`, `s_n` insert `1` as the coefficient
and move all prior factors to the tail, and `N_n` be the signed
cyclic norm on the full `n+1` factors. For `x : C_n`, projection after insertion is
`p_(n+1)(s_n(x))=1 ⊗ q^⊗(n+1)(consEquiv(x))`. -/
theorem normalizationLevelMap_consInsert (n : ℕ) (x : A ⊗[k] TensorPower k n A) :
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consInsert k A 1 n x) =
      1 ⊗ₜ[k] TensorPower.quotientMap
        (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)
        (TensorPower.consEquiv k A n x) := by
  let L : A ⊗[k] TensorPower k n A →ₗ[k]
      A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom.comp
      (TensorPower.consInsert k A 1 n)
  let R : A ⊗[k] TensorPower k n A →ₗ[k]
      A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    (TensorProduct.mk k A
      (TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A)) 1).comp
        ((TensorPower.quotientMap
          (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)).comp
            (TensorPower.consEquiv k A n).toLinearMap)
  have h : L = R := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consInsert k A 1 n (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      1 ⊗ₜ[k] TensorPower.quotientMap
        (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)
        (TensorPower.consEquiv k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    rw [TensorPower.consInsert_tmul, ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod,
      TensorPower.consEquiv_tmul, TensorPower.quotientMap_tprod]
  exact DFunLike.congr_fun h x

/-- Let `k` be a commutative ring and `A` a `k`-module with
distinguished element `1`. Put `Ā=A/(k·1)`, `q : A → Ā`,
`C_n=A ⊗[k] A^⊗n`, and `C̄_n=A ⊗[k] Ā^⊗n`.
Let `p_n=id_A ⊗ q^⊗n`, `s_n` insert `1` as the coefficient
and move all prior factors to the tail, and `N_n` be the signed
cyclic norm on the full `n+1` factors. For `x : C_n`, the inserted full norm projects to
`1 ⊗ N_n^Ā(q^⊗(n+1)(consEquiv(x)))`, where `N_n^Ā`
acts on the complete tensor power `Ā^⊗(n+1)`. -/
theorem normalizationLevelMap_consInsert_norm (n : ℕ) (x : A ⊗[k] TensorPower k n A) :
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consInsert k A 1 n (TensorPower.consNorm k A n x)) =
      1 ⊗ₜ[k] TensorPower.norm k (ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
        (TensorPower.quotientMap (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)
          (TensorPower.consEquiv k A n x)) := by
  rw [normalizationLevelMap_consInsert, TensorPower.consNorm_coordinates]
  exact congrArg (fun a => (1 : A) ⊗ₜ[k] a)
    (TensorPower.norm_natural (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ n
      (TensorPower.consEquiv k A n x))

/-- Let `k` be a commutative ring and `A` a `k`-module with
distinguished element `1`. Put `Ā=A/(k·1)`, `q : A → Ā`,
`C_n=A ⊗[k] A^⊗n`, and `C̄_n=A ⊗[k] Ā^⊗n`.
Let `p_n=id_A ⊗ q^⊗n`, `s_n` insert `1` as the coefficient
and move all prior factors to the tail, and `N_n` be the signed
cyclic norm on the full `n+1` factors. Rotating an inserted `1` puts it into a quotient-tail
position, so `p_(n+1)(t_(n+1)(s_n(x)))=0`. -/
theorem normalizationLevelMap_cyclic_consInsert (n : ℕ)
    (x : A ⊗[k] TensorPower k n A) :
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consCyclicOperator k A (n + 1) (TensorPower.consInsert k A 1 n x)) =
      0 := by
  let L : A ⊗[k] TensorPower k n A →ₗ[k]
      A ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) :=
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom.comp
      ((TensorPower.consCyclicOperator k A (n + 1)).comp (TensorPower.consInsert k A 1 n))
  have h : L = 0 := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consCyclicOperator k A (n + 1)
          (TensorPower.consInsert k A 1 n (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = 0
    erw [TensorPower.consInsert_tmul]
    let b : Fin (n + 2) → A := Fin.cons 1 (Fin.cons m a)
    change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consCyclicOperator k A (n + 1)
          (b 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail b))) = 0
    rw [TensorPower.consCyclicOperator_tmul, map_smul]
    have hb : (fun i : Fin (n + 1) => b i.castSucc) 0 = 1 := rfl
    rw [ModuleCat.Algebra.Hochschild.normalizationLevelMap_unit_factor
      k A A (n + 1) _ _ 0 hb, smul_zero]
  exact DFunLike.congr_fun h x

/-- Let `k` be a commutative ring and `A` a `k`-module with
distinguished element `1`. Put `Ā=A/(k·1)`, `q : A → Ā`,
`C_n=A ⊗[k] A^⊗n`, and `C̄_n=A ⊗[k] Ā^⊗n`.
Let `p_n=id_A ⊗ q^⊗n`, `s_n` insert `1` as the coefficient
and move all prior factors to the tail, and `N_n` be the signed
cyclic norm on the full `n+1` factors. If a tail factor `a_i` of `m ⊗ tprod(a)` equals `1`,
then projection of its full norm followed by insertion is zero. -/
theorem normalizationLevelMap_consInsert_norm_unit_factor (n : ℕ) (m : A)
    (a : Fin n → A) (i : Fin n) (hi : a i = 1) :
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consInsert k A 1 n
          (TensorPower.consNorm k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = 0 := by
  let S := ModuleCat.Algebra.Hochschild.unitSubmodule k A
  have hx : TensorPower.quotientMap S (n + 1)
      (TensorPower.consEquiv k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = 0 := by
    rw [TensorPower.consEquiv_tmul]
    have hmem : PiTensorProduct.tprod k (Fin.cons m a) ∈
        TensorPower.quotientRelations S (n + 1) :=
      Submodule.subset_span ⟨Fin.cons m a,
        ⟨i.succ, by
          rw [Fin.cons_succ, hi]
          exact ModuleCat.Algebra.Hochschild.one_mem_unitSubmodule k A⟩, rfl⟩
    rw [← TensorPower.quotientMap_ker] at hmem
    exact hmem
  rw [normalizationLevelMap_consInsert_norm]
  change (1 : A) ⊗ₜ[k] TensorPower.norm k
    (ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
      (TensorPower.quotientMap S (n + 1)
        (TensorPower.consEquiv k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = 0
  rw [hx, map_zero, TensorProduct.tmul_zero]

end GroundQuotient

section UnitalAlgebra

variable (k : Type u) (A : Type v) [CommRing k] [Ring A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The normalized regular Hochschild chain complex has
levels `C̄_n` and the induced boundary `b̄`. -/
def normalizedBComplex : ChainComplex (ModuleCat.{max u v} k) ℕ := by
  letI := regularAlgebra k A
  exact ModuleCat.Algebra.Hochschild.normalizedChainComplex k A A

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. Its degree-`n` object is the normalized chain level
`A ⊗[k] Ā^⊗n`. -/
@[simp]
theorem normalizedBComplex_X (n : ℕ) :
    (normalizedBComplex k A).X n =
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The bridge to the unital coefficient Hochschild complex
has identity component on the regular chain level `C_n` in every
 degree `n`. -/
theorem regularUnitalComplexIso_hom_f (n : ℕ) :
    letI := regularAlgebra k A
    (regularUnitalComplexIso k A).hom.f n = 𝟙 (chainLevel k A A n) := by
  letI := regularAlgebra k A
  change (complexIsoUnital (k := k) (A := A) (M := A)).hom.f n = 𝟙 _
  exact complexIsoUnital_hom_f n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The factorwise quotient maps form the chain projection
`p : C_*(A) → C̄_*(A)`. -/
def normalizedProjection : bComplex k A ⟶ normalizedBComplex k A := by
  letI := regularAlgebra k A
  exact (regularUnitalComplexIso k A).hom ≫
    ModuleCat.Algebra.Hochschild.normalizationProjection k A A

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The degree-`n` projection is precisely `p_n`, identity
on the coefficient and quotient on every tail factor. -/
@[simp]
theorem normalizedProjection_f (n : ℕ) :
    (normalizedProjection k A).f n =
      ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n := by
  letI := regularAlgebra k A
  change (regularUnitalComplexIso k A).hom.f n ≫
      (ModuleCat.Algebra.Hochschild.normalizationProjection k A A).f n = _
  let e : chainLevel k A A n ⟶ chainLevel k A A n :=
    (regularUnitalComplexIso k A).hom.f n
  let p : chainLevel k A A n ⟶ ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n :=
    (ModuleCat.Algebra.Hochschild.normalizationProjection k A A).f n
  have he : e = 𝟙 (chainLevel k A A n) := regularUnitalComplexIso_hom_f k A n
  have hp : p = ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n :=
    ModuleCat.Algebra.Hochschild.normalizationProjection_f k A A n
  change e ≫ p = ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n
  exact (congrArg (fun f : chainLevel k A A n ⟶ chainLevel k A A n => f ≫ p) he).trans
    ((Category.id_comp p).trans hp)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. Every `p_n` is epi, including degree zero. -/
instance normalizedProjection_f_epi (n : ℕ) : Epi ((normalizedProjection k A).f n) := by
  erw [normalizedProjection_f]
  exact ModuleCat.Algebra.Hochschild.normalizationLevelMap_epi k A A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The normalized chain projection `p` is a quasi-isomorphism. -/
instance normalizedProjection_quasiIso : _root_.QuasiIso (normalizedProjection k A) := by
  letI := regularAlgebra k A
  change _root_.QuasiIso ((regularUnitalComplexIso k A).hom ≫
    ModuleCat.Algebra.Hochschild.normalizationProjection k A A)
  infer_instance

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. For `x : C_n`, the projected Connes operator satisfies
`p_(n+1)(B_n(x))=p_(n+1)(s_n(N_n(x)))`, because the rotated
insertion term vanishes after quotienting. -/
theorem connesBoundary_normalization (n : ℕ) (x : chainLevel k A A n) :
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        ((connesBoundary k A n).hom x) =
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consInsert k A 1 n (TensorPower.consNorm k A n x)) := by
  rw [connesBoundary, connesBoundaryWith_apply, map_sub]
  change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
      (TensorPower.consInsert k A 1 n (TensorPower.consNorm k A n x)) -
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
      (TensorPower.consCyclicOperator k A (n + 1)
        (TensorPower.consInsert k A 1 n (TensorPower.consNorm k A n x))) = _
  rw [normalizationLevelMap_cyclic_consInsert, sub_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. If a representative tail factor `a_i` equals `1`,
then `p_(n+1)(B_n(m ⊗ tprod(a)))=0`. -/
theorem connesBoundary_normalization_unit_factor (n : ℕ) (m : A) (a : Fin n → A)
    (i : Fin n) (hi : a i = 1) :
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        ((connesBoundary k A n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = 0 := by
  rw [connesBoundary_normalization]
  exact normalizationLevelMap_consInsert_norm_unit_factor k A n m a i hi

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. Under the coefficient-bar identification with `C_n`,
`B_n` followed by `p_(n+1)` annihilates all degenerate simplices
obtained by inserting a unit tail factor. -/
theorem connesBoundary_normalization_degeneracies (n : ℕ) :
    letI := regularAlgebra k A
    DoldKan.DegeneraciesVanish
      ((ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A A n).hom ≫
        connesBoundary k A n ≫
          ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)) := by
  letI := regularAlgebra k A
  cases n with
  | zero =>
      exact (DoldKan.degeneraciesVanish_zero_iff_true _).mpr True.intro
  | succ n =>
      apply (DoldKan.degeneraciesVanish_succ_iff _).mpr
      intro i
      let f : chainLevel k A A (n + 1) ⟶
          ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A (n + 2) :=
        connesBoundary k A (n + 1) ≫
          ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 2)
      have hf : ModuleCat.Algebra.Hochschild.degeneracy k A A n i ≫ f = 0 := by
        apply ModuleCat.hom_ext
        apply ModuleCat.Algebra.Hochschild.tensorPower_ext
        intro m a
        change (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 2)).hom
            ((connesBoundary k A (n + 1)).hom
              ((ModuleCat.Algebra.Hochschild.degeneracy k A A n i).hom
                (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = 0
        rw [ModuleCat.Algebra.Hochschild.degeneracy_tprod]
        exact connesBoundary_normalization_unit_factor k A (n + 1) m
          (ModuleCat.Algebra.Hochschild.hochschildInsertOne i a) i
            (by simp [ModuleCat.Algebra.Hochschild.hochschildInsertOne])
      apply (cancel_epi (ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A A n).inv).1
      change (ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A A n).inv ≫
          ((ModuleCat.Algebra.Hochschild.coefficientBar k A A).σ i ≫
            ((ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A A (n + 1)).hom ≫ f)) =
        (ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A A n).inv ≫ 0
      calc
        _ = ModuleCat.Algebra.Hochschild.degeneracy k A A n i ≫ f := by
          simp only [ModuleCat.Algebra.Hochschild.degeneracy, Category.assoc]
        _ = 0 := hf
        _ = _ := Limits.comp_zero.symm

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The degeneracy-annihilating composite `p_(n+1)B_n`
descends uniquely to the degree-one map
`B̄_n : C̄_n → C̄_(n+1)`. -/
def normalizedBoundary (n : ℕ) :
    (normalizedBComplex k A).X n ⟶ (normalizedBComplex k A).X (n + 1) := by
  letI := regularAlgebra k A
  exact ModuleCat.Algebra.Hochschild.normalizationDescAt k A A n
    (connesBoundary k A n ≫
      ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1))
    (connesBoundary_normalization_degeneracies k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The descent is characterized by the projection square
`p_n ≫ B̄_n = B_n ≫ p_(n+1)`. -/
@[reassoc]
theorem normalizedProjection_boundary (n : ℕ) :
    (normalizedProjection k A).f n ≫ normalizedBoundary k A n =
      connesBoundary k A n ≫ (normalizedProjection k A).f (n + 1) := by
  letI := regularAlgebra k A
  rw [normalizedProjection_f, normalizedProjection_f]
  exact ModuleCat.Algebra.Hochschild.normalizationLevelMap_descAt k A A n
    (connesBoundary k A n ≫
      ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1))
    (connesBoundary_normalization_degeneracies k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. For `m : A` and a word `a : Fin n → A`,
`B̄_n(m ⊗ tprod(q∘a))=p_(n+1)(B_n(m ⊗ tprod(a)))`. -/
theorem normalizedBoundary_tmul_tprod (n : ℕ) (m : A) (a : Fin n → A) :
    (normalizedBoundary k A n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ (a i))) =
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        ((connesBoundary k A n).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) := by
  letI := regularAlgebra k A
  have h := ModuleCat.Algebra.Hochschild.normalizationDescAt_tmul_tprod k A A n
    (connesBoundary k A n ≫
      ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1))
    (connesBoundary_normalization_degeneracies k A n) m a
  exact h

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The same representative value is
`p_(n+1)(s_n(N_n(m ⊗ tprod(a))))`, using the norm on full
unnormalized words before quotienting. -/
theorem normalizedBoundary_eq_projected_consInsert_norm (n : ℕ) (m : A) (a : Fin n → A) :
    (normalizedBoundary k A n).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ (a i))) =
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A (n + 1)).hom
        (TensorPower.consInsert k A 1 n
          (TensorPower.consNorm k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))) :=
  (normalizedBoundary_tmul_tprod k A n m a).trans
    (connesBoundary_normalization k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. For `a : Fin(n+1) → A`, with `ρ=finRotate(n+1)`,
`B̄_n(a₀ ⊗ [a₁,…,a_n]) =
∑_(j=0)^n (-1)^(nj) • (1 ⊗ tprod(i ↦ q(a(ρ^j(i)))))`.
The quotient-tail order is the forward cyclic order. -/
theorem normalizedBoundary_tprod (n : ℕ) (a : Fin (n + 1) → A) :
    (normalizedBoundary k A n).hom
        (a 0 ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i : Fin n => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ (a i.succ))) =
      ∑ j : Fin (n + 1), (-1 : k) ^ (n * j.val) •
        (1 ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i : Fin (n + 1) =>
            (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ
              (a ((finRotate (n + 1) ^ j.val) i)))) := by
  classical
  let S := ModuleCat.Algebra.Hochschild.unitSubmodule k A
  let Q := ModuleCat.Algebra.Hochschild.quotientCarrier k A
  let x : TensorPower k (n + 1) Q := PiTensorProduct.tprod k (fun i => S.mkQ (a i))
  have hB : (normalizedBoundary k A n).hom
      (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin n => S.mkQ (a i.succ))) =
      1 ⊗ₜ[k] TensorPower.norm k Q n x :=
    (normalizedBoundary_eq_projected_consInsert_norm k A n (a 0) (Fin.tail a)).trans (by
      rw [normalizationLevelMap_consInsert_norm, TensorPower.consEquiv_tmul,
        Fin.cons_self_tail, TensorPower.quotientMap_tprod])
  let ρ := TensorPower.cyclicRepresentation k Q n
  let e : Fin (n + 1) ≃ Multiplicative (ZMod (n + 1)) :=
    (ZMod.finEquiv (n + 1)).toEquiv.trans
      (Multiplicative.ofAdd.trans (Equiv.inv (Multiplicative (ZMod (n + 1)))))
  have he (i : Fin (n + 1)) :
      e i = Multiplicative.ofAdd ((-(i.val : ℤ)) : ZMod (n + 1)) := by
    change (Multiplicative.ofAdd ((ZMod.finEquiv (n + 1)) i))⁻¹ = _
    rw [← ofAdd_neg]
    apply congrArg Multiplicative.ofAdd
    have hFin : (ZMod.finEquiv (n + 1)) i = (i.val : ZMod (n + 1)) :=
      (ZMod.natCast_zmod_val ((ZMod.finEquiv (n + 1)) i)).symm
    have hInt : ((i.val : ℤ) : ZMod (n + 1)) = (i.val : ZMod (n + 1)) :=
      Int.cast_natCast i.val
    exact congrArg (fun z : ZMod (n + 1) => -z) (hFin.trans hInt.symm)
  have hNorm : TensorPower.norm k Q n x =
      ∑ j : Fin (n + 1), ρ (Multiplicative.ofAdd ((-(j.val : ℤ)) : ZMod (n + 1))) x := by
    have hr : ρ.norm = ∑ j : Fin (n + 1), ρ (e j) :=
      (Fintype.sum_equiv e _ _ fun _ => rfl).symm
    have hr' : ρ.norm =
        ∑ j : Fin (n + 1), ρ (Multiplicative.ofAdd ((-(j.val : ℤ)) : ZMod (n + 1))) :=
      hr.trans (Finset.sum_congr rfl fun j _ => congrArg ρ (he j))
    rw [TensorPower.norm_eq_representation_norm]
    have h := congrArg (fun f : Module.End k (TensorPower k (n + 1) Q) => f x) hr'
    simpa only [LinearMap.sum_apply] using h
  rw [hB, hNorm, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (1 : A) ⊗ₜ[k]
      TensorPower.cyclicRepresentation k Q n
        (Multiplicative.ofAdd ((-(j.val : ℤ)) : ZMod (n + 1)))
        (PiTensorProduct.tprod k (fun i => S.mkQ (a i))) = _
  rw [TensorPower.cyclicRepresentation_inverse_natCast_tprod, TensorProduct.tmul_smul]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. On the degree-zero representative `a ⊗ ()`,
`B̄₀(a ⊗ ())=1 ⊗ q(a)`. -/
theorem normalizedBoundary_zero_tprod (a : A) :
    (normalizedBoundary k A 0).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i : Fin 0 => (Fin.elim0 i :
            ModuleCat.Algebra.Hochschild.quotientCarrier k A))) =
      1 ⊗ₜ[k] PiTensorProduct.tprod k
        (fun _ : Fin 1 => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ a) := by
  let S := ModuleCat.Algebra.Hochschild.unitSubmodule k A
  have he : (fun i : Fin 0 => S.mkQ (Fin.elim0 i : A)) =
      (fun i : Fin 0 => (Fin.elim0 i : A ⧸ S)) := by
    funext i
    exact Fin.elim0 i
  have h := normalizedBoundary_tmul_tprod k A 0 a
    (fun i : Fin 0 => (Fin.elim0 i : A))
  change (normalizedBoundary k A 0).hom
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => S.mkQ (Fin.elim0 i))) = _ at h
  rw [he] at h
  have hUnit :
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A 1).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => (1 : A))) = 0 :=
    ModuleCat.Algebra.Hochschild.normalizationLevelMap_unit_factor k A A 1 a _ 0 rfl
  exact h.trans (by
    rw [connesBoundary_zero_tprod, map_add,
      ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod, hUnit, add_zero])

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. In degree one,
`B̄₁(a ⊗ q(b))=1 ⊗ tprod(q(a),q(b))-1 ⊗ tprod(q(b),q(a))`.
The two terms have positive and negative signs respectively. -/
theorem normalizedBoundary_one_tprod (a b : A) :
    (normalizedBoundary k A 1).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k
          (fun _ : Fin 1 => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ b)) =
      1 ⊗ₜ[k] PiTensorProduct.tprod k
        (Fin.cons ((ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ a)
          (fun _ : Fin 1 => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ b)) -
        1 ⊗ₜ[k] PiTensorProduct.tprod k
          (Fin.cons ((ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ b)
            (fun _ : Fin 1 => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ a)) := by
  let S := ModuleCat.Algebra.Hochschild.unitSubmodule k A
  have hPair (x y : A) :
      (fun i : Fin 2 => S.mkQ ((Fin.cons (α := fun _ : Fin 2 => A) x (fun _ : Fin 1 => y)) i)) =
        Fin.cons (α := fun _ : Fin 2 => A ⧸ S) (S.mkQ x) (fun _ : Fin 1 => S.mkQ y) := by
    funext i
    cases i using Fin.cases <;> rfl
  have hUnit (x y : A) :
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A 2).hom
        (x ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons 1 (fun _ : Fin 1 => y))) = 0 :=
    ModuleCat.Algebra.Hochschild.normalizationLevelMap_unit_factor k A A 2 x _ 0 rfl
  have h := normalizedBoundary_tmul_tprod k A 1 a (fun _ : Fin 1 => b)
  exact h.trans (by
    rw [connesBoundary_one_tprod, map_sub, map_add, map_sub, hUnit, hUnit,
      ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod,
      ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod,
      hPair a b, hPair b a, add_zero, sub_zero]
    dsimp only [S]
    rfl)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The normalized Connes maps satisfy
`B̄_n ≫ B̄_(n+1)=0`. -/
theorem normalizedBoundary_square (n : ℕ) :
    normalizedBoundary k A n ≫ normalizedBoundary k A (n + 1) = 0 := by
  let P : ChainComplex (ModuleCat.{max u v} k) ℕ := bComplex k A
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ := normalizedBComplex k A
  let q : P ⟶ K := normalizedProjection k A
  have hq₀ : q.f n ≫ normalizedBoundary k A n =
      connesBoundary k A n ≫ q.f (n + 1) := normalizedProjection_boundary k A n
  have hq₁ : q.f (n + 1) ≫ normalizedBoundary k A (n + 1) =
      connesBoundary k A (n + 1) ≫ q.f (n + 2) :=
    normalizedProjection_boundary k A (n + 1)
  apply (cancel_epi (q.f n)).1
  change q.f n ≫ (normalizedBoundary k A n ≫ normalizedBoundary k A (n + 1)) =
    q.f n ≫ (0 : K.X n ⟶ K.X (n + 2))
  calc
    _ = (q.f n ≫ normalizedBoundary k A n) ≫ normalizedBoundary k A (n + 1) :=
      (Category.assoc _ _ _).symm
    _ = (connesBoundary k A n ≫ q.f (n + 1)) ≫ normalizedBoundary k A (n + 1) :=
      congrArg (fun a => a ≫ normalizedBoundary k A (n + 1)) hq₀
    _ = connesBoundary k A n ≫ (q.f (n + 1) ≫ normalizedBoundary k A (n + 1)) :=
      Category.assoc _ _ _
    _ = connesBoundary k A n ≫ (connesBoundary k A (n + 1) ≫ q.f (n + 2)) :=
      congrArg (fun a => connesBoundary k A n ≫ a) hq₁
    _ = (connesBoundary k A n ≫ connesBoundary k A (n + 1)) ≫ q.f (n + 2) :=
      (Category.assoc _ _ _).symm
    _ = 0 := (congrArg (fun a : P.X n ⟶ P.X (n + 2) => a ≫ q.f (n + 2))
      (connesBoundary_square k A n)).trans Limits.zero_comp
    _ = _ := Limits.comp_zero.symm

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. In degree `n+1`, the mixed relation is
`B̄_(n+1) ≫ b̄_(n+2,n+1) + b̄_(n+1,n) ≫ B̄_n=0`. -/
theorem normalizedBoundary_mixed (n : ℕ) :
    normalizedBoundary k A (n + 1) ≫ (normalizedBComplex k A).d (n + 2) (n + 1) +
        (normalizedBComplex k A).d (n + 1) n ≫ normalizedBoundary k A n = 0 := by
  let P : ChainComplex (ModuleCat.{max u v} k) ℕ := bComplex k A
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ := normalizedBComplex k A
  let q : P ⟶ K := normalizedProjection k A
  have hA : q.f (n + 1) ≫
      (normalizedBoundary k A (n + 1) ≫ K.d (n + 2) (n + 1)) =
      (connesBoundary k A (n + 1) ≫ P.d (n + 2) (n + 1)) ≫ q.f (n + 1) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ K.d (n + 2) (n + 1))
        (normalizedProjection_boundary k A (n + 1))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a => connesBoundary k A (n + 1) ≫ a)
            (q.comm (n + 2) (n + 1))).trans (Category.assoc _ _ _).symm)))
  have hB : q.f (n + 1) ≫ (K.d (n + 1) n ≫ normalizedBoundary k A n) =
      (P.d (n + 1) n ≫ connesBoundary k A n) ≫ q.f (n + 1) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ normalizedBoundary k A n) (q.comm (n + 1) n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a => P.d (n + 1) n ≫ a)
            (normalizedProjection_boundary k A n)).trans (Category.assoc _ _ _).symm)))
  apply (cancel_epi (q.f (n + 1))).1
  change q.f (n + 1) ≫
      (normalizedBoundary k A (n + 1) ≫ K.d (n + 2) (n + 1) +
        K.d (n + 1) n ≫ normalizedBoundary k A n) = q.f (n + 1) ≫ 0
  rw [Preadditive.comp_add, hA, hB, ← Preadditive.add_comp,
    connesBoundary_mixed, Limits.zero_comp, Limits.comp_zero]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. At the bottom degree,
`B̄₀ ≫ b̄_(1,0)=0`. -/
theorem normalizedBoundary_comp_d_zero :
    normalizedBoundary k A 0 ≫ (normalizedBComplex k A).d 1 0 = 0 := by
  let P : ChainComplex (ModuleCat.{max u v} k) ℕ := bComplex k A
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ := normalizedBComplex k A
  let q : P ⟶ K := normalizedProjection k A
  apply (cancel_epi (q.f 0)).1
  change q.f 0 ≫ (normalizedBoundary k A 0 ≫ K.d 1 0) = q.f 0 ≫ 0
  calc
    _ = (q.f 0 ≫ normalizedBoundary k A 0) ≫ K.d 1 0 := (Category.assoc _ _ _).symm
    _ = (connesBoundary k A 0 ≫ q.f 1) ≫ K.d 1 0 :=
      congrArg (fun a => a ≫ K.d 1 0) (normalizedProjection_boundary k A 0)
    _ = connesBoundary k A 0 ≫ (q.f 1 ≫ K.d 1 0) := Category.assoc _ _ _
    _ = connesBoundary k A 0 ≫ (P.d 1 0 ≫ q.f 0) :=
      congrArg (fun a => connesBoundary k A 0 ≫ a) (q.comm 1 0)
    _ = (connesBoundary k A 0 ≫ P.d 1 0) ≫ q.f 0 := (Category.assoc _ _ _).symm
    _ = 0 := (congrArg (fun a : P.X 0 ⟶ P.X 0 => a ≫ q.f 0)
      (connesBoundary_comp_d_zero k A)).trans Limits.zero_comp
    _ = _ := Limits.comp_zero.symm

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The degree-one components `B̄_n` give a homotopy from
zero to zero on the normalized `b̄`-complex, expressing its
anticommutation with the differential. -/
def normalizedBoundaryHomotopy :
    Homotopy (0 : normalizedBComplex k A ⟶ normalizedBComplex k A) 0 := by
  let K := normalizedBComplex k A
  let H : ∀ i j : ℕ, (ComplexShape.down ℕ).Rel j i → (K.X i ⟶ K.X j) :=
    fun i j hij => normalizedBoundary k A i ≫ (K.XIsoOfEq (by
      change i + 1 = j at hij
      exact hij)).hom
  have hH (n : ℕ) : H n (n + 1) (by rfl) = normalizedBoundary k A n := by
    change normalizedBoundary k A n ≫ 𝟙 (K.X (n + 1)) = normalizedBoundary k A n
    exact Category.comp_id _
  have h : Homotopy.nullHomotopicMap' H = (0 : K ⟶ K) := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
        let B : K.X 0 ⟶ K.X 1 := normalizedBoundary k A 0
        let d : K.X 1 ⟶ K.X 0 := K.d 1 0
        have hf : (Homotopy.nullHomotopicMap' H).f 0 = H 0 1 (by rfl) ≫ d :=
          Homotopy.nullHomotopicMap'_f_of_not_rel_left
            (k₁ := 1) (k₀ := 0) (by rfl) (by intro l; simp [ComplexShape.down_Rel]) H
        have hB : B ≫ d = 0 := normalizedBoundary_comp_d_zero k A
        change (Homotopy.nullHomotopicMap' H).f 0 = 0
        exact hf.trans ((congrArg (fun f : K.X 0 ⟶ K.X 1 => f ≫ d) (hH 0)).trans hB)
    | succ n =>
        let d₀ : K.X (n + 1) ⟶ K.X n := K.d (n + 1) n
        let d₁ : K.X (n + 2) ⟶ K.X (n + 1) := K.d (n + 2) (n + 1)
        have hf : (Homotopy.nullHomotopicMap' H).f (n + 1) =
            d₀ ≫ H n (n + 1) (by rfl) + H (n + 1) (n + 2) (by rfl) ≫ d₁ :=
          Homotopy.nullHomotopicMap'_f
            (k₂ := n + 2) (k₁ := n + 1) (k₀ := n) (by rfl) (by rfl) H
        have hB : d₀ ≫ normalizedBoundary k A n + normalizedBoundary k A (n + 1) ≫ d₁ = 0 :=
          by simpa only [d₀, d₁, add_comm] using normalizedBoundary_mixed k A n
        have ht := congrArg₂
          (fun (a : K.X n ⟶ K.X (n + 1)) (b : K.X (n + 1) ⟶ K.X (n + 2)) => d₀ ≫ a + b ≫ d₁)
          (hH n) (hH (n + 1))
        change (Homotopy.nullHomotopicMap' H).f (n + 1) = 0
        exact hf.trans (ht.trans hB)
  exact (Homotopy.ofEq h.symm).trans (Homotopy.nullHomotopy' H)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Put `Ā=A/(k·1)` as a ground-module
quotient, `C_n=A ⊗[k] A^⊗n`, `C̄_n=A ⊗[k] Ā^⊗n`, and
`p_n=id_A ⊗ q^⊗n`. The full and normalized boundaries are
`b,b̄`, and the Connes operator is `B=(1-t)sN`. The component from degree `n` to `n+1` of the normalized
Connes homotopy is exactly `B̄_n`. -/
@[simp]
theorem normalizedBoundaryHomotopy_hom (n : ℕ) :
    (normalizedBoundaryHomotopy k A).hom n (n + 1) = normalizedBoundary k A n := by
  dsimp only [normalizedBoundaryHomotopy, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', Homotopy.nullHomotopy]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, dif_pos rfl,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  all_goals first | exact dif_pos rfl | exact if_pos rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The normalized `b̄,B̄` data form a mixed complex,
with `b̄B̄+B̄b̄=0` and `B̄²=0`. -/
def normalizedMixedComplexModel : MixedComplex (ModuleCat.{max u v} k) :=
  MixedComplex.ofBoundaryHomotopy (normalizedBComplex k A) (normalizedBoundaryHomotopy k A)
    (fun n => by simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The underlying chain complex of the normalized mixed
object is `C̄_*(A)`. -/
@[simp]
theorem normalizedMixedComplexModel_underlying :
    (normalizedMixedComplexModel k A).underlying = normalizedBComplex k A := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The degree-`n` operator of the normalized mixed object
is the descended boundary `B̄_n`. -/
@[simp]
theorem normalizedMixedComplexModel_B (n : ℕ) :
    (normalizedMixedComplexModel k A).B n = normalizedBoundary k A n := normalizedBoundaryHomotopy_hom k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The normalized Connes double data has supported cells
`C̄_(q-p)(A)`, zero cells for `q<p`, stored vertical maps
`(-1)^p b̄`, and horizontal maps `B̄`. -/
def normalizedMixedConnesDoubleData : MixedComplex.ConnesDoubleData (normalizedMixedComplexModel k A) :=
  MixedComplex.ofBoundaryHomotopyConnesDoubleData (normalizedBComplex k A) (normalizedBoundaryHomotopy k A)
    (fun n => by simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The normalized mixed object has canonical cyclic/SBI
data consisting of its Connes bicomplex, column-zero comparison,
and translation by two of its column-zero quotient. -/
def normalizedMixedGenericCyclicData : MixedComplex.GenericMixedCyclicData (normalizedMixedComplexModel k A) :=
  (normalizedMixedComplexModel k A).connesCyclicData

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The chain projection `p`, together with
`p_n ≫ B̄_n=B_n ≫ p_(n+1)`, is a morphism from the regular
mixed complex to the normalized mixed complex. -/
def normalizedMixedComplexProjection : connesMixedComplexModel k A ⟶ normalizedMixedComplexModel k A :=
  MixedComplex.ofBoundaryHomotopyMap (connesBoundaryHomotopy k A)
    (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)
    (normalizedBoundaryHomotopy k A)
    (fun n => by simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n)
    (normalizedProjection k A) (fun n => by
      simpa only [connesBoundaryHomotopy_hom, normalizedBoundaryHomotopy_hom] using
        normalizedProjection_boundary k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The underlying chain map of the normalization mixed
morphism is the full normalized projection `p`. -/
@[simp]
theorem normalizedMixedComplexProjection_underlying :
    (normalizedMixedComplexProjection k A).underlying = normalizedProjection k A := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The normalized mixed bicomplex has both shapes
`down ℕ`, cells `C̄_(q-p)(A)` for `p≤q`, and the normalized
mixed differentials. -/
def normalizedMixedBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (normalizedMixedConnesDoubleData k A).K

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The bicomplex of the normalized mixed object agrees
with that built directly from `C̄_*`, its zero Connes homotopy,
and the square-zero components `B̄`. -/
theorem normalizedMixedBicomplex_eq_original :
    normalizedMixedBicomplex k A = ChainComplex.mixedBicomplex (normalizedBComplex k A)
      (normalizedBoundaryHomotopy k A) (fun n => by
        simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n) := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The model bicomplex in the normalized generic cyclic
data is `K̄`. -/
theorem normalizedMixedGenericCyclicData_model_K :
    (normalizedMixedGenericCyclicData k A).model.K = normalizedMixedBicomplex k A :=
  MixedComplex.ofBoundaryHomotopy_connesBicomplex _ _ _

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The normalized mixed total is `T̄=Tot(K̄)`, with
finite diagonal sum `T̄_n=⊕_(2p≤n) C̄_(n-2p)(A)`. -/
def normalizedMixedTotal : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (HomologicalComplex₂.total (normalizedMixedBicomplex k A) (ComplexShape.down ℕ))

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The mixed-complex projection induces the bicomplex
map `K → K̄` by the translated factorwise quotient maps. -/
def normalizedMixedProjection : connesMixedBicomplex k A ⟶ normalizedMixedBicomplex k A :=
  let P : ChainComplex (ModuleCat.{max u v} k) ℕ := bComplex k A
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ := normalizedBComplex k A
  let H : Homotopy (0 : P ⟶ P) 0 := connesBoundaryHomotopy k A
  let H' : Homotopy (0 : K ⟶ K) 0 := normalizedBoundaryHomotopy k A
  let q : P ⟶ K := normalizedProjection k A
  let hSquare : ∀ n : ℕ, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0 := by
    intro n
    simpa only [H, connesBoundaryHomotopy_hom] using connesBoundary_square k A n
  let hSquare' : ∀ n : ℕ, H'.hom n (n + 1) ≫ H'.hom (n + 1) (n + 2) = 0 := by
    intro n
    simpa only [H', normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n
  let hq : ∀ n : ℕ, q.f n ≫ H'.hom n (n + 1) = H.hom n (n + 1) ≫ q.f (n + 1) := by
    intro n
    simpa only [q, H, H', connesBoundaryHomotopy_hom, normalizedBoundaryHomotopy_hom] using
      normalizedProjection_boundary k A n
  ChainComplex.mixedBicomplexMap (H := H) (hSquare := hSquare) q H' hSquare' hq

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Column `p` of the mixed-bicomplex projection is the
translated column map of `p : C_* → C̄_*`, with the column's
vertical sign convention. -/
@[simp]
theorem normalizedMixedProjection_f (p : ℕ) :
    (normalizedMixedProjection k A).f p =
      ChainComplex.mixedColumnMap (normalizedProjection k A) p := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Totalizing `K → K̄` gives the chain map
`P : T → T̄`. -/
def normalizedMixedTotalProjection : connesMixedTotal k A ⟶ normalizedMixedTotal k A :=
  HomologicalComplex₂.total.map (normalizedMixedProjection k A) (ComplexShape.down ℕ)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The total projection `P : T → T̄` is a quasi-isomorphism,
from the normalization quasi-isomorphism in every translated
column and first-quadrant totalization. -/
instance normalizedMixedTotalProjection_quasiIso :
    _root_.QuasiIso (normalizedMixedTotalProjection k A) := by
  change _root_.QuasiIso (HomologicalComplex₂.total.map
    (ChainComplex.mixedBicomplexMap
      (H := connesBoundaryHomotopy k A)
      (hSquare := fun n => by
        simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)
      (normalizedProjection k A) (normalizedBoundaryHomotopy k A)
      (fun n => by
        simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n)
      (fun n => by
        simpa only [connesBoundaryHomotopy_hom, normalizedBoundaryHomotopy_hom] using
          normalizedProjection_boundary k A n))
    (ComplexShape.down ℕ))
  exact ChainComplex.quasiIso_total_mixedBicomplexMap (normalizedProjection k A)
    (connesBoundaryHomotopy k A) (normalizedBoundaryHomotopy k A)
    (fun n => by
      simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)
    (fun n => by
      simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n)
    (fun n => by
      simpa only [connesBoundaryHomotopy_hom, normalizedBoundaryHomotopy_hom] using
        normalizedProjection_boundary k A n)
    inferInstance

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The normalized total computes cyclic homology:
`H_n(T̄) ≅ HC_n(k,A)`, through the zigzag
`T̄ ← T → cyclicTotal(k,A)`. -/
def normalizedMixedCyclicHomologyIso (n : ℕ) :
    (normalizedMixedTotal k A).homology n ≅ cyclicHomology k A n :=
  (asIso (HomologicalComplex.homologyMap (normalizedMixedTotalProjection k A) n)).symm ≪≫
    mixedCyclicHomologyIso k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. The forward comparison `H_n(T̄) → HC_n(k,A)` is
`H_n(P)⁻¹` followed by the homology map of the positive
mixed-to-cyclic inclusion. -/
theorem normalizedMixedCyclicHomologyIso_hom (n : ℕ) :
    (normalizedMixedCyclicHomologyIso k A n).hom =
      (asIso (HomologicalComplex.homologyMap (normalizedMixedTotalProjection k A) n)).inv ≫
        HomologicalComplex.homologyMap (mixedToCyclic k A) n := by
  change (asIso (HomologicalComplex.homologyMap (normalizedMixedTotalProjection k A) n)).inv ≫
      (mixedCyclicHomologyIso k A n).hom = _
  exact congrArg
    (fun f => (asIso (HomologicalComplex.homologyMap (normalizedMixedTotalProjection k A) n)).inv ≫ f)
    (mixedCyclicHomologyIso_hom k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. Lifting the normalized zero-to-zero Connes homotopy
 gives a homotopy on `L_ℓ(C̄_*)`. -/
def normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    Homotopy
      (0 : ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (normalizedBComplex k A) ⟶
          ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (normalizedBComplex k A)) 0 where
  hom := ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomotopy
    (normalizedBoundaryHomotopy k A)).hom
  zero := ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomotopy
    (normalizedBoundaryHomotopy k A)).zero
  comm n := by
    simpa only [Functor.map_zero, HomologicalComplex.zero_f_apply] using
      ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomotopy
        (normalizedBoundaryHomotopy k A)).comm n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. The lifted homotopy component from degree `n` to
`n+1` is `L_ℓ(B̄_n)`. -/
@[simp]
theorem normalizedBoundaryHomotopyLift_hom.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A).hom n (n + 1) =
      (ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).map (normalizedBoundary k A n) := by
  change (ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).map
    ((normalizedBoundaryHomotopy k A).hom n (n + 1)) = _
  rw [normalizedBoundaryHomotopy_hom]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. The consecutive lifted normalized Connes components
have zero composite. -/
theorem normalizedBoundaryHomotopyLift_square.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A).hom n (n + 1) ≫
      (normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A).hom (n + 1) (n + 2) = 0 := by
  rw [normalizedBoundaryHomotopyLift_hom, normalizedBoundaryHomotopyLift_hom,
    ← Functor.map_comp, normalizedBoundary_square, Functor.map_zero]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. The lifted `b̄,B̄` data form a mixed complex in module
height `max(u,v,ℓ)`. -/
def normalizedMixedComplexModelLift.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] : MixedComplex (ModuleCat.{max groundNML algebraNML liftNML} k) :=
  MixedComplex.ofBoundaryHomotopy
    (((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedBComplex k A))
    (normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A)
    (normalizedBoundaryHomotopyLift_square.{groundNML, algebraNML, liftNML} k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. The underlying chain complex of that lifted normalized
mixed object is `L_ℓ(C̄_*(A))`. -/
@[simp]
theorem normalizedMixedComplexModelLift_underlying.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    (normalizedMixedComplexModelLift.{groundNML, algebraNML, liftNML} k A).underlying =
      ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (normalizedBComplex k A) := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. Its degree-`n` mixed operator is `L_ℓ(B̄_n)`. -/
@[simp]
theorem normalizedMixedComplexModelLift_B.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (normalizedMixedComplexModelLift.{groundNML, algebraNML, liftNML} k A).B n =
      (ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).map (normalizedBoundary k A n) :=
  normalizedBoundaryHomotopyLift_hom k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. The lifted projection satisfies
`L_ℓ(p_n) ≫ L_ℓ(B̄_n)=L_ℓ(B_n) ≫ L_ℓ(p_(n+1))`
for every degree `n`. -/
@[reassoc]
theorem normalizedProjection_boundaryLift.{groundNML, algebraNML, liftNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (normalizedProjection k A)).f n ≫
        (normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A).hom n (n + 1) =
      (connesBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A).hom n (n + 1) ≫
        (((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (normalizedProjection k A)).f (n + 1) := by
  let U := ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k
  let p := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map (normalizedProjection k A)
  let H := normalizedBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A
  let R := connesBoundaryHomotopyLift.{groundNML, algebraNML, liftNML} k A
  have hH : H.hom n (n + 1) = U.map (normalizedBoundary k A n) :=
    normalizedBoundaryHomotopyLift_hom k A n
  have hR : R.hom n (n + 1) = U.map (connesBoundary k A n) :=
    connesBoundaryHomotopyLift_hom k A n
  have h : U.map ((normalizedProjection k A).f n) ≫ U.map (normalizedBoundary k A n) =
      U.map (connesBoundary k A n) ≫ U.map ((normalizedProjection k A).f (n + 1)) :=
    (U.map_comp _ _).symm.trans
      ((congrArg (fun a => U.map a) (normalizedProjection_boundary k A n)).trans (U.map_comp _ _))
  change p.f n ≫ H.hom n (n + 1) = R.hom n (n + 1) ≫ p.f (n + 1)
  exact (congrArg (fun a => p.f n ≫ a) hH).trans
    (h.trans (congrArg (fun a => a ≫ p.f (n + 1)) hR.symm))

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. The lifted projection gives a bicomplex map
`L_ℓ(K) → L_ℓ(K̄)`. -/
def normalizedMixedProjectionLift.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    (((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A) ⟶
      (((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (normalizedMixedBicomplex k A) :=
  (((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (normalizedMixedProjection k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Write `C_*(A),C̄_*(A)` for regular
and normalized Hochschild chains, `p : C_* → C̄_*` for factorwise
quotient projection, and `B,B̄` for their Connes operators.
Their mixed bicomplexes and totals are `K,K̄` and `T,T̄`. Let `ℓ` be an extra carrier height and `L_ℓ` the module lift
from `max(u,v)` to `max(u,v,ℓ)`. For a supported cell `r+p=q`, the lifted bicomplex
projection is `L_ℓ(p_r)` under the source and target translated
cell identifications. -/
theorem normalizedMixedProjectionLift_component.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    (p r q : ℕ) (h : r + p = q) :
    ((normalizedMixedProjectionLift.{liftNML} k A).f p).f q =
      (ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).map
          (ChainComplex.mixedColumnIso (bComplex k A) p r q h).hom ≫
        (ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).map ((normalizedProjection k A).f r) ≫
          (ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).map
            (ChainComplex.mixedColumnIso (normalizedBComplex k A) p r q h).inv := by
  let U := ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k
  let φ := normalizedMixedProjection k A
  have hφ : (φ.f p).f q =
      (ChainComplex.mixedColumnIso (bComplex k A) p r q h).hom ≫
        (normalizedProjection k A).f r ≫
          (ChainComplex.mixedColumnIso (normalizedBComplex k A) p r q h).inv := by
    rw [normalizedMixedProjection_f]
    exact ChainComplex.mixedColumnMap_f_eq (normalizedProjection k A) p r q h
  let P : ChainComplex (ModuleCat.{max groundNML algebraNML} k) ℕ := bComplex k A
  let K : ChainComplex (ModuleCat.{max groundNML algebraNML} k) ℕ := normalizedBComplex k A
  let a : (ChainComplex.mixedColumn P p).X q ≅ P.X r :=
    ChainComplex.mixedColumnIso P p r q h
  let b : (ChainComplex.mixedColumn K p).X q ≅ K.X r :=
    ChainComplex.mixedColumnIso K p r q h
  let Q : P.X r ⟶ K.X r := (normalizedProjection k A).f r
  have hOuter : U.map (a.hom ≫ (Q ≫ b.inv)) =
      U.map a.hom ≫ U.map (Q ≫ b.inv) := U.map_comp a.hom (Q ≫ b.inv)
  have hInner : U.map (Q ≫ b.inv) = U.map Q ≫ U.map b.inv := U.map_comp Q b.inv
  have hPost : U.map a.hom ≫ U.map (Q ≫ b.inv) =
      U.map a.hom ≫ (U.map Q ≫ U.map b.inv) :=
    congrArg (fun f : U.obj (P.X r) ⟶ U.obj ((ChainComplex.mixedColumn K p).X q) =>
      U.map a.hom ≫ f) hInner
  change U.map ((φ.f p).f q) = _
  exact (congrArg U.map hφ).trans (hOuter.trans hPost)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. Totalizing the lifted bicomplex projection gives
`P^ℓ : T^ℓ → T̄^ℓ`. -/
def normalizedMixedTotalProjectionLift.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((HomologicalComplex₂.total ((((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A)) (ComplexShape.down ℕ))) ⟶
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (normalizedMixedBicomplex k A)) (ComplexShape.down ℕ))) :=
  HomologicalComplex₂.total.map (normalizedMixedProjectionLift.{liftNML} k A) (ComplexShape.down ℕ)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. The lifted total normalization projection `P^ℓ` is
a quasi-isomorphism, from exact lifting and the first-quadrant
column comparisons. -/
instance normalizedMixedTotalProjectionLift_quasiIso.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    _root_.QuasiIso (normalizedMixedTotalProjectionLift.{liftNML} k A) := by
  let U := ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k
  change _root_.QuasiIso (HomologicalComplex₂.total.map
    (normalizedMixedProjectionLift.{liftNML} k A) (ComplexShape.down ℕ))
  apply HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant
  intro p
  letI : _root_.QuasiIso ((normalizedMixedProjection k A).f p) := by
    rw [normalizedMixedProjection_f]
    exact ChainComplex.quasiIso_mixedColumnMap (normalizedProjection k A) inferInstance p
  change _root_.QuasiIso ((U.mapHomologicalComplex (ComplexShape.down ℕ)).map
    ((normalizedMixedProjection k A).f p))
  infer_instance

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. The normalized total-lift comparison is
`L_ℓ(T̄) ≅ Tot(L_ℓ K̄)`. -/
def normalizedMixedTotalLiftIso.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedMixedTotal k A) ≅
        ((HomologicalComplex₂.total
            ((((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (normalizedMixedBicomplex k A)) (ComplexShape.down ℕ))) := by
  let U := ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k
  let R := normalizedMixedBicomplex k A
  letI : ∀ n, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  exact HomologicalComplex₂.functorTotalIso U R

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. For the raw and normalized total-lift isomorphisms,
`L_ℓ(P) ≫ E_norm = E_raw ≫ P^ℓ`. -/
@[reassoc]
theorem map_normalizedMixedTotalProjection_lift.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (normalizedMixedTotalProjection k A) ≫
          (normalizedMixedTotalLiftIso.{liftNML} k A).hom =
      (connesMixedTotalLiftIso.{liftNML} k A).hom ≫ normalizedMixedTotalProjectionLift.{liftNML} k A := by
  let U := ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k
  let R := connesMixedBicomplex k A
  let N := normalizedMixedBicomplex k A
  letI : ∀ n, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  letI : ∀ n, PreservesColimit (Discrete.functor
      (N.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  have h := HomologicalComplex₂.functorTotalIso_hom_naturality U R N
    (normalizedMixedProjection k A)
  change (U.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (normalizedMixedTotalProjection k A) ≫ (normalizedMixedTotalLiftIso.{liftNML} k A).hom =
    (connesMixedTotalLiftIso.{liftNML} k A).hom ≫ normalizedMixedTotalProjectionLift.{liftNML} k A at h
  exact h

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. The lifted projection and positive inclusion give
`H_n(T̄^ℓ) ≅ H_n(Z^ℓ)` in every degree `n`. -/
def normalizedMixedCyclicHomologyLiftIso.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    ((HomologicalComplex₂.total ((((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (normalizedMixedBicomplex k A)) (ComplexShape.down ℕ))).homology n ≅
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{liftNML, max groundNML algebraNML} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A)) (ComplexShape.down ℕ))).homology n :=
  (asIso (HomologicalComplex.homologyMap (normalizedMixedTotalProjectionLift.{liftNML} k A) n)).symm ≪≫
    mixedCyclicHomologyLiftIso.{liftNML} k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. The forward lifted comparison is
`H_n(P^ℓ)⁻¹ ≫ H_n(i^ℓ)`. -/
theorem normalizedMixedCyclicHomologyLiftIso_hom.{liftNML, groundNML, algebraNML}
    (k : Type groundNML) [CommRing k] (A : Type algebraNML) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (normalizedMixedCyclicHomologyLiftIso.{liftNML} k A n).hom =
      (asIso (HomologicalComplex.homologyMap
        (normalizedMixedTotalProjectionLift.{liftNML} k A) n)).inv ≫
          HomologicalComplex.homologyMap (mixedToCyclicLift.{liftNML} k A) n := by
  change (asIso (HomologicalComplex.homologyMap
    (normalizedMixedTotalProjectionLift.{liftNML} k A) n)).inv ≫
      (mixedCyclicHomologyLiftIso.{liftNML} k A n).hom = _
  rw [mixedCyclicHomologyLiftIso_hom]

section Naturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. For every degree `n`, the quotient-level square is
`L_A(p_A,n) ≫ Φ̄_n = Φ_n ≫ L_B(p_B,n)`, where the two
carrier lifts put both algebras in the common height. -/
@[reassoc]
theorem normalizedProjection_f_mapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (ModuleCat.uliftFunctor.{w, max u v} k).map ((normalizedProjection k A).f n) ≫
        ModuleCat.Algebra.Hochschild.normalizedLevelMapLift
          (f : A →ₗ[k] B) (f : A →ₗ[k] B)
            (by change f (1 : A) = (1 : B); exact hOne) n =
      (bComplexMapLift f).f n ≫
        (ModuleCat.uliftFunctor.{v, max u w} k).map ((normalizedProjection k B).f n) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let qA : chainLevel k A A n ⟶
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n :=
    (normalizedProjection k A).f n
  let qB : chainLevel k B B n ⟶
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k B B n :=
    (normalizedProjection k B).f n
  let qA₀ : chainLevel k A A n ⟶
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n :=
    ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n
  let qB₀ : chainLevel k B B n ⟶
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k B B n :=
    ModuleCat.Algebra.Hochschild.normalizationLevelMap k B B n
  have hOneLinear : (f : A →ₗ[k] B) (1 : A) = (1 : B) := by
    change f (1 : A) = (1 : B)
    exact hOne
  let s := ModuleCat.Algebra.Hochschild.normalizedLevelMapLift
    (f : A →ₗ[k] B) (f : A →ₗ[k] B) hOneLinear n
  let r : UA.obj (chainLevel k A A n) ⟶ UB.obj (chainLevel k B B n) :=
    (bComplexMapLift f).f n
  let r₀ : UA.obj (chainLevel k A A n) ⟶ UB.obj (chainLevel k B B n) :=
    levelMapLift (f : A →ₗ[k] B) n
  have hA : UA.map qA = UA.map qA₀ :=
    congrArg (fun a : chainLevel k A A n ⟶
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k A A n => UA.map a)
        (normalizedProjection_f k A n)
  have hB : UB.map qB = UB.map qB₀ :=
    congrArg (fun a : chainLevel k B B n ⟶
      ModuleCat.Algebra.Hochschild.normalizedChainLevel k B B n => UB.map a)
        (normalizedProjection_f k B n)
  have hr : r = r₀ := bComplexMapLift_f f n
  have h : UA.map qA₀ ≫ s = r₀ ≫ UB.map qB₀ := by
    apply ModuleCat.hom_ext
    ext x
    change (ModuleCat.Algebra.Hochschild.normalizedLevelMapLift
        (f : A →ₗ[k] B) (f : A →ₗ[k] B) hOne n).hom
          (ULift.up (qA₀.hom x.down)) =
      ULift.up (qB₀.hom (TensorPower.consLevelMap (f : A →ₗ[k] B) n x.down))
    exact ModuleCat.Algebra.Hochschild.normalizedLevelMapLift_quotient
      (f : A →ₗ[k] B) (f : A →ₗ[k] B) hOne n x.down
  change UA.map qA ≫ s = r ≫ UB.map qB
  exact (congrArg (fun a => a ≫ s) hA).trans
    (h.trans (congrArg₂ (fun a b => a ≫ b) hr.symm hB.symm))

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The normalized word maps give a chain map between
the two lifted normalized `b̄`-complexes. -/
def normalizedBComplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedBComplex k A) ⟶
    ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedBComplex k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bComplex k A)
  let PB : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bComplex k B)
  let KA := (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj (normalizedBComplex k A)
  let KB := (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj (normalizedBComplex k B)
  let pA : PA ⟶ KA :=
    (UA.mapHomologicalComplex (ComplexShape.down ℕ)).map (normalizedProjection k A)
  let pB : PB ⟶ KB :=
    (UB.mapHomologicalComplex (ComplexShape.down ℕ)).map (normalizedProjection k B)
  let r : PA ⟶ PB := bComplexMapLift f
  let s (n : ℕ) : KA.X n ⟶ KB.X n :=
    ModuleCat.Algebra.Hochschild.normalizedLevelMapLift
      (f : A →ₗ[k] B) (f : A →ₗ[k] B) hOne n
  have h (n : ℕ) : pA.f n ≫ s n = r.f n ≫ pB.f n :=
    normalizedProjection_f_mapLift f hOne n
  refine ChainComplex.ofHom s ?_
  intro n
  letI : Epi (pA.f (n + 1)) := by
    change Epi (UA.map ((normalizedProjection k A).f (n + 1)))
    infer_instance
  apply (cancel_epi (pA.f (n + 1))).1
  calc
    pA.f (n + 1) ≫ (s (n + 1) ≫ KB.d (n + 1) n) =
        (r.f (n + 1) ≫ pB.f (n + 1)) ≫ KB.d (n + 1) n := by
      rw [← Category.assoc, h]
    _ = r.f (n + 1) ≫ (PB.d (n + 1) n ≫ pB.f n) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => r.f (n + 1) ≫ a) (pB.comm (n + 1) n))
    _ = (PA.d (n + 1) n ≫ r.f n) ≫ pB.f n :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ pB.f n) (r.comm (n + 1) n))
    _ = PA.d (n + 1) n ≫ (pA.f n ≫ s n) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => PA.d (n + 1) n ≫ a) (h n).symm)
    _ = (pA.f (n + 1) ≫ KA.d (n + 1) n) ≫ s n :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ s n) (pA.comm (n + 1) n).symm)
    _ = pA.f (n + 1) ≫ (KA.d (n + 1) n ≫ s n) := Category.assoc _ _ _

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The degree-`n` normalized map applies `f` to the
coefficient and its induced quotient map `Ā → B̄` to every
tail factor, with the canonical carrier lifts. -/
@[simp]
theorem normalizedBComplexMapLift_f (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (normalizedBComplexMapLift f hOne).f n =
      ModuleCat.Algebra.Hochschild.normalizedLevelMapLift
        (f : A →ₗ[k] B) (f : A →ₗ[k] B) hOne n := rfl

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The full chain maps satisfy
`L_A(p_A) ≫ Φ̄ = Φ ≫ L_B(p_B)`. -/
@[reassoc]
theorem normalizedProjection_mapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (normalizedProjection k A) ≫
        normalizedBComplexMapLift f hOne =
      bComplexMapLift f ≫
        ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (normalizedProjection k B) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact normalizedProjection_f_mapLift f hOne n

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The lifted normalized maps intertwine the descended
Connes boundaries:
`Φ̄_n ≫ B̄_B,n = B̄_A,n ≫ Φ̄_(n+1)`. -/
theorem normalizedBComplexMapLift_boundary (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (normalizedBComplexMapLift f hOne).f n ≫
        (normalizedBoundaryHomotopyLift.{u, w, v} k B).hom n (n + 1) =
      (normalizedBoundaryHomotopyLift.{u, v, w} k A).hom n (n + 1) ≫
        (normalizedBComplexMapLift f hOne).f (n + 1) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bComplex k A)
  let PB : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bComplex k B)
  let KA := (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj (normalizedBComplex k A)
  let KB := (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj (normalizedBComplex k B)
  let pA : PA ⟶ KA :=
    (UA.mapHomologicalComplex (ComplexShape.down ℕ)).map (normalizedProjection k A)
  let pB : PB ⟶ KB :=
    (UB.mapHomologicalComplex (ComplexShape.down ℕ)).map (normalizedProjection k B)
  let r : PA ⟶ PB := bComplexMapLift f
  let φ : KA ⟶ KB := normalizedBComplexMapLift f hOne
  let HA := normalizedBoundaryHomotopyLift.{u, v, w} k A
  let HB := normalizedBoundaryHomotopyLift.{u, w, v} k B
  let RA := connesBoundaryHomotopyLift.{u, v, w} k A
  let RB := connesBoundaryHomotopyLift.{u, w, v} k B
  have h (j : ℕ) : pA.f j ≫ φ.f j = r.f j ≫ pB.f j :=
    normalizedProjection_f_mapLift f hOne j
  have hA : pA.f n ≫ HA.hom n (n + 1) = RA.hom n (n + 1) ≫ pA.f (n + 1) :=
    normalizedProjection_boundaryLift k A n
  have hB : pB.f n ≫ HB.hom n (n + 1) = RB.hom n (n + 1) ≫ pB.f (n + 1) :=
    normalizedProjection_boundaryLift k B n
  have hRaw : r.f n ≫ RB.hom n (n + 1) = RA.hom n (n + 1) ≫ r.f (n + 1) :=
    bComplexMapLift_boundary f hOne n
  letI : Epi (pA.f n) := by
    change Epi (UA.map ((normalizedProjection k A).f n))
    infer_instance
  apply (cancel_epi (pA.f n)).1
  change pA.f n ≫ (φ.f n ≫ HB.hom n (n + 1)) =
    pA.f n ≫ (HA.hom n (n + 1) ≫ φ.f (n + 1))
  calc
    _ = (r.f n ≫ pB.f n) ≫ HB.hom n (n + 1) := by
      rw [← Category.assoc, h]
    _ = r.f n ≫ (RB.hom n (n + 1) ≫ pB.f (n + 1)) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => r.f n ≫ a) hB)
    _ = (RA.hom n (n + 1) ≫ r.f (n + 1)) ≫ pB.f (n + 1) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ pB.f (n + 1)) hRaw)
    _ = RA.hom n (n + 1) ≫ (pA.f (n + 1) ≫ φ.f (n + 1)) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun a => RA.hom n (n + 1) ≫ a) (h (n + 1)).symm)
    _ = (pA.f n ≫ HA.hom n (n + 1)) ≫ φ.f (n + 1) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ φ.f (n + 1)) hA.symm)
    _ = _ := Category.assoc _ _ _

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The homology maps of `Φ̄` commute with the induced
degree-one normalized Connes homology operators in degrees
`n,n+1`. -/
theorem normalizedBoundaryHomology_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    HomologicalComplex.homologyMap (normalizedBComplexMapLift f hOne) n ≫
        (normalizedBoundaryHomotopyLift.{u, w, v} k B).homologyDegreeMap
          (by show (ComplexShape.down ℕ).Rel (n + 1) n; rfl) =
      (normalizedBoundaryHomotopyLift.{u, v, w} k A).homologyDegreeMap
          (by show (ComplexShape.down ℕ).Rel (n + 1) n; rfl) ≫
        HomologicalComplex.homologyMap (normalizedBComplexMapLift f hOne) (n + 1) := by
  apply Homotopy.homologyDegreeMap_naturality_square
    (normalizedBoundaryHomotopyLift.{u, v, w} k A)
    (by show (ComplexShape.down ℕ).Rel (n + 1) n; rfl)
    (normalizedBoundaryHomotopyLift.{u, w, v} k B)
    (normalizedBComplexMapLift f hOne) (normalizedBComplexMapLift f hOne)
  exact normalizedBComplexMapLift_boundary f hOne n

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The normalized chain map and its Connes square form
a morphism of the lifted normalized mixed complexes. -/
def normalizedMixedComplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    normalizedMixedComplexModelLift.{u, v, w} k A ⟶ normalizedMixedComplexModelLift.{u, w, v} k B :=
  MixedComplex.ofBoundaryHomotopyMap (normalizedBoundaryHomotopyLift.{u, v, w} k A)
    (normalizedBoundaryHomotopyLift_square.{u, v, w} k A)
    (normalizedBoundaryHomotopyLift.{u, w, v} k B)
    (normalizedBoundaryHomotopyLift_square.{u, w, v} k B)
    (normalizedBComplexMapLift f hOne) (normalizedBComplexMapLift_boundary f hOne)

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The underlying chain map of the normalized mixed
morphism is `normalizedBComplexMapLift(f,hOne)`. -/
@[simp]
theorem normalizedMixedComplexMapLift_underlying (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    (normalizedMixedComplexMapLift f hOne).underlying = normalizedBComplexMapLift f hOne := rfl

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The normalized mixed-complex morphism induces a map
between the two lifted normalized Connes bicomplexes. -/
def normalizedMixedBicomplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    (((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (normalizedMixedBicomplex k A) ⟶
      (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (normalizedMixedBicomplex k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let K := normalizedBComplex k A
  let L := normalizedBComplex k B
  let H₀A := normalizedBoundaryHomotopy k A
  let H₀B := normalizedBoundaryHomotopy k B
  let HA := normalizedBoundaryHomotopyLift.{u, v, w} k A
  let HB := normalizedBoundaryHomotopyLift.{u, w, v} k B
  let hA : ∀ n, H₀A.hom n (n + 1) ≫ H₀A.hom (n + 1) (n + 2) = 0 := fun n => by
    dsimp only [H₀A]
    simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A n
  let hB : ∀ n, H₀B.hom n (n + 1) ≫ H₀B.hom (n + 1) (n + 2) = 0 := fun n => by
    dsimp only [H₀B]
    simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k B n
  let hcA : ∀ n, HA.hom n (n + 1) = UA.map (H₀A.hom n (n + 1)) := fun n =>
    (normalizedBoundaryHomotopyLift_hom k A n).trans
      (congrArg (fun a => UA.map a) (normalizedBoundaryHomotopy_hom k A n).symm)
  let hcB : ∀ n, HB.hom n (n + 1) = UB.map (H₀B.hom n (n + 1)) := fun n =>
    (normalizedBoundaryHomotopyLift_hom k B n).trans
      (congrArg (fun a => UB.map a) (normalizedBoundaryHomotopy_hom k B n).symm)
  exact ChainComplex.mixedBicomplexFunctorMap UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (normalizedMixedComplexMapLift f hOne).underlying
    (fun n => (normalizedMixedComplexMapLift f hOne).comm_B n)

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. For a supported cell `n+p=q`, the normalized
bicomplex-map component is `Φ̄_n` under the two lifted
translated-cell identifications. -/
theorem normalizedMixedBicomplexMapLift_component (f : A →ₙₐ[k] B) (hOne : f 1 = 1)
    (p n q : ℕ) (h : n + p = q) :
    ((normalizedMixedBicomplexMapLift f hOne).f p).f q =
      (ModuleCat.uliftFunctor.{w, max u v} k).map
          (ChainComplex.mixedColumnIso (normalizedBComplex k A) p n q h).hom ≫
        (normalizedBComplexMapLift f hOne).f n ≫
          (ModuleCat.uliftFunctor.{v, max u w} k).map
            (ChainComplex.mixedColumnIso (normalizedBComplex k B) p n q h).inv := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let K := normalizedBComplex k A
  let L := normalizedBComplex k B
  let H₀A := normalizedBoundaryHomotopy k A
  let H₀B := normalizedBoundaryHomotopy k B
  let HA := normalizedBoundaryHomotopyLift.{u, v, w} k A
  let HB := normalizedBoundaryHomotopyLift.{u, w, v} k B
  let hA : ∀ j, H₀A.hom j (j + 1) ≫ H₀A.hom (j + 1) (j + 2) = 0 := fun j => by
    dsimp only [H₀A]
    simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k A j
  let hB : ∀ j, H₀B.hom j (j + 1) ≫ H₀B.hom (j + 1) (j + 2) = 0 := fun j => by
    dsimp only [H₀B]
    simpa only [normalizedBoundaryHomotopy_hom] using normalizedBoundary_square k B j
  let hcA : ∀ j, HA.hom j (j + 1) = UA.map (H₀A.hom j (j + 1)) := fun j =>
    (normalizedBoundaryHomotopyLift_hom k A j).trans
      (congrArg (fun a => UA.map a) (normalizedBoundaryHomotopy_hom k A j).symm)
  let hcB : ∀ j, HB.hom j (j + 1) = UB.map (H₀B.hom j (j + 1)) := fun j =>
    (normalizedBoundaryHomotopyLift_hom k B j).trans
      (congrArg (fun a => UB.map a) (normalizedBoundaryHomotopy_hom k B j).symm)
  change ((ChainComplex.mixedBicomplexFunctorMap UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (normalizedBComplexMapLift f hOne) (normalizedBComplexMapLift_boundary f hOne)).f p).f q = _
  exact ChainComplex.mixedBicomplexFunctorMap_component UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (normalizedBComplexMapLift f hOne) (normalizedBComplexMapLift_boundary f hOne) p n q h

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The bicomplex normalization projections commute
with the two algebra maps:
`P_K,A ≫ f_K̄ = f_K ≫ P_K,B`. -/
theorem normalizedMixedProjectionLift_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    normalizedMixedProjectionLift.{w} k A ≫ normalizedMixedBicomplexMapLift f hOne =
      connesMixedBicomplexMapLift f hOne ≫ normalizedMixedProjectionLift.{v} k B := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let RA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A)
  let NA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k A)
  let RB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesMixedBicomplex k B)
  let NB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k B)
  let qA : RA ⟶ NA := normalizedMixedProjectionLift.{w} k A
  let qB : RB ⟶ NB := normalizedMixedProjectionLift.{v} k B
  let mR : RA ⟶ RB := connesMixedBicomplexMapLift f hOne
  let mN : NA ⟶ NB := normalizedMixedBicomplexMapLift f hOne
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  by_cases hpq : p ≤ q
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = r + p :=
      ⟨q - p, (Nat.sub_add_cancel hpq).symm⟩
    let aR : (RA.X p).X (r + p) ≅ UA.obj ((bComplex k A).X r) :=
      UA.mapIso (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl)
    let aN : (NA.X p).X (r + p) ≅ UA.obj ((normalizedBComplex k A).X r) :=
      UA.mapIso (ChainComplex.mixedColumnIso (normalizedBComplex k A) p r (r + p) rfl)
    let bR : (RB.X p).X (r + p) ≅ UB.obj ((bComplex k B).X r) :=
      UB.mapIso (ChainComplex.mixedColumnIso (bComplex k B) p r (r + p) rfl)
    let bN : (NB.X p).X (r + p) ≅ UB.obj ((normalizedBComplex k B).X r) :=
      UB.mapIso (ChainComplex.mixedColumnIso (normalizedBComplex k B) p r (r + p) rfl)
    let pA : UA.obj ((bComplex k A).X r) ⟶ UA.obj ((normalizedBComplex k A).X r) :=
      UA.map ((normalizedProjection k A).f r)
    let pB : UB.obj ((bComplex k B).X r) ⟶ UB.obj ((normalizedBComplex k B).X r) :=
      UB.map ((normalizedProjection k B).f r)
    let vR : UA.obj ((bComplex k A).X r) ⟶ UB.obj ((bComplex k B).X r) :=
      (bComplexMapLift f).f r
    let vN : UA.obj ((normalizedBComplex k A).X r) ⟶ UB.obj ((normalizedBComplex k B).X r) :=
      (normalizedBComplexMapLift f hOne).f r
    have hqA : (qA.f p).f (r + p) = aR.hom ≫ pA ≫ aN.inv :=
      normalizedMixedProjectionLift_component k A p r (r + p) rfl
    have hqB : (qB.f p).f (r + p) = bR.hom ≫ pB ≫ bN.inv :=
      normalizedMixedProjectionLift_component k B p r (r + p) rfl
    have hmR : (mR.f p).f (r + p) = aR.hom ≫ vR ≫ bR.inv :=
      connesMixedBicomplexMapLift_component f hOne p r (r + p) rfl
    have hmN : (mN.f p).f (r + p) = aN.hom ≫ vN ≫ bN.inv :=
      normalizedMixedBicomplexMapLift_component f hOne p r (r + p) rfl
    have hOriginal : pA ≫ vN = vR ≫ pB := by
      let PA : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
        (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj (bComplex k A)
      let NB₀ := (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj (normalizedBComplex k B)
      have h := congrArg (fun φ : PA ⟶ NB₀ => φ.f r) (normalizedProjection_mapLift f hOne)
      change pA ≫ vN = vR ≫ pB at h
      exact h
    change (qA.f p).f (r + p) ≫ (mN.f p).f (r + p) = (mR.f p).f (r + p) ≫ (qB.f p).f (r + p)
    calc
      _ = (aR.hom ≫ pA ≫ aN.inv) ≫ (aN.hom ≫ vN ≫ bN.inv) :=
        congrArg₂ (fun a b => a ≫ b) hqA hmN
      _ = aR.hom ≫ (pA ≫ vN) ≫ bN.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = aR.hom ≫ (vR ≫ pB) ≫ bN.inv :=
        congrArg (fun a => aR.hom ≫ a ≫ bN.inv) hOriginal
      _ = (aR.hom ≫ vR ≫ bR.inv) ≫ (bR.hom ≫ pB ≫ bN.inv) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := congrArg₂ (fun a b => a ≫ b) hmR.symm hqB.symm
  · have hZero : IsZero
        (((((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A)).X p).X q) :=
      Functor.map_isZero UA
        (ChainComplex.mixedBicomplex_isZero_cell (bComplex k A) (connesBoundaryHomotopy k A)
          (fun j => by simpa only [connesBoundaryHomotopy_hom] using
            connesBoundary_square k A j) p q (by omega))
    exact hZero.eq_of_src _ _

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. After totalization the normalization square is
`P_A^lift ≫ Tot(f_K̄) = Tot(f_K) ≫ P_B^lift`. -/
theorem normalizedMixedTotalProjectionLift_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    normalizedMixedTotalProjectionLift.{w} k A ≫
        HomologicalComplex₂.total.map (normalizedMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ) =
      HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ) ≫ normalizedMixedTotalProjectionLift.{v} k B := by
  change HomologicalComplex₂.total.map (normalizedMixedProjectionLift.{w} k A)
      (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map (normalizedMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ) = _
  exact (HomologicalComplex₂.total.map_comp (normalizedMixedProjectionLift.{w} k A)
    (normalizedMixedBicomplexMapLift f hOne) (ComplexShape.down ℕ)).symm.trans
      ((congrArg (fun φ => HomologicalComplex₂.total.map φ (ComplexShape.down ℕ))
        (normalizedMixedProjectionLift_naturality f hOne)).trans
          (HomologicalComplex₂.total.map_comp (connesMixedBicomplexMapLift f hOne)
            (normalizedMixedProjectionLift.{v} k B) (ComplexShape.down ℕ)))

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The normalized bicomplex map and total-lift
comparisons give the chain map between lifted normalized
mixed totals. -/
def normalizedMixedTotalMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (normalizedMixedTotal k A) ⟶
        ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (normalizedMixedTotal k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k A)
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k B)
  let eA := normalizedMixedTotalLiftIso.{w} k A
  let eB := normalizedMixedTotalLiftIso.{v} k B
  let φ : PA ⟶ PB := normalizedMixedBicomplexMapLift f hOne
  exact eA.hom ≫ HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) ≫ eB.inv

end Naturality

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. The normalized mixed homology lift is the canonical
isomorphism `L_ℓ(H_n(T̄)) ≅ H_n(Tot(L_ℓ K̄))`. -/
def normalizedMixedHomologyLiftIso.{lift, ground, algebra}
    (k : Type ground) (A : Type algebra) [CommRing k] [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).obj ((normalizedMixedTotal k A).homology n) ≅
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (normalizedMixedBicomplex k A))) (ComplexShape.down ℕ)).homology n := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let h : ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (normalizedMixedTotal k A)).homology n ≅
        U.obj ((normalizedMixedTotal k A).homology n) :=
    ((normalizedMixedTotal k A).sc n).mapHomologyIso U
  exact h.symm ≪≫ HomologicalComplex.homologyMapIso (normalizedMixedTotalLiftIso.{lift} k A) n

section HomologyNaturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The common-height total map induces a `k`-linear
map on the two unlifted normalized homology carriers,
`H_n(T̄_A) →ₗ[k] H_n(T̄_B)`. -/
def normalizedMixedHomologyLinearMap (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (normalizedMixedTotal k A).homology n →ₗ[k] (normalizedMixedTotal k B).homology n := by
  let eA := normalizedMixedHomologyLiftIso.{w} k A n
  let eB := normalizedMixedHomologyLiftIso.{v} k B n
  let φ := HomologicalComplex₂.total.map
    (normalizedMixedBicomplexMapLift f hOne) (ComplexShape.down ℕ)
  let m := eA.hom ≫ HomologicalComplex.homologyMap φ n ≫ eB.inv
  exact ULift.moduleEquiv.toLinearMap.comp
    (m.hom.comp ULift.moduleEquiv.symm.toLinearMap)

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. For `x : H_n(T̄_A)`, lifting the induced homology
value and comparing to total homology equals applying
`H_n(Tot(f_K̄))` to the compared lift of `x`. -/
theorem normalizedMixedHomologyLinearMap_lift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ)
    (z : (normalizedMixedTotal k A).homology n) :
    (normalizedMixedHomologyLiftIso.{v} k B n).hom
        (ULift.up (normalizedMixedHomologyLinearMap f hOne n z)) =
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (normalizedMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ)) n
            ((normalizedMixedHomologyLiftIso.{w} k A n).hom (ULift.up z)) := by
  let eA := normalizedMixedHomologyLiftIso.{w} k A n
  let eB := normalizedMixedHomologyLiftIso.{v} k B n
  let φ := HomologicalComplex₂.total.map
    (normalizedMixedBicomplexMapLift f hOne) (ComplexShape.down ℕ)
  change eB.hom (eB.inv (HomologicalComplex.homologyMap φ n (eA.hom (ULift.up z)))) =
    HomologicalComplex.homologyMap φ n (eA.hom (ULift.up z))
  exact ModuleCat.hom_inv_apply eB _

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The lifted normalized-to-cyclic comparisons satisfy
`H_n(Tot(f_K̄)) ≫ E_B^lift = E_A^lift ≫ H_n(Tot(f_cyc))`. -/
@[reassoc]
theorem normalizedMixedCyclicHomologyLiftIso_naturality
    (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (normalizedMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ)) n ≫
        (normalizedMixedCyclicHomologyLiftIso.{v} k B n).hom =
      (normalizedMixedCyclicHomologyLiftIso.{w} k A n).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)) n := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let RA := (HomologicalComplex₂.total
      (((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A))) (ComplexShape.down ℕ)
  let RB := (HomologicalComplex₂.total
      (((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k B))) (ComplexShape.down ℕ)
  let NA := (HomologicalComplex₂.total
      (((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k A))) (ComplexShape.down ℕ)
  let NB := (HomologicalComplex₂.total
      (((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k B))) (ComplexShape.down ℕ)
  let CA := (HomologicalComplex₂.total
      (((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A))) (ComplexShape.down ℕ)
  let CB := (HomologicalComplex₂.total
      (((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k B))) (ComplexShape.down ℕ)
  let qA : RA ⟶ NA := normalizedMixedTotalProjectionLift.{w} k A
  let qB : RB ⟶ NB := normalizedMixedTotalProjectionLift.{v} k B
  let iA : RA ⟶ CA := mixedToCyclicLift.{w} k A
  let iB : RB ⟶ CB := mixedToCyclicLift.{v} k B
  let mR : RA ⟶ RB := HomologicalComplex₂.total.map
    (connesMixedBicomplexMapLift f hOne) (ComplexShape.down ℕ)
  let mN : NA ⟶ NB := HomologicalComplex₂.total.map
    (normalizedMixedBicomplexMapLift f hOne) (ComplexShape.down ℕ)
  let mC : CA ⟶ CB := HomologicalComplex₂.total.map
    (cyclicBicomplexMap f) (ComplexShape.down ℕ)
  let Q : RA.homology n ≅ NA.homology n := asIso (HomologicalComplex.homologyMap qA n)
  let Q' : RB.homology n ≅ NB.homology n := asIso (HomologicalComplex.homologyMap qB n)
  let I : RA.homology n ⟶ CA.homology n := HomologicalComplex.homologyMap iA n
  let I' : RB.homology n ⟶ CB.homology n := HomologicalComplex.homologyMap iB n
  let r : RA.homology n ⟶ RB.homology n := HomologicalComplex.homologyMap mR n
  let a : NA.homology n ⟶ NB.homology n := HomologicalComplex.homologyMap mN n
  let b : CA.homology n ⟶ CB.homology n := HomologicalComplex.homologyMap mC n
  let E : NA.homology n ≅ CA.homology n := normalizedMixedCyclicHomologyLiftIso.{w} k A n
  let E' : NB.homology n ≅ CB.homology n := normalizedMixedCyclicHomologyLiftIso.{v} k B n
  have hQ : Q.hom ≫ a = r ≫ Q'.hom :=
    (HomologicalComplex.homologyMap_comp qA mN n).symm.trans
      ((congrArg (fun φ : RA ⟶ NB => HomologicalComplex.homologyMap φ n)
        (normalizedMixedTotalProjectionLift_naturality f hOne)).trans
          (HomologicalComplex.homologyMap_comp mR qB n))
  have hI : r ≫ I' = I ≫ b :=
    (HomologicalComplex.homologyMap_comp mR iB n).symm.trans
      ((congrArg (fun φ : RA ⟶ CB => HomologicalComplex.homologyMap φ n)
        (mixedToCyclicLift_naturality f hOne)).trans
          (HomologicalComplex.homologyMap_comp iA mC n))
  have hE : E.hom = Q.inv ≫ I := normalizedMixedCyclicHomologyLiftIso_hom.{w} k A n
  have hE' : E'.hom = Q'.inv ≫ I' := normalizedMixedCyclicHomologyLiftIso_hom.{v} k B n
  have hCancel : Q.hom ≫ E.hom = I :=
    (congrArg (fun φ : NA.homology n ⟶ CA.homology n => Q.hom ≫ φ) hE).trans
      (Q.hom_inv_id_assoc I)
  have hCancel' : Q'.hom ≫ E'.hom = I' :=
    (congrArg (fun φ : NB.homology n ⟶ CB.homology n => Q'.hom ≫ φ) hE').trans
      (Q'.hom_inv_id_assoc I')
  change a ≫ E'.hom = E.hom ≫ b
  apply (cancel_epi Q.hom).1
  have hLeft : Q.hom ≫ (a ≫ E'.hom) = I ≫ b :=
    (Category.assoc Q.hom a E'.hom).symm.trans
      ((congrArg (fun φ : RA.homology n ⟶ NB.homology n => φ ≫ E'.hom) hQ).trans
        ((Category.assoc r Q'.hom E'.hom).trans
          ((congrArg (fun φ : RB.homology n ⟶ CB.homology n => r ≫ φ) hCancel').trans hI)))
  have hRight : Q.hom ≫ (E.hom ≫ b) = I ≫ b :=
    (Category.assoc Q.hom E.hom b).symm.trans
      (congrArg (fun φ : RA.homology n ⟶ CA.homology n => φ ≫ b) hCancel)
  exact hLeft.trans hRight.symm

end HomologyNaturality

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. The regular and normalized mixed
totals are `T,T̄`, their projection is `P : T → T̄`, and the
positive mixed-to-cyclic map is `i : T → Z`, where `Z` is the
cyclic total. For an extra height `ℓ`, let `L_ℓ` lift carriers to
`max(u,v,ℓ)`; lifted-bicomplex totals are denoted by a superscript `ℓ`. The lift of the unlifted normalized cyclic comparison
commutes with the normalized and cyclic homology-lift
isomorphisms: both routes from `L_ℓ(H_n(T̄))` to
`H_n(Z^ℓ)` are equal. -/
@[reassoc]
theorem normalizedMixedCyclicHomologyLiftIso_lift.{lift, ground, algebra}
    (k : Type ground) (A : Type algebra) [CommRing k] [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (normalizedMixedHomologyLiftIso.{lift} k A n).hom ≫
        (normalizedMixedCyclicHomologyLiftIso.{lift} k A n).hom =
      (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map
          (normalizedMixedCyclicHomologyIso k A n).hom ≫
        (cyclicHomologyLiftIso.{lift} k A n).hom := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let η := HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n U
  have hTransport
      {K L : ChainComplex (ModuleCat.{max ground algebra} k) ℕ}
      {K' L' : ChainComplex (ModuleCat.{max lift ground algebra} k) ℕ}
      (φ : K ⟶ L) (φ' : K' ⟶ L') (eK : F.obj K ≅ K') (eL : F.obj L ≅ L')
      (hφ : F.map φ ≫ eL.hom = eK.hom ≫ φ') :
      U.map (HomologicalComplex.homologyMap φ n) ≫
          ((L.sc n).mapHomologyIso U).inv ≫ HomologicalComplex.homologyMap eL.hom n =
        (((K.sc n).mapHomologyIso U).inv ≫ HomologicalComplex.homologyMap eK.hom n) ≫
          HomologicalComplex.homologyMap φ' n := by
    let hK := (K.sc n).mapHomologyIso U
    let hL := (L.sc n).mapHomologyIso U
    let a := U.map (HomologicalComplex.homologyMap φ n)
    let b := HomologicalComplex.homologyMap (F.map φ) n
    let c := HomologicalComplex.homologyMap eK.hom n
    let d := HomologicalComplex.homologyMap eL.hom n
    let m := HomologicalComplex.homologyMap φ' n
    have hNative : a ≫ hL.inv = hK.inv ≫ b := by
      have h := η.inv.naturality φ
      change a ≫ hL.inv = hK.inv ≫ b at h
      exact h
    have hComponents : b ≫ d = c ≫ m :=
      (HomologicalComplex.homologyMap_comp (F.map φ) eL.hom n).symm.trans
        ((congrArg (fun ψ : F.obj K ⟶ L' => HomologicalComplex.homologyMap ψ n) hφ).trans
          (HomologicalComplex.homologyMap_comp eK.hom φ' n))
    change a ≫ (hL.inv ≫ d) = (hK.inv ≫ c) ≫ m
    exact (Category.assoc a hL.inv d).symm.trans
      ((congrArg (fun ψ : U.obj (K.homology n) ⟶ (F.obj L).homology n => ψ ≫ d)
        hNative).trans
          ((Category.assoc hK.inv b d).trans
            ((congrArg (fun ψ : (F.obj K).homology n ⟶ L'.homology n => hK.inv ≫ ψ)
              hComponents).trans ((Category.assoc hK.inv c m).symm))))
  let R₀ := connesMixedTotal k A
  let N₀ := normalizedMixedTotal k A
  let C₀ := cyclicTotal k A
  let R := ((HomologicalComplex₂.total
      (((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A))) (ComplexShape.down ℕ))
  let N := ((HomologicalComplex₂.total
      (((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k A))) (ComplexShape.down ℕ))
  let C := ((HomologicalComplex₂.total
      (((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A))) (ComplexShape.down ℕ))
  let eR : F.obj R₀ ≅ R := connesMixedTotalLiftIso.{lift} k A
  let eN : F.obj N₀ ≅ N := normalizedMixedTotalLiftIso.{lift} k A
  let eC : F.obj C₀ ≅ C := cyclicTotalLiftIso.{lift} k A
  let q₀ : R₀ ⟶ N₀ := normalizedMixedTotalProjection k A
  let q : R ⟶ N := normalizedMixedTotalProjectionLift.{lift} k A
  let i₀ : R₀ ⟶ C₀ := mixedToCyclic k A
  let i : R ⟶ C := mixedToCyclicLift.{lift} k A
  let L_R : U.obj (R₀.homology n) ≅ R.homology n := connesMixedHomologyLiftIso.{lift} k A n
  let L_N : U.obj (N₀.homology n) ≅ N.homology n := normalizedMixedHomologyLiftIso.{lift} k A n
  let L_C : U.obj (C₀.homology n) ≅ C.homology n := cyclicHomologyLiftIso.{lift} k A n
  let Q₀ : R₀.homology n ≅ N₀.homology n := asIso (HomologicalComplex.homologyMap q₀ n)
  let Q : R.homology n ≅ N.homology n := asIso (HomologicalComplex.homologyMap q n)
  let I₀ : R₀.homology n ⟶ C₀.homology n := HomologicalComplex.homologyMap i₀ n
  let I : R.homology n ⟶ C.homology n := HomologicalComplex.homologyMap i n
  let E₀ : N₀.homology n ≅ C₀.homology n := normalizedMixedCyclicHomologyIso k A n
  let E : N.homology n ≅ C.homology n := normalizedMixedCyclicHomologyLiftIso.{lift} k A n
  have hqTotal : F.map q₀ ≫ eN.hom = eR.hom ≫ q :=
    map_normalizedMixedTotalProjection_lift.{lift} k A
  have hiTotal : F.map i₀ ≫ eC.hom = eR.hom ≫ i := map_mixedToCyclic_lift.{lift} k A
  have hq : U.map Q₀.hom ≫ L_N.hom = L_R.hom ≫ Q.hom := by
    have h := hTransport q₀ q eR eN hqTotal
    change U.map Q₀.hom ≫ L_N.hom = L_R.hom ≫ Q.hom at h
    exact h
  have hi : U.map I₀ ≫ L_C.hom = L_R.hom ≫ I := by
    have h := hTransport i₀ i eR eC hiTotal
    change U.map I₀ ≫ L_C.hom = L_R.hom ≫ I at h
    exact h
  have hE₀ : E₀.hom = Q₀.inv ≫ I₀ := normalizedMixedCyclicHomologyIso_hom k A n
  have hE : E.hom = Q.inv ≫ I := normalizedMixedCyclicHomologyLiftIso_hom.{lift} k A n
  have hCancel₀ : Q₀.hom ≫ E₀.hom = I₀ :=
    (congrArg (fun φ : N₀.homology n ⟶ C₀.homology n => Q₀.hom ≫ φ) hE₀).trans
      (Q₀.hom_inv_id_assoc I₀)
  have hCancel : Q.hom ≫ E.hom = I :=
    (congrArg (fun φ : N.homology n ⟶ C.homology n => Q.hom ≫ φ) hE).trans
      (Q.hom_inv_id_assoc I)
  change L_N.hom ≫ E.hom = U.map E₀.hom ≫ L_C.hom
  apply (cancel_epi (U.map Q₀.hom)).1
  have hLeft : U.map Q₀.hom ≫ (L_N.hom ≫ E.hom) = L_R.hom ≫ I :=
    (Category.assoc (U.map Q₀.hom) L_N.hom E.hom).symm.trans
      ((congrArg (fun φ : U.obj (R₀.homology n) ⟶ N.homology n => φ ≫ E.hom) hq).trans
        ((Category.assoc L_R.hom Q.hom E.hom).trans
          (congrArg (fun φ : R.homology n ⟶ C.homology n => L_R.hom ≫ φ) hCancel)))
  have hMapped : U.map Q₀.hom ≫ U.map E₀.hom = U.map I₀ :=
    (U.map_comp Q₀.hom E₀.hom).symm.trans (congrArg U.map hCancel₀)
  have hRight : U.map Q₀.hom ≫ (U.map E₀.hom ≫ L_C.hom) = L_R.hom ≫ I :=
    (Category.assoc (U.map Q₀.hom) (U.map E₀.hom) L_C.hom).symm.trans
      ((congrArg (fun φ : U.obj (R₀.homology n) ⟶ U.obj (C₀.homology n) => φ ≫ L_C.hom)
        hMapped).trans hi)
  exact hLeft.trans hRight.symm

section ComparisonNaturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let `k` be a commutative ring and `A,B` unital rings with
`k`-module actions compatible with multiplication on both sides:
`r • (ab)=(r • a)b=a(r • b)`. For a nonunital `k`-algebra map
`f : A →ₙₐ[k] B`, assume `hOne : f(1_A)=1_B`. In degree `n ∈ ℕ`,
let `mN_f` be its map on normalized mixed-total homology and `HC_f`
its cyclic-homology map. The canonical comparisons
`E_A : H_n(normalizedMixedTotal(k,A)) ≅ HC_n(k,A)` and `E_B` satisfy
`E_B(mN_f(x))=HC_f(E_A(x))` for every `x`.
This is the commuting normalized-to-cyclic comparison square. -/
theorem normalizedMixedCyclicHomologyIso_naturality
    (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ)
    (x : (normalizedMixedTotal k A).homology n) :
    let E_A : (normalizedMixedTotal k A).homology n ≅ cyclicHomology k A n :=
      normalizedMixedCyclicHomologyIso k A n
    let E_B : (normalizedMixedTotal k B).homology n ≅ cyclicHomology k B n :=
      normalizedMixedCyclicHomologyIso k B n
    let mN₀ : (normalizedMixedTotal k A).homology n →ₗ[k]
        (normalizedMixedTotal k B).homology n := normalizedMixedHomologyLinearMap f hOne n
    let mC₀ : cyclicHomology k A n →ₗ[k] cyclicHomology k B n := cyclicHomologyLinearMap f n
    E_B.hom.hom (mN₀ x) = mC₀ (E_A.hom.hom x) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let NA₀ : ModuleCat.{max u v} k := (normalizedMixedTotal k A).homology n
  let NB₀ : ModuleCat.{max u w} k := (normalizedMixedTotal k B).homology n
  let CA₀ : ModuleCat.{max u v} k := cyclicHomology k A n
  let CB₀ : ModuleCat.{max u w} k := cyclicHomology k B n
  let NA : ModuleCat.{max u v w} k :=
    (HomologicalComplex₂.total
      (((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k A)) (ComplexShape.down ℕ)).homology n
  let NB : ModuleCat.{max u v w} k :=
    (HomologicalComplex₂.total
      (((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (normalizedMixedBicomplex k B)) (ComplexShape.down ℕ)).homology n
  let CA : ModuleCat.{max u v w} k :=
    (HomologicalComplex₂.total
      (((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)) (ComplexShape.down ℕ)).homology n
  let CB : ModuleCat.{max u v w} k :=
    (HomologicalComplex₂.total
      (((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cyclicBicomplex k B)) (ComplexShape.down ℕ)).homology n
  let L_NA : UA.obj NA₀ ≅ NA := normalizedMixedHomologyLiftIso.{w} k A n
  let L_NB : UB.obj NB₀ ≅ NB := normalizedMixedHomologyLiftIso.{v} k B n
  let L_CA : UA.obj CA₀ ≅ CA := cyclicHomologyLiftIso.{w} k A n
  let L_CB : UB.obj CB₀ ≅ CB := cyclicHomologyLiftIso.{v} k B n
  let E_A : NA₀ ≅ CA₀ := normalizedMixedCyclicHomologyIso k A n
  let E_B : NB₀ ≅ CB₀ := normalizedMixedCyclicHomologyIso k B n
  let E : NA ≅ CA := normalizedMixedCyclicHomologyLiftIso.{w} k A n
  let E' : NB ≅ CB := normalizedMixedCyclicHomologyLiftIso.{v} k B n
  let mN : NA ⟶ NB := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (normalizedMixedBicomplexMapLift f hOne)
      (ComplexShape.down ℕ)) n
  let mC : CA ⟶ CB := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)) n
  let mN₀ : NA₀ →ₗ[k] NB₀ := normalizedMixedHomologyLinearMap f hOne n
  let mC₀ : CA₀ →ₗ[k] CB₀ := cyclicHomologyLinearMap f n
  let x' : NB₀ := mN₀ x
  let y : CB₀ := mC₀ (E_A.hom.hom x)
  let xa : UA.obj NA₀ := ULift.up x
  let xb : UB.obj NB₀ := ULift.up x'
  let za : NA := L_NA.hom.hom xa
  let ca : UA.obj CA₀ := ULift.up (E_A.hom.hom x)
  have hLiftA : L_NA.hom ≫ E.hom = UA.map E_A.hom ≫ L_CA.hom :=
    normalizedMixedCyclicHomologyLiftIso_lift.{w} k A n
  have hLiftB : L_NB.hom ≫ E'.hom = UB.map E_B.hom ≫ L_CB.hom :=
    normalizedMixedCyclicHomologyLiftIso_lift.{v} k B n
  have hA : E.hom.hom za = L_CA.hom.hom ca := by
    have h := DFunLike.congr_fun
      (congrArg (fun φ : UA.obj NA₀ ⟶ CA => φ.hom) hLiftA) xa
    change E.hom.hom (L_NA.hom.hom xa) =
      L_CA.hom.hom ((UA.map E_A.hom).hom xa) at h
    exact h
  have hB : E'.hom.hom (L_NB.hom.hom xb) =
      L_CB.hom.hom (ULift.up (E_B.hom.hom x')) := by
    have h := DFunLike.congr_fun
      (congrArg (fun φ : UB.obj NB₀ ⟶ CB => φ.hom) hLiftB) xb
    change E'.hom.hom (L_NB.hom.hom xb) =
      L_CB.hom.hom ((UB.map E_B.hom).hom xb) at h
    exact h
  have hN : L_NB.hom.hom xb = mN.hom za :=
    normalizedMixedHomologyLinearMap_lift f hOne n x
  have hC : L_CB.hom.hom (ULift.up y) = mC.hom (L_CA.hom.hom ca) :=
    cyclicHomologyLinearMap_lift f n (E_A.hom.hom x)
  have hNaturality : mN ≫ E'.hom = E.hom ≫ mC :=
    normalizedMixedCyclicHomologyLiftIso_naturality f hOne n
  have hNat : E'.hom.hom (mN.hom za) = mC.hom (E.hom.hom za) := by
    have h := DFunLike.congr_fun (congrArg (fun φ : NA ⟶ CB => φ.hom) hNaturality) za
    change E'.hom.hom (mN.hom za) = mC.hom (E.hom.hom za) at h
    exact h
  have hValue : L_CB.hom.hom (ULift.up (E_B.hom.hom x')) =
      L_CB.hom.hom (ULift.up y) :=
    hB.symm.trans ((congrArg E'.hom.hom hN).trans
      (hNat.trans ((congrArg mC.hom hA).trans hC.symm)))
  let u₀ : UB.obj CB₀ := ULift.up (E_B.hom.hom x')
  let u₁ : UB.obj CB₀ := ULift.up y
  have hUp : u₀ = u₁ :=
    (ModuleCat.inv_hom_apply L_CB u₀).symm.trans
      ((congrArg L_CB.inv.hom hValue).trans (ModuleCat.inv_hom_apply L_CB u₁))
  change E_B.hom.hom (mN₀ x) = mC₀ (E_A.hom.hom x)
  exact congrArg (fun z : UB.obj CB₀ => z.down) hUp

/-- Let `k` be a commutative ring and `A,B` unital rings with
compatible central `k`-actions. Let `f : A →ₙₐ[k] B` satisfy
`hOne : f(1_A)=1_B`. In the common height `max(u,v,w)`, denote
its full and normalized chain maps by `Φ,Φ̄`, and the normalization
projections by `p_A,p_B`. The canonical normalized-to-cyclic comparisons
satisfy the linear-map equality
`E_B ∘ mN_f = HC_f ∘ E_A` in degree `n`, on the algebra
homology carriers. -/
theorem normalizedMixedCyclicHomologyIso_linear_naturality
    (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (normalizedMixedCyclicHomologyIso k B n).hom.hom.comp
        (normalizedMixedHomologyLinearMap f hOne n) =
      (cyclicHomologyLinearMap f n).comp (normalizedMixedCyclicHomologyIso k A n).hom.hom := by
  ext x
  exact normalizedMixedCyclicHomologyIso_naturality f hOne n x

end ComparisonNaturality

end UnitalAlgebra

end ModuleCat.Algebra.Hochschild.NonUnital
