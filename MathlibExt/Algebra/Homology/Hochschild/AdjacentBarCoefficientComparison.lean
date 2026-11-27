/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.EnvelopingCoefficient
public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarResolution
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor
public import MathlibExt.Algebra.Category.ModuleCat.CompatibleScalarRestriction
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Coefficient tensors of the enveloping bar resolution

Let `k` be a commutative ring, `A` an associative unital `k`-algebra,
and `M` a bimodule whose commuting left and right actions are
compatible with its ground-ring action. Set `E=A ⊗[k] Aᵐᵒᵖ` and
use the right action `m·(a ⊗ op(b))=b·m·a`.
Balanced tensoring the enveloping bar terms
`P_n=A ⊗[k] A^⊗(n+1)` gives
`M ⊗_E P_n ≅ M ⊗[k] A^⊗n`.

The first outer word factor acts on the right of `M` and the last
acts on its left. These identifications commute with the bar and
Hochschild differentials, giving a chain isomorphism. If `A` is
projective over `k`, the bar resolves the lifted regular `E`-module
`A` and identifies `HH_n(A,M)` with `L_n(M ⊗_E -)(A)`.
The coefficient module needs no flatness or projectivity condition.

## References

* J.-L. Loday, *Cyclic Homology*, §1.1, for the bar and enveloping-algebra description of Hochschild homology.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w w'

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. The coefficient balanced tensor is a functor from left
`E`-modules in height `max(u,v)` to `k`-modules in
`max(u,v,w)`, with value `M ⊗_E X`. -/
def coefficientTensorFunctor :
    ModuleCat.{max u v} (EnvelopingAlgebra k A) ⥤ ModuleCat.{max u v w} k := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  exact ModuleCat.BalancedTensor.functor k (EnvelopingAlgebra k A) M

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. The coefficient functor `F_M` is additive. -/
instance coefficientTensorFunctor_additive : (coefficientTensorFunctor k A M).Additive := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  exact ModuleCat.BalancedTensor.additive k (EnvelopingAlgebra k A) M

/-- Let `k` be a commutative ring, `A` an associative unital `k`-algebra,
`E=A ⊗[k] Aᵐᵒᵖ`, and `P_n=A ⊗[k] A^⊗(n+1)` with the outer
left `E`-action. Restricting the scalar action to `k` gives the outer
coordinate equivalence `P_n ≃ₗ[k] E ⊗[k] A^⊗n`, which records
first and last outer factors and the middle word. -/
def coefficientOuterCoordinate (n : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k (EnvelopingAlgebra k A))).obj
      (envelopingBarDegree k A n)) ≃ₗ[k]
        (EnvelopingAlgebra k A) ⊗[k] TensorPower k n A :=
  (((ModuleCat.restrictScalars (algebraMap k (EnvelopingAlgebra k A))).mapIso
    (envelopingBarDegreeEquivBaseChange k A n).toModuleIso).toLinearEquiv).trans
      (ModuleCat.compatibleRestrictScalarsEquiv k (EnvelopingAlgebra k A)
        ((EnvelopingAlgebra k A) ⊗[k] TensorPower k n A))

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `E=A ⊗[k] Aᵐᵒᵖ`. For a bar term element `x`,
the restricted coordinate equivalence satisfies
`coefficientOuterCoordinate_n(x)=TensorPower.outerCoordinate_n(x)`,
recording the first and opposite last factors in `E` and the middle
word in `A^⊗n`. -/
theorem coefficientOuterCoordinate_apply (n : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (EnvelopingAlgebra k A))).obj
      (envelopingBarDegree k A n)) :
    coefficientOuterCoordinate k A n x = TensorPower.outerCoordinate k A n x := rfl

/-- Let `k` be a commutative ring, `A` an associative unital `k`-algebra,
`E=A ⊗[k] Aᵐᵒᵖ`, and `P_n=A ⊗[k] A^⊗(n+1)` with the outer
left `E`-action. The outer coordinates are `E`-equivariant:
`ω_n(z·x)=z·ω_n(x)` for `z : E`, `x : P_n`. -/
theorem coefficientOuterCoordinate_smul (n : ℕ) (z : EnvelopingAlgebra k A)
    (x : envelopingBarDegree k A n) :
    coefficientOuterCoordinate k A n (z • x) = z • coefficientOuterCoordinate k A n x := by
  exact (envelopingBarDegreeEquivBaseChange k A n).map_smul z x

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Outer coordinates followed by balanced tensor cancellation
give `Ψ_n : F_M(P_n) ≃ₗ[k] M ⊗[k] A^⊗n`. -/
def coefficientTensorLevelEquiv (n : ℕ) :
    (coefficientTensorFunctor k A M).obj (envelopingBarDegree k A n) ≃ₗ[k]
      M ⊗[k] TensorPower k n A := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  letI := EnvelopingCoefficient.rightEnvelopingScalarComm k A M
  exact (TensorProduct.Balanced.congr (LinearEquiv.refl k M) (coefficientOuterCoordinate k A n)
    (fun _ _ => rfl) (coefficientOuterCoordinate_smul k A n)).trans
      (TensorProduct.Balanced.cancelEquiv k (EnvelopingAlgebra k A) M (TensorPower k n A))

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. For `m : M`, first outer factor `a₀ : A`, and tail
`a : Fin(n+1) → A`, the class `[m ⊗ (a₀ ⊗ tprod(a))]` maps to
`((a_last·m)·a₀) ⊗ tprod(init(a))` under `Ψ_n`. -/
theorem coefficientTensorLevelEquiv_mk_tprod (n : ℕ) (m : M) (a0 : A) (a : Fin (n + 1) → A) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    coefficientTensorLevelEquiv k A M n
        (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier
          m (a0 ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      (op a0 • (a (Fin.last n) • m)) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.init a) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  letI := EnvelopingCoefficient.rightEnvelopingScalarComm k A M
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  change TensorProduct.Balanced.cancelEquiv k (EnvelopingAlgebra k A) M (TensorPower k n A)
    (TensorProduct.Balanced.congr (LinearEquiv.refl k M) (coefficientOuterCoordinate k A n)
      (fun _ _ => rfl) (coefficientOuterCoordinate_smul k A n)
      (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier
        m (a0 ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
  erw [TensorProduct.Balanced.congr_mk]
  change TensorProduct.Balanced.cancelEquiv k (EnvelopingAlgebra k A) M (TensorPower k n A)
    (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M
      ((EnvelopingAlgebra k A) ⊗[k] TensorPower k n A) m
      (coefficientOuterCoordinate k A n (a0 ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
  erw [coefficientOuterCoordinate_apply, TensorPower.outerCoordinate_tprod,
    TensorProduct.Balanced.cancelEquiv_mk_tmul, EnvelopingCoefficient.rightEnvelopingModule_tmul]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. For `m : M`, `a : Fin n → A`, the inverse of `Ψ_n`
sends `m ⊗ tprod(a)` to the balanced class represented by
`m ⊗ (1 ⊗ tprod(snoc(a,1)))`. -/
theorem coefficientTensorLevelEquiv_symm_tprod (n : ℕ) (m : M) (a : Fin n → A) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    (coefficientTensorLevelEquiv k A M n).symm (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier
        m ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  apply (coefficientTensorLevelEquiv k A M n).injective
  rw [LinearEquiv.apply_symm_apply, coefficientTensorLevelEquiv_mk_tprod]
  simp only [Fin.snoc_last, Fin.init_snoc, op_one, one_smul]

private theorem mulAdjacent_lt {n : ℕ} (i j : Fin n) (a : Fin (n + 1) → A) (h : j < i) :
    hochschildMulAdjacent i a j = a j.castSucc := by
  rw [hochschildMulAdjacent, if_neg (ne_of_lt h), Fin.succAbove_succ_of_le i j (le_of_lt h)]

private theorem mulAdjacent_eq {n : ℕ} (i : Fin n) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent i a i = a i.castSucc * a i.succ := by
  rw [hochschildMulAdjacent, if_pos rfl]

private theorem mulAdjacent_gt {n : ℕ} (i j : Fin n) (a : Fin (n + 1) → A) (h : i < j) :
    hochschildMulAdjacent i a j = a j.succ := by
  rw [hochschildMulAdjacent, if_neg (ne_of_gt h), Fin.succAbove_succ_of_lt i j h]

omit [Ring A] in
private theorem dropFirst_snoc (n : ℕ) (a : Fin (n + 1) → A) (c : A) :
    hochschildDropFirst (Fin.snoc a c) = Fin.snoc (hochschildDropFirst a) c := by
  funext i
  refine Fin.lastCases
    (motive := fun t : Fin (n + 1) =>
      hochschildDropFirst (Fin.snoc (α := fun _ : Fin (n + 2) => A) a c) t =
        Fin.snoc (α := fun _ : Fin (n + 1) => A) (hochschildDropFirst a) c t)
    ?_ (fun j => ?_) i
  · simp only [hochschildDropFirst, Fin.succ_last, Fin.snoc_last]
  · simp only [hochschildDropFirst, Fin.succ_castSucc, Fin.snoc_castSucc]

private theorem mulAdjacent_snoc_castSucc (n : ℕ) (i : Fin n) (a : Fin (n + 1) → A) (c : A) :
    hochschildMulAdjacent i.castSucc (Fin.snoc a c) = Fin.snoc (hochschildMulAdjacent i a) c := by
  funext t
  refine Fin.lastCases
    (motive := fun t : Fin (n + 1) =>
      hochschildMulAdjacent i.castSucc (Fin.snoc (α := fun _ : Fin (n + 2) => A) a c) t =
        Fin.snoc (α := fun _ : Fin (n + 1) => A) (hochschildMulAdjacent i a) c t)
    ?_ (fun j => ?_) t
  · rw [mulAdjacent_gt A i.castSucc (Fin.last n) (Fin.snoc a c)
      (by simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_last] using i.isLt)]
    simp only [Fin.succ_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc]
    rcases lt_trichotomy j i with h | h | h
    · rw [mulAdjacent_lt A i.castSucc j.castSucc (Fin.snoc a c)
        (Fin.castSucc_lt_castSucc_iff.mpr h), mulAdjacent_lt A i j a h]
      simp only [Fin.snoc_castSucc]
    · subst j
      rw [mulAdjacent_eq A i.castSucc (Fin.snoc a c), mulAdjacent_eq A i a]
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
    · rw [mulAdjacent_gt A i.castSucc j.castSucc (Fin.snoc a c)
        (Fin.castSucc_lt_castSucc_iff.mpr h), mulAdjacent_gt A i j a h]
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc]

private theorem mulAdjacent_snoc_last (n : ℕ) (a : Fin (n + 1) → A) :
    hochschildMulAdjacent (Fin.last n) (Fin.snoc a (1 : A)) = a := by
  funext t
  refine Fin.lastCases
    (motive := fun t : Fin (n + 1) =>
      hochschildMulAdjacent (Fin.last n) (Fin.snoc (α := fun _ : Fin (n + 2) => A) a 1) t = a t)
    ?_ (fun j => ?_) t
  · rw [mulAdjacent_eq A (Fin.last n) (Fin.snoc a 1)]
    simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, mul_one]
  · rw [mulAdjacent_lt A (Fin.last n) j.castSucc (Fin.snoc a 1)
      (by simpa only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] using j.isLt)]
    simp only [Fin.snoc_castSucc]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. For an inverse representative with unit outer factors,
each adjacent bar face agrees under `Ψ_n` with the corresponding
coefficient Hochschild face, including the right first-endpoint
and left last-endpoint actions. -/
private theorem coefficientTensor_unit_face (n : ℕ) (i : Fin (n + 2)) (m : M) (a : Fin (n + 1) → A) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    ((coefficientTensorLevelEquiv k A M n).toLinearMap.comp
      (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m))
        ((NonUnital.regularFace k A (n + 1) i.castSucc).hom
          ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1))) = faceValue k A M n i m a := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  have hc := LinearMap.comp_apply (coefficientTensorLevelEquiv k A M n).toLinearMap
    (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m)
    ((NonUnital.regularFace k A (n + 1) i.castSucc).hom
      ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)))
  refine hc.trans ?_
  have he := congrFun (LinearEquiv.coe_toLinearMap (coefficientTensorLevelEquiv k A M n))
    (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m
      ((NonUnital.regularFace k A (n + 1) i.castSucc).hom
        ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1))))
  refine he.trans ?_
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
  · rw [Fin.castSucc_zero, NonUnital.regularFace_first_tprod, one_mul, dropFirst_snoc,
      coefficientTensorLevelEquiv_mk_tprod]
    simp only [Fin.snoc_apply_zero, Fin.snoc_last, Fin.init_snoc, one_smul, faceValue, Fin.cases_zero]
  · simp only [faceValue, Fin.cases_succ, Fin.lastCases_last, Fin.castSucc_succ]
    rw [NonUnital.regularFace_inner_tprod, mulAdjacent_snoc_last,
      coefficientTensorLevelEquiv_mk_tprod]
    simp only [op_one, one_smul, hochschildDropLast]
    rfl
  · simp only [faceValue, Fin.cases_succ, Fin.lastCases_castSucc, Fin.castSucc_succ]
    rw [NonUnital.regularFace_inner_tprod, mulAdjacent_snoc_castSucc,
      coefficientTensorLevelEquiv_mk_tprod]
    simp only [Fin.snoc_last, Fin.init_snoc, op_one, one_smul]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Applying `F_M` to the enveloping bar gives the coefficient
tensor chain complex with term `F_M(P_n)` and differential the
balanced tensor image of the bar differential. -/
def coefficientTensorComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (envelopingBar k A)

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. On a balanced representative `[m ⊗ x]` in degree `n+1`,
the mapped differential has value `[m ⊗ d_P(x)]` in degree `n`. -/
theorem coefficientTensorComplex_d_mk (n : ℕ) (m : M) (x : envelopingBarDegree k A (n + 1)) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (envelopingBarDegree k A (n + 1)).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    letI : Module k (envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    ((coefficientTensorComplex k A M).d (n + 1) n).hom
        (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A (n + 1)).carrier m x) =
      TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m
        (((envelopingBar k A).d (n + 1) n).hom x) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (envelopingBarDegree k A (n + 1)).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  exact ModuleCat.BalancedTensor.map_mk k (EnvelopingAlgebra k A) M
    ((envelopingBar k A).d (n + 1) n) m x

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. The degree equivalences satisfy
`Ψ_n ∘ d_(F_M(P)) = d_HH ∘ Ψ_(n+1)`, intertwining the full
bar and coefficient Hochschild boundaries. -/
theorem coefficientTensorLevelEquiv_boundary (n : ℕ) :
    (coefficientTensorLevelEquiv k A M n).toLinearMap.comp
        ((coefficientTensorComplex k A M).d (n + 1) n).hom =
      ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom.comp
        (coefficientTensorLevelEquiv k A M (n + 1)).toLinearMap := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (envelopingBarDegree k A (n + 1)).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  have h :
      ((coefficientTensorLevelEquiv k A M n).toLinearMap.comp
          ((coefficientTensorComplex k A M).d (n + 1) n).hom).comp
          (coefficientTensorLevelEquiv k A M (n + 1)).symm.toLinearMap =
        (((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom.comp
          (coefficientTensorLevelEquiv k A M (n + 1)).toLinearMap).comp
          (coefficientTensorLevelEquiv k A M (n + 1)).symm.toLinearMap := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change coefficientTensorLevelEquiv k A M n
        (((coefficientTensorComplex k A M).d (n + 1) n).hom
          ((coefficientTensorLevelEquiv k A M (n + 1)).symm
            (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom
        (coefficientTensorLevelEquiv k A M (n + 1)
          ((coefficientTensorLevelEquiv k A M (n + 1)).symm
            (m ⊗ₜ[k] PiTensorProduct.tprod k a)))
    erw [LinearEquiv.apply_symm_apply, coefficientTensorLevelEquiv_symm_tprod]
    let x : envelopingBarDegree k A (n + 1) :=
      (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)
    have hd := coefficientTensorComplex_d_mk k A M n m x
    have hstep := congrArg (coefficientTensorLevelEquiv k A M n) hd
    calc
      _ = coefficientTensorLevelEquiv k A M n
          (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m
            (((envelopingBar k A).d (n + 1) n).hom x)) := hstep
      _ = _ := by
        erw [envelopingBar_d_apply]
        let z : NonUnital.chainLevel k A A (n + 2) :=
          (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)
        have hsum := congrArg
          (fun d : NonUnital.chainLevel k A A (n + 2) ⟶ NonUnital.chainLevel k A A (n + 1) => d.hom z)
          (underlyingBar_d k A n)
        simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
          LinearMap.smul_apply] at hsum
        let U (i : Fin (n + 2)) : envelopingBarDegree k A n :=
          (NonUnital.regularFace k A (n + 1) i.castSucc).hom z
        have hsum' : ((underlyingBar k A).d (n + 1) n).hom z =
            (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • U i : envelopingBarDegree k A n) := hsum
        let L : (envelopingBarDegree k A n).carrier →ₗ[k] M ⊗[k] TensorPower k n A :=
          (coefficientTensorLevelEquiv k A M n).toLinearMap.comp
            (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m)
        have hvalue := congrArg L hsum'
        simp only [map_sum, map_zsmul] at hvalue
        erw [hvalue]
        erw [ModuleCat.Algebra.Hochschild.chainComplex_d, ModuleCat.Algebra.Hochschild.boundary_tprod]
        apply Finset.sum_congr rfl
        intro i _
        have hi := coefficientTensor_unit_face k A M n i m a
        have hL : L (U i) = faceValue k A M n i m a := by
          dsimp only [L, U, z, LinearMap.comp_apply]
          exact hi
        exact congrArg (fun t : M ⊗[k] TensorPower k n A => (-1 : ℤ) ^ i.val • t) hL
  exact (LinearMap.cancel_right
    (g := (coefficientTensorLevelEquiv k A M (n + 1)).symm.toLinearMap)
    (coefficientTensorLevelEquiv k A M (n + 1)).symm.surjective).1 h

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. The maps `Ψ_n` form a chain isomorphism
`F_M(P_*) ≅ C_*(A,M)` to the coefficient Hochschild complex. -/
def coefficientTensorChainIso : coefficientTensorComplex k A M ≅
    ModuleCat.Algebra.Hochschild.chainComplex k A M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientTensorLevelEquiv k A M n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      exact (coefficientTensorLevelEquiv_boundary k A M j).symm)

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. The degree-`n` forward component of the chain comparison
is the balanced tensor equivalence `Ψ_n`. -/
theorem coefficientTensorChainIso_hom_f (n : ℕ) :
    ((coefficientTensorChainIso k A M).hom.f n).hom =
      (coefficientTensorLevelEquiv k A M n).toLinearMap := rfl

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. The degree-`n` inverse component of the chain comparison
is `Ψ_n⁻¹`, given by insertion of unit outer factors. -/
theorem coefficientTensorChainIso_inv_f (n : ℕ) :
    ((coefficientTensorChainIso k A M).inv.f n).hom =
      (coefficientTensorLevelEquiv k A M n).symm.toLinearMap := rfl

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Assume `A` is projective as a `k`-module. The resolving
bar and chain comparison give
`HH_n(A,M) ≅ L_n(F_M)(A_reg)`, where `A_reg` is the lifted
left regular `E`-module with action `(a ⊗ op(b))·x=axb`. -/
def coefficientHochschildHomologyIsoDerived [Module.Projective k A] (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.chainComplex k A M).homology n ≅
      ((coefficientTensorFunctor k A M).leftDerived n).obj (regularEnvelopingTarget k A) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} k) (ComplexShape.down ℕ) n).mapIso
    (coefficientTensorChainIso k A M)).symm ≪≫
      ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj
        (coefficientTensorFunctor k A M) n).symm

section CoefficientNaturality

variable {N : Type w'} [AddCommGroup N] [Module k N] [Module A N] [Module Aᵐᵒᵖ N]
  [SMulCommClass A Aᵐᵒᵖ N] [SMulCommClass k A N] [SMulCommClass k Aᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Aᵐᵒᵖ N]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `N` be another such bimodule and `f : M →ₗ[k] N`
satisfy `f(a·m)=a·f(m)` and `f(m·a)=f(m)·a` for all `a,m`.
The coefficient carriers may have different heights. The induced linear map on each balanced bar term
`F_M(P_n) → F_N(P_n)` acts only on the coefficient factor. -/
def coefficientTensorLevelMap (f : M →ₗ[k] N)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) (n : ℕ) :
    (coefficientTensorFunctor k A M).obj (envelopingBarDegree k A n) →ₗ[k]
      (coefficientTensorFunctor k A N).obj (envelopingBarDegree k A n) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A N
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  exact TensorProduct.Balanced.map f LinearMap.id
    (fun r m => EnvelopingCoefficient.rightEnvelopingAction_naturality k A M f hLeft hRight r m)
    (fun _ _ => rfl)

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `N` be another such bimodule and `f : M →ₗ[k] N`
satisfy `f(a·m)=a·f(m)` and `f(m·a)=f(m)·a` for all `a,m`.
The coefficient carriers may have different heights. On every balanced representative, the coefficient map
has value `[m ⊗ x] ↦ [f(m) ⊗ x]`. -/
theorem coefficientTensorLevelMap_mk (f : M →ₗ[k] N)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) (n : ℕ) (m : M)
    (x : envelopingBarDegree k A n) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI := EnvelopingCoefficient.rightEnvelopingModule k A N
    letI : Module k (envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    coefficientTensorLevelMap k A M f hLeft hRight n
        (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier m x) =
      TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) N (envelopingBarDegree k A n).carrier (f m) x := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A N
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  exact TensorProduct.Balanced.map_mk f LinearMap.id
    (fun r m => EnvelopingCoefficient.rightEnvelopingAction_naturality k A M f hLeft hRight r m)
    (fun _ _ => rfl) m x

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `N` be another such bimodule and `f : M →ₗ[k] N`
satisfy `f(a·m)=a·f(m)` and `f(m·a)=f(m)·a` for all `a,m`.
The coefficient carriers may have different heights. The degreewise coefficient maps commute with the
mapped bar differentials: `d_N ∘ f_(n+1)=f_n ∘ d_M`. -/
theorem coefficientTensorLevelMap_boundary (f : M →ₗ[k] N)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) (n : ℕ) :
    ((coefficientTensorComplex k A N).d (n + 1) n).hom.comp
        (coefficientTensorLevelMap k A M f hLeft hRight (n + 1)) =
      (coefficientTensorLevelMap k A M f hLeft hRight n).comp
        ((coefficientTensorComplex k A M).d (n + 1) n).hom := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A N
  letI : Module k (envelopingBarDegree k A (n + 1)).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  apply TensorProduct.Balanced.hom_ext
  intro m x
  let y : envelopingBarDegree k A (n + 1) := x
  have hmap := coefficientTensorLevelMap_mk k A M f hLeft hRight (n + 1) m y
  have hdN := coefficientTensorComplex_d_mk k A N n (f m) y
  have hdM := coefficientTensorComplex_d_mk k A M n m y
  have hmap' := coefficientTensorLevelMap_mk k A M f hLeft hRight n m
    (((envelopingBar k A).d (n + 1) n).hom y)
  exact (congrArg ((coefficientTensorComplex k A N).d (n + 1) n).hom hmap).trans
    (hdN.trans ((hmap').symm.trans
      (congrArg (coefficientTensorLevelMap k A M f hLeft hRight n) hdM.symm)))

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `N` be another such bimodule and `f : M →ₗ[k] N`
satisfy `f(a·m)=a·f(m)` and `f(m·a)=f(m)·a` for all `a,m`.
The coefficient carriers may have different heights. The equivalences satisfy
`Ψ_n^N ∘ f_n = C_n(f) ∘ Ψ_n^M`, where the chain-level
Hochschild coefficient map applies `f` to `M` and fixes all
algebra word factors. -/
theorem coefficientTensorLevelEquiv_naturality (f : M →ₗ[k] N)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) (n : ℕ) :
    (coefficientTensorLevelEquiv k A N n).toLinearMap.comp
        (coefficientTensorLevelMap k A M f hLeft hRight n) =
      (ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) f n).comp
        (coefficientTensorLevelEquiv k A M n).toLinearMap := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A N
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  have h :
      ((coefficientTensorLevelEquiv k A N n).toLinearMap.comp
        (coefficientTensorLevelMap k A M f hLeft hRight n)).comp
          (coefficientTensorLevelEquiv k A M n).symm.toLinearMap =
      ((ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) f n).comp
        (coefficientTensorLevelEquiv k A M n).toLinearMap).comp
          (coefficientTensorLevelEquiv k A M n).symm.toLinearMap := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change coefficientTensorLevelEquiv k A N n
        (coefficientTensorLevelMap k A M f hLeft hRight n
          ((coefficientTensorLevelEquiv k A M n).symm (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) f n
        (coefficientTensorLevelEquiv k A M n
          ((coefficientTensorLevelEquiv k A M n).symm (m ⊗ₜ[k] PiTensorProduct.tprod k a)))
    rw [LinearEquiv.apply_symm_apply]
    let x : envelopingBarDegree k A n := (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)
    have hs := coefficientTensorLevelEquiv_symm_tprod k A M n m a
    have hmap := coefficientTensorLevelMap_mk k A M f hLeft hRight n m x
    have he := coefficientTensorLevelEquiv_mk_tprod k A N n (f m) (1 : A) (Fin.snoc a 1)
    simp only [Fin.snoc_last, Fin.init_snoc, op_one, one_smul] at he
    have hr := ModuleCat.Algebra.Hochschild.linearMap_tprod (NonUnitalAlgHom.id k A) f n m a
    have hr' : ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) f n
        (m ⊗ₜ[k] PiTensorProduct.tprod k a) = f m ⊗ₜ[k] PiTensorProduct.tprod k a := by
      exact hr
    exact (congrArg
      (fun z => coefficientTensorLevelEquiv k A N n
        (coefficientTensorLevelMap k A M f hLeft hRight n z)) hs).trans
      ((congrArg (coefficientTensorLevelEquiv k A N n) hmap).trans (he.trans hr'.symm))

  exact (LinearMap.cancel_right
    (g := (coefficientTensorLevelEquiv k A M n).symm.toLinearMap)
    (coefficientTensorLevelEquiv k A M n).symm.surjective).1 h

end CoefficientNaturality

section CommonWorldChainNaturality

variable {P : Type w} [AddCommGroup P] [Module k P] [Module A P] [Module Aᵐᵒᵖ P]
  [SMulCommClass A Aᵐᵒᵖ P] [SMulCommClass k A P] [SMulCommClass k Aᵐᵒᵖ P]
  [IsScalarTower k A P] [IsScalarTower k Aᵐᵒᵖ P]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `M′` be another such bimodule with the same carrier height
`w`, and `f : M →ₗ[k] M′` preserve both left and right `A`-actions. At the common coefficient height, the degreewise
balanced tensor maps form a chain map
`F_M(P_*) → F_M′(P_*)`. -/
def coefficientTensorComplexMap (f : M →ₗ[k] P)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) :
    coefficientTensorComplex k A M ⟶ coefficientTensorComplex k A P where
  f n := ModuleCat.ofHom (coefficientTensorLevelMap k A M f hLeft hRight n)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    exact coefficientTensorLevelMap_boundary k A M f hLeft hRight j

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `M′` be another such bimodule with the same carrier height
`w`, and `f : M →ₗ[k] M′` preserve both left and right `A`-actions. The Hochschild coefficient chain map applies `f` to
the coefficient and identity to every algebra factor. -/
def originalCoefficientChainMap (f : M →ₗ[k] P)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) :
    ModuleCat.Algebra.Hochschild.chainComplex k A M ⟶ ModuleCat.Algebra.Hochschild.chainComplex k A P :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k A) f n)) (by
      intro n
      rw [ModuleCat.Algebra.Hochschild.chainComplex_d, ModuleCat.Algebra.Hochschild.chainComplex_d]
      apply ModuleCat.hom_ext
      exact ModuleCat.Algebra.Hochschild.linearMap_boundary_comm (NonUnitalAlgHom.id k A) f
        hLeft (fun a m => hRight (op a) m) n)

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `M′` be another such bimodule with the same carrier height
`w`, and `f : M →ₗ[k] M′` preserve both left and right `A`-actions. The forward chain comparisons satisfy
`tensorBar(f) ≫ Ψ_M′ = Ψ_M ≫ Hochschild(f)`. -/
@[reassoc]
theorem coefficientTensorChainIso_hom_naturality (f : M →ₗ[k] P)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) :
    coefficientTensorComplexMap k A M f hLeft hRight ≫ (coefficientTensorChainIso k A P).hom =
      (coefficientTensorChainIso k A M).hom ≫ originalCoefficientChainMap k A M f hLeft hRight := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact coefficientTensorLevelEquiv_naturality k A M f hLeft hRight n

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. Let `M′` be another such bimodule with the same carrier height
`w`, and `f : M →ₗ[k] M′` preserve both left and right `A`-actions. The inverse chain comparisons satisfy
`Ψ_M⁻¹ ≫ tensorBar(f) = Hochschild(f) ≫ Ψ_M′⁻¹`. -/
@[reassoc]
theorem coefficientTensorChainIso_inv_naturality (f : M →ₗ[k] P)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m) :
    (coefficientTensorChainIso k A M).inv ≫ coefficientTensorComplexMap k A M f hLeft hRight =
      originalCoefficientChainMap k A M f hLeft hRight ≫ (coefficientTensorChainIso k A P).inv := by
  apply (cancel_mono (coefficientTensorChainIso k A P).hom).mp
  rw [Category.assoc, coefficientTensorChainIso_hom_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CommonWorldChainNaturality

end ModuleCat.Algebra.Hochschild.AdjacentBar

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Let `k` be a commutative ring, `A` an associative unital
`k`-algebra, and `M` an `A`-bimodule with commuting left/right actions
and a ground action compatible with both scalar towers. Put
`E=A ⊗[k] Aᵐᵒᵖ`, acting on the right of `M` by
`m·(a ⊗ op(b))=b·m·a`. Let `P_n=A ⊗[k] A^⊗(n+1)` be the
enveloping bar terms and `F_M(X)=M ⊗_E X`. For every degree-`n+1` element `z` of the coefficient
bar complex, `Ψ_n(d(z)) = d_HH(Ψ_(n+1)(z))`. -/
theorem coefficientTensorLevelEquiv_boundary_apply (n : ℕ)
    (z : (coefficientTensorComplex k A M).X (n + 1)) :
    coefficientTensorLevelEquiv k A M n
        (((coefficientTensorComplex k A M).d (n + 1) n).hom z) =
      ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom
        (coefficientTensorLevelEquiv k A M (n + 1) z) := by
  let I := coefficientTensorChainIso k A M
  have hn : (I.hom.f n).hom (((coefficientTensorComplex k A M).d (n + 1) n).hom z) =
      ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom
        ((I.hom.f (n + 1)).hom z) :=
    (ModuleCat.comp_apply ((coefficientTensorComplex k A M).d (n + 1) n) (I.hom.f n) z).symm.trans
      ((ConcreteCategory.congr_hom (I.hom.comm (n + 1) n).symm z).trans
        (ModuleCat.comp_apply (I.hom.f (n + 1))
          ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n) z))
  have h0 : (I.hom.f n).hom (((coefficientTensorComplex k A M).d (n + 1) n).hom z) =
      coefficientTensorLevelEquiv k A M n
        (((coefficientTensorComplex k A M).d (n + 1) n).hom z) :=
    (LinearMap.congr_fun (coefficientTensorChainIso_hom_f k A M n)
      (((coefficientTensorComplex k A M).d (n + 1) n).hom z)).trans
        (congrFun (LinearEquiv.coe_toLinearMap (coefficientTensorLevelEquiv k A M n))
          (((coefficientTensorComplex k A M).d (n + 1) n).hom z))
  have h1 : (I.hom.f (n + 1)).hom z = coefficientTensorLevelEquiv k A M (n + 1) z :=
    (LinearMap.congr_fun (coefficientTensorChainIso_hom_f k A M (n + 1)) z).trans
      (congrFun (LinearEquiv.coe_toLinearMap (coefficientTensorLevelEquiv k A M (n + 1))) z)
  exact h0.symm.trans (hn.trans (congrArg
    ((ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n).hom h1))

end ModuleCat.Algebra.Hochschild.AdjacentBar
