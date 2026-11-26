/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.GeneralizedTrace
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Coefficients
public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Corner
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import Mathlib.LinearAlgebra.Multilinear.Pi
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.List.OfFn

/-!
# Generalized matrix trace on coefficient Hochschild complexes

Let k be a commutative ring, A an associative unital k-algebra, M an
A-bimodule with commuting k-linear actions, and ι a finite matrix index
type. Write C_n(A,M) = M ⊗[k] A^⊗n. The generalized trace
T_n : C_n(Mat_ι(A),Mat_ι(M)) → C_n(A,M) sums the entries of all closed
index cycles:
T_n(X ⊗ a₁ ⊗ ⋯ ⊗ aₙ) =
∑_(i₀,…,iₙ) X_(i₀,i₁) ⊗ (a₁)_(i₁,i₂) ⊗ ⋯ ⊗ (aₙ)_(iₙ,i₀).
In degree zero this is the additive trace of X.

The maps T_n commute with every Hochschild face. The first face uses
the right coefficient action, the interior faces multiply adjacent
algebra factors in their given order, and the last face uses the left
coefficient action. Consequently they commute with b = ∑ᵢ(−1)^i δᵢ.

Lifting the coefficient modules to H = max(u,v,w,z), for the independent
worlds of k, A, M and ι, gives the trace chain map. For b ∈ ι, the
diagonal corner chain map K_b satisfies T ∘ K_b = id.

Reference: Loday, *Cyclic Homology*, §1.2.2.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators TensorProduct

namespace ModuleCat.Algebra.Hochschild.Matrix

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

universe u v w z

variable (k : Type u) [CommRing k]

section TensorGenerators

variable (A : Type v) [AddCommGroup A] [Module k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Let k be a commutative ring, A, M and N be k-modules, ι a
finite index type and n ≥ 0. Two k-linear maps from
Mat_ι(M) ⊗[k] Mat_ι(A)^⊗n to N are equal if they agree on every tensor
(U₀·m) ⊗ (U₁·a₁) ⊗ ⋯ ⊗ (Uₙ·aₙ), where Uⱼ ∈ Mat_ι(k) and
(U·x)ᵢⱼ = Uᵢⱼ • x. The carrier worlds of A, M, N and ι are independent. -/
theorem matrix_tensor_ext [Finite ι] {N : Type*} [AddCommGroup N] [Module k N]
    {n : ℕ}
    {f g : Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) →ₗ[k] N}
    (h : ∀ (U₀ : Matrix ι ι k) (m : M) (U : Fin n → Matrix ι ι k) (a : Fin n → A),
      f ((U₀.map (fun c => c • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t))) =
      g ((U₀.map (fun c => c • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t)))) : f = g := by
  classical
  cases nonempty_fintype ι
  apply TensorProduct.ext
  apply Matrix.ext_linearMap
  intro i j
  apply LinearMap.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.pi_ext
  intro r
  apply MultilinearMap.pi_ext
  intro s
  apply MultilinearMap.ext
  intro a
  change f (Matrix.single i j m ⊗ₜ[k]
    PiTensorProduct.tprod k
      (fun t => Matrix.of (Pi.single (r t) (Pi.single (s t) (a t))))) =
      g (Matrix.single i j m ⊗ₜ[k]
        PiTensorProduct.tprod k
          (fun t => Matrix.of (Pi.single (r t) (Pi.single (s t) (a t)))))
  have hm : (Matrix.single i j (1 : k)).map (fun c => c • m) =
      Matrix.single i j m := by
    change (Matrix.single i j (1 : k)).map (LinearMap.toSpanSingleton k M m) = _
    simpa only [LinearMap.toSpanSingleton_apply_one] using
      (Matrix.map_single i j (1 : k) (LinearMap.toSpanSingleton k M m))
  have hU (t : Fin n) :
      (Matrix.single (r t) (s t) (1 : k)).map (fun c => c • a t) =
        Matrix.of (Pi.single (r t) (Pi.single (s t) (a t))) := by
    change (Matrix.single (r t) (s t) (1 : k)).map
      (LinearMap.toSpanSingleton k A (a t)) = _
    calc
      _ = Matrix.single (r t) (s t) (a t) := by
        simpa only [LinearMap.toSpanSingleton_apply_one] using
          (Matrix.map_single (r t) (s t) (1 : k) (LinearMap.toSpanSingleton k A (a t)))
      _ = _ := Matrix.single_eq_of_single_single (r t) (s t) (a t)
  simpa only [hm, hU] using
    h (Matrix.single i j 1) m (fun t => Matrix.single (r t) (s t) 1) a

end TensorGenerators

variable (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

/-- Coefficient matrices over a k-module M carry the pointwise
ground action (λ • X)ᵢⱼ = λ • Xᵢⱼ. -/
local instance traceGroundMatrixModule : Module k (Matrix ι ι M) := inferInstance
/-- For a left A-module M and finite ι, the left matrix-algebra
action on Mat_ι(M) is (B • X)ᵢⱼ = ∑ₚ Bᵢₚ • Xₚⱼ. -/
local instance traceActorLeftModule : Module (Matrix ι ι A) (Matrix ι ι M) :=
  Coefficients.leftModule A M ι
/-- For a right A-module M and finite ι, the opposite matrix-algebra
action on Mat_ι(M) is (op B • X)ᵢⱼ = ∑ₚ op(Bₚⱼ) • Xᵢₚ. -/
local instance traceActorRightModule : Module (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.rightModule A M ι
local instance : SMulCommClass (Matrix ι ι A) (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.commute A M ι
local instance : IsScalarTower k (Matrix ι ι A) (Matrix ι ι M) :=
  Coefficients.leftTower A M ι k
local instance : IsScalarTower k (Matrix ι ι A)ᵐᵒᵖ (Matrix ι ι M) :=
  Coefficients.rightTower A M ι k
omit [DecidableEq ι] in
private theorem scaled_mul (U V : Matrix ι ι k) (a b : A) :
    (U.map (fun c => c • a)) * (V.map (fun c => c • b)) =
      (U * V).map (fun c => c • (a * b)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  exact smul_mul_smul_comm _ _ _ _
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M] [Module Aᵐᵒᵖ M] in
private theorem scaled_left (U V : Matrix ι ι k) (a : A) (m : M) :
    (U.map (fun c => c • a)) • (V.map (fun c => c • m)) =
      (U * V).map (fun c => c • (a • m)) := by
  ext i j
  rw [Coefficients.left_smul_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_assoc, smul_comm a, smul_smul]
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [Module A M] in
private theorem scaled_right (U V : Matrix ι ι k) (a : A) (m : M) :
    MulOpposite.op (V.map (fun c => c • a)) • (U.map (fun c => c • m)) =
      (U * V).map (fun c => c • (MulOpposite.op a • m)) := by
  ext i j
  rw [Coefficients.right_smul_apply]
  simp only [Matrix.mul_apply, MulOpposite.unop_op, Matrix.map_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  have hop (c : k) : MulOpposite.op (c • a) = c • MulOpposite.op a := rfl
  rw [hop, smul_assoc, smul_comm (MulOpposite.op a), smul_smul, mul_comm]

/-- For any monoid D, a tuple a₀,…,aₙ in D and i ∈ {0,…,n−1},
replace the adjacent entries aᵢ,a_(i+1) by their ordered product
aᵢ a_(i+1). The product of the resulting length-n tuple equals
a₀ ⋯ aₙ. No commutativity of D is assumed. -/
theorem product_mulAdjacent {D : Type*} [Monoid D] :
    ∀ (n : ℕ) (i : Fin n) (a : Fin (n + 1) → D),
      (List.ofFn (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i a)).prod =
        (List.ofFn a).prod := by
  intro n
  induction n with
  | zero =>
      intro i a
      exact i.elim0
  | succ n ih =>
      intro i a
      refine Fin.cases ?_ (fun j => ?_) i
      · have h : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent (0 : Fin (n + 1)) a =
            Fin.cons (α := fun _ => D) (a 0 * a 1) (fun t : Fin n => a t.succ.succ) := by
          funext t
          refine Fin.cases ?_ (fun l => ?_) t
          · simp [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent]
          · simp [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent,
              Fin.succ_ne_zero, Fin.one_succAbove_succ]
        rw [h, List.ofFn_cons, List.prod_cons]
        simp only [List.ofFn_succ, List.prod_cons, Fin.succ_zero_eq_one]
        exact mul_assoc _ _ _
      · have h : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent j.succ a =
            Fin.cons (α := fun _ => D) (a 0)
              (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent j
                (fun t => a t.succ)) := by
          funext t
          refine Fin.cases ?_ (fun l => ?_) t
          · have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
              fun he => Fin.succ_ne_zero j he.symm
            simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent,
              ite_eq_right hzero, Fin.cons_zero, Fin.succ_succAbove_zero]
          · by_cases hl : l = j
            · subst l
              simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent,
                ite_true, Fin.cons_succ, Fin.castSucc_succ]
            · have hsucc : l.succ ≠ j.succ :=
                fun he => hl (Fin.succ_inj.mp he)
              simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent,
                ite_eq_right hsucc, ite_eq_right hl, Fin.cons_succ, Fin.succ_succAbove_succ]
        rw [h, List.ofFn_cons, List.prod_cons, ih]
        simpa only [List.prod_cons] using
          (congrArg (List.prod : List D → D) (List.ofFn_succ (f := a))).symm

/-- For an A-bimodule M with commuting k-linear actions, the
degree traces satisfy T_n ∘ δ₀^Mat = δ₀^A ∘ T_(n+1).
The first face sends m ⊗ a₁ ⊗ ⋯ ⊗ a_(n+1) to
(m·a₁) ⊗ a₂ ⊗ ⋯ ⊗ a_(n+1), where m·a = op(a) • m. -/
theorem trace_face_first (n : ℕ) :
    (generalizedTrace k ι n).comp (Coefficients.face A M ι k n 0).hom =
      (ModuleCat.Algebra.Hochschild.face k A M n 0).hom.comp
        (generalizedTrace k ι (n + 1)) := by
  apply matrix_tensor_ext k A M ι
  intro U₀ m U a
  simp only [LinearMap.comp_apply]
  change generalizedTrace k ι n
      ((ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M) n 0).hom
        ((U₀.map (fun c => c • m)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t)))) = _
  rw [ModuleCat.Algebra.Hochschild.face_first_tprod, scaled_right]
  change generalizedTrace k ι n
      (((U₀ * U 0).map (fun c => c • (MulOpposite.op (a 0) • m))) ⊗ₜ[k]
        PiTensorProduct.tprod k
          (fun j : Fin n => (U j.succ).map (fun c => c • a j.succ))) = _
  calc
    _ = Matrix.trace ((U₀ * U 0) * (List.ofFn (fun j : Fin n => U j.succ)).prod) •
        ((MulOpposite.op (a 0) • m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j : Fin n => a j.succ)) :=
      generalizedTrace_scaled k ι n (U₀ * U 0) (fun j : Fin n => U j.succ)
        (MulOpposite.op (a 0) • m) (fun j : Fin n => a j.succ)
    _ = Matrix.trace (U₀ * (List.ofFn U).prod) •
        ((MulOpposite.op (a 0) • m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j : Fin n => a j.succ)) := by
      apply congrArg (fun c : k => c •
        ((MulOpposite.op (a 0) • m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j : Fin n => a j.succ)))
      rw [List.ofFn_succ (f := U), List.prod_cons]
      exact congrArg Matrix.trace (Matrix.mul_assoc U₀ (U 0) _)
    _ = _ := by
      rw [generalizedTrace_scaled k ι (n + 1) U₀ U m a, map_smul,
        ModuleCat.Algebra.Hochschild.face_first_tprod]
      rfl

/-- For an A-bimodule M with commuting k-linear actions and
i ∈ {0,…,n−1}, the interior face that replaces the algebra entries
a_(i+1),a_(i+2) by a_(i+1)a_(i+2) satisfies
T_n ∘ δ_(i+1)^Mat = δ_(i+1)^A ∘ T_(n+1).
The order of multiplication is retained for a noncommutative A. -/
theorem trace_face_inner (n : ℕ) (i : Fin n) :
    (generalizedTrace k ι n).comp
        (Coefficients.face A M ι k n i.castSucc.succ).hom =
      (ModuleCat.Algebra.Hochschild.face k A M n i.castSucc.succ).hom.comp
        (generalizedTrace k ι (n + 1)) := by
  apply matrix_tensor_ext k A M ι
  intro U₀ m U a
  simp only [LinearMap.comp_apply]
  change generalizedTrace k ι n
      ((ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M)
        n i.castSucc.succ).hom ((U₀.map (fun c => c • m)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t)))) = _
  rw [ModuleCat.Algebra.Hochschild.face_inner_tprod]
  have ht : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i
      (fun t => (U t).map (fun c => c • a t)) =
      (fun t => (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i U t).map
        (fun c => c • ModuleCat.Algebra.Hochschild.hochschildMulAdjacent i a t)) := by
    funext t
    by_cases h : t = i
    · subst t
      simpa only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent,
        ite_eq_left rfl, ite_true] using
        scaled_mul k A ι (U i.castSucc) (U i.succ) (a i.castSucc) (a i.succ)
    · simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, h, ite_false]
  rw [ht, generalizedTrace_scaled]
  rw [generalizedTrace_scaled, map_smul,
    ModuleCat.Algebra.Hochschild.face_inner_tprod]
  rw [product_mulAdjacent]

/-- For an A-bimodule M with commuting k-linear actions, the last
face sends m ⊗ a₁ ⊗ ⋯ ⊗ a_(n+1) to
(a_(n+1) • m) ⊗ a₁ ⊗ ⋯ ⊗ aₙ. It satisfies
T_n ∘ δ_(n+1)^Mat = δ_(n+1)^A ∘ T_(n+1), with the left matrix action
on the source coefficient and the left A-action on the target. -/
theorem trace_face_last (n : ℕ) :
    (generalizedTrace k ι n).comp
        (Coefficients.face A M ι k n (Fin.last (n + 1))).hom =
      (ModuleCat.Algebra.Hochschild.face k A M n (Fin.last (n + 1))).hom.comp
        (generalizedTrace k ι (n + 1)) := by
  apply matrix_tensor_ext k A M ι
  intro U₀ m U a
  simp only [LinearMap.comp_apply]
  change generalizedTrace k ι n
      ((ModuleCat.Algebra.Hochschild.face k (Matrix ι ι A) (Matrix ι ι M)
        n (Fin.last (n + 1))).hom ((U₀.map (fun c => c • m)) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun t => (U t).map (fun c => c • a t)))) = _
  rw [ModuleCat.Algebra.Hochschild.face_last_tprod, scaled_left]
  change generalizedTrace k ι n
      (((U (Fin.last n) * U₀).map (fun c => c • (a (Fin.last n) • m))) ⊗ₜ[k]
        PiTensorProduct.tprod k
          (fun j : Fin n => (U j.castSucc).map (fun c => c • a j.castSucc))) = _
  calc
    _ = Matrix.trace ((U (Fin.last n) * U₀) *
        (List.ofFn (fun j : Fin n => U j.castSucc)).prod) •
        ((a (Fin.last n) • m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j : Fin n => a j.castSucc)) :=
      generalizedTrace_scaled k ι n (U (Fin.last n) * U₀)
        (fun j : Fin n => U j.castSucc) (a (Fin.last n) • m)
        (fun j : Fin n => a j.castSucc)
    _ = Matrix.trace (U₀ * (List.ofFn U).prod) •
        ((a (Fin.last n) • m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j : Fin n => a j.castSucc)) := by
      apply congrArg (fun c : k => c •
        ((a (Fin.last n) • m) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun j : Fin n => a j.castSucc)))
      rw [List.ofFn_succ' U, List.prod_concat]
      change Matrix.trace ((U (Fin.last n) * U₀) *
          (List.ofFn (fun j : Fin n => U j.castSucc)).prod) =
        Matrix.trace (U₀ *
          ((List.ofFn (fun j : Fin n => U j.castSucc)).prod * U (Fin.last n)))
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = _ := by
      rw [generalizedTrace_scaled k ι (n + 1) U₀ U m a, map_smul,
        ModuleCat.Algebra.Hochschild.face_last_tprod]
      rfl

/-- Let k be a commutative ring, A a k-algebra and M an
A-bimodule whose commuting actions are k-linear. For every n ≥ 0 and
i ∈ {0,…,n+1}, the trace maps satisfy
T_n ∘ δᵢ^Mat = δᵢ^A ∘ T_(n+1) from
C_(n+1)(Mat_ι(A),Mat_ι(M)) to C_n(A,M). -/
theorem trace_face_comm (n : ℕ) (i : Fin (n + 2)) :
    (generalizedTrace k ι n).comp (Coefficients.face A M ι k n i).hom =
      (ModuleCat.Algebra.Hochschild.face k A M n i).hom.comp
        (generalizedTrace k ι (n + 1)) := by
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
  · exact trace_face_first k A M ι n
  · simpa only [Fin.succ_last] using trace_face_last k A M ι n
  · exact trace_face_inner k A M ι n l

/-- For a k-algebra A, a compatible A-bimodule M and finite
matrix index type ι, the trace maps satisfy
T_n ∘ b_n^Mat = b_n^A ∘ T_(n+1) for every n ≥ 0, where
b_n : C_(n+1) → C_n is ∑_(i=0)^(n+1) (−1)^i δᵢ.
The cyclic last face is included in this sum. -/
theorem trace_boundary_comm (n : ℕ) :
    (generalizedTrace k ι n).comp
        (ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A) (Matrix ι ι M) n).hom =
      (ModuleCat.Algebra.Hochschild.boundary k A M n).hom.comp
        (generalizedTrace k ι (n + 1)) := by
  apply LinearMap.ext
  intro x
  rw [ModuleCat.Algebra.Hochschild.boundary_eq_sum,
    ModuleCat.Algebra.Hochschild.boundary_eq_sum]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun y => (-1 : ℤ) ^ i.val • y)
    (LinearMap.congr_fun (trace_face_comm k A M ι n i) x)

/-- For independent carrier worlds u, v, w and z of k, A, M
and finite ι, put H = max(u,v,w,z). The lifted degree trace is
ULift^H Mat_ι(M) ⊗[k] Mat_ι(A)^⊗n →
ULift^H M ⊗[k] A^⊗n. It removes the source coefficient lift, applies
the closed-cycle trace T_n, and lifts the target coefficient. -/
def traceLinearLift (n : ℕ) :
    ULift.{max u v w z} (Matrix ι ι M) ⊗[k] TensorPower k n (Matrix ι ι A) →ₗ[k]
      ULift.{max u v w z} M ⊗[k] TensorPower k n A := by
  let eS : ULift.{max u v w z} (Matrix ι ι M) ⊗[k]
      TensorPower k n (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n
  let eT : ULift.{max u v w z} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k A M n
  exact eT.symm.toLinearMap.comp ((generalizedTrace k ι n).comp eS.toLinearMap)

omit [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M]
  [IsScalarTower k Aᵐᵒᵖ M] in
/-- For k-modules M and A with A a k-algebra, and finite ι, let
d_S and d_T remove the coefficient lifts at H = max(u,v,w,z).
The lifted degree trace T_n^H satisfies d_T(T_n^H(x)) = T_n(d_S(x))
for every source tensor x. No left or right A-action on M is needed
for this value equality. -/
theorem traceLinearLift_down (n : ℕ)
    (x : ULift.{max u v w z} (Matrix ι ι M) ⊗[k]
      TensorPower k n (Matrix ι ι A)) :
    (show ULift.{max u v w z} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A from
        ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k A M n)
      (traceLinearLift k A M ι n x) =
    generalizedTrace k ι n
      ((show ULift.{max u v w z} (Matrix ι ι M) ⊗[k]
        TensorPower k n (Matrix ι ι A) ≃ₗ[k]
        Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) from
          ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv
            k (Matrix ι ι A) (Matrix ι ι M) n) x) := by
  simp only [traceLinearLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- For an A-bimodule M with commuting k-linear actions and
H = max(u,v,w,z), the lifted traces satisfy
b_n^A ∘ T_(n+1)^H = T_n^H ∘ b_n^Mat from the degree n+1 matrix
Hochschild term with coefficient ULift^H Mat_ι(M) to the degree n
A-term with coefficient ULift^H M. -/
theorem traceLinearLift_boundary_comm (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.boundary k A (ULift.{max u v w z} M) n).hom.comp
        (traceLinearLift k A M ι (n + 1)) =
      (traceLinearLift k A M ι n).comp
        (ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A)
          (ULift.{max u v w z} (Matrix ι ι M)) n).hom := by
  let eS (j : ℕ) : ULift.{max u v w z} (Matrix ι ι M) ⊗[k]
      TensorPower k j (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k j (Matrix ι ι A) :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) j
  let eT (j : ℕ) : ULift.{max u v w z} M ⊗[k] TensorPower k j A ≃ₗ[k]
      M ⊗[k] TensorPower k j A :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k A M j
  have hS :
      (ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A) (Matrix ι ι M) n).hom.comp
          (eS (n + 1)).toLinearMap =
        (eS n).toLinearMap.comp (ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A)
          (ULift.{max u v w z} (Matrix ι ι M)) n).hom :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv_boundary_comm
      k (Matrix ι ι A) (Matrix ι ι M) n
  have hT :
      (ModuleCat.Algebra.Hochschild.boundary k A M n).hom.comp
          (eT (n + 1)).toLinearMap =
        (eT n).toLinearMap.comp
          (ModuleCat.Algebra.Hochschild.boundary k A (ULift.{max u v w z} M) n).hom :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv_boundary_comm k A M n
  apply LinearMap.ext
  intro x
  apply (eT n).injective
  change eT n
    ((ModuleCat.Algebra.Hochschild.boundary k A (ULift.{max u v w z} M) n).hom
      (traceLinearLift k A M ι (n + 1) x)) =
    eT n (traceLinearLift k A M ι n
      ((ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A)
        (ULift.{max u v w z} (Matrix ι ι M)) n).hom x))
  calc
    _ = (ModuleCat.Algebra.Hochschild.boundary k A M n).hom
        (eT (n + 1) (traceLinearLift k A M ι (n + 1) x)) :=
      (LinearMap.congr_fun hT _).symm
    _ = (ModuleCat.Algebra.Hochschild.boundary k A M n).hom
        (generalizedTrace k ι (n + 1) (eS (n + 1) x)) :=
      congrArg (ModuleCat.Algebra.Hochschild.boundary k A M n).hom
        (traceLinearLift_down k A M ι (n + 1) x)
    _ = generalizedTrace k ι n
        ((ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A) (Matrix ι ι M) n).hom
          (eS (n + 1) x)) :=
      (LinearMap.congr_fun (trace_boundary_comm k A M ι n) _).symm
    _ = generalizedTrace k ι n
        (eS n ((ModuleCat.Algebra.Hochschild.boundary k (Matrix ι ι A)
          (ULift.{max u v w z} (Matrix ι ι M)) n).hom x)) :=
      congrArg (generalizedTrace k ι n) (LinearMap.congr_fun hS x)
    _ = _ := (traceLinearLift_down k A M ι n _).symm

/-- For a k-algebra A, an A-bimodule M with commuting k-linear
actions, and a finite matrix index type ι, the generalized trace
defines C_*(Mat_ι(A),ULift^H Mat_ι(M)) → C_*(A,ULift^H M),
where H = max(u,v,w,z) retains the independent worlds of k, A, M and ι.
Its differential is the full alternating Hochschild boundary. -/
def traceChainMap :
    ModuleCat.Algebra.Hochschild.chainComplex k (Matrix ι ι A)
        (ULift.{max u v w z} (Matrix ι ι M)) ⟶
      ModuleCat.Algebra.Hochschild.chainComplex k A (ULift.{max u v w z} M) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (traceLinearLift k A M ι n)) (by
    intro n
    rw [ModuleCat.Algebra.Hochschild.chainComplex_d,
      ModuleCat.Algebra.Hochschild.chainComplex_d]
    exact ModuleCat.hom_ext (traceLinearLift_boundary_comm k A M ι n))

/-- For the generalized trace chain map between the coefficient
Hochschild complexes, the underlying k-linear degree-n component is
the lifted degree trace T_n^H, with H = max(u,v,w,z). -/
theorem traceChainMap_f (n : ℕ) :
    ((traceChainMap k A M ι).f n).hom = traceLinearLift k A M ι n := rfl

/-- Let M be an A-bimodule with commuting k-linear actions. For
X ∈ Mat_ι(M) and aⱼ ∈ Mat_ι(A), removing the target coefficient lift
from the degree-n trace of up(X) ⊗ a₁ ⊗ ⋯ ⊗ aₙ gives
∑_(i₀,…,iₙ) X_(i₀,i₁) ⊗ (a₁)_(i₁,i₂) ⊗ ⋯ ⊗ (aₙ)_(iₙ,i₀).
The sum ranges over all ι-valued closed cycles, with indices modulo n+1;
in degree zero it is the additive matrix trace. -/
theorem traceChainMap_f_tprod (n : ℕ) (X : Matrix ι ι M)
    (a : Fin n → Matrix ι ι A) :
    (show ULift.{max u v w z} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A from
        ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k A M n)
      (((traceChainMap k A M ι).f n).hom (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    ∑ γ : Fin (n + 1) → ι, X (γ 0) (γ 1) ⊗ₜ[k]
      PiTensorProduct.tprod k (fun j => a j (γ j.succ) (γ (j.succ + 1))) := by
  let eT : ULift.{max u v w z} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k A M n
  let eS : ULift.{max u v w z} (Matrix ι ι M) ⊗[k]
      TensorPower k n (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n
  change eT (traceLinearLift k A M ι n
    (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  calc
    _ = generalizedTrace k ι n
        (eS (ULift.up X ⊗ₜ[k] PiTensorProduct.tprod k a)) :=
      traceLinearLift_down k A M ι n _
    _ = generalizedTrace k ι n (X ⊗ₜ[k] PiTensorProduct.tprod k a) :=
      congrArg (generalizedTrace k ι n)
        (ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv_tprod
          k (Matrix ι ι A) (Matrix ι ι M) n
          (ULift.up X : ULift.{max u v w z} (Matrix ι ι M)) a)
    _ = _ := generalizedTrace_tmul_tprod k ι n X a

/-- For a k-algebra A, an A-bimodule M with commuting k-linear
actions, finite ι and b ∈ ι, the diagonal-corner chain map followed
by the generalized trace is the identity on C_*(A,ULift^H M),
where H = max(u,v,w,z). Thus T ∘ K_b = id as chain maps. -/
theorem cornerChainMap_comp_trace (b : ι) :
    cornerChainMap k A M ι b ≫ traceChainMap k A M ι =
      𝟙 (ModuleCat.Algebra.Hochschild.chainComplex k A (ULift.{max u v w z} M)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  rcases m with ⟨m⟩
  let eT : ULift.{max u v w z} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A :=
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv k A M n
  apply eT.injective
  change eT (((traceChainMap k A M ι).f n).hom
      (((cornerChainMap k A M ι b).f n).hom
        (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    eT (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)
  rw [cornerChainMap_f_tprod, traceChainMap_f_tprod,
    ModuleCat.Algebra.Hochschild.coefficientUnliftEquiv_tprod]
  exact (generalizedTrace_tmul_tprod k ι n (cornerLinear k ι b m)
    (fun j => cornerLinear k ι b (a j))).symm.trans
      (generalizedTrace_corner_tprod k ι b n m a)

end ModuleCat.Algebra.Hochschild.Matrix
