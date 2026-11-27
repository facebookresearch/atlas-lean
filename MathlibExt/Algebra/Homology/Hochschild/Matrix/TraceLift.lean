/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Trace

/-!
# Generalized trace at an arbitrary common coefficient height

Let k be a commutative ring, A an associative unital k-algebra, M an
A-bimodule with commuting k-linear left and right actions, and ι a finite
matrix index type. The generalized trace has degree maps
Mat_ι(M) ⊗[k] Mat_ι(A)^⊗n → M ⊗[k] A^⊗n given by summing matrix
entries around all closed index cycles.

For independent carrier universes u, v, w and z of k, A, M and ι, and
an arbitrary additional height t, lift both coefficient modules to
H = max(u,v,w,z,t). The resulting trace commutes with the signed
Hochschild boundary and defines
C_*(Mat_ι(A),ULift^H Mat_ι(M)) → C_*(A,ULift^H M).
Removing the coefficient lifts recovers the closed-cycle trace in each
degree. Taking t = 0 recovers the height max(u,v,w,z) chain map.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe t u v w z

namespace ModuleCat.Algebra.Hochschild.Matrix

variable (k : Type u) [CommRing k]
  (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  (ι : Type z) [Fintype ι] [DecidableEq ι]

attribute [local instance] Coefficients.leftModule Coefficients.rightModule
  Coefficients.commute Coefficients.leftTower Coefficients.rightTower
  ModuleCat.Algebra.Hochschild.uliftSMulCommClass

/-- For k, A, M and finite ι as in the coefficient Hochschild
complex, and H = max(u,v,w,z,t), the degree-n trace is the k-linear map
ULift^H Mat_ι(M) ⊗[k] Mat_ι(A)^⊗n →
ULift^H M ⊗[k] A^⊗n. It removes the source coefficient lift, takes the
closed-cycle generalized trace, and lifts the target coefficient. -/
def traceLinearLiftAt (n : ℕ) :
    ULift.{max u v w z t} (Matrix ι ι M) ⊗[k] TensorPower k n (Matrix ι ι A) →ₗ[k]
      ULift.{max u v w z t} M ⊗[k] TensorPower k n A :=
  (show ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
    M ⊗[k] TensorPower k n A from coefficientUnliftEquiv k A M n).symm.toLinearMap.comp
      ((generalizedTrace k ι n).comp
        (show ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
          TensorPower k n (Matrix ι ι A) ≃ₗ[k]
          Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) from
            coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n).toLinearMap)
omit [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M] [Module A M]
  [Module Aᵐᵒᵖ M] in
/-- For k-modules M and A with A a k-algebra, a finite matrix
index type ι and H = max(u,v,w,z,t), let d_S and d_T remove the source
and target coefficient lifts. The degree-n lifted trace T_n^H satisfies
d_T(T_n^H(x)) = T_n(d_S(x)) for every source tensor x. This value
identity does not require coefficient left or right A-actions. -/
theorem traceLinearLiftAt_down (n : ℕ)
    (x : ULift.{max u v w z t} (Matrix ι ι M) ⊗[k] TensorPower k n (Matrix ι ι A)) :
    (show ULift.{max u v w z t} M ⊗[k] TensorPower k n A ≃ₗ[k]
      M ⊗[k] TensorPower k n A from coefficientUnliftEquiv k A M n)
        (traceLinearLiftAt.{t} k A M ι n x) =
    generalizedTrace k ι n
      ((show ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
        TensorPower k n (Matrix ι ι A) ≃ₗ[k]
        Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι A) from
          coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) n) x) := by
  simp only [traceLinearLiftAt, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- Let M be an A-bimodule whose commuting left and right actions
are k-linear, and let H = max(u,v,w,z,t). For every n ≥ 0, the lifted
degree traces satisfy b_n^A ∘ T_(n+1)^H = T_n^H ∘ b_n^Mat from
C_(n+1)(Mat_ι(A),ULift^H Mat_ι(M)) to C_n(A,ULift^H M).
Both Hochschild boundaries are the alternating sums of their faces. -/
theorem traceLinearLiftAt_boundary_comm (n : ℕ) :
    (boundary k A (ULift.{max u v w z t} M) n).hom.comp
        (traceLinearLiftAt.{t} k A M ι (n + 1)) =
      (traceLinearLiftAt.{t} k A M ι n).comp
        (boundary k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) n).hom := by
  let eS (j : ℕ) : ULift.{max u v w z t} (Matrix ι ι M) ⊗[k]
      TensorPower k j (Matrix ι ι A) ≃ₗ[k]
      Matrix ι ι M ⊗[k] TensorPower k j (Matrix ι ι A) :=
    coefficientUnliftEquiv k (Matrix ι ι A) (Matrix ι ι M) j
  let eT (j : ℕ) : ULift.{max u v w z t} M ⊗[k] TensorPower k j A ≃ₗ[k]
      M ⊗[k] TensorPower k j A := coefficientUnliftEquiv k A M j
  have hS : (boundary k (Matrix ι ι A) (Matrix ι ι M) n).hom.comp
      (eS (n + 1)).toLinearMap = (eS n).toLinearMap.comp
        (boundary k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) n).hom :=
    coefficientUnliftEquiv_boundary_comm k (Matrix ι ι A) (Matrix ι ι M) n
  have hT : (boundary k A M n).hom.comp (eT (n + 1)).toLinearMap =
      (eT n).toLinearMap.comp (boundary k A (ULift.{max u v w z t} M) n).hom :=
    coefficientUnliftEquiv_boundary_comm k A M n
  apply LinearMap.ext
  intro x
  apply (eT n).injective
  change eT n ((boundary k A (ULift.{max u v w z t} M) n).hom
      (traceLinearLiftAt.{t} k A M ι (n + 1) x)) =
    eT n (traceLinearLiftAt.{t} k A M ι n
      ((boundary k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) n).hom x))
  calc
    _ = (boundary k A M n).hom
        (eT (n + 1) (traceLinearLiftAt.{t} k A M ι (n + 1) x)) :=
      (LinearMap.congr_fun hT _).symm
    _ = (boundary k A M n).hom (generalizedTrace k ι (n + 1) (eS (n + 1) x)) :=
      congrArg (boundary k A M n).hom
        (traceLinearLiftAt_down.{t} k A M ι (n + 1) x)
    _ = generalizedTrace k ι n
        ((boundary k (Matrix ι ι A) (Matrix ι ι M) n).hom (eS (n + 1) x)) :=
      (LinearMap.congr_fun (trace_boundary_comm k A M ι n) _).symm
    _ = generalizedTrace k ι n
        (eS n ((boundary k (Matrix ι ι A)
          (ULift.{max u v w z t} (Matrix ι ι M)) n).hom x)) :=
      congrArg (generalizedTrace k ι n) (LinearMap.congr_fun hS x)
    _ = _ := (traceLinearLiftAt_down.{t} k A M ι n _).symm

/-- For a k-algebra A, an A-bimodule M with commuting k-linear
actions, a finite matrix index type ι and arbitrary extra height t,
the closed-cycle trace defines the chain map
C_*(Mat_ι(A),ULift^H Mat_ι(M)) → C_*(A,ULift^H M),
where H = max(u,v,w,z,t) retains all independent carrier worlds. -/
def traceChainMapAt :
    chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) ⟶
      chainComplex k A (ULift.{max u v w z t} M) :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (traceLinearLiftAt.{t} k A M ι n)) (by
      intro n
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      exact traceLinearLiftAt_boundary_comm.{t} k A M ι n)

/-- For a k-algebra A and an A-bimodule M with commuting k-linear
actions, the trace chain map with t = 0 is equal to the trace chain map
whose coefficient modules are lifted to max(u,v,w,z). The source and
target Hochschild complexes and every degree map agree. -/
theorem traceChainMapAt_zero : traceChainMapAt.{0} k A M ι =
    traceChainMap k A M ι := rfl

end ModuleCat.Algebra.Hochschild.Matrix
