/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.Trace

/-!
# The finite trace at a specified common coefficient lift height

The trace and corner maps lift to a specified common coefficient
height and compose with heterogeneous Morita maps. Their down
maps are `coefficientUnliftEquiv`, with both original carrier
universes retained.
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

/-- The same native finite trace with only the coefficient lifted to a requested upper height. -/
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
/-- The target down map gives the original trace of the original source down map. -/
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

/-- The original boundary square is transported through the two coefficient lifts. -/
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

/-- The trace chain map at a common upper height, without a world equality premise. -/
def traceChainMapAt :
    chainComplex k (Matrix ι ι A) (ULift.{max u v w z t} (Matrix ι ι M)) ⟶
      chainComplex k A (ULift.{max u v w z t} M) :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (traceLinearLiftAt.{t} k A M ι n)) (by
      intro n
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      exact traceLinearLiftAt_boundary_comm.{t} k A M ι n)

/-- At zero additional height this is the original chosen trace chain map. -/
theorem traceChainMapAt_zero : traceChainMapAt.{0} k A M ι =
    traceChainMap k A M ι := rfl

end ModuleCat.Algebra.Hochschild.Matrix
