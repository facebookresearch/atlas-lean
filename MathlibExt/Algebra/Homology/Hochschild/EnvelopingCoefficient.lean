/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Original left/right coefficient actions and native enveloping action. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarEnveloping
public import MathlibExt.Algebra.Module.AlgHomAction
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-!
# Bimodules as right enveloping modules

The commuting left and right actions on M give a right action of
A ⊗[k] Aᵐᵒᵖ. The opposite element op(a ⊗ op(b)) acts by the right
a-action after the left b-action, matching the Hochschild endpoint
order. Ground, algebra and coefficient universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w w'

namespace ModuleCat.Algebra.Hochschild.EnvelopingCoefficient

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Native tensor lifting packages the original two commuting coefficient actions. -/
def rightEnvelopingAction :
    (AdjacentBar.EnvelopingAlgebra k A)ᵐᵒᵖ →ₐ[k] Module.End k M :=
  (Algebra.TensorProduct.lift (Algebra.lsmul (A := Aᵐᵒᵖ) k k M)
    ((Algebra.lsmul (A := A) k k M).comp (AlgEquiv.opOp k A).symm.toAlgHom)
    (fun a b => by
      change ((Algebra.lsmul (A := Aᵐᵒᵖ) k k M) a) *
        ((Algebra.lsmul (A := A) k k M) ((AlgEquiv.opOp k A).symm b)) =
      ((Algebra.lsmul (A := A) k k M) ((AlgEquiv.opOp k A).symm b)) *
        ((Algebra.lsmul (A := Aᵐᵒᵖ) k k M) a)
      apply LinearMap.ext
      intro m
      exact (smul_comm ((AlgEquiv.opOp k A).symm b) a (m : M)).symm)).comp
    (Algebra.TensorProduct.opAlgEquiv k k A Aᵐᵒᵖ).symm.toAlgHom

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- The enveloping pure tensor retains the original first-right/last-left endpoint convention. -/
theorem rightEnvelopingAction_tmul (a0 aLast : A) (m : M) :
    rightEnvelopingAction k A M (op (a0 ⊗ₜ[k] op aLast)) m = op a0 • (aLast • m) := by
  simp only [rightEnvelopingAction, AlgHom.comp_apply]
  exact congrArg (fun f : Module.End k M => f m)
    (Algebra.TensorProduct.lift_tmul (Algebra.lsmul (A := Aᵐᵒᵖ) k k M)
      ((Algebra.lsmul (A := A) k k M).comp (AlgEquiv.opOp k A).symm.toAlgHom)
      (fun a b => by
      change ((Algebra.lsmul (A := Aᵐᵒᵖ) k k M) a) *
        ((Algebra.lsmul (A := A) k k M) ((AlgEquiv.opOp k A).symm b)) =
      ((Algebra.lsmul (A := A) k k M) ((AlgEquiv.opOp k A).symm b)) *
        ((Algebra.lsmul (A := Aᵐᵒᵖ) k k M) a)
      apply LinearMap.ext
      intro m
      exact (smul_comm ((AlgEquiv.opOp k A).symm b) a (m : M)).symm)
      (op a0) (op (op aLast)))

/-- The right enveloping module is the native pullback of that original representation. -/
@[instance_reducible]
def rightEnvelopingModule : Module (AdjacentBar.EnvelopingAlgebra k A)ᵐᵒᵖ M :=
  Module.compHom M (rightEnvelopingAction k A M).toRingHom

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Ground scalars of the original coefficient remain unchanged in the enveloping module. -/
theorem rightEnvelopingScalarTower :
    letI := rightEnvelopingModule k A M
    IsScalarTower k (AdjacentBar.EnvelopingAlgebra k A)ᵐᵒᵖ M :=
  AlgHom.moduleEnd_compHom_isScalarTower (rightEnvelopingAction k A M)

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- The enveloping operators are linear for the original ground action. -/
theorem rightEnvelopingScalarComm :
    letI := rightEnvelopingModule k A M
    SMulCommClass k (AdjacentBar.EnvelopingAlgebra k A)ᵐᵒᵖ M := by
  letI := rightEnvelopingModule k A M
  constructor
  intro c e m
  change c • (rightEnvelopingAction k A M e m) = rightEnvelopingAction k A M e (c • m)
  exact ((rightEnvelopingAction k A M e).map_smul c m).symm

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- The original pure action is retained after native pullback to a module. -/
theorem rightEnvelopingModule_tmul (a0 aLast : A) (m : M) :
    letI := rightEnvelopingModule k A M
    op (a0 ⊗ₜ[k] op aLast) • m = op a0 • (aLast • m) :=
  rightEnvelopingAction_tmul k A M a0 aLast m

section Naturality

variable {N : Type w'} [AddCommGroup N] [Module k N] [Module A N] [Module Aᵐᵒᵖ N]
  [SMulCommClass A Aᵐᵒᵖ N] [SMulCommClass k A N] [SMulCommClass k Aᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Aᵐᵒᵖ N]

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [SMulCommClass k A N] [SMulCommClass k Aᵐᵒᵖ N] in
/-- Preserving the original left and right actions preserves the enveloping action. -/
theorem rightEnvelopingAction_naturality (f : M →ₗ[k] N)
    (hLeft : ∀ (a : A) (m : M), f (a • m) = a • f m)
    (hRight : ∀ (b : Aᵐᵒᵖ) (m : M), f (b • m) = b • f m)
    (z : AdjacentBar.EnvelopingAlgebra k A) (m : M) :
    f (rightEnvelopingAction k A M (op z) m) = rightEnvelopingAction k A N (op z) (f m) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have hM := rightEnvelopingAction_tmul k A M a b.unop m
    have hN := rightEnvelopingAction_tmul k A N a b.unop (f m)
    rw [op_unop] at hM hN
    rw [hM, hN, hRight, hLeft]
  | add z z' hz hz' =>
    let p := rightEnvelopingAction k A M
    let q := rightEnvelopingAction k A N
    have hM : @Eq M (p (op (z + z')) m) (p (op z) m + p (op z') m) :=
      (congrArg (fun t : Module.End k M => t m)
        ((congrArg p (MulOpposite.op_add z z')).trans (p.map_add (op z) (op z')))).trans
        (LinearMap.add_apply (p (op z)) (p (op z')) m)
    have hN : @Eq N (q (op (z + z')) (f m)) (q (op z) (f m) + q (op z') (f m)) :=
      (congrArg (fun t : Module.End k N => t (f m))
        ((congrArg q (MulOpposite.op_add z z')).trans (q.map_add (op z) (op z')))).trans
        (LinearMap.add_apply (q (op z)) (q (op z')) (f m))
    calc
      _ = f (p (op z) m + p (op z') m) := congrArg f hM
      _ = f (p (op z) m) + f (p (op z') m) := f.map_add _ _
      _ = q (op z) (f m) + q (op z') (f m) := congrArg₂ (fun a b : N => a + b) hz hz'
      _ = _ := hN.symm

end Naturality

end ModuleCat.Algebra.Hochschild.EnvelopingCoefficient
