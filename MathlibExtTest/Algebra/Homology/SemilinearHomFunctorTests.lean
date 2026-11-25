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

public import MathlibExt.Algebra.Homology.SemilinearHomFunctor
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.NormNum

/-!
# Semilinear Hom on a Boolean complex

The source modules are infinite sequence modules, and the only source
differential is multiplication by two. The Boolean shape has one edge, so
successive differentials vanish. Source Hom reverses that edge.

The semimodule client uses `ℕ → ℤ`; its source has no additive inverses.
The module client uses `ℤ → ZMod 6`, with coefficient maps and a rank-two
tensor factor over the quotient ring. Both retain a nonzero differential
after Hom and tensor comparison. A lifted comparison has output carrier
universe one while its source, coefficient and Boolean index remain in
universe zero.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped TensorProduct

namespace MathlibExtTest.Algebra.Homology.SemilinearHomFunctor

private def edge : ComplexShape Bool where
  Rel a b := a = false ∧ b = true
  next_eq h₁ h₂ := h₁.2.trans h₂.2.symm
  prev_eq h₁ h₂ := h₁.1.trans h₂.1.symm

private abbrev NatP := SemimoduleCat.of ℕ (ℕ → ℕ)
private abbrev IntN := SemimoduleCat.of ℤ ℤ
private abbrev IntU := SemimoduleCat.of ℤ (Fin 2 → ℤ)
private abbrev natσ : ℕ →+* ℤ := Nat.castRingHom ℤ

private def natEval : NatP →ₛₗ[natσ] IntN :=
  natσ.toSemilinearMap.comp (LinearMap.proj (0 : ℕ) : NatP →ₗ[ℕ] ℕ)

private def intPair : IntU := fun i => if i = 0 then 3 else 5

private def natSource : HomologicalComplex (SemimoduleCat.{0} ℕ) edge where
  X _ := NatP
  d a b := if a = false ∧ b = true then
    SemimoduleCat.ofHom ((2 : ℕ) • (LinearMap.id : NatP →ₗ[ℕ] NatP)) else 0
  shape a b h := if_neg h
  d_comp_d' a b c h₁ h₂ := by
    have h : (true : Bool) = false := h₁.2.symm.trans h₂.1
    cases h

private abbrev natHom :=
  (SemimoduleCat.semilinearHomSourceComplexFunctor natσ IntN edge).obj (op natSource)

private abbrev natLeft :=
  ((SemimoduleCat.tensorRightFunctor IntU).mapHomologicalComplex edge.symm).obj natHom

private abbrev natRight :=
  (SemimoduleCat.semilinearHomSourceComplexFunctor natσ
    (SemimoduleCat.of ℤ (IntN ⊗[ℤ] IntU)) edge).obj (op natSource)

private abbrev natComparison : natLeft ⟶ natRight :=
  (SemimoduleCat.semilinearHomSourceComplexTensorIso natσ IntN IntU edge).hom.app
    (op natSource)

example : ((SemimoduleCat.semilinearHomSourceFunctor natσ IntN).map
    (SemimoduleCat.ofHom ((2 : ℕ) • (LinearMap.id : NatP →ₗ[ℕ] NatP))).op).hom
    natEval (fun _ => (1 : ℕ)) = 2 := by
  norm_num [SemimoduleCat.semilinearHomSourceFunctor_map_apply, natEval]

private theorem nat_comparison_values :
    TensorProduct.piScalarRight ℤ ℤ ℤ (Fin 2)
        ((natComparison.f false).hom (natEval ⊗ₜ[ℤ] intPair) (fun _ => (2 : ℕ))) 0 = 6 ∧
    TensorProduct.piScalarRight ℤ ℤ ℤ (Fin 2)
        ((natComparison.f false).hom (natEval ⊗ₜ[ℤ] intPair) (fun _ => (2 : ℕ))) 1 = 10 := by
  constructor <;>
    rw [SemimoduleCat.semilinearHomSourceComplexTensorIso_hom_f_apply] <;>
    norm_num [natEval, intPair, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]

example :
    TensorProduct.piScalarRight ℤ ℤ ℤ (Fin 2)
        ((natComparison.f false).hom
          ((natLeft.d true false).hom (natEval ⊗ₜ[ℤ] intPair))
          (fun _ => (1 : ℕ))) 0 = 6 ∧
    TensorProduct.piScalarRight ℤ ℤ ℤ (Fin 2)
        ((natComparison.f false).hom
          ((natLeft.d true false).hom (natEval ⊗ₜ[ℤ] intPair))
          (fun _ => (1 : ℕ))) 1 = 10 := by
  constructor <;>
    rw [SemimoduleCat.semilinearHomSourceComplexTensorIso_d_hom_apply] <;>
    norm_num [natSource, natEval, intPair, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]

example :
    (natComparison.f false).hom ((natLeft.d true false).hom (natEval ⊗ₜ[ℤ] intPair)) =
      (natRight.d true false).hom ((natComparison.f true).hom (natEval ⊗ₜ[ℤ] intPair)) := by
  exact (congrArg (fun f : natLeft.X true ⟶ natRight.X false =>
    f.hom (natEval ⊗ₜ[ℤ] intPair)) (natComparison.comm true false)).symm

example : (natEval ⊗ₜ[ℤ] intPair : (NatP →ₛₗ[natσ] IntN) ⊗[ℤ] IntU) ≠ 0 := by
  intro h
  have hv := nat_comparison_values.1
  rw [h, map_zero, LinearMap.zero_apply, map_zero, Pi.zero_apply] at hv
  norm_num at hv

private abbrev LiftIntN := SemimoduleCat.of ℤ (ULift.{1} ℤ)

private def liftedNatEval : NatP →ₛₗ[natσ] LiftIntN :=
  (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm.toLinearMap.comp natEval

example :
    TensorProduct.piScalarRight ℤ ℤ ℤ (Fin 2)
      (TensorProduct.map (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toLinearMap
        (LinearMap.id : IntU →ₗ[ℤ] IntU)
        ((((SemimoduleCat.semilinearHomSourceComplexTensorIso natσ LiftIntN IntU edge).hom.app
          (op natSource)).f false).hom (liftedNatEval ⊗ₜ[ℤ] intPair)
            (fun _ => (2 : ℕ)))) 0 = 6 := by
  rw [SemimoduleCat.semilinearHomSourceComplexTensorIso_hom_f_apply,
    TensorProduct.map_tmul]
  norm_num [liftedNatEval, natEval, intPair, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

private abbrev S := ZMod 6
private abbrev σ : ℤ →+* S := algebraMap ℤ S
private abbrev ZP := ModuleCat.of ℤ (ℕ → ℤ)
private abbrev N := ModuleCat.of S S
private abbrev U := ModuleCat.of S (Fin 2 → S)

private def modEval : ZP →ₛₗ[σ] N :=
  σ.toSemilinearMap.comp (LinearMap.proj (0 : ℕ) : ZP →ₗ[ℤ] ℤ)

private def modBasis : U := fun i => if i = 0 then 1 else 0

example : (2 : S) ≠ 0 ∧ (3 : S) ≠ 0 ∧ (2 : S) * 3 = 0 := by decide

private def modSource : HomologicalComplex (ModuleCat.{0} ℤ) edge where
  X _ := ZP
  d a b := if a = false ∧ b = true then
    ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ZP →ₗ[ℤ] ZP)) else 0
  shape a b h := if_neg h
  d_comp_d' a b c h₁ h₂ := by
    have h : (true : Bool) = false := h₁.2.symm.trans h₂.1
    cases h

private abbrev modHom :=
  (ModuleCat.semilinearHomSourceComplexFunctor σ N edge).obj (op modSource)

private abbrev modLeft :=
  (((ModuleCat.tensorBifunctorAt S).flip.obj U).mapHomologicalComplex edge.symm).obj modHom

private abbrev modRight :=
  (ModuleCat.semilinearHomSourceComplexFunctor σ (ModuleCat.tensorObjAt S N U) edge).obj
    (op modSource)

private abbrev modComparison : modLeft ⟶ modRight :=
  (ModuleCat.semilinearHomSourceComplexTensorIso σ N U edge).hom.app (op modSource)

example : (ModuleCat.semilinearMapLinearEquiv σ ZP N ((3 : S) • modEval)).hom
    (fun _ => (1 : ℤ)) = 3 := by
  norm_num [ModuleCat.semilinearMapLinearEquiv_apply, modEval]

private theorem mod_comparison_values :
    TensorProduct.piScalarRight S S S (Fin 2)
        ((modComparison.f false).hom (modEval ⊗ₜ[S] modBasis) (fun _ => (2 : ℤ))) 0 = 2 ∧
    TensorProduct.piScalarRight S S S (Fin 2)
        ((modComparison.f false).hom (modEval ⊗ₜ[S] modBasis) (fun _ => (2 : ℤ))) 1 = 0 := by
  constructor <;>
    rw [ModuleCat.semilinearHomSourceComplexTensorIso_hom_f_apply] <;>
    norm_num [modEval, modBasis, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]

example :
    TensorProduct.piScalarRight S S S (Fin 2)
        ((modComparison.f false).hom
          ((modLeft.d true false).hom (modEval ⊗ₜ[S] modBasis))
          (fun _ => (1 : ℤ))) 0 = 2 ∧
    TensorProduct.piScalarRight S S S (Fin 2)
        ((modComparison.f false).hom
          ((modLeft.d true false).hom (modEval ⊗ₜ[S] modBasis))
          (fun _ => (1 : ℤ))) 1 = 0 := by
  constructor <;>
    rw [ModuleCat.semilinearHomSourceComplexTensorIso_d_hom_apply] <;>
    norm_num [modSource, modEval, modBasis, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]

private def coefficientComplex : HomologicalComplex (ModuleCat.{0} S) edge where
  X _ := N
  d a b := if a = false ∧ b = true then
    ModuleCat.ofHom ((3 : S) • (LinearMap.id : N →ₗ[S] N)) else 0
  shape a b h := if_neg h
  d_comp_d' a b c h₁ h₂ := by
    have h : (true : Bool) = false := h₁.2.symm.trans h₂.1
    cases h

private abbrev coeffHom :=
  (ModuleCat.semilinearHomCoeffComplexFunctor σ ZP edge).obj coefficientComplex

private abbrev coeffLeft :=
  (((ModuleCat.tensorBifunctorAt S).flip.obj U).mapHomologicalComplex edge).obj coeffHom

private abbrev coeffComparison :=
  (ModuleCat.semilinearHomCoeffComplexTensorIso σ ZP U edge).hom.app coefficientComplex

example :
    TensorProduct.piScalarRight S S S (Fin 2)
        ((coeffComparison.f true).hom
          ((coeffLeft.d false true).hom (modEval ⊗ₜ[S] modBasis))
          (fun _ => (1 : ℤ))) 0 = 3 ∧
    TensorProduct.piScalarRight S S S (Fin 2)
        ((coeffComparison.f true).hom
          ((coeffLeft.d false true).hom (modEval ⊗ₜ[S] modBasis))
          (fun _ => (1 : ℤ))) 1 = 0 := by
  constructor <;>
    rw [ModuleCat.semilinearHomCoeffComplexTensorIso_d_hom_apply] <;>
    norm_num [coefficientComplex, modEval, modBasis, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]

example :
    TensorProduct.piScalarRight S S S (Fin 2)
        (((((ModuleCat.semilinearHomSourceComplexTensorIsoAt.{1, 0, 0, 0, 0, 0, 0}
          σ N U edge).hom.app (op modSource)).f false).hom
          (ULift.up (modEval ⊗ₜ[S] modBasis))).down (fun _ => (2 : ℤ))) 0 = 2 := by
  rw [ModuleCat.semilinearHomSourceComplexTensorIsoAt_hom_f_apply]
  norm_num [modEval, modBasis, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

example : (modComparison.f false).hom (modEval ⊗ₜ[S] modBasis) ≠ 0 := by
  intro h
  have hv := mod_comparison_values.1
  rw [h, LinearMap.zero_apply, map_zero, Pi.zero_apply] at hv
  exact (by decide : (2 : S) ≠ 0) hv

end MathlibExtTest.Algebra.Homology.SemilinearHomFunctor
