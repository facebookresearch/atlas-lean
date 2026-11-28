/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.Resolution
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.ZMod.Basic

/-!
# Regular enveloping coefficients in characteristic six

For the matrix Lie algebra over ZMod6, the regular coefficient boundary has
positive right-product value: the generators e01 and e10 give e10*e01, whose
(1,1) entry is one. The opposite product has that entry zero. The same
constructed complex supplies projective nonzero terms, square-zero boundary
and the scalar augmentation of its projective resolution.
-/

noncomputable section
open CategoryTheory ChevalleyEilenberg
open scoped TensorProduct
namespace MathlibExtTest.EnvelopingResolution
private abbrev R := ZMod 6
private instance : Fact (1 < 6) := ⟨by decide⟩
private abbrev Mat := Matrix (Fin 2) (Fin 2) R
private instance : LieRing Mat := LieRing.ofAssociativeRing
private instance : LieAlgebra R Mat := LieAlgebra.ofAssociativeAlgebra
private instance : Module.Free R Mat := Module.Free.of_equiv (Matrix.ofLinearEquiv R)
private abbrev U := UniversalEnvelopingAlgebra R Mat
private abbrev K := envelopingComplex R Mat
private abbrev Q := envelopingProjectiveResolution R Mat
private def x : Mat := !![0, 1; 0, 0]
private def y : Mat := !![0, 0; 1, 0]
private def eval : U →ₐ[R] Mat :=
  UniversalEnvelopingAlgebra.lift R (LieHom.id : Mat →ₗ⁅R⁆ Mat)
private lemma eval_ι (a : Mat) : eval (UniversalEnvelopingAlgebra.ι R a) = a :=
  UniversalEnvelopingAlgebra.lift_ι_apply R (LieHom.id : Mat →ₗ⁅R⁆ Mat) a
private def zeroWord : ⋀[R]^0 Mat := exteriorPower.ιMulti R 0 Fin.elim0
private def z1 : K.X 1 :=
  exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] UniversalEnvelopingAlgebra.ι R y
private def z2 : K.X 2 := exteriorPower.ιMulti R 2 ![x, y] ⊗ₜ[R] (1 : U)
private def readZero (z : K.X 0) : Mat := eval (envelopingZeroEquiv R Mat z)
private lemma zeroWordValue : exteriorPower.zeroEquiv R Mat zeroWord = 1 := by
  simp [zeroWord]
private lemma readZero_tmul (a : U) : readZero (zeroWord ⊗ₜ[R] a) = eval a := by
  unfold readZero
  rw [envelopingZeroEquiv_tmul, zeroWordValue, one_smul]
private lemma readZero_zero : readZero 0 = 0 := by
  unfold readZero
  rw [map_zero, map_zero]
private lemma firstBoundary : (K.d 1 0).hom z1 =
    zeroWord ⊗ₜ[R] (UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x) :=
  envelopingComplex_d_one R Mat x (UniversalEnvelopingAlgebra.ι R y)
private lemma firstValue : readZero ((K.d 1 0).hom z1) = y * x := by
  rw [firstBoundary, readZero_tmul, map_mul, eval_ι, eval_ι]
private lemma firstEntry : readZero ((K.d 1 0).hom z1) 1 1 = (1 : R) := by
  rw [firstValue]
  decide
private lemma z1_nonzero : z1 ≠ 0 := by
  intro h
  have hz := congrArg (fun z : K.X 1 => readZero ((K.d 1 0).hom z) 1 1) h
  have h0 : readZero ((K.d 1 0).hom (0 : K.X 1)) 1 1 = 0 := by
    rw [LinearMap.map_zero, readZero_zero]
    rfl
  exact one_ne_zero (firstEntry.symm.trans (hz.trans h0))
example : (2 : R) * 3 = 0 ∧ (2 : R) ≠ 0 ∧ (3 : R) ≠ 0 := by decide
example : eval ((rightRegularLieRingModule R Mat).bracket x
    (UniversalEnvelopingAlgebra.ι R y)) = -(y * x) := by
  change eval (-(UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x)) = _
  rw [map_neg, map_mul, eval_ι, eval_ι]
example : readZero ((K.d 1 0).hom z1) 1 1 = (1 : R) := firstEntry
example : UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x ≠
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y := by
  intro h
  have hc := congrArg (fun a : U => eval a) h
  rw [map_mul, eval_ι, eval_ι, map_mul, eval_ι, eval_ι] at hc
  exact (by decide : y * x ≠ x * y) hc
example : Module.Projective U (K.X 1) ∧ ∃ z : K.X 1, z ≠ 0 :=
  ⟨inferInstance, ⟨z1, z1_nonzero⟩⟩
example : K.d 2 1 ≫ K.d 1 0 = 0 := K.d_comp_d 2 1 0
example : (K.d 1 0).hom ((K.d 2 1).hom z2) = 0 := by
  have h := congrArg (fun f => f.hom z2) (K.d_comp_d 2 1 0)
  exact h
example : Q.π.f 0 (zeroWord ⊗ₜ[R] (algebraMap R U 2)) = ULift.up (2 : R) := by
  let p : K.X 0 := zeroWord ⊗ₜ[R] (algebraMap R U 2)
  have hz : envelopingZeroEquiv R Mat p = algebraMap R U 2 := by
    calc
      _ = (exteriorPower.zeroEquiv R Mat zeroWord) • (algebraMap R U 2) :=
        envelopingZeroEquiv_tmul R Mat zeroWord (algebraMap R U 2)
      _ = _ := by rw [zeroWordValue, one_smul]
  have ha : envelopingAugmentationComponent R Mat p = ULift.up (2 : R) := by
    calc
      _ = ULift.up (UniversalEnvelopingAlgebra.augmentation R Mat
          (envelopingZeroEquiv R Mat p)) := envelopingAugmentationComponent_apply R Mat p
      _ = _ := by
        apply ULift.ext
        change UniversalEnvelopingAlgebra.augmentation R Mat
          (envelopingZeroEquiv R Mat p) = 2
        rw [hz]
        exact (UniversalEnvelopingAlgebra.augmentation R Mat).commutes 2
  have hp := congrArg
    (fun f : K.X 0 ⟶ envelopingTrivialObject R Mat => f.hom p)
    (envelopingAugmentation_f_zero R Mat)
  change Q.π.f 0 p = envelopingAugmentationComponent R Mat p at hp
  exact hp.trans ha
end MathlibExtTest.EnvelopingResolution
