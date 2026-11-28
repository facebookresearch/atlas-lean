/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.CoimageSequence
import MathlibExt.Algebra.Homology.HomologicalComplexModuleCokernel
import MathlibExt.LinearAlgebra.KernelCokernelMap
import Mathlib.Data.ZMod.Basic
meta import Mathlib.Tactic.NormNum

/-!
# Cokernel coordinates and the degree-zero edge

Multiplication by two induces a quotient map that sends the class of one to
that of two over ZMod 5. The resulting class is neither zero nor the original
class. The canonical coimage sequence and its transported connecting maps
are exercised on module chain complexes, with the degree-zero differential
constraint imposed by the natural-number complex shape.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

namespace MathlibExtTest.Algebra.Homology.CokernelCoordinates

abbrev F := ZMod 5

def twice : F →ₗ[F] F := (2 : F) • LinearMap.id

lemma compatible :
    (0 : F →ₗ[F] F).comp twice = twice.comp (0 : F →ₗ[F] F) := by simp

example : LinearMap.mapCoker (0 : F →ₗ[F] F) 0 twice compatible
    (Submodule.Quotient.mk (1 : F)) = Submodule.Quotient.mk (2 : F) := by
  rw [LinearMap.mapCoker_mk]
  rfl

example : LinearMap.mapCoker (0 : F →ₗ[F] F) 0 twice compatible
    (Submodule.Quotient.mk (1 : F)) ≠ 0 := by
  rw [LinearMap.mapCoker_mk]
  intro h
  have hz := (Submodule.Quotient.mk_eq_zero _).mp h
  simp only [LinearMap.range_zero, Submodule.mem_bot] at hz
  norm_num [twice] at hz
  exact (by decide : (2 : ZMod 5) ≠ 0) hz

example : LinearMap.mapCoker (0 : F →ₗ[F] F) 0 twice compatible
    (Submodule.Quotient.mk (1 : F)) ≠ Submodule.Quotient.mk (1 : F) := by
  rw [LinearMap.mapCoker_mk]
  intro h
  have hz := (Submodule.Quotient.eq _).mp h
  simp only [LinearMap.range_zero, Submodule.mem_bot] at hz
  norm_num [twice] at hz
  exact (by decide : (1 : ZMod 5) ≠ 0) hz

variable {K L : ChainComplex (ModuleCat F) ℕ} (f : K ⟶ L)

example : coimageSequence f = ShortComplex.cokernelSequence (kernel.ι f) := rfl

example : (coimageSequence f).ShortExact := coimageSequence_shortExact f

example (h : QuasiIso (Abelian.factorThruCoimage f)) :
    coimageTargetBoundary f h 1 0 (by simp) ≫
      homologyMap (kernel.ι f) 0 = 0 :=
  coimageTargetBoundary_comp_kernelHomologyMap f h 1 0 (by simp)

example (i : ℕ) :
    (cokernel.π f).f i ≫ (moduleCokernelDegreeIso f i).hom =
      ModuleCat.ofHom (LinearMap.range (f.f i).hom).mkQ :=
  moduleCokernelDegreeIso_projection f i

example : L.d 0 0 = 0 := L.shape 0 0 (by simp)

example :
    ModuleCat.ofHom (LinearMap.range (f.f 0).hom).mkQ ≫
        moduleRangeQuotientD f 0 0 = 0 := by
  rw [moduleRangeQuotientD_projection]
  rw [L.shape 0 0 (by simp), zero_comp]

end MathlibExtTest.Algebra.Homology.CokernelCoordinates
