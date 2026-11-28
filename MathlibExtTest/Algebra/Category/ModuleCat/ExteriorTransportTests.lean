/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Category.ModuleCat.ExteriorPower
import MathlibExt.Algebra.Category.ModuleCat.RingEquivTensorUniverse
import MathlibExt.Algebra.Category.ModuleCat.UliftComposition
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.ULift

/-!
# Exterior transport with independent ring and module universes

The ground ring is in universe zero, the lifted coefficient ring is in universe
one, and the modules have carrier universe two. Degree-one exterior powers,
scalar extension and restriction along a ring equivalence retain their actual
pure-tensor coordinates. The in-universe module lift retains the value seven.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace MathlibExtTest.ExteriorTransport

private abbrev S := ULift.{1} ℤ
private abbrev M : ModuleCat.{2} ℤ := ModuleCat.of ℤ (ULift.{2} ℤ)
private def vectors : Fin 1 → M := fun _ => ULift.up 3

example :
    ((ModuleCat.exteriorPowerOneNatIso.{0, 2} ℤ).hom.app M).hom
        (exteriorPower.ιMulti ℤ 1 vectors) = ULift.up (3 : ℤ) := by
  change exteriorPower.oneEquiv ℤ M (exteriorPower.ιMulti ℤ 1 vectors) = _
  exact exteriorPower.oneEquiv_ιMulti (R := ℤ) (M := M) vectors

example : exteriorPower.ιMulti ℤ 1 vectors ≠ 0 := by
  intro hz
  have h : (ULift.up (3 : ℤ) : M) = 0 :=
    (exteriorPower.oneEquiv_ιMulti (R := ℤ) (M := M) vectors).symm.trans
      ((congrArg (exteriorPower.oneEquiv ℤ M) hz).trans
        (exteriorPower.oneEquiv ℤ M).map_zero)
  exact (by decide : (3 : ℤ) ≠ 0) (congrArg ULift.down h)

example :
    ((ModuleCat.exteriorPowerBaseChangeNatIso.{0, 2, 1} ℤ S 1).hom.app M).hom
        ((ULift.up (2 : ℤ) : S) ⊗ₜ[ℤ, algebraMap ℤ S]
          exteriorPower.ιMulti ℤ 1 vectors) =
      (ULift.up (2 : ℤ) : S) • exteriorPower.ιMulti S 1
        (M := (ModuleCat.extendScalars (algebraMap ℤ S)).obj M)
        (fun i => (1 : S) ⊗ₜ[ℤ, algebraMap ℤ S] vectors i) := by
  change ((ModuleCat.exteriorPowerBaseChangeComponent.{0, 2, 1} ℤ S 1 M).hom).hom
    _ = _
  exact ModuleCat.exteriorPowerBaseChangeComponent_hom_tmul_ιMulti
    ℤ S 1 M (ULift.up 2) vectors

private abbrev e : ℤ ≃+* S := ULift.ringEquiv.symm
private abbrev U : ModuleCat.{2} S := ModuleCat.of S (ULift.{2} S)
private abbrev U₀ : ModuleCat.{2} ℤ := (ModuleCat.restrictScalars e.toRingHom).obj U
private abbrev x : U₀ := ULift.up (ULift.up (2 : ℤ))
private abbrev y : U₀ := ULift.up (ULift.up (3 : ℤ))

example :
    (ModuleCat.RingEquivUniverse.tensorIso.{0, 1, 2} e U U).hom (x ⊗ₜ[ℤ] y) =
      (show U from x) ⊗ₜ[S] (show U from y) :=
  ModuleCat.RingEquivUniverse.tensorIso_hom_tmul e U U x y

example :
    ((ModuleCat.uliftFunctorWithinIso.{0, 0, 2} ℤ).hom.app M).hom
        (ULift.up (ULift.up (7 : ℤ) : M)) = ULift.up (7 : ℤ) :=
  ModuleCat.uliftFunctorWithinIso_hom_up (R := ℤ) M (ULift.up 7)

end MathlibExtTest.ExteriorTransport
