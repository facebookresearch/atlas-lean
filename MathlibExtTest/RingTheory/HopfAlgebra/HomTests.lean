/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

import MathlibExt.RingTheory.HopfAlgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic
meta import Mathlib.Tactic.NormNum

/-!
# Antipode naturality across group-algebra carrier universes

The coefficient ring is ZMod 6. A group-algebra morphism doubles integer
exponents and lifts its target group to a larger universe. A coefficient-two
term remains nonzero under the antipode and moves to exponent -2. The
coefficient-two and coefficient-three terms are nonzero, but their product
vanishes, so no domain hypothesis is available in this calculation.
-/

noncomputable section

namespace MathlibExtTest.HopfAlgebraHom

private abbrev R := ZMod 6
private abbrev G := Multiplicative ℤ
private abbrev H := ULift.{1} G
private abbrev A := MonoidAlgebra R G
private abbrev B := MonoidAlgebra R H

private def double : G →* H where
  toFun g := ULift.up (Multiplicative.ofAdd (2 * g.toAdd))
  map_one' := by
    apply ULift.ext
    change Multiplicative.ofAdd ((2 : ℤ) * 0) = Multiplicative.ofAdd 0
    rw [mul_zero]
  map_mul' g h := by
    apply ULift.ext
    change Multiplicative.ofAdd (2 * (g.toAdd + h.toAdd)) =
      Multiplicative.ofAdd (2 * g.toAdd + 2 * h.toAdd)
    rw [mul_add]

private def F : A →ₐc[R] B := MonoidAlgebra.mapDomainBialgHom R double
private def x : A := MonoidAlgebra.single (Multiplicative.ofAdd 1) (2 : R)
private def y : A := MonoidAlgebra.single (Multiplicative.ofAdd 1) (3 : R)

private lemma F_antipode_x :
    F (HopfAlgebra.antipode R x) =
      MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (-2))) (2 : R) := by
  rw [F.map_antipode]
  simp only [F, x, MonoidAlgebra.mapDomainBialgHom_single,
    MonoidAlgebra.antipode_single, CommSemiring.antipode_eq_id, LinearMap.id_apply]
  rfl

example : (2 : R) * 3 = 0 ∧ (2 : R) ≠ 0 ∧ (3 : R) ≠ 0 := by decide

example : double (Multiplicative.ofAdd 1) =
    (ULift.up (Multiplicative.ofAdd 2) : H) := by rfl

example : F x = MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd 2)) (2 : R) := by
  simp only [F, x, MonoidAlgebra.mapDomainBialgHom_single]
  rfl

example : F (HopfAlgebra.antipode R x) =
    MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd (-2))) (2 : R) :=
  F_antipode_x

example : (F (HopfAlgebra.antipode R x)).coeff
    (ULift.up (Multiplicative.ofAdd (-2))) = (2 : R) := by
  rw [F_antipode_x, MonoidAlgebra.coeff_single, Finsupp.single_eq_same]

example : F (HopfAlgebra.antipode R x) ≠ 0 := by
  intro h
  have hc := congrArg (fun z : B => z.coeff (ULift.up (Multiplicative.ofAdd (-2)))) h
  rw [F_antipode_x, MonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
  change (2 : R) = 0 at hc
  exact (by decide : (2 : R) ≠ 0) hc

example : x * y = 0 ∧ x ≠ 0 ∧ y ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [x, y, MonoidAlgebra.single_mul_single] <;> decide
  · intro h
    have hc := congrArg (fun z : A => z.coeff (Multiplicative.ofAdd 1)) h
    simp only [x, MonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
    change (2 : R) = 0 at hc
    exact (by decide : (2 : R) ≠ 0) hc
  · intro h
    have hc := congrArg (fun z : A => z.coeff (Multiplicative.ofAdd 1)) h
    simp only [y, MonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
    change (3 : R) = 0 at hc
    exact (by decide : (3 : R) ≠ 0) hc

example : ¬ Bialgebra.IsPrimitiveElem R x := by
  intro h
  have hc := h.counit_eq_zero
  simp only [x, MonoidAlgebra.counit_single] at hc
  change Bialgebra.counitAlgHom R R (2 : R) = 0 at hc
  rw [Bialgebra.counitAlgHom_self, AlgHom.id_apply] at hc
  exact (by decide : (2 : R) ≠ 0) hc

example : (F (HopfAlgebra.antipode R x)).coeff
    (ULift.up (Multiplicative.ofAdd 2)) = 0 := by
  rw [F_antipode_x, MonoidAlgebra.coeff_single]
  have hne : (ULift.up (Multiplicative.ofAdd (-2)) : H) ≠
      ULift.up (Multiplicative.ofAdd 2) := by
    intro h
    have hi := congrArg (fun z : H => z.down.toAdd) h
    norm_num at hi
  simp only [Finsupp.single_apply, if_neg hne]

end MathlibExtTest.HopfAlgebraHom
