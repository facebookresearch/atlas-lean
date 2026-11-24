/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Product
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Ring.Pi

/-!
# General linear groups over a Pi of semirings

Compose the existing entrywise Matrix.piRingEquiv with Mathlib's Pi-units
equivalence. Coordinates retain the original ring evaluations, and the
inverse recombines original matrix entries. No stable or K-theory carrier
is defined here.
-/

@[expose] public section

set_option autoImplicit false

universe uR uS v

namespace Matrix.GeneralLinearGroup

variable {ι : Type} (R : ι → Type uR) [∀ i, Semiring (R i)]

/-- Stock entrywise matrix and Pi-units equivalences on original GL carriers. -/
def piEquiv (n : Type v) [Fintype n] [DecidableEq n] :
    GL n (∀ i, R i) ≃* ∀ i, GL n (R i) :=
  (Units.mapEquiv (Matrix.piRingEquiv (β := R) (n := n)).toMulEquiv).trans
    MulEquiv.piUnits

/-- Each GL coordinate is the original entrywise unital ring-hom map. -/
@[simp]
theorem piEquiv_apply (n : Type v) [Fintype n] [DecidableEq n]
    (A : GL n (∀ i, R i)) (i : ι) :
    piEquiv R n A i = mapRingHom (Pi.evalRingHom R i) A := by
  apply Units.ext
  rfl

/-- The inverse GL matrix has the original entries of every supplied factor. -/
@[simp]
theorem coe_piEquiv_symm_apply (n : Type v) [Fintype n] [DecidableEq n]
    (A : ∀ i, GL n (R i)) (p q : n) (i : ι) :
    ((↑((piEquiv R n).symm A) : Matrix n n (∀ i, R i)) p q) i =
      (A i : Matrix n n (R i)) p q := rfl

/-- Original Pi GL equivalence commutes with independently sized coefficient maps. -/
theorem piEquiv_mapRingHom {S : ι → Type uS} [∀ i, Semiring (S i)]
    (n : Type v) [Fintype n] [DecidableEq n] (φ : ∀ i, R i →+* S i)
    (A : GL n (∀ i, R i)) (i : ι) :
    piEquiv S n
        (mapRingHom (RingHom.pi (fun j => (φ j).comp (Pi.evalRingHom R j))) A) i =
      mapRingHom (φ i) (piEquiv R n A i) := by
  apply Units.ext
  rfl

end Matrix.GeneralLinearGroup
