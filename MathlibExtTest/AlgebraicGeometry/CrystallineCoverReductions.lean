/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# A crystalline cover retains the original closed reduction

In particular, changing a zero reduction ideal to a nonzero dual-number
ideal is not a cover, even when the thickening scheme map is identity.
The epsilon ideal below is the actual kernel of the original augmentation.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests

noncomputable section

example (p : ℕ) (A : PDBase) (S : Over A.reduction)
    (P Q : Obj p A S) (f : Q ⟶ P) (hP : P.ideal=⊥) (hQ : Q.ideal≠⊥) :
    ¬IsCover p A S P (fun _ : Unit => Q) (fun _ => f) := by
  intro h
  apply hQ
  have e := h.2.1 ()
  simpa only [hP, Ideal.map_bot] using e

example (R : Type) [CommRing R] [Nontrivial R] :
    RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom ≠ ⊥ := by
  intro h
  have hm : TrivSqZeroExt.inr (1 : R) ∈ RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom := by
    simp
  rw [h, Ideal.mem_bot] at hm
  have e := congrArg (TrivSqZeroExt.snd : TrivSqZeroExt R R → R) hm
  exact (one_ne_zero : (1 : R) ≠ 0) (by simpa using e)

#print axioms MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests.cover_mem
