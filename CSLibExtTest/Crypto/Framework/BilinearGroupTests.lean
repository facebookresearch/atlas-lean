/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Framework.BilinearGroup

/-!
# Tests for the bilinear-group interface

Toy-model numerics at `q = 7` (by `decide`), a kernel-triviality spot check,
the toy BDH win, and axiom audits for the toy construction and the BDH theorem.
-/

namespace Cslib.Crypto.Framework

/-- The toy model at `q = 7`. -/
def toy7 : BilinearGroupData := BilinearGroupData.toyModel 7 (by decide)

/-- Decidable equality on the toy target group (definitionally `ZMod 7`-based). -/
instance toy7GTDecEq : DecidableEq toy7.GT :=
  inferInstanceAs (DecidableEq (Multiplicative (ZMod 7)))

/-- Pairing numerics at `q = 7`: `e 2 3 = gT ^ 6`. -/
example : toy7.e (Multiplicative.ofAdd (2 : ZMod 7)) (Multiplicative.ofAdd (3 : ZMod 7))
    = toy7.gT ^ 6 := by decide

/-- Nondegeneracy spot at `q = 7`: `e 2 3 ≠ 1`. -/
example : toy7.e (Multiplicative.ofAdd (2 : ZMod 7)) (Multiplicative.ofAdd (3 : ZMod 7))
    ≠ 1 := by decide

/-- Kernel triviality at `q = 7`. -/
example (a : Multiplicative (ZMod 7)) (h : ∀ b, toy7.e a b = 1) : a = 1 :=
  BilinearGroupData.eq_one_of_forall_e_eq_one_left toy7 a h

/-- The BDH toy win at `q = 7`. -/
example : toy7.bdhAdvantage (BilinearGroupData.toyBdhAdversary 7) = 1 :=
  BilinearGroupData.toy_bdhAdvantage_eq_one 7 _

#print axioms BilinearGroupData.toyModel
#print axioms toy7
#print axioms BilinearGroupData.toy_bdhAdvantage_eq_one

end Cslib.Crypto.Framework
