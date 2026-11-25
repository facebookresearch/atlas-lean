/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelResidueExponentPeriod

open MetaMathlibExt

example (p r k l n : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (hk : r + 1 ≤ k) (hkl : k ≤ l)
    (hmod : k ≡ l [MOD (p ^ r).totient]) (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue (k := k) (p := p) (r := r) n = gobelResidue l p r n :=
  gobelResidue_eq_of_modEq_totient (p := p) (r := r) (k := k) (l := l) (n := n)
    (hp := hp) (hr := hr) (hk := hk) (hkl := hkl) (hmod := hmod) (hn := hn) (hnr := hnr)

-- The initial value does not depend on the exponent.
example (k : ℕ) : gobelResidue k 3 1 1 = some 2 := rfl

-- The period is 1, and the step from 2 to 3 starts in `ZMod 1`.
example : gobelResidue 3 2 1 3 = some 0 := by
  rw [← gobelResidue_eq_of_modEq_totient 2 1 2 3 3 (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)]
  decide +kernel

-- The period is 20, and the step from 5 to 6 uses only one power of 5.
example : gobelResidue 23 5 2 6 = some 3 := by
  rw [← gobelResidue_eq_of_modEq_totient 5 2 3 23 6 (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)]
  decide +kernel

-- A divisibility test actually fails at index 19, and the failure is periodic too.
example : gobelResidue 24 19 1 19 = none := by
  rw [← gobelResidue_eq_of_modEq_totient 19 1 6 24 19 (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)]
  decide +kernel
