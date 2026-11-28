/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.LimOne
import Mathlib.Data.ZMod.Basic

/-! Tests for `MathlibExt.Algebra.Homology.LimOne`. -/

set_option autoImplicit false

#check @LimOne.differenceMap
#check @LimOne.differenceMap_apply
#check @LimOne.mem_ker_differenceMap_iff
#check @LimOne.limOne
#check @LimOne.differenceMap_surjective
#check @LimOne.subsingleton_limOne

/-- The reductions `ℤ/ℓ^(n+2) → ℤ/ℓ^(n+1)`, the tower `(ℤ/ℓ^(n+1))` of the `ℓ`-adic integers. -/
def reduction (ℓ : ℕ) (n : ℕ) : ZMod (ℓ ^ (n + 1 + 1)) →+ ZMod (ℓ ^ (n + 1)) :=
  (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))).toAddMonoidHom

/-- `R¹ lim (ℤ/ℓ^(n+1)) = 0`: the reductions are surjective. -/
example (ℓ : ℕ) :
    Subsingleton (LimOne.limOne (A := fun n => ZMod (ℓ ^ (n + 1))) (reduction ℓ)) :=
  LimOne.subsingleton_limOne _ fun _ => ZMod.ringHom_surjective _

/-- For the constant tower of `ℤ` with identity transition maps, the kernel of the difference map
is the constant sequences. -/
example (x : ℕ → ℤ) :
    x ∈ (LimOne.differenceMap (A := fun _ => ℤ) fun _ => AddMonoidHom.id ℤ).ker ↔
      ∀ n, x (n + 1) = x n :=
  LimOne.mem_ker_differenceMap_iff _ x

/-- For the constant tower of `ℤ` with identity transition maps, `R¹ lim = 0`. -/
example : Subsingleton (LimOne.limOne (A := fun _ => ℤ) fun _ => AddMonoidHom.id ℤ) :=
  LimOne.subsingleton_limOne _ fun _ => Function.surjective_id

#print axioms LimOne.differenceMap
#print axioms LimOne.mem_ker_differenceMap_iff
#print axioms LimOne.differenceMap_surjective
#print axioms LimOne.subsingleton_limOne
