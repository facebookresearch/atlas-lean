/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.Solvable
import Mathlib.FieldTheory.AbelRuffini

/-!
Canonical symmetric-group nonsolvability and irreducible-root radical obstruction. No
alternating-group simplicity assertion.
-/

set_option autoImplicit false
noncomputable section

#check Group.IsSolvable

example : ¬ Group.IsSolvable (Equiv.Perm (Fin 5)) := Equiv.Perm.not_isSolvable_fin_5
example (X : Type*) (h : 5 ≤ Cardinal.mk X) : ¬ Group.IsSolvable (Equiv.Perm X) :=
  Equiv.Perm.not_isSolvable X h

example {F E : Type*} [Field F] [Field E] [Algebra F E]
    {x : E} (hx : x ∈ solvableByRad F E) {p : Polynomial F}
    (hp : Irreducible p) (hpx : Polynomial.aeval x p = 0) : Group.IsSolvable p.Gal :=
  isSolvable_gal_of_irreducible hx hp hpx

#print axioms Group.IsSolvable
#print axioms Equiv.Perm.not_isSolvable_fin_5
#print axioms Equiv.Perm.not_isSolvable
#print axioms isSolvable_gal_of_irreducible

end
