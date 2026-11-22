/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Quiver.Path

/-!
# Extension and cancellation of full native paths under endpoint equality

The original full path concatenation is cancelled only after the actual
original endpoint equalities are retained. Heterogeneous equality
records those exact endpoints; no original arrow is replaced.
Path extension retains the complete original prefix and edge at those endpoints.
-/

@[expose] public section

universe u v
namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V]

/-- Equal endpoints and whole path/edge readbacks retain the native path constructor. -/
lemma cons_heq {a a' b b' c c' : V}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {p : Path a b} {q : Path a' b'} (hp : HEq p q)
    {e : b ⟶ c} {f : b' ⟶ c'} (he : HEq e f) : HEq (p.cons e) (q.cons f) := by
  cases ha
  cases hb
  cases hc
  cases eq_of_heq hp
  cases eq_of_heq he
  rfl

/-- Complete native path cancellation retains both original endpoints. -/
lemma comp_heq_cancel_left {x y z x' y' z' : V} (hx : x = x') (hy : y = y') (hz : z = z')
    {a : Path x y} {a' : Path x' y'} {b : Path y z} {b' : Path y' z'}
    (ha : HEq a a') (hab : HEq (a.comp b) (a'.comp b')) : HEq b b' := by
  subst x'
  subst y'
  subst z'
  have h := eq_of_heq ha
  subst a'
  exact heq_of_eq (comp_injective_right a (eq_of_heq hab))

end Quiver.Path
