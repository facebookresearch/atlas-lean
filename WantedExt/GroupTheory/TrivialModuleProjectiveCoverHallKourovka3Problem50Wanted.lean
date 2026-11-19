/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Projective cover of the trivial module and Hall p'-subgroups (Kourovka Notebook Problem 3.50)

Kourovka Notebook, Archive of Solved Problems, Problem 3.50 (A. I. Saksonov): let `G` be a group of
order `p^α m`, where `p` is a prime, `p` and `m` are coprime, and let `k` be an algebraically closed
field of characteristic `p`. Is it true that if the indecomposable projective module corresponding
to the `1`-representation of `G` has `k`-dimension `p^α`, then `G` has a Hall `p'`-subgroup? The
converse is trivially true.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.TrivialModuleProjectiveCoverHallKourovka3Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.50 (A. I.
Saksonov). UnsolvedMath record UM-00700199 (`KOU-3.50`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is finite. The projective indecomposable module of the trivial representation is `kG e` for a
primitive idempotent `e` of `kG` (the only idempotents `f` with `f e = f = e f` are `0` and `e`)
with augmentation `ε(e) = 1`, `ε = MonoidAlgebra.lift k k G 1`; its dimension is that of the range
of right multiplication by `e`. A Hall `p'`-subgroup is a subgroup of order `m`.
-/

/-- Kourovka 3.50 (A. I. Saksonov): let `G` be a finite group of order `p^α m` with `p` prime and
`p ∤ m`, and let `k` be an algebraically closed field of characteristic `p`. If the indecomposable
projective `kG`-module of the trivial representation, `kG e` for a primitive idempotent `e` of `kG`
with augmentation `ε(e) = 1`, has `k`-dimension `p^α`, then `G` has a Hall `p'`-subgroup (a
subgroup of order `m`). -/
def projectiveCoverDimensionImpliesHall : Prop :=
  ∀ (p α m : ℕ) (G : Type) [Group G] [Finite G] (k : Type) [Field k] [IsAlgClosed k] [CharP k p],
    p.Prime → Nat.card G = p ^ α * m → Nat.Coprime p m →
    (∃ e : MonoidAlgebra k G, IsIdempotentElem e ∧
      (∀ f : MonoidAlgebra k G, IsIdempotentElem f → f * e = f → e * f = f → f = 0 ∨ f = e) ∧
      MonoidAlgebra.lift k k G 1 e = 1 ∧
      Module.finrank k (LinearMap.range (LinearMap.mulRight k e)) = p ^ α) →
    ∃ H : Subgroup G, Nat.card H = m

/--
Resolved false: the Kourovka Archive answers 3.50 "No, not always", citing Example 4.5 of Willems
(Math. Z. 171 (1980)): a finite group without a Hall `p'`-subgroup whose projective cover of the
trivial module over an algebraically closed field of characteristic `p` has dimension `p^α`. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.50 (A. I. Saksonov);
resolution: W. Willems, Math. Z. 171 (1980), 163-174, Example 4.5; Kourovka Archive, Problem 3.50:
No, not always: see Example 4.5, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted projectiveCoverDimensionImpliesHall_refuted :
    ¬ projectiveCoverDimensionImpliesHall

end MathlibExt.GroupTheory.TrivialModuleProjectiveCoverHallKourovka3Problem50Wanted
