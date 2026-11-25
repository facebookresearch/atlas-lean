/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shortest elements of normal closures in free groups (Kourovka Notebook Problem 11.82)

Kourovka Notebook, Archive of Solved Problems, Problem 11.82 (V. N. Remeslennikov): let `R` be the
normal closure of an element `r` in a free group `F` with the natural length function, and `s` an
element of minimal length in `R`. Is `s` conjugate to one of `r`, `r⁻¹`, `[r, f]`, `[r⁻¹, f]` for
some `f ∈ F`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

namespace MathlibExt.GroupTheory.NormalClosureMinimalElementKourovka11Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.82 (V. N.
Remeslennikov). UnsolvedMath record UM-00700774 (`KOU-11.82`), dataset ulamai/UnsolvedMath v1.8.0.

The length is the reduced word length `FreeGroup.norm`. "Minimal length in `R`" is among the
nontrivial elements of `R` (the identity has length 0 and is `[r, 1]`), and `r ≠ 1`. Commutators
follow the source convention `[x, y] = x⁻¹ y⁻¹ x y`. The free group has an arbitrary basis `α :
Type`.
-/

/-- **Shortest elements of normal closures in free groups (Kourovka 11.82, Remeslennikov).** The
statement that for every free group $F$ and every $r \ne 1$ in $F$, if $s$ is a nontrivial element
of the normal closure $R$ of $r$ in $F$ whose reduced word length is minimal among the nontrivial
elements of $R$, then $s$ is conjugate to $r$, to $r^{-1}$, or, for some $f \in F$, to
$[r, f] = r^{-1} f^{-1} r f$ or to $[r^{-1}, f] = r f^{-1} r^{-1} f$. -/
def minimalNormalClosureElementConj : Prop :=
  ∀ (α : Type) [DecidableEq α] (r : FreeGroup α), r ≠ 1 →
    ∀ s ∈ Subgroup.normalClosure {r}, s ≠ 1 →
    (∀ t ∈ Subgroup.normalClosure {r}, t ≠ 1 → s.norm ≤ t.norm) →
    IsConj s r ∨ IsConj s r⁻¹ ∨
      ∃ f : FreeGroup α, IsConj s (r⁻¹ * f⁻¹ * r * f) ∨ IsConj s (r * f⁻¹ * r⁻¹ * f)

/--
**Negative answer to Kourovka 11.82 on shortest elements of normal closures.** There are a free
group $F$, an element $r \ne 1$ of $F$, and a nontrivial element $s$ of the normal closure $R$ of
$r$ in $F$ whose reduced word length is minimal among the nontrivial elements of $R$, such that $s$
is conjugate neither to $r$ nor to $r^{-1}$, nor, for any $f \in F$, to
$[r, f] = r^{-1} f^{-1} r f$ or to $[r^{-1}, f] = r f^{-1} r^{-1} f$.

The Kourovka Archive answers 11.82 "No, not always" (McCool).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.82 (V. N.
Remeslennikov); resolution: J. McCool, Glasgow Math. J. 43, no. 1 (2001), 123-124, Kourovka Archive,
Problem 11.82: "No, not always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted minimalNormalClosureElementConj_refuted : ¬ minimalNormalClosureElementConj

end MathlibExt.GroupTheory.NormalClosureMinimalElementKourovka11Problem82Wanted
