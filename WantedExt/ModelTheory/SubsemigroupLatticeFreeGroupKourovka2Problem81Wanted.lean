/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recognizing free groups by subsemigroup lattices (Kourovka Notebook Problem 2.81)

Kourovka Notebook, Problem 2.81 (L. N. Shevrin), marked solved in the 21st issue: (a) does there
exist an axiomatizable class of lattices `𝔎` such that the lattice of all subsemigroups of a
semigroup `S` is isomorphic to some lattice in `𝔎` if and only if `S` is a free group? (b) The same
question for free abelian groups.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.ModelTheory.Order

@[expose] public section

namespace MathlibExt.ModelTheory.SubsemigroupLatticeFreeGroupKourovka2Problem81Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 2.81 (L. N. Shevrin). UnsolvedMath record
UM-00700151 (`KOU-2.81`), dataset ulamai/UnsolvedMath v1.8.0.

Axiomatizable means elementary: `𝔎` is the class of lattices satisfying a first-order theory `T` in
Mathlib's language of orders (lattice operations are definable from `≤`), so the lattice of
subsemigroups (the empty subsemigroup included) is isomorphic to a lattice in `𝔎` exactly when it
satisfies `T`. Semigroups are nonempty, as in the resolving preprint; free groups and free abelian
groups of every rank, `0` included, count. The resolution is an AI-generated solution confirmed by
O. G. Kharlampovich and accepted by the editors.
-/

open FirstOrder FirstOrder.Language

/-- The semigroup `S` is a free group: its multiplication is that of a free group, i.e. `S` is
multiplicatively isomorphic to `FreeGroup X` for some `X` (rank `0` allowed). -/
def IsFreeGroupSemigroup (S : Type) [Semigroup S] : Prop :=
  ∃ X : Type, Nonempty (S ≃* FreeGroup X)

/-- The semigroup `S` is a free abelian group (of any rank, `0` included). -/
def IsFreeAbelianGroupSemigroup (S : Type) [Semigroup S] : Prop :=
  ∃ X : Type, Nonempty (S ≃* Multiplicative (FreeAbelianGroup X))

/-- Kourovka 2.81(a) (L. N. Shevrin): some axiomatizable class of lattices `𝔎` detects free
groups: there is a first-order theory `T` in the language of orders such that, for every
(nonempty) semigroup `S`, the lattice of all subsemigroups of `S` (the empty one included)
satisfies `T`, i.e. is isomorphic to a lattice in `𝔎 = Mod T`, exactly when `S` is a free
group. -/
def axiomatizableClassDetectsFreeGroups : Prop :=
  ∃ T : Language.order.Theory, ∀ (S : Type) [Semigroup S] [Nonempty S],
    (letI := Language.orderStructure (Subsemigroup S); Subsemigroup S ⊨ T) ↔
      IsFreeGroupSemigroup S

/-- Kourovka 2.81(b): the same with free abelian groups. -/
def axiomatizableClassDetectsFreeAbelianGroups : Prop :=
  ∃ T : Language.order.Theory, ∀ (S : Type) [Semigroup S] [Nonempty S],
    (letI := Language.orderStructure (Subsemigroup S); Subsemigroup S ⊨ T) ↔
      IsFreeAbelianGroupSemigroup S

/--
Resolved true: the Kourovka Notebook (21st issue) answers 2.81(a) "Yes", by an AI-generated solution
confirmed by O. G. Kharlampovich: Jayadevan (2026) gives a single lattice sentence `Φ_fr` such that
the subsemigroup lattice of a nonempty semigroup `S` satisfies `Φ_fr` exactly when `S` is a free
group (of any rank). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 2.81 (L. N. Shevrin);
resolution: A. Jayadevan, Finite first-order recognition of freeness from subsemigroup lattices,
preprint, version 1.0.0, Zenodo, 12 September 2026, Abstract: sentences Φ_fr and Φ_ab in the
language {∧, ∨} such that L(S) ⊨ Φ_fr exactly when the nonempty semigroup S is a free group and L(S)
⊨ Φ_ab exactly when S is a free abelian group, ranks arbitrary including zero; the Kourovka Notebook
(21st issue) marks 2.81 solved (AI solution confirmed by O. G. Kharlampovich),
https://zenodo.org/records/22721223.
-/
public theorem_wanted axiomatizableClassDetectsFreeGroups_holds :
    axiomatizableClassDetectsFreeGroups

/--
Resolved true: the Kourovka Notebook (21st issue) answers 2.81(b) "Yes", by the same AI-generated
solution confirmed by O. G. Kharlampovich: Jayadevan (2026) gives a single lattice sentence `Φ_ab`
that holds in the subsemigroup lattice of a nonempty semigroup `S` exactly when `S` is a free
abelian group (of any rank). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 2.81 (L. N.
Shevrin); resolution: A. Jayadevan, Finite first-order recognition of freeness from subsemigroup
lattices, preprint, version 1.0.0, Zenodo, 12 September 2026, Abstract: sentences Φ_fr and Φ_ab in
the language {∧, ∨} such that L(S) ⊨ Φ_fr exactly when the nonempty semigroup S is a free group and
L(S) ⊨ Φ_ab exactly when S is a free abelian group, ranks arbitrary including zero; the Kourovka
Notebook (21st issue) marks 2.81 solved (AI solution confirmed by O. G. Kharlampovich),
https://zenodo.org/records/22721223.
-/
public theorem_wanted axiomatizableClassDetectsFreeAbelianGroups_holds :
    axiomatizableClassDetectsFreeAbelianGroups

end MathlibExt.ModelTheory.SubsemigroupLatticeFreeGroupKourovka2Problem81Wanted
