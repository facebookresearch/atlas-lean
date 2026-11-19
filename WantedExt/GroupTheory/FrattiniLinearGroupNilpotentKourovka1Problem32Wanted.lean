/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Frattini subgroup of a finitely generated linear group (Kourovka Notebook Problem 1.32)

Kourovka Notebook, Archive of Solved Problems, Problem 1.32 (M. I. Kargapolov): is the Frattini
subgroup of a finitely generated matrix group over a field nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.FrattiniLinearGroupNilpotentKourovka1Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.32 (M. I.
Kargapolov). UnsolvedMath record UM-00700027 (`KOU-1.32`), dataset ulamai/UnsolvedMath v1.8.0.

A matrix group over a field `K` is a subgroup of `GL_n(K)`; its Frattini subgroup is Mathlib's
`frattini` (the intersection of the maximal subgroups). Fields are taken in `Type`.
-/

/-- Kourovka 1.32 (M. I. Kargapolov): the Frattini subgroup of a finitely generated subgroup of
`GL_n(K)`, `K` a field, is nilpotent. -/
def frattiniOfFGLinearGroupNilpotent : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (G : Subgroup (GL (Fin n) K)), G.FG →
    Group.IsNilpotent (frattini G)

/--
Resolved true: the Kourovka Archive answers 1.32 "Yes, it is", citing Platonov: the Frattini
subgroup of a finitely generated linear group over a field is nilpotent. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.32 (M. I. Kargapolov); resolution:
V. P. Platonov, Soviet Math. Dokl. 7 (1966), 1557-1560, Kourovka Archive, Problem 1.32 (Yes, it is).
-/
public theorem_wanted frattiniOfFGLinearGroupNilpotent_holds : frattiniOfFGLinearGroupNilpotent

end MathlibExt.GroupTheory.FrattiniLinearGroupNilpotentKourovka1Problem32Wanted
