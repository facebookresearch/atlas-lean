/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Frobenius groups with kernel and complement (Kourovka Notebook Problems 6.53 and 6.54)

Shared definition for the Frobenius-group problems of the Kourovka Notebook: `G = F ⋊ H` is a
Frobenius group with kernel `F` and complement `H` in the sense of Problem 6.53 (no finiteness is
assumed). Problem 6.53 uses it for the possible kernels and complements, Problem 6.54 for infinite
finitely generated Frobenius groups. The definition is the one used by the OpenConjectures entry for
Kourovka Problem 6.55.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.End

@[expose] public section

namespace MathlibExt.GroupTheory.FrobeniusGroupShared

/-- **Frobenius group with given kernel and complement.** For subgroups $F$ and $H$ of a group $G$,
$G$ is a Frobenius group with kernel $F$ and complement $H$ (Kourovka 6.53) if $G = F \rtimes H$
(that is, $F$ is normal in $G$, $F \cap H = 1$ and $FH = G$), $F \ne 1$, $H \ne 1$,
$H \cap gHg^{-1} = 1$ for every $g \in G \setminus H$, and the non-trivial elements of $F$ are
exactly the elements of $G$ that lie in no conjugate $gHg^{-1}$ of $H$. -/
def IsFrobeniusGroup {G : Type*} [Group G] (F H : Subgroup G) : Prop :=
  F.Normal ∧ F ⊓ H = ⊥ ∧ F ⊔ H = ⊤ ∧ F ≠ ⊥ ∧ H ≠ ⊥ ∧
    (∀ g : G, g ∉ H → H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥) ∧
    ∀ x : G, (x ∈ F ∧ x ≠ 1) ↔ ∀ g : G, x ∉ H.map (MulAut.conj g).toMonoidHom

end MathlibExt.GroupTheory.FrobeniusGroupShared
