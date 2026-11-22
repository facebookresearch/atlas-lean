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

/-- `G` is a Frobenius group with kernel `F` and complement `H` (Kourovka 6.53): `G = F ⋊ H`
(`F` normal, `F ∩ H = 1`, `F H = G`), `H ∩ Hᵍ = 1` for every `g ∉ H`, the non-trivial elements
of `F` are exactly the elements lying in no conjugate of `H`, and `F` and `H` are
non-trivial. -/
def IsFrobeniusGroup {G : Type*} [Group G] (F H : Subgroup G) : Prop :=
  F.Normal ∧ F ⊓ H = ⊥ ∧ F ⊔ H = ⊤ ∧ F ≠ ⊥ ∧ H ≠ ⊥ ∧
    (∀ g : G, g ∉ H → H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥) ∧
    ∀ x : G, (x ∈ F ∧ x ≠ 1) ↔ ∀ g : G, x ∉ H.map (MulAut.conj g).toMonoidHom

end MathlibExt.GroupTheory.FrobeniusGroupShared
