/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynormal subgroups that are not paranormal (Kourovka Notebook Problem 14.50)

Kourovka Notebook, Archive of Solved Problems, Problem 14.50 (Z. I. Borevich; A. S. Kondratiev): a
subgroup `A` of `G` is paranormal (polynormal) if `A^x ≤ ⟨A^u | u ∈ ⟨A, A^x⟩⟩` (respectively `A^x ≤
⟨A^u | u ∈ A^⟨x⟩⟩`) for every `x ∈ G`. Is every polynormal subgroup of a finite group paranormal?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.PolynormalParanormalSubgroupKourovka14Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.50 (Z. I.
Borevich; A. S. Kondratiev). UnsolvedMath record UM-00701035 (`KOU-14.50`), dataset
ulamai/UnsolvedMath v1.8.0.

`A^x = x⁻¹ A x` and `A^⟨x⟩ = ⟨A^(xⁿ) | n ∈ ℤ⟩`. Both conditions quantify over all `x` and take `u`
from a subgroup, so they do not depend on the conjugation convention.
-/

variable {G : Type*} [Group G]

/-- The conjugate subgroup `A^x = x⁻¹ A x`. -/
def conjSubgroup (A : Subgroup G) (x : G) : Subgroup G :=
  A.map (MulAut.conj x⁻¹).toMonoidHom

/-- `A` is paranormal (Z. I. Borevich): `A^x ≤ ⟨A^u | u ∈ ⟨A, A^x⟩⟩` for every `x ∈ G`. -/
def IsParanormal (A : Subgroup G) : Prop :=
  ∀ x : G, conjSubgroup A x ≤ ⨆ u ∈ A ⊔ conjSubgroup A x, conjSubgroup A u

/-- `A` is polynormal (Z. I. Borevich): `A^x ≤ ⟨A^u | u ∈ A^⟨x⟩⟩` for every `x ∈ G`, where
`A^⟨x⟩ = ⟨A^(xⁿ) | n ∈ ℤ⟩`. -/
def IsPolynormal (A : Subgroup G) : Prop :=
  ∀ x : G, conjSubgroup A x ≤ ⨆ u ∈ (⨆ n : ℤ, conjSubgroup A (x ^ n)), conjSubgroup A u

/-- Kourovka 14.50 (Z. I. Borevich; A. S. Kondratiev): every polynormal subgroup of a finite group
is paranormal. -/
def polynormalImpliesParanormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsPolynormal A → IsParanormal A

/--
Resolved false: the Kourovka Archive answers 14.50 "Not always", citing Mysovskikh: some finite
group has a polynormal subgroup that is not paranormal. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 14.50 (Z. I. Borevich; A. S. Kondratiev); resolution: V.
I. Mysovskikh, Dokl. Math. 60 (1999), 71-72, Kourovka Archive, Problem 14.50 (answer: Not always).
-/
public theorem_wanted polynormalImpliesParanormal_refuted : ¬ polynormalImpliesParanormal

end MathlibExt.GroupTheory.PolynormalParanormalSubgroupKourovka14Problem50Wanted
