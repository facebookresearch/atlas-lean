/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Actual inactive factors of even permutations

A permutation fixing a specified active set restricts to its complement,
and extending that restriction is the original permutation. The existing
support/sign theorem preserves its evenness. Adding five identity
coordinates places the SAME restriction in an alternating group whose
perfectness is already proved in Mathlib. These are actual algebraic
factors for the full parameterized inactive-loop construction.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Equiv.Perm

variable {Index : Type u}

private theorem fixedSet_invariant (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x) : ∀ x, σ x ∈ s ↔ x ∈ s := by
  intro x
  constructor
  · intro hx
    have he : σ (σ x) = σ x := hfix (σ x) hx
    have hx' : σ x = x := σ.injective he
    exact hx' ▸ hx
  · intro hx
    rw [hfix x hx]
    exact hx

private theorem support_not_fixedSet (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x) : ∀ x, σ x ≠ x → x ∉ s :=
  fun x hx hs => hx (hfix x hs)

/-- The original permutation restricted to the literal complement of its
fixed active set. No complementary permutation witness is supplied. -/
public def inactiveRestriction (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x) :
    Equiv.Perm {x : Index // x ∉ s} :=
  σ.subtypePerm (fun x => not_congr (fixedSet_invariant σ s hfix x))

private theorem inactiveRestriction_apply_computed (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x)
    (x : {x : Index // x ∉ s}) :
    (inactiveRestriction σ s hfix x).val = σ x.val := rfl

/-- The restricted permutation has the SAME original value on every
literal inactive point. -/
public theorem inactiveRestriction_apply (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x)
    (x : {x : Index // x ∉ s}) :
    (inactiveRestriction σ s hfix x).val = σ x.val :=
  inactiveRestriction_apply_computed σ s hfix x

private theorem inactiveRestriction_extends_computed (σ : Equiv.Perm Index) (s : Set Index)
    [DecidablePred (· ∈ s)] (hfix : ∀ x ∈ s, σ x = x) :
    Equiv.Perm.ofSubtype (inactiveRestriction σ s hfix) = σ := by
  have hp : ∀ x : Index, σ x ∉ s ↔ x ∉ s :=
    fun x => not_congr (fixedSet_invariant σ s hfix x)
  exact Equiv.Perm.ofSubtype_subtypePerm
    (α := Index) (p := fun x : Index => x ∉ s) (f := σ)
    hp (support_not_fixedSet σ s hfix)

/-- Extending the actual inactive restriction by the identity recovers
the WHOLE original permutation. -/
public theorem inactiveRestriction_extends (σ : Equiv.Perm Index) (s : Set Index)
    [DecidablePred (· ∈ s)] (hfix : ∀ x ∈ s, σ x = x) :
    Equiv.Perm.ofSubtype (inactiveRestriction σ s hfix) = σ :=
  inactiveRestriction_extends_computed σ s hfix

variable [Fintype Index] [DecidableEq Index]

/-- The restriction has the original sign, since the permutation is the
identity on the complementary active set. -/
public theorem inactiveRestriction_sign (σ : Equiv.Perm Index) (s : Set Index)
    [DecidablePred (· ∈ s)] (hfix : ∀ x ∈ s, σ x = x) :
    Equiv.Perm.sign (inactiveRestriction σ s hfix) = Equiv.Perm.sign σ :=
  sign_subtypePerm σ (fun x => not_congr (fixedSet_invariant σ s hfix x))
    (support_not_fixedSet σ s hfix)

section PurePaddedPermutation

omit [Fintype Index] [DecidableEq Index]

/-- Five identity coordinates are added only to the inactive finite index;
the coefficient ring is not changed. -/
public abbrev InactivePaddedIndex (s : Set Index) : Type u :=
  {x : Index // x ∉ s} ⊕ Fin 5

/-- The same actual inactive permutation with an identity on those five
additional coordinates. -/
public def paddedInactivePermutation (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x) :
    Equiv.Perm (InactivePaddedIndex s) :=
  Equiv.sumCongr (inactiveRestriction σ s hfix) (1 : Equiv.Perm (Fin 5))

private theorem paddedInactivePermutation_eq_computed (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x) :
    paddedInactivePermutation σ s hfix =
      Equiv.sumCongr (inactiveRestriction σ s hfix) (1 : Equiv.Perm (Fin 5)) := rfl

/-- The whole padded permutation retains its original restriction and
the literal identity on the five added coordinates. -/
public theorem paddedInactivePermutation_eq (σ : Equiv.Perm Index) (s : Set Index)
    (hfix : ∀ x ∈ s, σ x = x) :
    paddedInactivePermutation σ s hfix =
      Equiv.sumCongr (inactiveRestriction σ s hfix) (1 : Equiv.Perm (Fin 5)) :=
  paddedInactivePermutation_eq_computed σ s hfix

end PurePaddedPermutation

/-- An even original permutation gives an actual member of the padded
inactive alternating group. -/
public theorem paddedInactivePermutation_even (σ : Equiv.Perm Index) (s : Set Index)
    [DecidablePred (· ∈ s)] (hfix : ∀ x ∈ s, σ x = x)
    (heven : Equiv.Perm.sign σ = 1) :
    paddedInactivePermutation σ s hfix ∈ alternatingGroup (InactivePaddedIndex s) := by
  rw [mem_alternatingGroup]
  change Equiv.Perm.sign
    (Equiv.sumCongr (inactiveRestriction σ s hfix) (1 : Equiv.Perm (Fin 5))) = 1
  rw [sign_sumCongr, inactiveRestriction_sign, heven, map_one, mul_one]

/-- This genuine finite alternating group is perfect by its existing
commutator theorem. No finite general-linear commutator claim is used. -/
public theorem inactiveAlternating_isPerfect (s : Set Index)
    [DecidablePred (· ∈ s)] :
    Group.IsPerfect (alternatingGroup (InactivePaddedIndex s)) := by
  apply Group.isPerfect_def.mpr
  apply commutator_alternatingGroup_eq_top
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
  exact Nat.le_add_left 5 _

end Equiv.Perm
