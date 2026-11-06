/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthSignSpace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! The genuine equal-sign Mathieu monomial subgroup in the sixth spatial flag stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem golaySign_zero : golaySignIsometry 0 = 1 := golaySignHom.map_one

private theorem golaySign_add (d e : golayCode) :
    golaySignIsometry (d + e) = golaySignIsometry d * golaySignIsometry e :=
  golaySignHom.map_mul (Multiplicative.ofAdd d) (Multiplicative.ofAdd e)

private theorem golaySign_inv (d : golayCode) : (golaySignIsometry d)⁻¹ = golaySignIsometry d := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

private theorem golayPermutation_zero : golayPermutationIsometry 1 = 1 :=
  golayPermutationHom.map_one

private theorem golayPermutation_mul (p q : golayAutomorphismSubgroup) :
    golayPermutationIsometry (p * q) = golayPermutationIsometry p * golayPermutationIsometry q :=
  golayPermutationHom.map_mul p q

private theorem golayPermutation_inv (p : golayAutomorphismSubgroup) :
    (golayPermutationIsometry p)⁻¹ = golayPermutationIsometry p⁻¹ :=
  (golayPermutationHom.map_inv p).symm

/-- A genuine equal-sign codeword followed by an actual flag permutation. -/
def leechRootedA2SixthMonomialPair
    (a : leechRootedA2SixthSignSpace × leechRootedA2SixthPermutationFlag) : leechIsomSubgroup :=
  golayMonomialPair (a.1.val, a.2.val)

/-- The actual constructed monomial subgroup preserving the sixth spatial rooted flag. -/
def leechRootedA2SixthMonomialSubgroup : Subgroup leechIsomSubgroup where
  carrier := {g | ∃ c : leechRootedA2SixthSignSpace, ∃ p : leechRootedA2SixthPermutationFlag,
    g = leechRootedA2SixthMonomialPair (c, p)}
  one_mem' := ⟨0, 1, by
    change 1 = golaySignIsometry 0 * golayPermutationIsometry 1
    rw [golaySign_zero, golayPermutation_zero, mul_one]⟩
  mul_mem' := by
    rintro a b ⟨c, p, rfl⟩ ⟨d, q, rfl⟩
    let e : leechRootedA2SixthSignSpace :=
      ⟨golayCodePermutation p.val d.val,
        leechRootedA2SixthSignSpace_permutation p.val p.property d⟩
    refine ⟨c + e, p * q, ?_⟩
    change (golaySignIsometry c.val * golayPermutationIsometry p.val) *
      (golaySignIsometry d.val * golayPermutationIsometry q.val) =
        golaySignIsometry (c.val + e.val) * golayPermutationIsometry (p.val * q.val)
    rw [golaySign_add, golayPermutation_mul]
    calc
      _ = golaySignIsometry c.val *
          (golayPermutationIsometry p.val * golaySignIsometry d.val) *
            golayPermutationIsometry q.val := by simp only [mul_assoc]
      _ = _ := by
        rw [golayPermutation_sign_commute]
        rfl
  inv_mem' := by
    rintro a ⟨c, p, rfl⟩
    let e : leechRootedA2SixthSignSpace :=
      ⟨golayCodePermutation p.val⁻¹ c.val,
        leechRootedA2SixthSignSpace_permutation p.val⁻¹
          (leechRootedA2SixthPermutationFlag.inv_mem p.property) c⟩
    refine ⟨e, p⁻¹, ?_⟩
    change (golaySignIsometry c.val * golayPermutationIsometry p.val)⁻¹ =
      golaySignIsometry e.val * golayPermutationIsometry p.val⁻¹
    rw [mul_inv_rev, golaySign_inv, golayPermutation_inv, golayPermutation_sign_commute]

/-- Distinct restricted source pairs still give distinct actual original monomial isometries. -/
theorem leechRootedA2SixthMonomialPair_injective :
    Function.Injective leechRootedA2SixthMonomialPair := by
  rintro ⟨c, p⟩ ⟨d, q⟩ h
  have he := golayMonomialPair_injective h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact Subtype.ext (congrArg Prod.snd he)

/-- The genuine restricted codeword/permutation pairs enumerate the actual subgroup. -/
def leechRootedA2SixthMonomialEnumeration
    (a : leechRootedA2SixthSignSpace × leechRootedA2SixthPermutationFlag) :
    leechRootedA2SixthMonomialSubgroup := ⟨leechRootedA2SixthMonomialPair a, a.1, a.2, rfl⟩

/-- This restricted original monomial parametrization is genuinely bijective. -/
theorem leechRootedA2SixthMonomialEnumeration_bijective :
    Function.Bijective leechRootedA2SixthMonomialEnumeration := by
  constructor
  · intro a b h
    exact leechRootedA2SixthMonomialPair_injective (congrArg Subtype.val h)
  · rintro ⟨g, c, p, h⟩
    exact ⟨(c, p), Subtype.ext h.symm⟩

/-- The constructed actual sixth flag monomial subgroup has 41287680 elements in Co0. -/
theorem leechRootedA2SixthMonomialSubgroup_card :
    Nat.card leechRootedA2SixthMonomialSubgroup = 41287680 := by
  rw [← Nat.card_congr (Equiv.ofBijective leechRootedA2SixthMonomialEnumeration
    leechRootedA2SixthMonomialEnumeration_bijective), Nat.card_prod,
    leechRootedA2SixthSignSpace_card, leechRootedA2SixthPermutationFlag_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
