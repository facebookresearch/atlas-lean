/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSignCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPointwiseSection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! The actual positive pointwise monomial subgroup of the recovered coordinate octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual pointwise octad permutations preserve the positive sign subspace. -/
theorem generatedNinth_octad_sign_space_permutation (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedNinthSectionOctadPointwise)
    (c : generatedNinthOctadSignSpace generatedNinthSectionCode) :
    golayCodePermutation p c.val ∈ generatedNinthOctadSignSpace generatedNinthSectionCode := by
  intro i hi
  have hpi : p.val.symm i = i := p.val.symm_apply_eq.mpr (hp i hi).symm
  change c.val.val (p.val.symm i) = 0
  rw [hpi]
  exact c.property i hi

private theorem generatedNinthOctadSign_zero : golaySignIsometry 0 = 1 := golaySignHom.map_one

private theorem generatedNinthOctadSign_add (d e : golayCode) :
    golaySignIsometry (d + e) = golaySignIsometry d * golaySignIsometry e :=
  golaySignHom.map_mul (Multiplicative.ofAdd d) (Multiplicative.ofAdd e)

private theorem generatedNinthOctadSign_inv (d : golayCode) :
    (golaySignIsometry d)⁻¹ = golaySignIsometry d := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

private theorem generatedNinthOctadPermutation_zero : golayPermutationIsometry 1 = 1 :=
  golayPermutationHom.map_one

private theorem generatedNinthOctadPermutation_mul (p q : golayAutomorphismSubgroup) :
    golayPermutationIsometry (p * q) = golayPermutationIsometry p * golayPermutationIsometry q :=
  golayPermutationHom.map_mul p q

private theorem generatedNinthOctadPermutation_inv (p : golayAutomorphismSubgroup) :
    (golayPermutationIsometry p)⁻¹ = golayPermutationIsometry p⁻¹ :=
  (golayPermutationHom.map_inv p).symm

/-- A genuine octad-positive codeword followed by an actual pointwise octad permutation. -/
def generatedNinthOctadMonomialPair
    (a : (generatedNinthOctadSignSpace generatedNinthSectionCode) ×
      generatedNinthSectionOctadPointwise) : leechIsomSubgroup :=
  golayMonomialPair (a.1.val, a.2.val)

/-- The actual constructed monomial subgroup preserving the recovered octad pointwise. -/
def generatedNinthOctadMonomialSubgroup : Subgroup leechIsomSubgroup where
  carrier := {g | ∃ c : (generatedNinthOctadSignSpace generatedNinthSectionCode),
    ∃ p : generatedNinthSectionOctadPointwise,
    g = generatedNinthOctadMonomialPair (c, p)}
  one_mem' := ⟨0, 1, by
    change 1 = golaySignIsometry 0 * golayPermutationIsometry 1
    rw [generatedNinthOctadSign_zero, generatedNinthOctadPermutation_zero, mul_one]⟩
  mul_mem' := by
    rintro a b ⟨c, p, rfl⟩ ⟨d, q, rfl⟩
    let e : (generatedNinthOctadSignSpace generatedNinthSectionCode) :=
      ⟨golayCodePermutation p.val d.val,
        generatedNinth_octad_sign_space_permutation p.val p.property d⟩
    refine ⟨c + e, p * q, ?_⟩
    change (golaySignIsometry c.val * golayPermutationIsometry p.val) *
      (golaySignIsometry d.val * golayPermutationIsometry q.val) =
        golaySignIsometry (c.val + e.val) * golayPermutationIsometry (p.val * q.val)
    rw [generatedNinthOctadSign_add, generatedNinthOctadPermutation_mul]
    calc
      _ = golaySignIsometry c.val *
          (golayPermutationIsometry p.val * golaySignIsometry d.val) *
            golayPermutationIsometry q.val := by simp only [mul_assoc]
      _ = _ := by
        rw [golayPermutation_sign_commute]
        rfl
  inv_mem' := by
    rintro a ⟨c, p, rfl⟩
    let e : (generatedNinthOctadSignSpace generatedNinthSectionCode) :=
      ⟨golayCodePermutation p.val⁻¹ c.val,
        generatedNinth_octad_sign_space_permutation p.val⁻¹
          (generatedNinthSectionOctadPointwise.inv_mem p.property) c⟩
    refine ⟨e, p⁻¹, ?_⟩
    change (golaySignIsometry c.val * golayPermutationIsometry p.val)⁻¹ =
      golaySignIsometry e.val * golayPermutationIsometry p.val⁻¹
    rw [mul_inv_rev, generatedNinthOctadSign_inv, generatedNinthOctadPermutation_inv,
      golayPermutation_sign_commute]

/-- Distinct restricted source pairs still give distinct actual original monomial isometries. -/
theorem generatedNinthOctadMonomialPair_injective :
    Function.Injective generatedNinthOctadMonomialPair := by
  rintro ⟨c, p⟩ ⟨d, q⟩ h
  have he := golayMonomialPair_injective h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact Subtype.ext (congrArg Prod.snd he)

/-- The genuine restricted codeword/permutation pairs enumerate the actual subgroup. -/
def generatedNinthOctadMonomialEnumeration
    (a : (generatedNinthOctadSignSpace generatedNinthSectionCode) ×
      generatedNinthSectionOctadPointwise) :
    generatedNinthOctadMonomialSubgroup := ⟨generatedNinthOctadMonomialPair a, a.1, a.2, rfl⟩

/-- This restricted original monomial parametrization is genuinely bijective. -/
theorem generatedNinthOctadMonomialEnumeration_bijective :
    Function.Bijective generatedNinthOctadMonomialEnumeration := by
  constructor
  · intro a b h
    exact generatedNinthOctadMonomialPair_injective (congrArg Subtype.val h)
  · rintro ⟨g, c, p, h⟩
    exact ⟨(c, p), Subtype.ext h.symm⟩

/-- The constructed actual octad pointwise monomial subgroup has 512 elements in Co0. -/
theorem generatedNinthOctadMonomialSubgroup_card :
    Nat.card generatedNinthOctadMonomialSubgroup = 512 := by
  rw [← Nat.card_congr (Equiv.ofBijective generatedNinthOctadMonomialEnumeration
    generatedNinthOctadMonomialEnumeration_bijective), Nat.card_prod,
    generatedNinth_section_octad_sign_space_card, generatedNinth_section_octad_pointwise_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
