/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean`,
`Theorems/Thm_ModularForm_S2_Gamma0_one_eq_zero.lean`,
`P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` and
`P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed, the names restated in Mathlib style, and the proofs rewritten to use
Mathlib's `CuspForm` / `ModularForm` API directly.
-/

module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic

/-!
# Vanishing of weight-two cusp forms on `Γ₀(1)` and `Γ₀(2)`

The space of weight-two cusp forms on `Γ₀(2)` is zero. This is the final
step of the classical proof of Fermat's Last Theorem via the Frey curve:
a Frey curve is modular, Ribet's level lowering puts its mod-`p`
representation in `S₂(Γ₀(2))`, and that space being zero gives the
contradiction. Along the way we record the two reusable ingredients, the
product norm of a cusp form over a finite-index subgroup and the index
`[SL(2, ℤ) : Γ₀(2)] = 3`, which let the weight-two case be reduced to the
weight-six level-one dimension formula.

## Mathematical references

For the classical level-one dimension formula, see Jean-Pierre Serre,
*A Course in Arithmetic*, Springer (1973), Chapter VII ("Modular forms").

The formal norm and vanishing inputs are in
https://github.com/leanprover-community/mathlib4 at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`:
* `Mathlib/NumberTheory/ModularForms/NormTrace.lean` defines the product
  `ModularForm.norm` and proves `ModularForm.norm_eq_zero_iff`.
* `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`
  proves `CuspForm.rank_eq_zero_of_weight_lt_twelve`, via division by
  the weight-twelve discriminant and negative-weight vanishing.

For the index and the full reduction, the pinned
`P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` cited above proves
`Gamma0_two_index_eq_three` by identifying cosets with the three nonzero
first-column vectors mod 2. The product norm of a weight-two cusp form
therefore has level one and weight six. It is a cusp form because its
factors are cusp translates; weight-six vanishing and the norm criterion
then force the original form to vanish.
-/

@[expose] public section

open UpperHalfPlane SlashInvariantForm Matrix Matrix.SpecialLinearGroup
open scoped CongruenceSubgroup MatrixGroups UpperHalfPlane

namespace CuspForm

/-- The product norm of a cusp form: for `𝒢` of finite relative index in `ℋ`,
the product of the `ℋ / 𝒢`-translates of `f`, viewed as a cusp form on the
larger group `ℋ` at weight `k * [ℋ : 𝒢]`. This lifts Mathlib's
`ModularForm.norm` to cusp forms; the only new work is checking vanishing
at the cusps, which follows because each translate is a cusp form. -/
noncomputable def norm {𝒢 : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]
    {k : ℤ} [CuspFormClass F 𝒢 k] (ℋ : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] (f : F) :
    CuspForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)) where
  __ := ModularForm.norm ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_norm, IsZeroAtImInfty,
      Filter.ZeroAtFilter]
    let := Fintype.ofFinite (ℋ ⧸ 𝒢.subgroupOf ℋ)
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    refine Filter.ZeroAtFilter.smul _ ?_
    change Filter.Tendsto _ _ (nhds 0)
    rw [show (0 : ℂ) = ∏ _q : ℋ ⧸ 𝒢.subgroupOf ℋ, (0 : ℂ) by
        rw [Finset.prod_const, Finset.card_univ, zero_pow Fintype.card_ne_zero],
      Finset.prod_fn]
    refine tendsto_finsetProd _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ ?_)
    refine (CuspForm.translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The coercion of the norm of a cusp form is the norm of its coercion as a
modular form. -/
lemma coe_norm_eq_coe_modularFormNorm {𝒢 : Subgroup (GL (Fin 2) ℝ)} {F : Type*}
    [FunLike F ℍ ℂ] {k : ℤ} [CuspFormClass F 𝒢 k] (ℋ : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] (f : F) :
    (CuspForm.norm ℋ f : ℍ → ℂ) = (ModularForm.norm ℋ f : ℍ → ℂ) := rfl

/-- The norm of a cusp form vanishes if and only if the form itself vanishes:
the norm is a product of translates, and a translate of a nonzero form is
nonzero. -/
lemma norm_eq_zero_iff {𝒢 : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]
    {k : ℤ} [CuspFormClass F 𝒢 k] (ℋ : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] (f : F) :
    CuspForm.norm ℋ f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  rw [← ModularForm.norm_eq_zero_iff ℋ f, ← DFunLike.coe_injective.eq_iff,
    ← @DFunLike.coe_injective.eq_iff (ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ))),
    coe_norm_eq_coe_modularFormNorm]
  simp only [FunLike.coe_zero]

end CuspForm

namespace CongruenceSubgroup

/-- The first column of a matrix in `SL(2, ℤ)`, reduced mod 2. Two matrices in
the same left `Γ₀(2)`-coset have the same first column mod 2, so this
descends to a map from the coset space to the nonzero vectors in
`(ZMod 2)²`, which has exactly three elements. -/
private def firstColMod2 (g : SL(2, ℤ)) : ZMod 2 × ZMod 2 :=
  ((g.1 0 0 : ZMod 2), (g.1 1 0 : ZMod 2))

private lemma det_eq_one_mod2 (g : SL(2, ℤ)) :
    (g.1 0 0 : ZMod 2) * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun n : ℤ => (n : ZMod 2)) h
  push_cast at this
  exact this

private lemma firstColMod2_ne_zero (g : SL(2, ℤ)) : firstColMod2 g ≠ 0 := by
  intro h
  rw [firstColMod2, Prod.ext_iff] at h
  obtain ⟨h00, h10⟩ := h
  simp only [Prod.fst_zero, Prod.snd_zero] at h00 h10
  have hdet := det_eq_one_mod2 g
  rw [h00, h10, zero_mul, mul_zero, sub_zero] at hdet
  exact one_ne_zero hdet.symm

private lemma Gamma0_two_diag_eq_one {h : SL(2, ℤ)}
    (hh : h ∈ Gamma0 2) : (h.1 0 0 : ZMod 2) = 1 := by
  have hh10 : (h.1 1 0 : ZMod 2) = 0 := Gamma0_mem.1 hh
  have hdet := det_eq_one_mod2 h
  rw [hh10, mul_zero, sub_zero] at hdet
  exact (show ∀ a b : ZMod 2, a * b = 1 → a = 1 by decide) _ _ hdet

private lemma firstColMod2_mul_mem (g : SL(2, ℤ)) {h : SL(2, ℤ)}
    (hh : h ∈ Gamma0 2) : firstColMod2 (g * h) = firstColMod2 g := by
  have hh10 : (h.1 1 0 : ZMod 2) = 0 := Gamma0_mem.1 hh
  have hh00 : (h.1 0 0 : ZMod 2) = 1 := Gamma0_two_diag_eq_one hh
  have hmul : ∀ i : Fin 2, (g * h).1 i 0 = g.1 i 0 * h.1 0 0 + g.1 i 1 * h.1 1 0 :=
    fun i => by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  unfold firstColMod2
  refine Prod.ext ?_ ?_ <;> simp only [hmul] <;> push_cast <;> rw [hh10, hh00] <;> ring

/-- The map from the coset space `SL(2, ℤ) / Γ₀(2)` to nonzero vectors in
`(ZMod 2)²`, induced by the first column mod 2. -/
private def cosetToProj : SL(2, ℤ) ⧸ Gamma0 2 → {p : ZMod 2 × ZMod 2 // p ≠ 0} :=
  Quotient.lift (fun g => ⟨firstColMod2 g, firstColMod2_ne_zero g⟩) fun g₁ g₂ hg => by
    have hg' : g₁⁻¹ * g₂ ∈ Gamma0 2 := QuotientGroup.leftRel_apply.mp hg
    refine Subtype.ext ?_
    change firstColMod2 g₁ = firstColMod2 g₂
    conv_rhs => rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by group]
    exact (firstColMod2_mul_mem g₁ hg').symm

private lemma cosetToProj_injective : Function.Injective cosetToProj := by
  rintro ⟨g₁⟩ ⟨g₂⟩ heq
  have heq' : firstColMod2 g₁ = firstColMod2 g₂ := congrArg Subtype.val heq
  rw [firstColMod2, firstColMod2, Prod.mk.injEq] at heq'
  obtain ⟨h00, h10⟩ := heq'
  refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
  rw [Gamma0_mem]
  have hinv10 : (g₁⁻¹).1 1 0 = -g₁.1 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp
  have hinv11 : (g₁⁻¹).1 1 1 = g₁.1 0 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp
  have hmul : (g₁⁻¹ * g₂).1 1 0
      = (g₁⁻¹).1 1 0 * g₂.1 0 0 + (g₁⁻¹).1 1 1 * g₂.1 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmul, hinv10, hinv11]
  push_cast
  rw [h00, h10]; ring

private lemma cosetToProj_surjective : Function.Surjective cosetToProj := by
  rintro ⟨p, hp⟩
  have key : p = (0, 1) ∨ p = (1, 0) ∨ p = (1, 1) :=
    (show ∀ q : ZMod 2 × ZMod 2, q ≠ 0 → q = (0, 1) ∨ q = (1, 0) ∨ q = (1, 1) by decide)
      p hp
  rcases key with rfl | rfl | rfl
  · refine ⟨QuotientGroup.mk ⟨!![(0 : ℤ), -1; 1, 0], by
        rw [Matrix.det_fin_two]; norm_num⟩, ?_⟩
    apply Subtype.ext
    dsimp only
    decide
  · refine ⟨QuotientGroup.mk 1, ?_⟩
    apply Subtype.ext
    dsimp only
    decide
  · refine ⟨QuotientGroup.mk ⟨!![(1 : ℤ), 0; 1, 1], by
        rw [Matrix.det_fin_two]; norm_num⟩, ?_⟩
    apply Subtype.ext
    dsimp only
    decide

/-- The index of `Γ₀(2)` in `SL(2, ℤ)` is 3: the cosets are classified by
the first column mod 2, and there are three nonzero vectors in `(ZMod 2)²`. -/
theorem Gamma0_two_index_eq_three : (Gamma0 2).index = 3 := by
  rw [Subgroup.index,
    Nat.card_congr (Equiv.ofBijective _ ⟨cosetToProj_injective, cosetToProj_surjective⟩),
    Nat.card_eq_fintype_card]
  decide

end CongruenceSubgroup

namespace ModularForm

/-- `Γ₀(1)` is the whole of `SL(2, ℤ)`: the congruence condition mod 1 is vacuous. -/
private lemma Gamma0_one_eq_top :
    (CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private lemma coe_Gamma0_one_eq_SL :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

/-- The image of `Γ(1)` in `GL(2, ℝ)` is the full special linear group. -/
private lemma coe_Gamma_one_eq_SL :
    ((CongruenceSubgroup.Gamma 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [CongruenceSubgroup.Gamma_one_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

/-- Transfer a vanishing statement for cusp forms along an equality of
subgroups. -/
private lemma cuspForm_eq_zero_of_subgroup_eq {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)}
    (h : Γ₂ = Γ₁) {k : ℤ} (H : ∀ g : CuspForm Γ₂ k, g = 0) (f : CuspForm Γ₁ k) :
    f = 0 := by
  subst h
  exact H f

/-- There is no nonzero weight-six cusp form on the full modular group:
the dimension formula gives rank zero below weight 12. -/
private theorem S6_levelOne_eq_zero (f : CuspForm Γ(1) 6) : f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma_one_eq_SL.symm
    (fun g : CuspForm 𝒮ℒ 6 => rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := 6) (by norm_num)) g) f

private theorem S6_levelOne_eq_zero' {k : ℤ} (hk : k = 6) (f : CuspForm Γ(1) k) :
    f = 0 := by
  subst hk
  exact S6_levelOne_eq_zero f

/-- The relative index of `Γ₀(2)` in `Γ₀(1)`, viewed as subgroups of
`GL(2, ℝ)`, is 3. This is the finite-index input the norm construction
needs to move a weight-two form on `Γ₀(2)` to weight six on `Γ₀(1)`. -/
private lemma card_quotient_eq_three :
    Nat.card ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
      (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
        (↑(CongruenceSubgroup.Gamma 1))) = 3 := by
  change Subgroup.relIndex (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ))
    (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) = 3
  change Subgroup.relIndex ((CongruenceSubgroup.Gamma0 2).map (mapGL ℝ))
    ((CongruenceSubgroup.Gamma 1).map (mapGL ℝ)) = 3
  rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
    CongruenceSubgroup.Gamma_one_top, Subgroup.relIndex_top_right,
    CongruenceSubgroup.Gamma0_two_index_eq_three]

/-- `Γ₀(2)` has finite relative index in `Γ₀(1)` as subgroups of `GL(2, ℝ)`. -/
instance : Subgroup.IsFiniteRelIndex
    (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ))
    (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨by change Nat.card _ ≠ 0; rw [card_quotient_eq_three]; decide⟩

/-- Every weight-two cusp form on `Γ₀(1)` is zero: `Γ₀(1)` is the full
modular group, and the dimension formula gives rank zero below weight 12. -/
theorem S2_Gamma0_one_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) :
    f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma0_one_eq_SL.symm
    (fun g : CuspForm 𝒮ℒ 2 => rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := 2) (by norm_num)) g) f

/-- Every weight-two cusp form on `Γ₀(2)` is zero. Take the norm of `f`
to `Γ₀(1)`: it has weight `2 * [Γ₀(1) : Γ₀(2)] = 6`, hence vanishes by the
level-one dimension formula, and the norm vanishes only when `f` does. -/
theorem S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) :
    f = 0 := by
  have hweight : (2 : ℤ) * Nat.card
      ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
        (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
          (↑(CongruenceSubgroup.Gamma 1))) = 6 := by
    rw [card_quotient_eq_three]
    norm_num
  have hf0 : (f : ℍ → ℂ) = 0 :=
    (CuspForm.norm_eq_zero_iff
      (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f).1
      (S6_levelOne_eq_zero' hweight
        (CuspForm.norm (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f))
  exact DFunLike.coe_injective (by simpa using hf0)

end ModularForm
