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
`Theorems/Thm_CuspForm_levelTwo_weight_four_eq_zero.lean`,
`P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean`,
`P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean` and
`P2M/Sol/S_CuspForm_levelTwo_weight_four_eq_zero.lean`
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

import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Vanishing of cusp forms of weights two and four on `Γ₀(1)` and `Γ₀(2)`

The spaces of cusp forms of weights two and four on `Γ₀(2)` are zero.
The weight-two case is the final step of the classical proof of Fermat's
Last Theorem via the Frey curve: a Frey curve is modular, Ribet's level
lowering puts its mod-`p` representation in `S₂(Γ₀(2))`, and that space
being zero gives the contradiction. Along the way we record the two
reusable ingredients, the product norm of a cusp form over a finite-index
subgroup and the index `[SL(2, ℤ) : Γ₀(2)] = 3`, which let the weight-two
case be reduced to the weight-six level-one dimension formula. For weight
four, the product of a form with its `S`- and `ST`-translates is a
weight-twelve level-one cusp form whose first `q`-expansion coefficient
vanishes, so the product, and hence the form itself, is zero.

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
  cuspForm_eq_zero_of_subgroup_eq CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
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

noncomputable section WeightFour

open ModularGroup
open scoped Topology Manifold ModularForm

namespace CuspForm.LevelTwoWeightFour

local notation "Γ₀(" N ")" => (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

private def γ₁ : SL(2, ℤ) := ⟨!![1, 0; -2, 1], by norm_num [Matrix.det_fin_two_of]⟩

private def γ₂ : SL(2, ℤ) := ⟨!![-1, -1; 2, 1], by norm_num [Matrix.det_fin_two_of]⟩

private theorem S_mul_T_mul_T : S * T * T = γ₁ * S := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem S_mul_T_mul_S : S * T * S = γ₂ * (S * T) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem S_mul_S : S * S = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem T_mem : T ∈ CongruenceSubgroup.Gamma0 2 := by
  simp [CongruenceSubgroup.Gamma0_mem, coe_T]

private theorem neg_one_mem : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 2 := by
  simp [CongruenceSubgroup.Gamma0_mem]

private theorem γ₁_mem : γ₁ ∈ CongruenceSubgroup.Gamma0 2 := by
  show ((γ₁ 1 0 : ZMod 2) = 0)
  decide

private theorem γ₂_mem : γ₂ ∈ CongruenceSubgroup.Gamma0 2 := by
  show ((γ₂ 1 0 : ZMod 2) = 0)
  decide

variable (f : CuspForm Γ₀(2) 4)

private theorem slash_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 2) :
    (⇑f) ∣[(4 : ℤ)] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

private def f₁ : ℍ → ℂ := (⇑f) ∣[(4 : ℤ)] S

private def f₂ : ℍ → ℂ := (⇑f) ∣[(4 : ℤ)] (S * T)

private theorem f_slash_T : (⇑f) ∣[(4 : ℤ)] T = ⇑f := slash_mem f T_mem

private theorem f₁_slash_T : (f₁ f) ∣[(4 : ℤ)] T = f₂ f := by
  rw [f₁, f₂, ← SlashAction.slash_mul]

private theorem f₂_slash_T : (f₂ f) ∣[(4 : ℤ)] T = f₁ f := by
  rw [f₂, f₁, ← SlashAction.slash_mul, S_mul_T_mul_T, SlashAction.slash_mul,
    slash_mem f γ₁_mem]

private theorem f_slash_S : (⇑f) ∣[(4 : ℤ)] S = f₁ f := rfl

private theorem f₁_slash_S : (f₁ f) ∣[(4 : ℤ)] S = ⇑f := by
  rw [f₁, ← SlashAction.slash_mul, S_mul_S, slash_mem f neg_one_mem]

private theorem f₂_slash_S : (f₂ f) ∣[(4 : ℤ)] S = f₂ f := by
  rw [f₂, ← SlashAction.slash_mul, S_mul_T_mul_S, SlashAction.slash_mul,
    slash_mem f γ₂_mem]

private def g : ℍ → ℂ := f₁ f * f₂ f

private def F : ℍ → ℂ := ⇑f * g f

private theorem g_slash_T : (g f) ∣[(8 : ℤ)] T = g f := by
  rw [g, show (8 : ℤ) = 4 + 4 by norm_num, ModularForm.mul_slash_SL2, f₁_slash_T,
    f₂_slash_T, mul_comm]

private theorem g_slash_S : (g f) ∣[(8 : ℤ)] S = ⇑f * f₂ f := by
  rw [g, show (8 : ℤ) = 4 + 4 by norm_num, ModularForm.mul_slash_SL2, f₁_slash_S,
    f₂_slash_S]

private theorem F_slash_T : (F f) ∣[(12 : ℤ)] T = F f := by
  rw [F, show (12 : ℤ) = 4 + 8 by norm_num, ModularForm.mul_slash_SL2, f_slash_T,
    g_slash_T]

private theorem F_slash_S : (F f) ∣[(12 : ℤ)] S = F f := by
  rw [F, show (12 : ℤ) = 4 + 8 by norm_num, ModularForm.mul_slash_SL2, f_slash_S,
    g_slash_S, g, f₁]
  ring

private theorem F_slash (γ : SL(2, ℤ)) : (F f) ∣[(12 : ℤ)] γ = F f :=
  SlashInvariantForm.slash_action_generators_SL2Z (F_slash_S f) (F_slash_T f) γ

private theorem mdifferentiable_f₁ : MDiff (f₁ f) := (CuspFormClass.holo f).slash _ _
private theorem mdifferentiable_f₂ : MDiff (f₂ f) := (CuspFormClass.holo f).slash _ _
private theorem mdifferentiable_g : MDiff (g f) :=
  (mdifferentiable_f₁ f).mul (mdifferentiable_f₂ f)
private theorem mdifferentiable_F : MDiff (F f) :=
  (CuspFormClass.holo f).mul (mdifferentiable_g f)

private theorem isZeroAtImInfty_f : IsZeroAtImInfty (⇑f) :=
  CuspFormClass.zero_at_infty f
private theorem isZeroAtImInfty_f₁ : IsZeroAtImInfty (f₁ f) :=
  CuspFormClass.zero_at_infty_slash f S
private theorem isZeroAtImInfty_f₂ : IsZeroAtImInfty (f₂ f) :=
  CuspFormClass.zero_at_infty_slash f (S * T)

private theorem isZeroAtImInfty_mul {u v : ℍ → ℂ} (hu : IsZeroAtImInfty u)
    (hv : IsZeroAtImInfty v) : IsZeroAtImInfty (u * v) := by
  have h := hu.mul hv
  simp at h
  exact h

private theorem isZeroAtImInfty_g : IsZeroAtImInfty (g f) :=
  isZeroAtImInfty_mul (isZeroAtImInfty_f₁ f) (isZeroAtImInfty_f₂ f)

private theorem isZeroAtImInfty_F : IsZeroAtImInfty (F f) :=
  isZeroAtImInfty_mul (isZeroAtImInfty_f f) (isZeroAtImInfty_g f)

private def Fc : CuspForm 𝒮ℒ 12 where
  toFun := F f
  slash_action_eq' γ hγ := by
    obtain ⟨γ, rfl⟩ := hγ
    exact F_slash f γ
  holo' := mdifferentiable_F f
  zero_at_cusps' {c} hc := by
    obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    rw [OnePoint.isZeroAt_iff rfl]
    change IsZeroAtImInfty ((F f) ∣[(12 : ℤ)] γ)
    rw [F_slash]
    exact isZeroAtImInfty_F f

@[simp]
private theorem coe_Fc : ⇑(Fc f) = F f := rfl

private theorem vAdd_apply_of_slash_T {u : ℍ → ℂ} {k : ℤ}
    (hT : u ∣[k] T = u) (τ : ℍ) : u ((1 : ℝ) +ᵥ τ) = u τ := by
  have h := congrFun hT τ
  rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul] at h
  have hd : denom (T : GL (Fin 2) ℝ) τ = 1 := by
    simp [ModularGroup.denom_apply, coe_T]
  simpa [hd] using h

private theorem periodic_comp_ofComplex_of_slash_T {u : ℍ → ℂ} {k : ℤ}
    (hT : u ∣[k] T = u) : Function.Periodic (u ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < Complex.im w
  · have hw' : 0 < Complex.im (w + 1) := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw',
      ofComplex_apply_of_im_pos hw]
    convert vAdd_apply_of_slash_T hT ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have hw0 : Complex.im w ≤ 0 := not_lt.mp hw
    have hw1 : Complex.im (w + (1 : ℝ)) ≤ 0 := by simpa using hw0
    simp only [Function.comp_apply]
    rw [show w + 1 = w + (1 : ℝ) by simp, ofComplex_apply_of_im_nonpos hw1,
      ofComplex_apply_of_im_nonpos hw0]

private theorem periodic_g : Function.Periodic (g f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_slash_T (g_slash_T f)

private theorem analyticAt_cuspFunction_g : AnalyticAt ℂ (cuspFunction 1 (g f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic_g f) (mdifferentiable_g f)
    (isZeroAtImInfty_g f).isBoundedAtImInfty

private theorem qExpansion_g_coeff_zero : (qExpansion 1 (g f)).coeff 0 = 0 := by
  rw [qExpansion_coeff_zero one_pos (analyticAt_cuspFunction_g f) (periodic_g f)]
  exact (isZeroAtImInfty_g f).valueAtInfty_eq_zero

private theorem qExpansion_f_coeff_zero : (qExpansion 1 (⇑f)).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (by simp)

private theorem qExpansion_F :
    qExpansion 1 (F f) = qExpansion 1 (⇑f) * qExpansion 1 (g f) :=
  qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (by simp))
    (analyticAt_cuspFunction_g f)

private theorem qExpansion_F_coeff_one : (qExpansion 1 (F f)).coeff 1 = 0 := by
  rw [qExpansion_F, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    Finset.sum_cons, Finset.Nat.antidiagonal_zero, Finset.map_singleton,
    Finset.sum_singleton]
  simp [qExpansion_g_coeff_zero, qExpansion_f_coeff_zero]

private theorem Fc_eq_zero : Fc f = 0 := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve (Fc f)
  have h1 : (qExpansion 1 (⇑(Fc f))).coeff 1 = c := by
    rw [← hc, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_smul,
      CuspForm.coe_discriminant, ModularForm.discriminant_qExpansion_coeff_one,
      smul_eq_mul, mul_one]
  rw [coe_Fc, qExpansion_F_coeff_one] at h1
  rw [← hc, ← h1, zero_smul]

private theorem F_eq_zero : F f = 0 := by
  have := congrArg (fun h : CuspForm 𝒮ℒ 12 => ⇑h) (Fc_eq_zero f)
  simpa using this

private theorem eq_zero_or_eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDiff u)
    (hv : MDiff v) (huv : u * v = 0) : u = 0 ∨ v = 0 := by
  classical
  by_contra h
  rw [not_or] at h
  obtain ⟨hu0, hv0⟩ := h
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, u τ₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hu0 (funext h')
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hUdef
  have hUopen : IsOpen U := isOpen_upperHalfPlaneSet
  have hUconn : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hu' : DifferentiableOn ℂ (u ∘ ofComplex) U :=
    UpperHalfPlane.mdifferentiable_iff.mp hu
  have hv' : DifferentiableOn ℂ (v ∘ ofComplex) U :=
    UpperHalfPlane.mdifferentiable_iff.mp hv
  have hva : AnalyticOnNhd ℂ (v ∘ ofComplex) U := hv'.analyticOnNhd hUopen
  have hz₀ : ((τ₀ : ℂ)) ∈ U := τ₀.im_pos
  have hcont : ContinuousAt (u ∘ ofComplex) (τ₀ : ℂ) :=
    (hu'.continuousOn.continuousAt (hUopen.mem_nhds hz₀))
  have hne : ∀ᶠ z in nhds (τ₀ : ℂ), (u ∘ ofComplex) z ≠ 0 :=
    hcont.eventually_ne (by simpa using hτ₀)
  have hev : (v ∘ ofComplex) =ᶠ[nhds (τ₀ : ℂ)] 0 := by
    filter_upwards [hne, hUopen.mem_nhds hz₀] with z hz hzU
    have := congrFun huv (ofComplex z)
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hz
  have hvU : Set.EqOn (v ∘ ofComplex) 0 U :=
    hva.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hz₀ hev
  apply hv0
  funext τ
  have := hvU τ.im_pos
  simpa using this

private theorem f_eq_zero_of_slash_eq_zero {γ : SL(2, ℤ)}
    (h : (⇑f) ∣[(4 : ℤ)] γ = 0) : f = 0 := by
  have h' : (⇑f) = 0 := by
    have := congrArg (fun u : ℍ → ℂ => u ∣[(4 : ℤ)] γ⁻¹) h
    simpa [← SlashAction.slash_mul] using this
  exact DFunLike.coe_injective (h'.trans FunLike.coe_zero.symm)

private theorem eq_zero : f = 0 := by
  have hF := F_eq_zero f
  rw [F] at hF
  rcases eq_zero_or_eq_zero_of_mul_eq_zero (CuspFormClass.holo f)
      (mdifferentiable_g f) hF with h0 | hg
  · exact DFunLike.coe_injective (h0.trans FunLike.coe_zero.symm)
  · rw [g] at hg
    rcases eq_zero_or_eq_zero_of_mul_eq_zero (mdifferentiable_f₁ f)
        (mdifferentiable_f₂ f) hg with h1 | h2
    · exact f_eq_zero_of_slash_eq_zero f (γ := S) h1
    · exact f_eq_zero_of_slash_eq_zero f (γ := S * T) h2

end CuspForm.LevelTwoWeightFour

end WeightFour

namespace ModularForm

/-- Every weight-four cusp form on `Γ₀(2)` is zero. Multiply `f` by its
`S`- and `ST`-translates to get a weight-twelve level-one cusp form; its
first `q`-expansion coefficient vanishes, so it is zero, and a product of
holomorphic functions on the upper half plane vanishes only if a factor
does. -/
theorem S4_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 4) :
    f = 0 :=
  CuspForm.LevelTwoWeightFour.eq_zero f

end ModularForm
