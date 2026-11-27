/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.DecreasingFiltration
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Tests for decreasing filtrations and Hodge numbers

Concrete checks of `MathlibExt.LinearAlgebra.DecreasingFiltration` on `ℚ`, `Fin 2 → ℚ` and
`ℚ × ℚ`: single-jump filtrations, a two-step filtration with jumps at `0` and `3` together with
its induced and quotient filtrations, additivity of the Hodge number in short exact sequences,
monotonicity and rigidity, and functoriality of `comap` and `map`.
-/

open Module DecreasingFiltration

namespace MathlibExtTest.LinearAlgebra.DecreasingFiltration

/-! ### The single-jump filtration -/

/-- `single 5` on `Fin 2 → ℚ` has Hodge number `5 · 2 = 10`. -/
example : (single 5 : DecreasingFiltration ℚ (Fin 2 → ℚ)).hodgeNumber = 10 := by
  rw [hodgeNumber_single, Module.finrank_fin_fun]
  norm_num

/-- On the line `ℚ`, the Hodge number of `single 7` is its jump `7`. -/
example : (single 7 : DecreasingFiltration ℚ ℚ).hodgeNumber = 7 :=
  hodgeNumber_of_finrank_eq_one _ (Module.finrank_self ℚ) (by simp) (by simp)

/-- A filtration of a finite-dimensional space reaches `0` and the whole space. -/
example (F : DecreasingFiltration ℚ (Fin 2 → ℚ)) :
    (∃ i, F.Fil i = ⊥) ∧ ∃ i, F.Fil i = ⊤ :=
  ⟨F.exists_fil_eq_bot, F.exists_fil_eq_top⟩

/-! ### A two-step filtration of `Fin 2 → ℚ` with jumps at `0` and `3` -/

/-- The line in `Fin 2 → ℚ` spanned by the first standard basis vector. -/
def line : Submodule ℚ (Fin 2 → ℚ) := ℚ ∙ Pi.single 0 1

/-- The line `line` has dimension `1`. -/
theorem finrank_line : finrank ℚ line = 1 :=
  finrank_span_singleton (by simp)

/-- The filtration of `Fin 2 → ℚ` with `Fil^i = ⊤` for `i ≤ 0`, `Fil^i = line` for
`1 ≤ i ≤ 3` and `Fil^i = ⊥` for `4 ≤ i`; its jumps are at `0` and `3`. -/
def twoStep : DecreasingFiltration ℚ (Fin 2 → ℚ) where
  Fil i := if i ≤ 0 then ⊤ else if i ≤ 3 then line else ⊥
  antitone i j hij := by
    dsimp only
    split_ifs <;> first | exact le_rfl | exact le_top | exact bot_le | omega
  iInf_eq_bot := eq_bot_iff.2 (iInf_le_of_le 4 (by simp))
  iSup_eq_top := eq_top_iff.2 (le_iSup_of_le 0 (by simp))

/-- The steps of `twoStep`, by definition. -/
theorem twoStep_fil (i : ℤ) :
    twoStep.Fil i = if i ≤ 0 then ⊤ else if i ≤ 3 then line else ⊥ :=
  rfl

/-- The two-step filtration has Hodge number `0 · 1 + 3 · 1 = 3`. -/
theorem hodgeNumber_twoStep : twoStep.hodgeNumber = 3 := by
  rw [twoStep.hodgeNumber_eq_sum (show (0 : ℤ) ≤ 4 by norm_num) (by simp [twoStep_fil])
    (by simp [twoStep_fil])]
  have h : ∀ i ∈ Finset.Ioo (0 : ℤ) 4, (finrank ℚ (twoStep.Fil i) : ℤ) = 1 := by
    intro i hi
    rw [Finset.mem_Ioo] at hi
    rw [twoStep_fil, ite_eq_right (by omega), ite_eq_left (by omega), finrank_line,
      Nat.cast_one]
  rw [Finset.sum_congr rfl h]
  simp

/-- The graded piece `gr^3` of `twoStep` is `line / 0`, of dimension `1`. -/
example : finrank ℚ (twoStep.gr 3) = 1 := by
  have h := twoStep.finrank_gr 3
  have h₃ : finrank ℚ (twoStep.Fil 3) = 1 := by
    rw [show twoStep.Fil 3 = line by simp [twoStep_fil], finrank_line]
  have h₄ : finrank ℚ (twoStep.Fil (3 + 1)) = 0 := by
    rw [show twoStep.Fil (3 + 1) = ⊥ by simp [twoStep_fil], finrank_bot]
  omega

/-- Steps of `twoStep` below the step `Fil^0 = ⊤` are `⊤`, and steps above `Fil^4 = ⊥` are `⊥`. -/
example : twoStep.Fil (-5) = ⊤ ∧ twoStep.Fil 9 = ⊥ :=
  ⟨twoStep.fil_eq_top_of_le (j := 0) (by simp [twoStep_fil]) (by norm_num),
    twoStep.fil_eq_bot_of_le (i := 4) (by simp [twoStep_fil]) (by norm_num)⟩

/-- The filtration induced by `twoStep` on `line` is `single 3`. -/
theorem comap_twoStep : twoStep.comap line.subtype line.injective_subtype = single 3 := by
  ext i
  rw [comap_fil, single_fil, twoStep_fil]
  split_ifs <;> first | omega | simp

/-- The quotient filtration of `twoStep` on `(Fin 2 → ℚ) ⧸ line` is `single 0`. -/
theorem map_twoStep : twoStep.map line.mkQ line.mkQ_surjective = single 0 := by
  ext i
  rw [map_fil, single_fil, twoStep_fil]
  split_ifs <;> first | omega | simp

/-- The filtration induced on `line` has Hodge number `3 · 1 = 3`. -/
example : (twoStep.comap line.subtype line.injective_subtype).hodgeNumber = 3 := by
  rw [comap_twoStep, hodgeNumber_single, finrank_line]
  norm_num

/-- The quotient filtration on `(Fin 2 → ℚ) ⧸ line` has Hodge number `0 · 1 = 0`. -/
example : (twoStep.map line.mkQ line.mkQ_surjective).hodgeNumber = 0 := by
  rw [map_twoStep, hodgeNumber_single, zero_mul]

/-- Additivity along `0 → line → Fin 2 → ℚ → (Fin 2 → ℚ) ⧸ line → 0`: `3 = 3 + 0`. -/
example : twoStep.hodgeNumber =
    (twoStep.comap line.subtype line.injective_subtype).hodgeNumber +
      (twoStep.map line.mkQ line.mkQ_surjective).hodgeNumber :=
  twoStep.hodgeNumber_eq_add_of_exact _ _ (LinearMap.exact_subtype_mkQ line)

/-- `twoStep` lies below `single 3`. -/
theorem twoStep_fil_le (i : ℤ) :
    twoStep.Fil i ≤ (single 3 : DecreasingFiltration ℚ (Fin 2 → ℚ)).Fil i := by
  rw [twoStep_fil, single_fil]
  split_ifs <;> first | omega | simp

/-- Monotonicity of the Hodge number: `3 ≤ 3 · 2`. -/
example : twoStep.hodgeNumber ≤ (single 3 : DecreasingFiltration ℚ (Fin 2 → ℚ)).hodgeNumber :=
  hodgeNumber_le_of_le twoStep_fil_le

/-- `twoStep` lies below `single 3` but has a smaller Hodge number, so the two differ. -/
example : twoStep ≠ single 3 := by
  intro h
  have := congrArg hodgeNumber h
  rw [hodgeNumber_twoStep, hodgeNumber_single, Module.finrank_fin_fun] at this
  norm_num at this

/-! ### Short exact sequences, rigidity and functoriality -/

/-- For `0 → ℚ → ℚ × ℚ → ℚ → 0` (`LinearMap.inl` and `LinearMap.snd`), the Hodge numbers of the
induced and quotient filtrations of `single n` add up to `2 n`. -/
example (n : ℤ) :
    ((single n : DecreasingFiltration ℚ (ℚ × ℚ)).comap (LinearMap.inl ℚ ℚ ℚ)
        LinearMap.inl_injective).hodgeNumber +
      ((single n : DecreasingFiltration ℚ (ℚ × ℚ)).map (LinearMap.snd ℚ ℚ ℚ)
        LinearMap.snd_surjective).hodgeNumber = 2 * n := by
  rw [← hodgeNumber_eq_add_of_exact _ _ _ Function.Exact.inl_snd, hodgeNumber_single,
    Module.finrank_prod, Module.finrank_self]
  push_cast
  ring

/-- A filtration of `Fin 2 → ℚ` below `single 0` with nonnegative Hodge number is `single 0`. -/
example (F : DecreasingFiltration ℚ (Fin 2 → ℚ)) (h : ∀ i, F.Fil i ≤ (single 0).Fil i)
    (h' : 0 ≤ F.hodgeNumber) : F = single 0 :=
  eq_of_le_of_hodgeNumber_le h (by rwa [hodgeNumber_single, zero_mul])

/-- Inducing along a linear equivalence keeps the Hodge number. -/
example (e : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ)) :
    (twoStep.comap (e : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) e.injective).hodgeNumber = 3 := by
  rw [hodgeNumber_comap_linearEquiv, hodgeNumber_twoStep]

/-- Inducing in two steps along `LinearMap.id` and `line.subtype`. -/
example : (twoStep.comap line.subtype line.injective_subtype).comap LinearMap.id
      Function.injective_id =
    twoStep.comap (line.subtype ∘ₗ LinearMap.id)
      (line.injective_subtype.comp Function.injective_id) :=
  comap_comap _ _ _

/-- Taking quotients in two steps along `line.mkQ` and `LinearMap.id`. -/
example : (twoStep.map line.mkQ line.mkQ_surjective).map LinearMap.id Function.surjective_id =
    twoStep.map (LinearMap.id ∘ₗ line.mkQ) (Function.surjective_id.comp line.mkQ_surjective) :=
  map_map _ _ _

/-- The commutative square with identity maps on the sides `j` and `j'`. -/
example (F : DecreasingFiltration ℚ (ℚ × ℚ)) :
    (F.map (LinearMap.snd ℚ ℚ ℚ) LinearMap.snd_surjective).comap LinearMap.id
        Function.injective_id =
      (F.comap LinearMap.id Function.injective_id).map (LinearMap.snd ℚ ℚ ℚ)
        LinearMap.snd_surjective :=
  F.comap_map_eq_map_comap _ _ _ _ (by rw [LinearMap.comp_id, LinearMap.id_comp])
    (by rw [LinearMap.range_id]; exact le_top)

/-- On the zero space, every filtration has Hodge number `0`. -/
example (F : DecreasingFiltration ℚ (Fin 0 → ℚ)) : F.hodgeNumber = 0 :=
  F.hodgeNumber_eq_zero_of_finrank_eq_zero (Module.finrank_fin_fun ℚ)

end MathlibExtTest.LinearAlgebra.DecreasingFiltration
