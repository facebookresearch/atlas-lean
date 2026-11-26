/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.LocalLevelOne

@[expose] public section

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LocalLevelOneTest

variable (p : HeightOneSpectrum (𝓞 ℚ))

/-- `localEmbed` puts `g` at `p` and the identity matrix at every other place. -/
example (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ p) (g : GL (Fin 2) (p.adicCompletion ℚ))
    (i j : Fin 2) :
    (localEmbed (𝓞 ℚ) ℚ p g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j p =
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∧
      (localEmbed (𝓞 ℚ) ℚ p g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j w =
        (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j := by
  rw [coe_localEmbed]
  exact ⟨localMat_apply_self _ _ _ _ _ _, localMat_apply_of_ne _ _ _ _ _ _ hw⟩

/-- Membership in the local level-one subgroup forces integral entries of `k` and of `k⁻¹`. -/
example (k : GL (Fin 2) (p.adicCompletion ℚ)) (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (i j : Fin 2) :
    (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ ∧
      ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈
        p.adicCompletionIntegers ℚ :=
  ⟨(mem_localLevelOne_iff.mp hk).1.integral i j, (mem_localLevelOne_iff.mp hk).2.integral i j⟩

private theorem idealBound_top : idealBound (𝓞 ℚ) ⊤ p = 1 := by
  rw [idealBound, ite_eq_right_iff.mpr fun h => absurd h top_ne_bot, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero p.associates_irreducible]
  rfl

private theorem idealBound_bot : idealBound (𝓞 ℚ) ⊥ p = 0 := by
  simp [idealBound]

private theorem valued_unif :
    Valued.v (uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
  valued_uniformizerUnit (𝓞 ℚ) ℚ p

private theorem unif_mem :
    (uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_unif]
  exact (WithZero.exp_lt_one_iff.mpr (by norm_num)).le

/-- The lower unipotent matrix `!![1, 0; y, 1]`. -/
private noncomputable def lowerUnip (y : p.adicCompletion ℚ) : GL (Fin 2) (p.adicCompletion ℚ) where
  val := !![1, 0; y, 1]
  inv := !![1, 0; -y, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The diagonal matrix `diag(a, b)` for units `a` and `b`. -/
private noncomputable def diagUnit (a b : (p.adicCompletion ℚ)ˣ) : GL (Fin 2) (p.adicCompletion ℚ) where
  val := !![(a : p.adicCompletion ℚ), 0; 0, (b : p.adicCompletion ℚ)]
  inv := !![((a⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ), 0;
    0, ((b⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `!![1, 0; ϖ, 1]` lies in the local level-one subgroup at the full ideal. -/
example : lowerUnip p (uniformizerUnit (𝓞 ℚ) ℚ p) ∈ localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have h := unif_mem p
  refine mem_localLevelOne_iff.mpr ⟨⟨fun i j => ?_, ?_, ?_⟩, ⟨fun i j => ?_, ?_, ?_⟩⟩ <;>
    simp only [lowerUnip, Units.inv_mk, idealBound_top]
  · fin_cases i <;> fin_cases j <;> simp [h, one_mem, zero_mem]
  · simpa using (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h
  · simp
  · fin_cases i <;> fin_cases j <;> simp [h, one_mem, zero_mem]
  · simpa using (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h
  · simp

/-- At the zero ideal the lower-left entry must vanish, so `!![1, 0; ϖ, 1]` is not of level one
there: the subgroup depends on the ideal through its lower-left condition. -/
example : lowerUnip p (uniformizerUnit (𝓞 ℚ) ℚ p) ∉ localLevelOne (𝓞 ℚ) ℚ p ⊥ := fun h => by
  have hll := (mem_localLevelOne_iff.mp h).1.lowerLeft
  simp only [lowerUnip, idealBound_bot] at hll
  simp at hll

/-- The unit `1 + ϖ`. -/
private noncomputable def onePlusUnif : (p.adicCompletion ℚ)ˣ :=
  Units.mk0 (1 + (uniformizerUnit (𝓞 ℚ) ℚ p : p.adicCompletion ℚ)) fun h => by
    have := Valuation.map_one_add_of_lt Valued.v
      ((valued_unif p).trans_lt (WithZero.exp_lt_one_iff.mpr (by norm_num)))
    rw [h, map_zero] at this
    exact zero_ne_one this

/-- At the zero ideal the lower-right entry must equal `1`, so `diag(1, 1 + ϖ)` is not of level
one there. -/
example : diagUnit p 1 (onePlusUnif p) ∉ localLevelOne (𝓞 ℚ) ℚ p ⊥ := fun h => by
  have hlr := (mem_localLevelOne_iff.mp h).1.lowerRight
  simp only [diagUnit, onePlusUnif, idealBound_bot, Units.val_mk0] at hlr
  simp at hlr

/-- `diag(ϖ, 1)` has integral entries, but its inverse does not, so it is not of level one. -/
example : diagUnit p (uniformizerUnit (𝓞 ℚ) ℚ p) 1 ∉ localLevelOne (𝓞 ℚ) ℚ p ⊤ := fun h => by
  have hint := (mem_localLevelOne_iff.mp h).2.integral 0 0
  simp only [diagUnit, Units.inv_mk, HeightOneSpectrum.mem_adicCompletionIntegers] at hint
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Units.val_inv_eq_inv_val, map_inv₀, valued_unif] at hint
  rw [← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hint
  norm_num at hint

end LocalLevelOneTest
