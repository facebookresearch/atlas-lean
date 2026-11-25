/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.JacquetIntegral2

@[expose] public section

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction AutomorphicForm
open scoped NNReal ENNReal

/-- `exactSource` consumer with the original binders, including the Borel σ-algebra fixed
inside the conclusion. -/
example
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := borel _
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν < ∞) ∧
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ∫⁻ y, ‖f (w₀ * unipotentGL2 y * (unipotentGL2 x * g))‖ₑ ∂ν =
          ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν) ∧
      (∀ (t₁ t₂ : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ∫⁻ y, ‖f (w₀ * unipotentGL2 y * (diagonal2 p ![t₁, t₂] * g))‖ₑ ∂ν =
          ENNReal.ofReal (‖((χ 0 t₂ : ℂˣ) : ℂ)‖ * ‖((χ 1 t₁ : ℂˣ) : ℂ)‖ *
              Real.sqrt (‖(t₁ : p.adicCompletion ℚ)‖ / ‖(t₂ : p.adicCompletion ℚ)‖)) *
            ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν) ∧
      (∃ C : ℝ≥0, ∀ k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ∫⁻ y, ‖f (w₀ * unipotentGL2 y * k)‖ₑ ∂ν ≤ C) :=
  letI : MeasurableSpace (p.adicCompletion ℚ) := borel _
  haveI : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩
  absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
    p χ cχ hcχ ϖ hϖ hdom f hf hfsm w₀ hw₀

/-- The higher unit groups at level `0` are the units of valuation `1`. -/
example (p : HeightOneSpectrum (𝓞 ℚ)) (u : (p.adicCompletion ℚ)ˣ) :
    u ∈ higherUnitsAt ℚ p 0 ↔ Valued.v (u : p.adicCompletion ℚ) = 1 := by
  simp [mem_higherUnitsAt_iff]

/-- Boundary check: the identity lies in the local level-one subgroup, so the bound in the last
conjunct is a genuine constraint on a nonempty set. -/
example (p : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
  Subgroup.one_mem _

/-- The level-one characterization: membership forces integral entries of `k` and `k⁻¹`. -/
example (p : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ))
    (hk : k ∈ AdelicLevel.localLevelOne (𝓞 ℚ) ℚ p ⊤) (i j : Fin 2) :
    (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ :=
  (AdelicLevel.mem_localLevelOne_iff.mp hk).1.integral i j
