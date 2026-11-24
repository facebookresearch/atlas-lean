/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.HeckeCharacter

@[expose] public section

open NumberField IsDedekindDomain

/-- Exact-source consumer: the original binders and conclusion. -/
private theorem exactSource
    (K : Type*) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ₁ : NumberField.IsIdeleClassChar (𝓞 K) K χ₁)
    (hχ₂ : NumberField.IsIdeleClassChar (𝓞 K) K χ₂)
    (hc₁ : Continuous χ₁)
    (hc₂ : Continuous χ₂)
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      χ₁ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v
            (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v)))
        = χ₂ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v
            (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v)))) :
    χ₁ = χ₂ :=
  HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq_of_continuous
    K χ₁ χ₂ hχ₁ hχ₂ hc₁ hc₂ 𝔣₁ 𝔣₂ hmod₁ hmod₂ S hS

/-- The local test element is a genuine uniformizer: its valuation is
`exp (-1)`, not `1`, so agreement on it is a nontrivial local condition. -/
example (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (NumberField.AdelicLevel.uniformizerUnit (𝓞 ℚ) ℚ v :
      v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
  NumberField.AdelicLevel.valued_uniformizerUnit (𝓞 ℚ) ℚ v

/-- Consumer in the standard restricted-product idele topology: characters
on `TopologicalIdeleGroup`, continuous for that topology, are determined by
their values on the local uniformizer ideles outside a finite set. -/
theorem exactSourceTopological
    (K : Type*) [Field K] [NumberField K]
    (ψ₁ ψ₂ : NumberField.TopologicalIdeleGroup (𝓞 K) K →* ℂˣ)
    (hψ₁ : Continuous ψ₁)
    (hψ₂ : Continuous ψ₂)
    (hχ₁ : NumberField.IsIdeleClassChar (𝓞 K) K
      (ψ₁.comp (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom))
    (hχ₂ : NumberField.IsIdeleClassChar (𝓞 K) K
      (ψ₂.comp (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom))
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K
      (ψ₁.comp (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom) 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K
      (ψ₂.comp (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom) 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      ψ₁ (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K
          (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
            (NumberField.AdelicLevel.localUnit (𝓞 K) K v
              (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v))))
        = ψ₂ (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K
          (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
            (NumberField.AdelicLevel.localUnit (𝓞 K) K v
              (NumberField.AdelicLevel.uniformizerUnit (𝓞 K) K v))))) :
    ψ₁ = ψ₂ := by
  have key := HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq K
    (ψ₁.comp (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom)
    (ψ₂.comp (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom)
    hχ₁ hχ₂ (by
      have hcomp : (ψ₁.comp
            (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom).comp
          (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).symm.toMonoidHom = ψ₁ := by
        ext b
        simp
      rw [hcomp]
      exact hψ₁) (by
      have hcomp : (ψ₂.comp
            (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).toMonoidHom).comp
          (NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).symm.toMonoidHom = ψ₂ := by
        ext b
        simp
      rw [hcomp]
      exact hψ₂) 𝔣₁ 𝔣₂ hmod₁ hmod₂ S hS
  ext b
  exact congrArg (fun u : ℂˣ => (u : ℂ)) (DFunLike.congr_fun key
    ((NumberField.TopologicalIdeleGroup.unitsEquiv (𝓞 K) K).symm b))
