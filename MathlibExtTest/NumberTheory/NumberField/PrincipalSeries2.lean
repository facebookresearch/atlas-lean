/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.PrincipalSeries2

@[expose] public section

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

/-- `exactSource` consumer with the original binders: membership unfolds to
local constancy, unipotent invariance, and the diagonal transformation law. -/
example (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :
    f ∈ principalSeries2 p χ ↔
      IsLocallyConstant f ∧
        (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          f (upperUnipotent2 p x * g) = f g) ∧
        ∀ (a : Fin 2 → (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          f (diagonal2 p a * g) = torusChar2 p χ a * halfModulus2 p a * f g :=
  mem_principalSeries2_iff

example (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) :
    (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) ∈ principalSeries2 p χ :=
  Submodule.zero_mem _

example (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    rightTranslate2 p g f ∈ principalSeries2 p χ :=
  rightTranslate2_mem_principalSeries2 hf g

/-- Boundary check: the torus factor is `1` for the trivial character,
so the diagonal law for a constant function reduces to the modulus factor. -/
example (p : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 2 → (p.adicCompletion ℚ)ˣ) :
    torusChar2 p (fun _ => 1) a = 1 := by
  simp [torusChar2]
