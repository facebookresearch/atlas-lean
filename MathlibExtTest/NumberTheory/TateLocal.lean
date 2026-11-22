/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TateLocal

@[expose] public section

open TateLocal IsDedekindDomain
open scoped NumberField

namespace TateLocalTest

/-- Consumer with the original binders: membership in the test space unfolds
to the two defining properties. -/
example {X : Type*} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  mem_testSpace_iff

/-- Nontrivial instance: the indicator of the whole space in a compact
discrete two-point space lies in the test space, and it is not zero. -/
example : ((Set.univ.indicator fun _ : Fin 2 => (1 : ℂ)) : Fin 2 → ℂ) ∈
      testSpace (Fin 2) ∧
    ((Set.univ.indicator fun _ : Fin 2 => (1 : ℂ)) : Fin 2 → ℂ) ≠ 0 := by
  constructor
  · exact indicator_mem_testSpace isClopen_univ isCompact_univ 1
  · intro h
    have h1 := congrFun h 0
    simp at h1

/-- The zero function is a test function on any locally compact field. -/
example {K : Type*} [Field K] [TopologicalSpace K] :
    (0 : K → ℂ) ∈ testSpace K := by
  rw [mem_testSpace_iff]
  exact ⟨by simpa using
    (IsLocallyConstant.const (0 : ℂ) :
      IsLocallyConstant (Function.const K (0 : ℂ))), HasCompactSupport.zero⟩

/-- Consumer for the conductor API at a finite place of a number field,
with the trivial character. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (s : ℂ) :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 ∧
      localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s =
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ :=
  ⟨conductorExponentAt_one K v, localLFactorAt_one K v s⟩

/-- The uniformizer unit really has valuation `exp (-1)`. -/
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (uniformizerUnit K v : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) :=
  valued_uniformizerUnit K v

/-- Modulus API on a concrete locally compact field. -/
example : modulus (2 : ℝ) ≠ 0 ∧ modulus (1 : ℝ) = 1 :=
  ⟨modulus_ne_zero (by norm_num), modulus_one⟩

end TateLocalTest
