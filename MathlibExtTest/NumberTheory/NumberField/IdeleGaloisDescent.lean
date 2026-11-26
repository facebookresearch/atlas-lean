/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.IdeleGaloisDescent

@[expose] public section

open NumberField

/-- The trivial descent datum over `ℚ`. -/
example : haveI : Subsingleton (ℚ ≃ₐ[ℚ] ℚ) :=
      ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩
    Nonempty (IdeleGaloisDescent (𝓞 ℚ) ℚ ℚ) :=
  ⟨IdeleGaloisDescent.identityDescent (𝓞 ℚ) ℚ ℚ⟩

/-- The inverse automorphisms of a descent datum are continuous. -/
example (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] (D : IdeleGaloisDescent R E F)
    (g : F ≃ₐ[E] F) : Continuous (D.act g).symm :=
  D.continuous_act_symm g
