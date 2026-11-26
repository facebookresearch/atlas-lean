/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.SigmaAdelicAction

@[expose] public section

open NumberField NumberField.AdelicHeight

universe u v

/-- Consumer with the original binders: both fields in `Type`, as in the source statement. -/
private theorem exactSource (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.sigmaAdelicAct K L D σ g) =
      NumberField.AdelicHeight.adelicHeight L g :=
  AutomorphicForm.adelicHeight_sigmaAdelicAct K L D σ g

/-- The same statement with the two fields in different, higher universes. -/
private theorem exactSource_universe (K : Type u) (L : Type (v + 1)) [Field K] [Field L]
    [NumberField L] [Algebra K L] (D : IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (AutomorphicForm.sigmaAdelicAct K L D σ g) = adelicHeight L g :=
  AutomorphicForm.adelicHeight_sigmaAdelicAct K L D σ g

/-- The identity automorphism acts trivially, for any descent datum. -/
example (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : IdeleGaloisDescent (𝓞 L) K L) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.sigmaAdelicAct K L D 1 g = g := by
  rw [AutomorphicForm.sigmaAdelicAct_one]
  rfl

/-- Over `ℚ` the hypothesis is inhabited by the trivial descent datum, and the theorem
specializes to the height of the identity, which is `1`. -/
example :
    haveI : Subsingleton (ℚ ≃ₐ[ℚ] ℚ) :=
      ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩
    adelicHeight ℚ (AutomorphicForm.sigmaAdelicAct ℚ ℚ
      (IdeleGaloisDescent.identityDescent (𝓞 ℚ) ℚ ℚ) 1 1) = 1 := by
  rw [map_one, adelicHeight_one]
