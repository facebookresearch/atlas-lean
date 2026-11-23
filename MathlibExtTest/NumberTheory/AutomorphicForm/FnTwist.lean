/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.FnTwist

@[expose] public section

open NumberField

namespace AutomorphicFormFnTwistTest

/-- `exactSource` consumer with the original binders. -/
public theorem exactSource (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F,
      AutomorphicForm.rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : AutomorphicForm.HasArchType₀ F χ φ) :
    AutomorphicForm.HasArchType₀ F χ (AutomorphicForm.fnTwist F η φ) :=
  AutomorphicForm.hasArchType₀_fnTwist F η χ hφ

/-- Higher-universe consumer. -/
public theorem exactSourceTypeOne (F : Type 1) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F,
      AutomorphicForm.rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : AutomorphicForm.HasArchType₀ F χ φ) :
    AutomorphicForm.HasArchType₀ F χ (AutomorphicForm.fnTwist F η φ) :=
  AutomorphicForm.hasArchType₀_fnTwist F η χ hφ

/-- The zero function satisfies every archimedean type condition, and its
twist is again zero at every argument. -/
public example (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F,
      AutomorphicForm.rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.fnTwist F η (fun _ => (0 : ℂ)) g = 0 := by
  simp [AutomorphicForm.fnTwist_apply]

/-- Boundary: the character value matters. If `χ k ≠ 1` at some place, the
constant function `1` does not satisfy the corresponding archimedean
character condition, so the prescribed character cannot be dropped. -/
public theorem constant_one_fails_of_ne_one (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F)
    (χ : AutomorphicForm.rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (k : AutomorphicForm.rowIsometrySubgroup₀ w.Completion) (hχ : χ k ≠ 1) :
    ¬ AutomorphicForm.HasArchCharacterAt₀ F w χ (fun _ => (1 : ℂ)) := by
  intro h
  have hk := h k 1
  simp only [mul_one] at hk
  exact hχ (Units.val_eq_one.mp hk.symm)

end AutomorphicFormFnTwistTest
