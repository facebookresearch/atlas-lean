/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Monad.BarChange
public import Mathlib.CategoryTheory.Monad.Types

/-!
# Concrete monad-change bar clients

The inclusions from the identity monad to Option and from Option to List are actual monad
morphisms. For regular List modules, degree zero leaves a list of lists unchanged, whereas
degree one sends None to an empty list and Some to a singleton. The composite bar comparison
is evaluated through its composite-to-iterated restriction isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace CategoryTheory.Monad.BarChangeClient

/-- The identity Type monad used by the concrete client. -/
abbrev identityMonad : Monad (Type) := ofTypeMonad Id

/-- The option Type monad used by the concrete client. -/
abbrev optionMonad : Monad (Type) := ofTypeMonad Option

/-- The list Type monad used by the concrete client. -/
abbrev listMonad : Monad (Type) := ofTypeMonad List

private def idToOption : identityMonad ⟶ optionMonad where
  app X := ↾(fun x : X => some x)
  naturality X Y f := by
    ext x
    rfl
  app_η X := by
    ext x
    rfl
  app_μ X := by
    ext x
    rfl

private def optionToList : optionMonad ⟶ listMonad where
  app X := ↾(@Option.toList X)
  naturality X Y f := by
    ext x
    cases x <;> rfl
  app_η X := by
    ext x
    rfl
  app_μ X := by
    ext x
    cases x with
    | none => rfl
    | some x => cases x <;> rfl

private abbrev rightList : RightModule listMonad (Type) :=
  RightModule.regular listMonad

private abbrev leftList : LeftModule (Type) listMonad :=
  LeftModule.regular (T := listMonad)

example : idToOption.app ℕ (7 : ℕ) = some (7 : ℕ) := rfl

example : optionToList.app ℕ none = [] := rfl

example : optionToList.app ℕ (some 7) = [7] := rfl

example :
    (((barChangeHom optionToList rightList leftList).app
      (Opposite.op (SimplexCategory.mk 0))).app ℕ)
      ([[2, 3], []] : List (List ℕ)) = [[2, 3], []] := by
  rw [barChangeHom_app_app_op_mk, monadPowHom_zero_app]
  change List.map _root_.id ([[2, 3], []] : List (List ℕ)) = [[2, 3], []]
  rfl

example :
    (((barChangeHom optionToList rightList leftList).app
      (Opposite.op (SimplexCategory.mk 1))).app ℕ)
      ([none, some [2, 3]] : List (Option (List ℕ))) = [[], [[2, 3]]] := by
  rw [barChangeHom_app_app_op_mk, monadPowHom_succ_app, monadPowHom_zero_app]
  change List.map Option.toList ([none, some [2, 3]] : List (Option (List ℕ))) =
    [[], [[2, 3]]]
  rfl

example :
    (((barChangeHom idToOption
      ((rightModuleRestrictAlongHom optionToList).obj rightList)
      ((leftModuleRestrictAlongHom optionToList).obj leftList)).app
      (Opposite.op (SimplexCategory.mk 1))).app ℕ)
      ([[2, 3], []] : List (List ℕ)) = [some [2, 3], some []] := by
  rw [barChangeHom_app_app_op_mk, monadPowHom_succ_app, monadPowHom_zero_app]
  change List.map some ([[2, 3], []] : List (List ℕ)) = [some [2, 3], some []]
  rfl

example :
    ((((twoSidedBarRestrictCompIso idToOption optionToList rightList leftList).hom ≫
      barChangeHom idToOption
        ((rightModuleRestrictAlongHom optionToList).obj rightList)
        ((leftModuleRestrictAlongHom optionToList).obj leftList) ≫
      barChangeHom optionToList rightList leftList).app
      (Opposite.op (SimplexCategory.mk 1))).app ℕ)
      ([[2, 3], []] : List (List ℕ)) = [[[2, 3]], [[]]] := by
  rw [barChangeHom_comp idToOption optionToList rightList leftList]
  rw [barChangeHom_app_app_op_mk, monadPowHom_succ_app, monadPowHom_zero_app]
  change List.map (fun x : List ℕ => [x]) ([[2, 3], []] : List (List ℕ)) =
    [[[2, 3]], [[]]]
  rfl

end CategoryTheory.Monad.BarChangeClient
