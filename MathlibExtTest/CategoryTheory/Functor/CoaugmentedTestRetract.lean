/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: @toskua
-/

import MathlibExt.CategoryTheory.Functor.CoaugmentedTestRetract
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Functor.CoaugmentedTestRetract

namespace MathlibExtTest.CoaugmentedTestRetract

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) (η : 𝟭 C ⟶ T)

example (X E : C) [IsIso (η.app E)] :
    homRetraction T η X E =
      fun g => η.app X ≫ g ≫ CategoryTheory.inv (η.app E) := rfl

example (X E : C) [IsIso (η.app E)] :
    Function.LeftInverse (homRetraction T η X E) (fun g => T.map g) :=
  homRetraction_map T η X E

example {X Y E : C} [IsIso (η.app E)] (f : X ⟶ Y)
    (g : T.obj Y ⟶ T.obj E) :
    homRetraction T η X E (T.map f ≫ g) = f ≫ homRetraction T η Y E g :=
  homRetraction_source T η f g

example (X : C) {E E' : C} [IsIso (η.app E)] [IsIso (η.app E')]
    (p : E ⟶ E') (g : T.obj X ⟶ T.obj E) :
    homRetraction T η X E' (g ≫ T.map p) = homRetraction T η X E g ≫ p :=
  homRetraction_target T η X p g

example {X Y E : C} (f : X ⟶ Y) [IsIso (T.map f)] [IsIso (η.app E)] :
    Function.Bijective (fun g : Y ⟶ E => f ≫ g) :=
  precomp_bijective_of_map_isIso T η f

example (X E : C) (g : X ⟶ E) :
    homRetraction (𝟭 C) (𝟙 (𝟭 C)) X E g = g := by
  simpa only [Functor.id_map] using homRetraction_map (𝟭 C) (𝟙 (𝟭 C)) X E g

run_cmd do
  let env ← Lean.getEnv
  let names := #[
    ``homRetraction, ``homRetraction_map, ``homRetraction_source,
    ``homRetraction_target, ``precomp_bijective_of_map_isIso]
  let moduleIndex ← match env.getModuleIdx? `MathlibExt.CategoryTheory.Functor.CoaugmentedTestRetract with
    | some i => pure i
    | none => throwError "missing canonical coaugmentation module"
  for n in names do
    let info ← match env.find? n with
      | some i => pure i
      | none => throwError "missing public coaugmentation declaration {n}"
    unless env.getModuleIdxFor? n == some moduleIndex do
      throwError "coaugmentation declaration has wrong source module {n}"
    if info.isUnsafe then throwError "unsafe coaugmentation declaration {n}"
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "unexpected axiom {ax} in {n}"

#lint only unusedArguments in MathlibExt.CategoryTheory.Functor.CoaugmentedTestRetract

end MathlibExtTest.CoaugmentedTestRetract
