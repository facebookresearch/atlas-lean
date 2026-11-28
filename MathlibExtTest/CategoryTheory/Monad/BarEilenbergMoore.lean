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

public import MathlibExt.CategoryTheory.Monad.BarEilenbergMoore
public import Mathlib.CategoryTheory.Monad.Types

/-!
# Literal Eilenberg–Moore bar clients

Use the option algebra on Bool pointed at false. In its actual evaluated-and-
forgotten free-algebra bar, the two degree-one faces send Some None to None and Some false.
The literal comparison preserves this element, and the transported augmentation section is
Some on the algebra carrier. The section followed by augmentation is identity, while their
reverse composite changes None.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Monad

namespace MathlibExtTest.CategoryTheory.Monad.BarEilenbergMoore

/-- The option monad on types. -/
abbrev T : Monad Type := ofTypeMonad Option

/-- The option algebra on Bool with the specified default value. -/
def pointed (b : Bool) : T.Algebra where
  A := Bool
  a := ↾fun o => o.getD b
  unit := by ext x; rfl
  assoc := by
    ext o
    rcases o with _ | _ | x <;> rfl

/-- Negation carries the false-pointed option algebra to the true-pointed algebra. -/
def notHom : pointed false ⟶ pointed true where
  f := ↾not
  h := by
    ext o
    rcases o with _ | x <;> rfl

/-- The option algebra pointed at false. -/
abbrev alg := pointed false

example :
    (emLiteralAugmented alg).left.obj (Opposite.op (SimplexCategory.mk 1)) =
      Option (Option Bool) := rfl

example :
    (emLiteralAugmented alg).left.map (SimplexCategory.δ (0 : Fin 2)).op
      (some none : Option (Option Bool)) = none := rfl

example :
    (emLiteralAugmented alg).left.map (SimplexCategory.δ (1 : Fin 2)).op
      (some none : Option (Option Bool)) = some false := rfl

example :
    (emLiteralResolutionIso alg).hom.left.app (Opposite.op (SimplexCategory.mk 1))
      (some none : Option (Option Bool)) = some none := by
  rw [emLiteralResolutionIso_hom_left_app]
  rfl

example : (emExtra alg).s' (false : Bool) = some false := by
  rw [emExtra_s']
  rfl

example : (emExtra alg).s' (true : Bool) = some true := by
  rw [emExtra_s']
  rfl

example :
    (emLiteralAugmented alg).hom.app (Opposite.op (SimplexCategory.mk 0))
      ((emExtra alg).s' (true : Bool)) = true := by
  rw [emExtra_s']
  rfl

example :
    (emExtra alg).s'
      ((emLiteralAugmented alg).hom.app (Opposite.op (SimplexCategory.mk 0))
        (none : Option Bool)) = some false := by
  rw [emExtra_s']
  rfl

example :
    (emLiteralHom notHom).left.app (Opposite.op (SimplexCategory.mk 0))
      (some true : Option Bool) = some false := rfl

end MathlibExtTest.CategoryTheory.Monad.BarEilenbergMoore
