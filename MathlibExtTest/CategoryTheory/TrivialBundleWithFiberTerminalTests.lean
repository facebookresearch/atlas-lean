/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.TrivialBundleWithFiberTerminal
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Clients of the terminal-base fixed-fiber trivial bundles

`TrivialBundleWithFiber.ofIsTerminal` presents a map to a terminal object as a trivial bundle
whose second projection is the identity, so its product lift is the second component. For the
map `Bool ⟶ PUnit` of types, the lift of the parity map on `ℕ` is the parity map.

`TrivialBundleWithFiber.ofIsPullbackOfFac` presents the pulled-back map of a pullback square
along a map factoring through a terminal object, with fixed fiber `pullback p b`. Its second
projection followed by the two legs of `pullback p b` is the top map of the square and the base
map followed by the factorization. This is checked for an arbitrary square and for the chosen
pullback square, together with the product lift of the returned bundle.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.TrivialBundleWithFiberTerminalTests

variable {C : Type u} [Category.{v} C]

/-! ### `ofIsTerminal` -/

/-- The second projection of the bundle over a terminal base is the identity. -/
example {E B : C} (p : E ⟶ B) (hB : IsTerminal B) :
    (TrivialBundleWithFiber.ofIsTerminal p hB).r = 𝟙 E :=
  rfl

/-- The product lift of the bundle over a terminal base is the second component. -/
example {E B X : C} (p : E ⟶ B) (hB : IsTerminal B) (x : X ⟶ B) (y : X ⟶ E) :
    BinaryFan.IsLimit.lift (TrivialBundleWithFiber.ofIsTerminal p hB).isLimit x y = y :=
  rfl

/-- Every map into the total space is the product lift of its two components. -/
example {E B X : C} (p : E ⟶ B) (hB : IsTerminal B) (m : X ⟶ E) :
    m = BinaryFan.IsLimit.lift (TrivialBundleWithFiber.ofIsTerminal p hB).isLimit (m ≫ p) m :=
  BinaryFan.IsLimit.hom_ext (TrivialBundleWithFiber.ofIsTerminal p hB).isLimit
    (BinaryFan.IsLimit.lift_fst _ _ _).symm
    ((Category.comp_id m).trans (BinaryFan.IsLimit.lift_snd _ _ _).symm)

/-- The map of types `Bool ⟶ PUnit` with fiber `Bool`. -/
noncomputable abbrev boolOverPoint :
    TrivialBundleWithFiber Bool (Types.isTerminalPUnit.from Bool) :=
  TrivialBundleWithFiber.ofIsTerminal (Types.isTerminalPUnit.from Bool) Types.isTerminalPUnit

/-- Its second projection fixes each Boolean. -/
example (x : Bool) : boolOverPoint.r x = x :=
  rfl

/-- The lift of the parity map on `ℕ` evaluates as that map: `3` goes to `false`. -/
example :
    BinaryFan.IsLimit.lift boolOverPoint.isLimit (Types.isTerminalPUnit.from ℕ)
      (↾fun n : ℕ => decide (n % 2 = 0)) 3 = false :=
  rfl

/-- The same lift sends `4` to `true`. -/
example :
    BinaryFan.IsLimit.lift boolOverPoint.isLimit (Types.isTerminalPUnit.from ℕ)
      (↾fun n : ℕ => decide (n % 2 = 0)) 4 = true :=
  rfl

/-! ### `ofIsPullbackOfFac` -/

section Pullback

variable {E E' B B' T : C} {p' : E' ⟶ B'} {p : E ⟶ B} {f : B' ⟶ B} {f' : E' ⟶ E}
  (sq : IsPullback f' p' p f) (hT : IsTerminal T) (a : B' ⟶ T) (b : T ⟶ B)
  (fac : a ≫ b = f) [HasPullback p b]

/-- The second projection of the returned bundle, with fixed fiber `pullback p b`, is the
canonical lift of the top map and the base map followed by `a`. -/
example :
    (TrivialBundleWithFiber.ofIsPullbackOfFac sq hT a b fac).r =
      pullback.lift f' (p' ≫ a) (by simp [fac, sq.w]) ≫ 𝟙 (pullback p b) :=
  rfl

/-- The second projection followed by the first leg of the fiber is the top map. -/
theorem r_fst :
    (TrivialBundleWithFiber.ofIsPullbackOfFac sq hT a b fac).r ≫ pullback.fst p b = f' := by
  change (pullback.lift f' (p' ≫ a) (by simp [fac, sq.w]) ≫ 𝟙 (pullback p b)) ≫
    pullback.fst p b = f'
  simp

/-- The second projection followed by the second leg of the fiber is the base map followed by
the map to the terminal object. -/
theorem r_snd :
    (TrivialBundleWithFiber.ofIsPullbackOfFac sq hT a b fac).r ≫ pullback.snd p b = p' ≫ a := by
  change (pullback.lift f' (p' ≫ a) (by simp [fac, sq.w]) ≫ 𝟙 (pullback p b)) ≫
    pullback.snd p b = p' ≫ a
  simp

/-- The returned bundle exhibits `E'` as the product of `B'` and the fixed fiber. -/
example {X : C} (x : X ⟶ B') (y : X ⟶ pullback p b) :
    BinaryFan.IsLimit.lift (TrivialBundleWithFiber.ofIsPullbackOfFac sq hT a b fac).isLimit x y ≫
      p' = x :=
  BinaryFan.IsLimit.lift_fst _ _ _

example {X : C} (x : X ⟶ B') (y : X ⟶ pullback p b) :
    BinaryFan.IsLimit.lift (TrivialBundleWithFiber.ofIsPullbackOfFac sq hT a b fac).isLimit x y ≫
      (TrivialBundleWithFiber.ofIsPullbackOfFac sq hT a b fac).r = y :=
  BinaryFan.IsLimit.lift_snd _ _ _

/-- For the chosen pullback square, the fiber coordinate recovers the first pullback leg. -/
example [HasPullback p f] :
    (TrivialBundleWithFiber.ofIsPullbackOfFac (IsPullback.of_hasPullback p f) hT a b fac).r ≫
      pullback.fst p b = pullback.fst p f :=
  r_fst (IsPullback.of_hasPullback p f) hT a b fac

/-- For the chosen pullback square, the fiber coordinate followed by the second leg is the second
pullback leg followed by `a`. -/
example [HasPullback p f] :
    (TrivialBundleWithFiber.ofIsPullbackOfFac (IsPullback.of_hasPullback p f) hT a b fac).r ≫
      pullback.snd p b = pullback.snd p f ≫ a :=
  r_snd (IsPullback.of_hasPullback p f) hT a b fac

end Pullback

end MathlibExtTest.CategoryTheory.TrivialBundleWithFiberTerminalTests
