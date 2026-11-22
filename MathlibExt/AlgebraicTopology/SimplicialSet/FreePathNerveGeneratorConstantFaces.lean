/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGeneratorCoordinates

/-!
# The SAME full original constant faces of generating-arrow cells

Constant native ordinal coefficients retain the original individual
source or target vertex and every native identity map. No original
edge orientation or coefficient is replaced.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- A constant source coefficient reads the SAME entire original constant source word. -/
theorem generatorCell_constant_zero {x y : V} (f : x ⟶ y) (n : ℕ) :
    (generatorCell V f).app (op ⦋n⦌)
      (SSet.stdSimplex.objMk (OrderHom.const (Fin (n + 1)) (0 : Fin 2))) =
        (Functor.const (Fin (n + 1)) (C := Paths V)).obj (x : Paths V) := by
  change (OrderHom.const (Fin (n + 1)) (0 : Fin 2)).toFunctor ⋙ generatorWord V f =
    (Functor.const (Fin (n + 1)) (C := Paths V)).obj (x : Paths V)
  apply Functor.hext (D := Paths V) (fun _ => rfl)
  intro i j g
  rfl

/-- A constant target coefficient reads the SAME entire original constant target word. -/
theorem generatorCell_constant_one {x y : V} (f : x ⟶ y) (n : ℕ) :
    (generatorCell V f).app (op ⦋n⦌)
      (SSet.stdSimplex.objMk (OrderHom.const (Fin (n + 1)) (1 : Fin 2))) =
        (Functor.const (Fin (n + 1)) (C := Paths V)).obj (y : Paths V) := by
  change (OrderHom.const (Fin (n + 1)) (1 : Fin 2)).toFunctor ⋙ generatorWord V f =
    (Functor.const (Fin (n + 1)) (C := Paths V)).obj (y : Paths V)
  apply Functor.hext (D := Paths V) (fun _ => rfl)
  intro i j g
  rfl

end CategoryTheory.FreePathNerveCoordinates
