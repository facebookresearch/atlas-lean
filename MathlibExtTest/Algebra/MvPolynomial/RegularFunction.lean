/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.MvPolynomial.RegularFunction
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Basic.Real.Basic

open MvPolynomial

namespace MvPolynomial.RegularFunction

/-- Evaluation at a point distributes over composition. -/
example {σ τ ι : Type*} (F : RegularFunction ℚ σ τ)
    (G : RegularFunction ℚ τ ι) (a : σ → ℚ) :
    (G.comp F).aeval a = G.aeval (F.aeval a) :=
  comp_aeval G F a

/-- Composition evaluation also works after scalar extension. -/
example {σ τ ι : Type*} (F : RegularFunction ℚ σ τ)
    (G : RegularFunction ℚ τ ι) (a : σ → ℝ) :
    (G.comp F).aeval a = G.aeval (F.aeval a) :=
  comp_aeval G F a

/-- The Jacobian of a rectangular map is a codomain-by-domain matrix:
its `(j, i)` entry differentiates the `j`-th component in the `i`-th variable. -/
example (F : RegularFunction ℚ (Fin 2) (Fin 3)) (j : Fin 3) (i : Fin 2) :
    F.Jacobian j i = MvPolynomial.pderiv i (F j) :=
  Jacobian_apply F j i

/-- Composition applies componentwise by polynomial substitution. -/
example (G : RegularFunction ℚ (Fin 2) (Fin 3)) (F : RegularFunction ℚ (Fin 1) (Fin 2))
    (i : Fin 3) :
    (G.comp F) i = MvPolynomial.bind₁ F (G i) :=
  comp_apply G F i

/-- The identity regular function has the coordinate polynomials as components. -/
example (i : Fin 2) : id ℚ (Fin 2) i = MvPolynomial.X i :=
  id_apply i

/-- Left identity law for composition. -/
example (F : RegularFunction ℚ (Fin 2) (Fin 3)) :
    (id ℚ (Fin 3)).comp F = F :=
  id_comp F

/-- Right identity law for composition. -/
example (F : RegularFunction ℚ (Fin 2) (Fin 3)) :
    F.comp (id ℚ (Fin 2)) = F :=
  comp_id F

/-- Composition of regular functions is associative. -/
example (H : RegularFunction ℚ (Fin 3) (Fin 4)) (G : RegularFunction ℚ (Fin 2) (Fin 3))
    (F : RegularFunction ℚ (Fin 1) (Fin 2)) :
    (H.comp G).comp F = H.comp (G.comp F) :=
  comp_assoc H G F

/-- Pointwise form of evaluation/composition compatibility. -/
example {σ τ ι : Type*} (F : RegularFunction ℚ σ τ)
    (G : RegularFunction ℚ τ ι) (a : σ → ℚ) (i : ι) :
    (G.comp F).aeval a i = G.aeval (F.aeval a) i := by
  rw [comp_aeval]

/-- Iterated composition evaluates inside-out. -/
example {σ τ ι κ : Type*} (F : RegularFunction ℚ σ τ)
    (G : RegularFunction ℚ τ ι) (H : RegularFunction ℚ ι κ)
    (a : σ → ℚ) :
    (H.comp (G.comp F)).aeval a = H.aeval (G.aeval (F.aeval a)) := by
  rw [comp_aeval, comp_aeval]

end MvPolynomial.RegularFunction
