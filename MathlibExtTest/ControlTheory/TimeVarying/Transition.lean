/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.TimeVarying.Transition
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix
open scoped Matrix.Norms.Elementwise
open ControlTheory

-- With the constant identity fundamental matrix, every
-- transition is the identity: at equal times by
-- `transition_self`, and in composition by
-- `transition_mul`.
example : transition (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 2 2 = 1 := by
  haveI : Invertible (1 : Matrix (Fin 2) (Fin 2) ℝ) := ⟨1, mul_one _, mul_one _⟩
  exact transition_self _ _

example : transition (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 3 1
    * transition (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 0
    = transition (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 3 0 := by
  haveI : Invertible (1 : Matrix (Fin 2) (Fin 2) ℝ) := ⟨1, mul_one _, mul_one _⟩
  exact transition_mul _ _ _ _

-- With `A = 0` and constant `X = 1`, the transition has
-- derivative `0 * Φ(t, s) = 0`.
example (t s : ℝ) :
    HasDerivAt (fun u => transition (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) u s)
      ((0 : Matrix (Fin 2) (Fin 2) ℝ)
        * transition (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) t s) t := by
  apply transition_hasDerivAt (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ))
  have h : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 t :=
    hasDerivAt_const (x := t) (c := (1 : Matrix (Fin 2) (Fin 2) ℝ))
  simpa using h

#print axioms transition_self
#print axioms transition_mul
#print axioms transition_hasDerivAt
