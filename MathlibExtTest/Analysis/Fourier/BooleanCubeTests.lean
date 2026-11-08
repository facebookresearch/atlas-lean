/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCube

open BooleanCube

/-- The extension of a constant function is the corresponding constant. -/
example (b : Bool) :
    multilinearExtension (n := 3) (fun _ => b) =
      MvPolynomial.C (if b then (1 : ℝ) else 0) :=
  multilinearExtension_const b

/-- A coordinate projection has Boolean degree one. -/
example (i : Fin 4) : booleanDegree (fun x : BoolCube 4 => x i) = 1 :=
  booleanDegree_projection i

/-- The two-bit AND function has Boolean degree two. -/
example : booleanDegree (allTrueFunction (n := 2)) = 2 :=
  booleanDegree_allTrue_two

/-- Evaluation recovers the function at cube points. -/
example (f : BoolCube 2 → Bool) (y : BoolCube 2) :
    MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0)
      (multilinearExtension f) = if f y then 1 else 0 :=
  eval_multilinearExtension f y

/-- The indicator of any Boolean function has Fourier degree at most its
Boolean degree. -/
example (f : BoolCube 3 → Bool) :
    MultilinearDegreeLE 3 (fun x => if f x then (1 : ℝ) else 0)
      (booleanDegree f) :=
  multilinearDegreeLE_indicator f
