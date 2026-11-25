/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Matrix.TraceDistance
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Independent matrix-norm constructions in one environment

The sum of the singular values of a square complex matrix and the trace
of the square root of its Gram matrix have separate declaration families.
Both constructions, their scalar laws and the singular-value distance
constructors can be imported together, including on the empty index type.
-/

example : Matrix.singularValueTraceNorm (0 : Matrix (Fin 0) (Fin 0) ℂ) = 0 :=
  Matrix.singularValueTraceNorm_zero

example : Matrix.traceNorm (0 : Matrix (Fin 0) (Fin 0) ℂ) = 0 :=
  Matrix.traceNorm_zero

example : Matrix.traceNormDist (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 = 0 := by
  simp [Matrix.traceNormDist]
