/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.JordanBlock

open MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted

variable {K : Type*} [Field K]

example (μ : K) (s : ℕ) (i j : Fin s) :
    jordanBlock s μ i j = (if i.val + 1 = j.val then 1 else if i = j then μ else 0) :=
  jordanBlock_apply s μ i j

example (μ : K) : jordanBlock 2 μ (0 : Fin 2) (1 : Fin 2) = 1 := rfl

example (μ : K) : jordanBlock 2 μ (0 : Fin 2) (0 : Fin 2) = μ := rfl

example (μ : K) : jordanBlock 2 μ (1 : Fin 2) (0 : Fin 2) = 0 := rfl
