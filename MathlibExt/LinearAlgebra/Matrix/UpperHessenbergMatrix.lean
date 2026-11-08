/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs

/-!
# Upper Hessenberg matrices

The definition is recorded from Huilan Li and Trueman MacHenry,
*Permanents and Determinants, Weighted Isobaric Polynomials, and Integer
Sequences*, Journal of Integer Sequences 16 (2013), Article 13.3.5.

A square matrix is upper Hessenberg when every entry strictly below its
first subdiagonal is zero.

Stable source identifiers: concept `jis_sem_90166bc6652ac1c81120f42f`,
statement `jis_453961c69e4159797cfa575d`.

This module publicly imports the canonical `Matrix.IsUpperHessenberg` definition.
It supports any preordered index type with a successor order. On `Fin n`,
`Matrix.isUpperHessenberg_fin_iff` identifies it with the source condition
`∀ i j, j.val + 1 < i.val → M i j = 0`.
-/
