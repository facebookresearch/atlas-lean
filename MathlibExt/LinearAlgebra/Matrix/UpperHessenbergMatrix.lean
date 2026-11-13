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

Mathlib now provides `Matrix.IsUpperHessenberg`. Its
`Matrix.isUpperHessenberg_fin_iff` identifies the predicate on `Fin n`
with the same entrywise condition `j.val + 1 < i.val → M i j = 0`.
This module retains the existing import path for consumers.

Stable source identifiers: concept `jis_sem_90166bc6652ac1c81120f42f`,
statement `jis_453961c69e4159797cfa575d`.
-/
