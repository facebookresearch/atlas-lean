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

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial

/-!
# The polynomial variable Koszul complex for an arbitrary index type

For a commutative ring R and any variable type I, the Koszul complex of the variables in
MvPolynomial I R is built on exterior powers of the free finitely supported module. Its terms
are free, and every positive-degree cycle is a boundary. The quotient augmentation identifies
the degree-zero coefficient with the polynomial ring modulo the variable ideal.

This module provides the canonical general polynomial Koszul API through its import.
-/
