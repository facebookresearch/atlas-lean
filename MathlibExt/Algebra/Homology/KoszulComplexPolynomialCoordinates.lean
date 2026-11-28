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

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial.Coordinates

/-!
# Polynomial Koszul coefficient coordinates and their degree filtration

For a commutative ring R and linearly ordered variable type I, the
Koszul complex over P = MvPolynomial I R has coefficient coordinates
(Set.powersetCard I n) →₀ P in exterior degree n. The signed deletion
differential multiplies a coefficient by the deleted variable.
Coefficientwise homogeneous projections and the filtration by polynomial
degree plus exterior degree describe its homogeneous cycles and
boundaries. The variable type and coefficient-ring worlds are independent.
-/
