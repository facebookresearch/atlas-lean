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

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial.Homogeneous

/-!
# Homogeneous coefficients in the polynomial Koszul complex

For a commutative ring R and a linearly ordered variable type I, use the exterior basis of the
finitely supported polynomial module to project every coefficient to a fixed polynomial
degree. These projections are additive, and the Koszul differential raises polynomial
coefficient degree by one.

The imported general API gives the homogeneous cycle and boundary coordinate laws, including
the degree-zero coefficient case in positive exterior degree.
-/
