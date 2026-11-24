/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.CrossingQuotient

@[expose] public section

noncomputable section

namespace MvPolynomial.CrossingQuotient

/-- Consumer using the original binders of the crossing quotient carrier. -/
example {W : Type*} [CommRing W] (t : W) : Type _ := CrossingQuotient W t

example {W : Type*} [CommRing W] (t : W) : CrossingQuotient W t := U t * V t

theorem exactSource {W : Type*} [CommRing W] (t : W) :
    U t * V t = algebraMap W (CrossingQuotient W t) t := U_mul_V t

end MvPolynomial.CrossingQuotient

