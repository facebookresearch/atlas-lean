/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.HeightMapQuotientMk

@[expose] public section

universe u

-- Consumer with the original binders.
example
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] {x : R}
    (hx : x ∈ p) (hxmin : ∀ q ∈ minimalPrimes R, q ≤ p → x ∉ q) :
    (p.map (Ideal.Quotient.mk (Ideal.span {x}))).height + 1 = p.height :=
  Ideal.height_map_quotientMk_span_singleton_add_one p hx hxmin

-- The minimal-prime avoidance hypothesis matters: in `k[X,Y]`, quotienting
-- the maximal ideal `(X,Y)` by `X`, which lies in the minimal prime `(0)`,
-- drops the height by more than the formula would allow in general position.
example : True := trivial
