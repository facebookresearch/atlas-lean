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

-- The minimal-prime avoidance hypothesis matters: for `x = 0` and
-- `p = ⊥` over a field, `x` lies in the minimal prime `⊥`, and the
-- conclusion fails since both heights are `0`, so `0 + 1 ≠ 0`.
example {K : Type} [Field K] :
    ¬ ((⊥ : Ideal K).map (Ideal.Quotient.mk (Ideal.span {(0 : K)}))).height + 1 =
      (⊥ : Ideal K).height := by
  simp
