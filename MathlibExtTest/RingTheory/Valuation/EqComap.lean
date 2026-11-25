/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.EqComap

@[expose] public section

open scoped WithZero

namespace ValuationEqComapTest

universe u v

/-- Exact-source consumer, with the original binders and universes. -/
theorem exactSource {L : Type u} {L' : Type v} [Field L] [Field L']
    {v : Valuation L' (WithZero (Multiplicative ℤ))}
    {w : Valuation L (WithZero (Multiplicative ℤ))}
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (σ : L ≃+* L')
    (hle : w.valuationSubring ≤ v.valuationSubring.comap σ.toRingHom) :
    w = v.comap σ.toRingHom :=
  Valuation.eq_comap_of_valuationSubring_le_comap hv hw σ hle

/-- Higher-universe consumer: fields in different universes. -/
theorem higherUniverse {L : Type (u + 1)} {L' : Type v} [Field L] [Field L']
    {v : Valuation L' (WithZero (Multiplicative ℤ))}
    {w : Valuation L (WithZero (Multiplicative ℤ))}
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (σ : L ≃+* L') (hle : w.valuationSubring ≤
      v.valuationSubring.comap σ.toRingHom) :
    w = v.comap σ.toRingHom :=
  Valuation.eq_comap_of_valuationSubring_le_comap hv hw σ hle

end ValuationEqComapTest
