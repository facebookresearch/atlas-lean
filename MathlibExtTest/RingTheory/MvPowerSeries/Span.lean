/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.Span

@[expose] public section

open MvPowerSeries

example {R : Type*} [CommRing R] (ϖ : R) (n k : ℕ) (F : MvPowerSeries (Fin n) R) :
    F ∈ Ideal.span {(C ϖ : MvPowerSeries (Fin n) R)} ⊔
        Ideal.ofList ((List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).take k) ↔
      ∀ m : Fin n →₀ ℕ, (∀ j : Fin n, (j : ℕ) < k → m j = 0) → ϖ ∣ coeff m F :=
  MvPowerSeries.mem_span_C_sup_ofList_take_iff ϖ n k F

example {R : Type*} [CommRing R] (n : ℕ) :
    Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) R)) =
      RingHom.ker (constantCoeff : MvPowerSeries (Fin n) R →+* R) :=
  MvPowerSeries.span_range_X_eq_ker_constantCoeff n
