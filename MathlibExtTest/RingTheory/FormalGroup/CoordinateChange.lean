/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.FormalGroup.CoordinateChange

@[expose] public section

open FormalGroup

/-- Source-shaped consumer with the original binders. -/
private theorem exactSource {R : Type*} [CommRing R] (F : FormalGroup R) (u : PowerSeries R)
    (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u)) :
    ∃ F' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F', ψ.series = u) ∧
      (F.IsComm → F'.IsComm) ∧
      ∀ F'' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F'', ψ.series = u) → F'' = F' :=
  FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one F u hu0 hu1

/-- Higher-universe consumer: the coefficient ring may live in `Type 1`. -/
private theorem exactSourceTypeOne {R : Type 1} [CommRing R] (F : FormalGroup R)
    (u : PowerSeries R) (hu0 : PowerSeries.constantCoeff u = 0)
    (hu1 : IsUnit (PowerSeries.coeff 1 u)) :
    ∃ F' : FormalGroup R, ∃ ψ : FormalGroup.LawIso F F', ψ.series = u :=
  (FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one F u hu0 hu1).elim
    fun F' h => ⟨F', h.1⟩

/-- The identity series transports a law to itself. -/
example {R : Type*} [CommRing R] (F : FormalGroup R) :
    ∃ F' : FormalGroup R, ∃ ψ : FormalGroup.LawIso F F', ψ.series = PowerSeries.X :=
  (exactSource F PowerSeries.X (by simp) (by simp)).elim fun F' h => ⟨F', h.1⟩
