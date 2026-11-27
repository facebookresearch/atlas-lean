/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.GrandCoupling

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.GrandCoupling`

* `integral_g_codeMap` (the coding map has law `μ`) for the random-cluster mass on `K₂` at
  `p = 1/2`, `q = 2`, tested on the coordinate observable;
* `abs_coord_le_one` on a concrete configuration;
* `fk_grandCoupling_fkg_cross` on `K₂` for the coordinate observable;
* `osss_grand_coupling` for an arbitrary monotonic measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.GrandCoupling

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open MeasureTheory

-- The law of the coding map under `Vcube` is the random-cluster mass on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    ∫ u, Lindeberg.coord s(0, 1)
        (codeMap (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (σ : Fin n → Sym2 (Fin 2)) u) ∂(Vcube n)
      = ∑ x, Lindeberg.coord s(0, 1) x * MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 x :=
  integral_g_codeMap _
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) σ _

-- The coordinate observable is bounded by `1` in absolute value.
example : |Lindeberg.coord (s(0, 1) : Sym2 (Fin 2)) (fun _ => true)| ≤ 1 :=
  abs_coord_le_one _ _

-- The FKG cross inequality for the grand coupling on `K₂`, for the coordinate observable.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (e : Sym2 (Fin 2)) (U : Fin n → ℝ) (s₁ s₂ : ℕ) :
    (∫ Vv, Lindeberg.coord s(0, 1) (codeMap (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (σ : Fin n → Sym2 (Fin 2)) (Wt U Vv s₁)) ∂(Vcube n))
        * (∫ Vv, Lindeberg.coord e (codeMap (MonotonicFK.fkMass ⊤ (1 / 2) 2)
            (σ : Fin n → Sym2 (Fin 2)) (Wt U Vv s₂)) ∂(Vcube n))
      ≤ ∫ Vv, Lindeberg.coord s(0, 1) (codeMap (MonotonicFK.fkMass ⊤ (1 / 2) 2)
            (σ : Fin n → Sym2 (Fin 2)) (Wt U Vv s₁))
          * Lindeberg.coord e (codeMap (MonotonicFK.fkMass ⊤ (1 / 2) 2)
            (σ : Fin n → Sym2 (Fin 2)) (Wt U Vv s₂)) ∂(Vcube n) :=
  fk_grandCoupling_fkg_cross ⊤ (by norm_num) (by norm_num) (by norm_num) σ
    (Lindeberg.coord_mono _) (abs_coord_le_one _) e U s₁ s₂

-- The grand-coupling FKG inequality for any monotonic measure (first component).
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ) (t : ℕ) :
    (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1)))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n) :=
  (osss_grand_coupling hpos hmono σ hf hfC e U t).1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.GrandCoupling
