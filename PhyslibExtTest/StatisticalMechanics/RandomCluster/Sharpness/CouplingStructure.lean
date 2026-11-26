/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CouplingStructure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CouplingStructure`

* `osss_coupling` applied to the random-cluster mass on `K₂` at `p = 1/2`, `q = 2`, for an
  arbitrary order and observable: the first-coordinate identity, and the marginal identity for the
  bounded test function `h = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CouplingStructure

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Coding
open _root_.StatMech.OSSS.GrandCoupling _root_.StatMech.OSSS.AdaptMConditional
open _root_.StatMech.OSSS.CouplingStructure MeasureTheory

-- At time `0` the adapted coupling reproduces `f` of the first code on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ)
    (U V : Fin n → ℝ) :
    f (codeMap (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (σ : Fin n → Sym2 (Fin 2))
        (adaptWt U V (stopVal (MonotonicFK.fkMass ⊤ (1 / 2) 2) σ f U) 0))
      = f (codeMap (MonotonicFK.fkMass ⊤ (1 / 2) 2) (σ : Fin n → Sym2 (Fin 2)) U) :=
  (osss_coupling (f := f)
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) σ U V).1

-- The coupling has the right marginals: tested against the bounded function `1`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ)
    (U V : Fin n → ℝ) :
    ∫ p, (fun (_ _ : ConfigSpace (Sym2 (Fin 2))) => (1 : ℝ))
        (codeMap (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (σ : Fin n → Sym2 (Fin 2)) p.1)
        (codeMap (MonotonicFK.fkMass ⊤ (1 / 2) 2) (σ : Fin n → Sym2 (Fin 2))
          (adaptWt p.1 p.2 (stopVal (MonotonicFK.fkMass ⊤ (1 / 2) 2) σ f p.1) n))
        ∂((Vcube n).prod (Vcube n))
      = ∑ x, (∑ y, (1 : ℝ) * MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 y)
          * MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 x :=
  (osss_coupling (f := f)
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) σ U V).2.1 (fun _ _ => 1) (Ch := 1) (fun _ _ => by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CouplingStructure
