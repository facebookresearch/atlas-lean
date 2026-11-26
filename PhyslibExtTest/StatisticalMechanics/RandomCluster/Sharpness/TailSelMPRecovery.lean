/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPRecovery

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPRecovery`

* `tsc_tailSelMP_at_s_eq_t` for the FK mass on the complete graph `K₂` at `p = 1/2`, `q = 2`,
  an arbitrary observable and `t = s = 1`;
* `tsc_restrictedSum_at_s_eq_t`: the restricted-sum identity at `s = t`, same instance;
* `tsc_stopValC_stable` applied to two configurations agreeing on the prefix;
* `tsc_stopValC_determinesC`: the observable is determined at its stopping step.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPRecovery

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.AdaptMConditional
open _root_.StatMech.OSSS.Coding

-- The tail selection is measure preserving at `s = t`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ)
    (A : {i : Fin n // (i : ℕ) < 1} → ℝ) :
    atl_TailSelMP (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f 1 1 A :=
  tsc_tailSelMP_at_s_eq_t _ σ f 1 A

-- The restricted-sum identity at `s = t`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ)
    (A : {i : Fin n // (i : ℕ) < 1} → ℝ) :
    tsm_TailSelMP_restrictedSum (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ f 1 1 A :=
  tsc_restrictedSum_at_s_eq_t _ σ f 1 A

-- The stopping step is stable under changes after it.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ)
    (X X' : ConfigSpace (Sym2 (Fin 2)))
    (hagree : ∀ e ∈ prefixSet (σ : Fin n → Sym2 (Fin 2)) (stopValC σ f X), X e = X' e) :
    stopValC σ f X' = stopValC σ f X :=
  tsc_stopValC_stable σ f X X' _ hagree rfl

-- The observable is determined at its stopping step.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (f : ConfigSpace (Sym2 (Fin 2)) → ℝ)
    (X : ConfigSpace (Sym2 (Fin 2))) :
    detAtC (σ : Fin n → Sym2 (Fin 2)) f X (stopValC σ f X) :=
  tsc_stopValC_determinesC σ f X

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPRecovery
