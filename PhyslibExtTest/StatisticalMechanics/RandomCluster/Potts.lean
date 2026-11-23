/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Potts

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Potts`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` with `q = 2` or `q = 3` spin values:
* `monoIndicator` is `1` on a monochromatic pair and `0` on a bichromatic one;
* `agreement` is `1` for a constant spin configuration and `0` for a non-constant one;
* `pottsWeight` is `exp (β J)` resp. `1` on these configurations, and `1` at `β = 0`;
* at `β = 0` the partition function is `q ^ |V|` (`pottsZ ⊤ 3 0 J = 9`) and `pottsProb` is the
  uniform distribution `1 / 9`;
* `pottsProb` is positive and normalized, and `pottsPMF` has the expected point masses.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Potts

open _root_.StatMech _root_.StatMech.Potts

/-- The constant spin configuration `0` on `Fin 2` with `q` values. -/
def constSpin (q : ℕ) [NeZero q] : Fin 2 → Fin q := fun _ => 0

/-- The non-constant spin configuration `i ↦ i` on `Fin 2` with two values. -/
def idSpin : Fin 2 → Fin 2 := fun i => i

/-- The agreement count of a configuration on `⊤ : SimpleGraph (Fin 2)` is the monochromatic
indicator of its single edge `s(0, 1)`. -/
theorem agreement_top_fin2 {q : ℕ} (σ : Fin 2 → Fin q) :
    agreement (⊤ : SimpleGraph (Fin 2)) σ = monoIndicator σ s(0, 1) := by
  have h : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
    ext e
    induction e with
    | _ x y => fin_cases x <;> fin_cases y <;> simp
  rw [agreement, h, Finset.sum_singleton]

-- A monochromatic pair has indicator `1`.
example : monoIndicator (constSpin 3) s(0, 1) = 1 := by simp [constSpin]

-- A bichromatic pair has indicator `0`.
example : monoIndicator idSpin s(0, 1) = 0 := by simp [idSpin]

-- The constant configuration agrees on the single edge of `⊤`.
example : agreement (⊤ : SimpleGraph (Fin 2)) (constSpin 3) = 1 := by
  rw [agreement_top_fin2]; simp [constSpin]

-- The configuration `i ↦ i` disagrees on the single edge.
example : agreement (⊤ : SimpleGraph (Fin 2)) idSpin = 0 := by
  rw [agreement_top_fin2]; simp [idSpin]

-- The Boltzmann weight of the constant configuration is `exp (β J)`.
example (β J : ℝ) : pottsWeight (⊤ : SimpleGraph (Fin 2)) β J (constSpin 3) = Real.exp (β * J) := by
  rw [pottsWeight, agreement_top_fin2]; simp [constSpin]

-- The Boltzmann weight of a bichromatic configuration is `1`.
example (β J : ℝ) : pottsWeight (⊤ : SimpleGraph (Fin 2)) β J idSpin = 1 := by
  rw [pottsWeight, agreement_top_fin2]; simp [idSpin]

/-- At infinite temperature `β = 0` the Potts partition function counts configurations. -/
theorem pottsZ_beta_zero (q : ℕ) (J : ℝ) :
    pottsZ (⊤ : SimpleGraph (Fin 2)) q 0 J = (q : ℝ) ^ 2 := by
  simp [pottsZ, pottsWeight]

-- With three colours on two vertices, `Z = 9` at `β = 0`.
example (J : ℝ) : pottsZ (⊤ : SimpleGraph (Fin 2)) 3 0 J = 9 := by
  rw [pottsZ_beta_zero]; norm_num

-- At `β = 0` the Gibbs measure is uniform.
example (J : ℝ) (σ : Fin 2 → Fin 3) : pottsProb (⊤ : SimpleGraph (Fin 2)) 3 0 J σ = 1 / 9 := by
  rw [pottsProb, pottsZ_beta_zero]; simp [pottsWeight]; norm_num

-- `pottsProb` is positive and sums to one (here `q = 2`, `β = 1`, `J = 1`).
example (σ : Fin 2 → Fin 2) : 0 < pottsProb (⊤ : SimpleGraph (Fin 2)) 2 1 1 σ :=
  pottsProb_pos _ 2 1 1 σ

-- The Gibbs probabilities are normalized.
example : ∑ σ : Fin 2 → Fin 2, pottsProb (⊤ : SimpleGraph (Fin 2)) 2 1 1 σ = 1 :=
  pottsProb_sum_eq_one _ 2 1 1

-- `pottsPMF` puts mass `pottsProb` on each configuration.
example :
    pottsPMF (⊤ : SimpleGraph (Fin 2)) 2 1 1 idSpin
      = ENNReal.ofReal (pottsProb (⊤ : SimpleGraph (Fin 2)) 2 1 1 idSpin) := by
  simp

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Potts
