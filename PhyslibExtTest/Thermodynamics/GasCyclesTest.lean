/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Thermodynamics.GasCycles

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for `PhyslibExt.Thermodynamics.GasCycles`

A freezer between `250 K` and `300 K` that absorbs `4000 J` per cycle for `1000 J` of work:

* its Clausius residual is `2/3 J/K` and both coefficients of performance lie strictly below the
  reversible bounds `5` and `6`;
* the general results apply to it: the Clausius inequality forces positive work, the bounds hold,
  and the reversible machine (`5000 J` absorbed, `6000 J` rejected) attains them.

At equal reservoir temperatures `300 K` the coefficients have no finite bound: some admissible
cycle has both coefficients above `10`.

An ideal Otto loop of a monatomic gas (`Cv = 3 J/K`, `nR = 2 J/K`, `γ = 5/3`) compressed by `8`
from `300 K` and heated by `3000 J`:

* its states are `1200 K`, `2200 K` and `550 K`; it rejects `750 J` and does `2250 J` of net work;
* the general results apply to it: both legs lie on the adiabat, the rejected heat and the net
  work are positive, and the work-to-heat ratio is `ottoEfficiency 8 (5/3) = 3/4`;
* with zero heat input it does no work, and `0 / 0` is not the efficiency.

An ideal Diesel loop of the same gas at `r = 8` with cutoff ratio `rc = 125/64`:

* its states are `1200 K`, `9375/4 K` and `234375/256 K`; it takes in `22875/4 J`, rejects
  `472725/256 J`, does `991275/256 J` of net work and has efficiency `13217/19520`, below the Otto
  value `3/4`;
* the general results apply to it: the ideal-gas law places the cutoff state on the isobar of
  state `2`, the heats and the net work are positive, and the work-to-heat ratio is the Diesel
  efficiency, below the Otto efficiency;
* at `rc = 1` no heat is added and Lean's value of the formula is not the Otto efficiency, which
  is the limit as `rc` decreases to `1`; a cutoff ratio `16` above `r` turns the last adiabatic
  leg into a compression.

An air-standard Brayton loop (`R = 287 J/(kg K)`, `cp = 2009/2 J/(kg K)`, `γ = 7/5`) at pressure
ratio `(3/2) ^ 7`, so `a = 9/4`, from `300 K` with the turbine inlet at `1350 K`:

* its states are `675 K` and `600 K`; per unit mass it absorbs `678037.5 J/kg`, rejects
  `301350 J/kg` and does `376687.5 J/kg` of net work, with efficiency `5/9 < 7/9 = 1 - T₁ / T₃`;
* the general results apply to it: the loop is nondegenerate, the four leg balances fix the signs
  of the shaft works and heats, and every ideal-gas state at the compressor exit pressure on the
  inlet adiabat has the temperature `675 K`;
* without compression it does no work, and a turbine inlet below `675 K` gives no positive work;
* its compressor inlet is the coldest and its turbine inlet the hottest state, so `1 - T₁ / T₃` is
  the Carnot efficiency between them; at a pressure ratio below one the same inequality holds
  with a negative `1 - T₁ / T₃`, which is why the comparison requires `rp > 1`.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.GasCycles

open _root_.GasCycles

-- Fixture: a freezer between `Tc = 250` K and `Th = 300` K absorbs `Qc = 4000` J and takes
-- `W = 1000` J, rejecting `Qh = 5000` J. Its Clausius residual is `2/3` J/K, and
-- `COP_R = 4 < 5 = Tc / (Th - Tc)`, `COP_HP = 5 < 6 = Th / (Th - Tc)`. The reversible machine with
-- `Qc = 5000` J and `Qh = 6000` J has zero residual and attains both bounds.
example :
    (5000 : ℝ) / 300 - 4000 / 250 = 2 / 3 ∧ (4000 : ℝ) / 1000 < 250 / (300 - 250) ∧
      (5000 : ℝ) / 1000 < 300 / (300 - 250) ∧ (6000 : ℝ) / 300 - 5000 / 250 = 0 ∧
      (5000 : ℝ) / 1000 = 250 / (300 - 250) ∧ (6000 : ℝ) / 1000 = 300 / (300 - 250) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

-- The freezer and the reversible machine through the general results: the Clausius inequality
-- forces positive work, both coefficients of performance obey the reversible bounds, and the
-- reversible machine attains the refrigerator bound because its Clausius residual is zero.
example :
    (0 : ℝ) < 1000 ∧
      ((4000 : ℝ) / 1000 ≤ 250 / (300 - 250) ∧ (5000 : ℝ) / 1000 ≤ 300 / (300 - 250)) ∧
      (5000 : ℝ) / 1000 = 250 / (300 - 250) := by
  refine ⟨work_pos_of_clausius (Qh := 5000) (Qc := 4000) (Tc := 250) (Th := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cop_le_carnot (Qh := 5000) (Qc := 4000) (W := 1000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), ?_⟩
  exact (cop_eq_carnot_iff (Qh := 6000) (Qc := 5000) (W := 1000) (Tc := 250) (Th := 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1.2 (by norm_num)

-- Equal reservoir temperatures, `T = 300` K, and the bound `M = 10`: `cop_unbounded_of_eq` gives
-- an admissible cycle (`Qc > 0`, `W = Qh - Qc > 0`, Clausius inequality) whose coefficients of
-- performance both exceed `10`, so `10` is not an upper bound on `COP_R` over all admissible
-- cycles at that temperature.
example :
    (∃ Qh Qc W : ℝ, 0 < Qc ∧ W = Qh - Qc ∧ 0 < W ∧ 0 ≤ Qh / 300 - Qc / 300 ∧
        10 < Qc / W ∧ 10 < Qh / W) ∧
      ¬ ∀ Qh Qc W : ℝ, 0 < Qc → W = Qh - Qc → 0 < W → 0 ≤ Qh / 300 - Qc / 300 →
        Qc / W ≤ 10 := by
  have h := cop_unbounded_of_eq (T := 300) (by norm_num) 10
  refine ⟨h, fun hall => ?_⟩
  obtain ⟨Qh, Qc, W, hQc, hW, hWpos, hcl, hR, -⟩ := h
  have hle := hall Qh Qc W hQc hW hWpos hcl
  linarith

-- Fixture: a monatomic ideal gas (`Cv = 3` J/K, `nR = 2` J/K, so `γ = 5/3`) compressed by
-- `r = 8` from `T₁ = 300` K and heated by `Qin = 3000` J reaches `T₂ = 1200` K, `T₃ = 2200` K and
-- `T₄ = 550` K, rejects `750` J and does `2250` J of net work: `η = 3/4 = 1 - 8 ^ (1 - 5/3)`.
example :
    ottoCompressedTemp 300 8 (5 / 3) = 1200 ∧ ottoPeakTemp 300 8 (5 / 3) 3 3000 = 2200 ∧
      ottoExpandedTemp 300 8 (5 / 3) 3 3000 = 550 ∧ ottoHeatOut 300 8 (5 / 3) 3 3000 = 750 ∧
      ottoNetWork 300 8 (5 / 3) 3 3000 = 2250 ∧ ottoEfficiency 8 (5 / 3) = 3 / 4 := by
  have h8_23 : (8 : ℝ) ^ ((2 : ℝ) / 3) = 4 := by
    have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [h8, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : ((3 : ℕ) : ℝ) * ((2 : ℝ) / 3) = 2 := by norm_num
    rw [hexp, Real.rpow_two]
    norm_num
  have h23 : (5 / 3 - 1 : ℝ) = (2 : ℝ) / 3 := by norm_num
  have h8_comp : (8 : ℝ) ^ (5 / 3 - 1 : ℝ) = 4 := by
    rw [h23, h8_23]
  have hneg : (1 - 5 / 3 : ℝ) = -((2 : ℝ) / 3) := by norm_num
  have h8_neg : (8 : ℝ) ^ (1 - 5 / 3 : ℝ) = 1 / 4 := by
    rw [hneg, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), h8_23]
    norm_num
  have hcomp : ottoCompressedTemp 300 8 (5 / 3) = 1200 := by
    simp only [ottoCompressedTemp]
    rw [h8_comp]
    norm_num
  have hpeak : ottoPeakTemp 300 8 (5 / 3) 3 3000 = 2200 := by
    simp only [ottoPeakTemp, hcomp]
    norm_num
  have hexp : ottoExpandedTemp 300 8 (5 / 3) 3 3000 = 550 := by
    simp only [ottoExpandedTemp, hpeak]
    rw [h8_neg]
    norm_num
  have hheat : ottoHeatOut 300 8 (5 / 3) 3 3000 = 750 := by
    simp only [ottoHeatOut, hexp]
    norm_num
  have hwork : ottoNetWork 300 8 (5 / 3) 3 3000 = 2250 := by
    simp only [ottoNetWork, hpeak, hexp, hcomp]
    norm_num
  have heff : ottoEfficiency 8 (5 / 3) = 3 / 4 := by
    simp only [ottoEfficiency]
    rw [h8_neg]
    norm_num
  exact ⟨hcomp, hpeak, hexp, hheat, hwork, heff⟩

-- The monatomic loop through the general results, at `V₁ = 1`: `otto_cycle` puts both legs on
-- the adiabat, compression `T₂ * (V₁ / r) ^ (γ - 1) = T₁ * V₁ ^ (γ - 1)` and expansion
-- `T₄ * V₁ ^ (γ - 1) = T₃ * (V₁ / r) ^ (γ - 1)`, and gives positive rejected heat and net work;
-- `ottoNetWork_div_heatIn` identifies the work-to-heat ratio with `ottoEfficiency 8 (5/3)`, which
-- is `3/4` because `8 ^ (2/3) = 4`.
example :
    ottoCompressedTemp 300 8 (5 / 3) * (1 / 8) ^ ((5 : ℝ) / 3 - 1) = 300 * 1 ^ ((5 : ℝ) / 3 - 1) ∧
      ottoExpandedTemp 300 8 (5 / 3) 3 3000 * 1 ^ ((5 : ℝ) / 3 - 1) =
        ottoPeakTemp 300 8 (5 / 3) 3 3000 * (1 / 8) ^ ((5 : ℝ) / 3 - 1) ∧
      0 < ottoHeatOut 300 8 (5 / 3) 3 3000 ∧ 0 < ottoNetWork 300 8 (5 / 3) 3 3000 ∧
      ottoNetWork 300 8 (5 / 3) 3 3000 / 3000 = ottoEfficiency 8 (5 / 3) ∧
      ottoEfficiency 8 (5 / 3) = 3 / 4 := by
  obtain ⟨hc, he, -, hq, hw, -⟩ := otto_cycle (T₁ := 300) (V₁ := 1) (r := 8) (γ := 5 / 3)
    (Cv := 3) (nR := 2) (Qin := 3000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have h8 : (8 : ℝ) ^ (1 - (5 : ℝ) / 3) = 1 / 4 := by
    rw [show (1 : ℝ) - 5 / 3 = -(2 / 3) by norm_num, Real.rpow_neg (by norm_num),
      show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨hc, he, hq, hw,
    (ottoNetWork_div_heatIn (T₁ := 300) (by norm_num) (by norm_num) (by norm_num)).1, ?_⟩
  rw [ottoEfficiency, h8]
  norm_num

-- Zero heat input on the same gas: the loop does no net work, and the work-to-heat ratio `0 / 0`
-- is not the Otto efficiency.
example :
    ottoNetWork 300 8 (5 / 3) 3 0 = 0 ∧
      ottoNetWork 300 8 (5 / 3) 3 0 / 0 ≠ ottoEfficiency 8 (5 / 3) :=
  otto_zero_heatIn (by norm_num) (by norm_num)

private lemma cube_rpow (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : y ^ 3 = x) :
    x ^ ((1 / 3 : ℝ)) = y := by
  have h1 : (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) := by norm_num
  have hroot : (x ^ ((1 / 3 : ℝ))) ^ 3 = x := by
    rw [h1]
    exact Real.rpow_inv_natCast_pow hx (by norm_num : 3 ≠ 0)
  have heq : (x ^ ((1 / 3 : ℝ))) ^ 3 = y ^ 3 := by rw [hroot, ← h]
  have hx' : 0 ≤ x ^ ((1 / 3 : ℝ)) := Real.rpow_nonneg hx _
  have heq_rpow : (x ^ ((1 / 3 : ℝ))) ^ (((3 : ℕ)) : ℝ) = y ^ (((3 : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact heq
  have h3' : (((3 : ℕ)) : ℝ) ≠ 0 := by norm_num
  exact (Real.rpow_left_inj hx' hy h3').mp heq_rpow

private lemma rpow_two_thirds (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : y ^ 3 = x ^ 2) :
    x ^ ((2 / 3 : ℝ)) = y := by
  have h23 : (2 / 3 : ℝ) = 2 * (1 / 3) := by ring
  have hmul : x ^ ((2 / 3 : ℝ)) = (x ^ ((2 : ℝ))) ^ ((1 / 3 : ℝ)) := by
    rw [h23, Real.rpow_mul hx]
  have hsq : x ^ ((2 : ℝ)) = x ^ 2 := by
    have h2 : (2 : ℝ) = (((2 : ℕ)) : ℝ) := by norm_num
    rw [h2, Real.rpow_natCast]
  rw [hmul, hsq]
  have hx2 : 0 ≤ x ^ 2 := by positivity
  exact cube_rpow _ _ hx2 hy h

-- Fixture, a cutoff strictly between one and `r`: the monatomic gas of the Otto fixture
-- (`Cv = 3`, `nR = 2`, `γ = 5 / 3`, `T₁ = 300`) at `r = 8` with cutoff ratio
-- `rc = 125 / 64 = (5 / 4) ^ 3` has `T₂ = 1200`, `T₃ = 9375 / 4`, `T₄ = 234375 / 256`, heat input
-- `22875 / 4`, rejected heat `472725 / 256`, net work `991275 / 256` and efficiency
-- `13217 / 19520`, below the Otto efficiency `3 / 4` at the same `r`.
example :
    ottoCompressedTemp 300 8 (5 / 3) = 1200 ∧
      dieselCutoffTemp 300 8 (5 / 3) (125 / 64) = 9375 / 4 ∧
      dieselExpandedTemp 300 8 (5 / 3) (125 / 64) = 234375 / 256 ∧
      dieselHeatIn 300 8 (5 / 3) 3 (125 / 64) = 22875 / 4 ∧
      dieselHeatOut 300 8 (5 / 3) 3 (125 / 64) = 472725 / 256 ∧
      dieselNetWork 300 8 (5 / 3) 3 2 (125 / 64) = 991275 / 256 ∧
      dieselEfficiency 8 (5 / 3) (125 / 64) = 13217 / 19520 ∧
      ottoEfficiency 8 (5 / 3) = 3 / 4 := by
  have h8_23 : (8 : ℝ) ^ ((2 / 3 : ℝ)) = 4 :=
    rpow_two_thirds _ _ (by norm_num) (by norm_num) (by norm_num)
  have h512_23 : (125 / 512 : ℝ) ^ ((2 / 3 : ℝ)) = 25 / 64 :=
    rpow_two_thirds _ _ (by norm_num) (by norm_num) (by norm_num)
  have h64_23 : (125 / 64 : ℝ) ^ ((2 / 3 : ℝ)) = 25 / 16 :=
    rpow_two_thirds _ _ (by norm_num) (by norm_num) (by norm_num)
  have h53m1 : ((5 / 3 : ℝ) - 1) = 2 / 3 := by norm_num
  have h1m53 : ((1 : ℝ) - 5 / 3) = -(2 / 3) := by norm_num
  have h53 : (5 / 3 : ℝ) = 1 + 2 / 3 := by norm_num
  have h8_53m1 : (8 : ℝ) ^ ((5 / 3 - 1 : ℝ)) = 4 := by rw [h53m1]; exact h8_23
  have h8_1m53 : (8 : ℝ) ^ ((1 - 5 / 3 : ℝ)) = 1 / 4 := by
    rw [h1m53, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), h8_23]
    norm_num
  have hrr : ((125 / 64 : ℝ) / 8) = 125 / 512 := by norm_num
  have h512_53m1 : ((125 / 64 : ℝ) / 8) ^ ((5 / 3 - 1 : ℝ)) = 25 / 64 := by
    rw [hrr, h53m1]; exact h512_23
  have h64_53 : (125 / 64 : ℝ) ^ ((5 / 3 : ℝ)) = 3125 / 1024 := by
    rw [h53, Real.rpow_add (by norm_num : (0 : ℝ) < 125 / 64), Real.rpow_one, h64_23]
    norm_num
  have hT₂ : ottoCompressedTemp 300 8 (5 / 3) = 1200 := by
    simp [ottoCompressedTemp, h8_53m1]
    norm_num
  have hT₃ : dieselCutoffTemp 300 8 (5 / 3) (125 / 64) = 9375 / 4 := by
    simp [dieselCutoffTemp, hT₂]
    norm_num
  have hT₄ : dieselExpandedTemp 300 8 (5 / 3) (125 / 64) = 234375 / 256 := by
    simp [dieselExpandedTemp, hT₃, h512_53m1]
    norm_num
  have hQin : dieselHeatIn 300 8 (5 / 3) 3 (125 / 64) = 22875 / 4 := by
    simp [dieselHeatIn, hT₃, hT₂]
    norm_num
  have hQout : dieselHeatOut 300 8 (5 / 3) 3 (125 / 64) = 472725 / 256 := by
    simp [dieselHeatOut, hT₄]
    norm_num
  have hW : dieselNetWork 300 8 (5 / 3) 3 2 (125 / 64) = 991275 / 256 := by
    simp [dieselNetWork, hT₃, hT₄, hT₂]
    norm_num
  have hEff : dieselEfficiency 8 (5 / 3) (125 / 64) = 13217 / 19520 := by
    simp [dieselEfficiency, h8_1m53, h64_53]
    norm_num
  have hOtto : ottoEfficiency 8 (5 / 3) = 3 / 4 := by
    simp [ottoEfficiency, h8_1m53]
    norm_num
  exact ⟨hT₂, hT₃, hT₄, hQin, hQout, hW, hEff, hOtto⟩

-- The monatomic Diesel loop through the general results, at `V₁ = 1`: `diesel_cycle` gives
-- positive heat input, rejected heat and net work, `dieselNetWork_div_heatIn` identifies the
-- work-to-heat ratio with `dieselEfficiency 8 (5/3) (125/64)`, and
-- `dieselEfficiency_lt_ottoEfficiency` puts it below the Otto efficiency at `r = 8`.
example :
    0 < dieselHeatIn 300 8 (5 / 3) 3 (125 / 64) ∧ 0 < dieselHeatOut 300 8 (5 / 3) 3 (125 / 64) ∧
      0 < dieselNetWork 300 8 (5 / 3) 3 2 (125 / 64) ∧
      dieselNetWork 300 8 (5 / 3) 3 2 (125 / 64) / dieselHeatIn 300 8 (5 / 3) 3 (125 / 64) =
        dieselEfficiency 8 (5 / 3) (125 / 64) ∧
      dieselEfficiency 8 (5 / 3) (125 / 64) < ottoEfficiency 8 (5 / 3) := by
  obtain ⟨-, -, -, -, -, hQin, hQout, hW, -, -⟩ := diesel_cycle (T₁ := 300) (V₁ := 1) (r := 8)
    (γ := 5 / 3) (Cv := 3) (nR := 2) (rc := 125 / 64) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hQin, hQout, hW,
    (dieselNetWork_div_heatIn (T₁ := 300) (nR := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1,
    dieselEfficiency_lt_ottoEfficiency (by norm_num) (by norm_num) (by norm_num)⟩

-- The ideal-gas law fixes the cutoff state of the same loop at `V₁ = 1`: a state at the cutoff
-- volume `125/64 * (1/8)` on the isobar of state `2` has temperature `rc * T₂`, and the first law
-- on the isobaric leg gives the heat input `γ * Cv * (T₃ - T₂)`.
example {p T₃ : ℝ} (h₂ : p * (1 / 8) = 2 * ottoCompressedTemp 300 8 (5 / 3))
    (h₃ : p * (125 / 64 * (1 / 8)) = 2 * T₃) :
    T₃ = dieselCutoffTemp 300 8 (5 / 3) (125 / 64) ∧
      3 * (T₃ - ottoCompressedTemp 300 8 (5 / 3)) + p * (125 / 64 * (1 / 8) - 1 / 8) =
        dieselHeatIn 300 8 (5 / 3) 3 (125 / 64) :=
  dieselIsobaric_eos (V₁ := 1) (by norm_num) (by norm_num) (by norm_num) h₂ h₃

-- Unit cutoff ratio on the same gas: no heat is added, the loop does no net work, and Lean's
-- value `1` of the formula at `rc = 1` is not the Otto efficiency, which is the limit as the
-- cutoff ratio decreases to one.
example :
    dieselHeatIn 300 8 (5 / 3) 3 1 = 0 ∧ dieselNetWork 300 8 (5 / 3) 3 2 1 = 0 ∧
      dieselEfficiency 8 (5 / 3) 1 = 1 ∧ dieselEfficiency 8 (5 / 3) 1 ≠ ottoEfficiency 8 (5 / 3) ∧
      Filter.Tendsto (fun rc => dieselEfficiency 8 (5 / 3) rc) (nhdsWithin 1 (Set.Ioi 1))
        (nhds (ottoEfficiency 8 (5 / 3))) :=
  diesel_unit_cutoff (by norm_num) (by norm_num)

-- Outside the cycle domain the formulas are not efficiencies of the declared cycle, which is why
-- `dieselEfficiency_lt_ottoEfficiency` assumes `1 < rc < r`: at `r = 1/2`, `rc = 2 > r` and
-- `γ = 2` both formulas are negative.
example : dieselEfficiency (1 / 2) 2 2 = -2 ∧ ottoEfficiency (1 / 2) 2 = -1 := by
  have h : ((1 : ℝ) / 2) ^ ((1 : ℝ) - 2) = 2 := by
    rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [Real.rpow_two]
    norm_num
  refine ⟨?_, ?_⟩ <;> simp only [dieselEfficiency, ottoEfficiency, h, h2] <;> norm_num

-- The Otto efficiency at `r = 8` is the limit of the Diesel efficiency as the cutoff ratio
-- decreases to one.
example : Filter.Tendsto (fun rc => dieselEfficiency 8 (5 / 3) rc) (nhdsWithin 1 (Set.Ioi 1))
    (nhds (ottoEfficiency 8 (5 / 3))) :=
  dieselEfficiency_tendsto_ottoEfficiency (by norm_num)

-- A cutoff ratio `16` above `r = 8` is not the declared cycle: the cutoff volume exceeds
-- `V₁ = 1`, so the leg back to `V₁` is a compression with negative work output.
example :
    (1 : ℝ) < 16 * (1 / 8) ∧
      dieselCutoffTemp 300 8 (5 / 3) 16 < dieselExpandedTemp 300 8 (5 / 3) 16 ∧
      3 * (dieselCutoffTemp 300 8 (5 / 3) 16 - dieselExpandedTemp 300 8 (5 / 3) 16) < 0 :=
  diesel_cutoff_above_ratio (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

-- Fixture: air-standard cycle with `R = 287` J/(kg K) and `cp = 2009/2` J/(kg K)
-- (`R / cp = 2/7`, `γ = 7/5`) at pressure ratio `rp = (3/2) ^ 7 = 2187/128`, so `a = 9/4`. From
-- `T₁ = 300` K the compressor reaches `T₂ = 675` K; with the turbine inlet at `T₃ = 1350` K the
-- turbine exit is `T₄ = 600` K. Per unit mass `Qin = 1356075/2` J/kg, `Qout = 301350` J/kg,
-- `Wnet = 753375/2` J/kg and `η = 5/9 < 7/9 = 1 - T₁ / T₃`.
example :
    braytonTempRatio (2187 / 128) 287 (2009 / 2) = 9 / 4 ∧
      braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) = 675 ∧
      braytonExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) = 600 ∧
      braytonHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) = 1356075 / 2 ∧
      braytonHeatOut 300 1350 (2187 / 128) 287 (2009 / 2) = 301350 ∧
      braytonNetWork 300 1350 (2187 / 128) 287 (2009 / 2) = 753375 / 2 ∧
      braytonEfficiency (2187 / 128) 287 (2009 / 2) = 5 / 9 ∧
      (5 / 9 : ℝ) < 1 - 300 / 1350 := by
  have hexp : (287 : ℝ) / (2009 / 2) = 2 / 7 := by norm_num
  have hrp : (2187 / 128 : ℝ) = (3 / 2) ^ 7 := by norm_num
  have h72 : ((7 : ℕ) : ℝ) * (2 / 7) = 2 := by norm_num
  have ha : braytonTempRatio (2187 / 128) 287 (2009 / 2) = 9 / 4 := by
    simp only [braytonTempRatio]
    rw [hexp, hrp, ← Real.rpow_natCast,
      ← Real.rpow_mul (show (0 : ℝ) ≤ 3 / 2 by norm_num), h72, Real.rpow_two]
    norm_num
  have hT₂ : braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) = 675 := by
    simp only [braytonCompressedTemp, ha]
    norm_num
  have hT₄ : braytonExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) = 600 := by
    simp only [braytonExpandedTemp, ha]
    norm_num
  have hQin : braytonHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) = 1356075 / 2 := by
    simp only [braytonHeatIn, hT₂]
    norm_num
  have hQout : braytonHeatOut 300 1350 (2187 / 128) 287 (2009 / 2) = 301350 := by
    simp only [braytonHeatOut, hT₄]
    norm_num
  have hW : braytonNetWork 300 1350 (2187 / 128) 287 (2009 / 2) = 753375 / 2 := by
    simp only [braytonNetWork, hT₂, hT₄]
    norm_num
  have heff : braytonEfficiency (2187 / 128) 287 (2009 / 2) = 5 / 9 := by
    simp only [braytonEfficiency, ha]
    norm_num
  have hlt : (5 / 9 : ℝ) < 1 - 300 / 1350 := by norm_num
  exact ⟨ha, hT₂, hT₄, hQin, hQout, hW, heff, hlt⟩

-- `a = (2187 / 128) ^ (287 / (2009 / 2)) = ((3 / 2) ^ 7) ^ (2 / 7) = 9 / 4`.
private lemma braytonTempRatio_air : braytonTempRatio (2187 / 128) 287 (2009 / 2) = 9 / 4 := by
  rw [braytonTempRatio, show (2187 / 128 : ℝ) = (3 / 2) ^ (7 : ℕ) by norm_num,
    show (287 : ℝ) / (2009 / 2) = 2 / 7 by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

-- The air-standard loop through the general results: `brayton_cycle` gives positive heat input
-- and net work, the work-to-heat ratio `1 - 1 / a = 5/9` and its comparison with
-- `1 - T₁ / T₃ = 7/9`.
example :
    0 < braytonHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) ∧
      0 < braytonNetWork 300 1350 (2187 / 128) 287 (2009 / 2) ∧
      braytonNetWork 300 1350 (2187 / 128) 287 (2009 / 2) /
          braytonHeatIn 300 1350 (2187 / 128) 287 (2009 / 2) = 5 / 9 ∧
      (5 / 9 : ℝ) < 1 - 300 / 1350 := by
  have hT₂ : braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) = 675 := by
    rw [braytonCompressedTemp, braytonTempRatio_air]
    norm_num
  obtain ⟨hQ, -, hW, he, hc⟩ := brayton_cycle (cp := 2009 / 2) (R := 287) (rp := 2187 / 128)
    (T₁ := 300) (T₃ := 1350) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hT₂]; norm_num)
  rw [braytonTempRatio_air] at he hc
  refine ⟨hQ, hW, ?_, ?_⟩
  · rw [he]
    norm_num
  · norm_num

-- Signs on the same loop: the compressor's engineering work output is
-- `workOut (753375 / 2) = -753375 / 2` J/kg (a work input), the turbine's is
-- `workOut (-753375) = 753375` J/kg, the heater absorbs `1356075 / 2` J/kg and the cooler
-- `-301350` J/kg. The four leg balances give the net shaft output `753375 / 2` J/kg, which is the
-- net heat.
example :
    ProcessPorts.workOut (753375 / 2) + ProcessPorts.workOut (-753375) =
        braytonNetWork 300 1350 (2187 / 128) 287 (2009 / 2) ∧
      ProcessPorts.workOut (753375 / 2) + ProcessPorts.workOut (-753375) =
        1356075 / 2 + -301350 := by
  have hT₂ : braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) = 675 := by
    rw [braytonCompressedTemp, braytonTempRatio_air]
    norm_num
  have hT₄ : braytonExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) = 600 := by
    rw [braytonExpandedTemp, braytonTempRatio_air]
    norm_num
  have h := brayton_leg_energy (cp := 2009 / 2) (R := 287) (rp := 2187 / 128) (T₁ := 300)
    (T₃ := 1350) (q₁₂ := 0) (q₂₃ := 1356075 / 2) (q₃₄ := 0) (q₄₁ := -301350)
    (w₁₂ := 753375 / 2) (w₂₃ := 0) (w₃₄ := -753375) (w₄₁ := 0)
    (by rw [hT₂]; norm_num [ProcessPorts.workOut]) (by rw [hT₂]; norm_num [ProcessPorts.workOut])
    (by rw [hT₄]; norm_num [ProcessPorts.workOut]) (by rw [hT₄]; norm_num [ProcessPorts.workOut])
    rfl rfl rfl rfl
  exact ⟨h.2.2.1, h.2.2.2⟩

-- Every ideal-gas state at the compressor exit pressure `rp p₁` (with `p₁ = 1`) on the adiabat
-- through the inlet state (`p₁ = 1`, `T₁ = 300` K, `v₁ = 287 · 300`) has the temperature `675` K.
example {T v : ℝ} (hv : 0 < v) (hgas : 2187 / 128 * 1 * v = 287 * T)
    (had : 1 * (300 * 287 : ℝ) ^ ((2009 / 2 : ℝ) / (2009 / 2 - 287)) =
      2187 / 128 * 1 * v ^ ((2009 / 2 : ℝ) / (2009 / 2 - 287))) :
    T = 675 := by
  have h := braytonCompressedTemp_eq_of_adiabat (cp := 2009 / 2) (R := 287) (rp := 2187 / 128)
    (T₁ := 300) (p₁ := 1) (v₁ := 300 * 287) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hv (by norm_num) hgas had
  rw [h, braytonCompressedTemp, braytonTempRatio_air]
  norm_num

-- Degenerate boundary: without compression (`rp = 1`) the loop does no work for any turbine inlet
-- temperature, and on the air loop the work is positive exactly when `T₃ > 675` K, so a turbine
-- inlet at `600` K gives no positive work.
example :
    braytonNetWork 300 1350 1 287 (2009 / 2) = 0 ∧
      ¬ 0 < braytonNetWork 300 600 (2187 / 128) 287 (2009 / 2) := by
  refine ⟨(brayton_zero_work (cp := 2009 / 2) (R := 287) (rp := 2187 / 128) (T₁ := 300)
    (T₃ := 1350) (by norm_num)).2, ?_⟩
  rw [braytonNetWork_pos_iff (by norm_num) (by norm_num) (by norm_num), braytonCompressedTemp,
    braytonTempRatio_air]
  norm_num

-- The extreme temperatures of the air loop: `braytonEfficiency_lt_carnot` orders the states,
-- `T₁ = 300 K < T₂ = 675 K < T₃ = 1350 K` and `T₁ < T₄ = 600 K < T₃`, and `η = 5/9` is below
-- the Carnot efficiency `1 - T₁ / T₃ = 7/9` between the coldest and the hottest state.
example :
    (300 : ℝ) < braytonCompressedTemp 300 (2187 / 128) 287 (2009 / 2) ∧
      (300 : ℝ) < braytonExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) ∧
      braytonExpandedTemp 1350 (2187 / 128) 287 (2009 / 2) < 1350 ∧
      braytonEfficiency (2187 / 128) 287 (2009 / 2) < 1 - 300 / 1350 :=
  braytonEfficiency_lt_carnot (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [braytonCompressedTemp, braytonTempRatio_air]; norm_num)

-- `a = (128 / 2187) ^ (287 / (2009 / 2)) = ((2 / 3) ^ 7) ^ (2 / 7) = 4 / 9`.
private lemma braytonTempRatio_expansion :
    braytonTempRatio (128 / 2187) 287 (2009 / 2) = 4 / 9 := by
  rw [braytonTempRatio, show (128 / 2187 : ℝ) = (2 / 3) ^ (7 : ℕ) by norm_num,
    show (287 : ℝ) / (2009 / 2) = 2 / 7 by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

-- Why the comparison requires `rp > 1`: at `rp = (2/3) ^ 7 = 128/2187 < 1` the same gas has
-- `a = 4/9 < 1`, and `T₃ = 200 K` above `T₂ = 400/3 K` is colder than `T₁ = 300 K`. The inequality
-- `1 - 1 / a < 1 - T₁ / T₃` still holds (`-5/4 < -1/2`), but `1 - T₁ / T₃` is negative, not a
-- Carnot efficiency between a hot and a cold reservoir.
example :
    braytonCompressedTemp 300 (128 / 2187) 287 (2009 / 2) < 200 ∧ (200 : ℝ) < 300 ∧
      1 - (300 : ℝ) / 200 < 0 ∧
      braytonEfficiency (128 / 2187) 287 (2009 / 2) < 1 - 300 / 200 := by
  rw [braytonCompressedTemp, braytonEfficiency, braytonTempRatio_expansion]
  norm_num

end PhyslibExtTest.Thermodynamics.GasCycles
