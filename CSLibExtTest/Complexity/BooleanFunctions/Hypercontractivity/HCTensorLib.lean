/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.HCTensorLib

/-!
# Tests for the tensorization of the two-point hypercontractive inequality

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.HCTensorLib`:

* `PBiasedHCLib (1/2)` is proved (`htl_lib_half`); at `ρ = 1, u = 1, v = -1` it is an equality
  (both sides equal `1`);
* the theorems conditional on `PBiasedHCLib p` at a single `p` (`htl_hypercontractivity_fin`,
  `htl_lowDegreeWeight`, `htl_perCoord_hc`, `htl_summed_hc`, `htl_capped_hc`, `htl_master_open`)
  instantiated at `p = 1/2` with `H := htl_lib_half`, `ρ = 1/2` or `ρ = 1`, on `Fin 2`, `Bool`
  and the dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`;
* `htl_kkl_logGain_half` at the dictator;
* `htl_lib_rho_zero` at `p = 3/4`.

Not tested non-degenerately: the window-conditional theorems `htl_kkl_logGain`,
`htl_rhoOptimise_of_lib`, `htl_kklHC_of_lib`, `htl_PBiasedHC_of_lib`, `htl_sharpThreshold` and
`htl_openResidue_of_lib` assume `∀ p ∈ (1/2, q), PBiasedHCLib p`. This fails for every
`q > 9/10` (`dtpc_pbiasedHCLib_nine_tenths_false`, tested in `DecoupledTwoPointRefutation`) and is
open for `q ∈ (1/2, 9/10]`. The tests record the degenerate window `q = 1/2`, where the
hypothesis holds because `(1/2, 1/2)` is empty; `htl_kkl_logGain` cannot be applied there since
it also needs a point `p ∈ (1/2, q)`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.HCTensorLib

open StatMech StatMech.OSSS StatMech.Probability

example : PBiasedHCLib (1 / 2) := htl_lib_half

/-- `PBiasedHCLib (1/2)` at `ρ = 1, u = 1, v = -1` is an equality: both sides equal `1`. -/
example :
    ((1 - (1 / 2 : ℝ)) * 1 + (1 / 2) * (-1)) ^ 2
        + (1 : ℝ) ^ 2 * ((1 / 2) * (1 - 1 / 2)) * (1 - (-1)) ^ 2 = 1
      ∧ ((1 - (1 / 2 : ℝ)) * |(1 : ℝ)| ^ (1 + (1 : ℝ) ^ 2)
          + (1 / 2) * |(-1 : ℝ)| ^ (1 + (1 : ℝ) ^ 2)) ^ (2 / (1 + (1 : ℝ) ^ 2)) = 1 := by
  norm_num

example :
    ((1 - (1 / 2 : ℝ)) * 1 + (1 / 2) * (-1)) ^ 2
        + (1 : ℝ) ^ 2 * ((1 / 2) * (1 - 1 / 2)) * (1 - (-1)) ^ 2
      ≤ ((1 - (1 / 2 : ℝ)) * |(1 : ℝ)| ^ (1 + (1 : ℝ) ^ 2)
          + (1 / 2) * |(-1 : ℝ)| ^ (1 + (1 : ℝ) ^ 2)) ^ (2 / (1 + (1 : ℝ) ^ 2)) :=
  htl_lib_half 1 zero_le_one le_rfl 1 (-1)

example (f : (Fin 2 → Bool) → ℝ) :
    ptn_qnorm (1 / 2) 2 (ptn_kop (1 / 2) (1 / 2) f) ≤ ptn_qnorm (1 / 2) (5 / 4) f :=
  htl_hypercontractivity_fin (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) htl_lib_half 2 f

example (f : ConfigSpace Bool → ℝ) :
    (∑ S : Finset Bool, (((1 : ℝ) / 2) ^ S.card) ^ 2 * (ptn_coeff (1 / 2) f S) ^ 2)
      ≤ (ptn_qnorm (1 / 2) (5 / 4) f) ^ 2 :=
  htl_lowDegreeWeight (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    htl_lib_half f

/-- The dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`. -/
def dict1 (ω : ConfigSpace (Fin 1)) : Bool := ω 0

example :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 1) => 0 ∈ S),
        ((1 : ℝ) ^ (S.erase 0).card) ^ 2
          * (ptn_coeff (1 / 2) (fun ω => if dict1 ω then (1 : ℝ) else 0) S / ptn_sigma (1 / 2)) ^ 2)
      ≤ (infl (bernoulliWeight (1 / 2)) (fun ω => if dict1 ω then (1 : ℝ) else 0) 0)
          ^ (2 / (2 : ℝ)) :=
  htl_perCoord_hc (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) htl_lib_half
    dict1 0

example :
    (1 / (ptn_sigma (1 / 2)) ^ 2) * ∑ S : Finset (Fin 1), (S.card : ℝ)
        * (((1 : ℝ) ^ (S.card - 1)) ^ 2
          * (ptn_coeff (1 / 2) (fun ω => if dict1 ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ∑ e : Fin 1, (infl (bernoulliWeight (1 / 2))
          (fun ω => if dict1 ω then (1 : ℝ) else 0) e) ^ (2 / (2 : ℝ)) :=
  htl_summed_hc (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) htl_lib_half dict1

example :
    (1 / (ptn_sigma (1 / 2)) ^ 2) * ∑ S : Finset (Fin 1), (S.card : ℝ)
        * (((1 : ℝ) ^ (S.card - 1)) ^ 2
          * (ptn_coeff (1 / 2) (fun ω => if dict1 ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (bernoulliWeight (1 / 2)) (fun ω => if dict1 ω then (1 : ℝ) else 0))
          ^ (2 / (2 : ℝ) - 1)
        * totalInfl (bernoulliWeight (1 / 2)) (fun ω => if dict1 ω then (1 : ℝ) else 0) :=
  htl_capped_hc (by norm_num) (by norm_num) zero_le_one le_rfl (by norm_num) le_rfl htl_lib_half
    dict1

example :
    (∑ S : Finset (Fin 1), 4 * (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
        * (ptn_coeff (1 / 2) (fun ω => if dict1 ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (bernoulliWeight (1 / 2)) (fun ω => if dict1 ω then (1 : ℝ) else 0))
          ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
        * totalInfl (bernoulliWeight (1 / 2)) (fun ω => if dict1 ω then (1 : ℝ) else 0) :=
  htl_master_open (by norm_num) (by norm_num) htl_lib_half dict1 (by norm_num) (by norm_num)

example :
    2 * (expect (bernoulliWeight (1 / 2 : ℝ)) (fun ω => if dict1 ω then (1 : ℝ) else 0)
          * (1 - expect (bernoulliWeight (1 / 2 : ℝ)) (fun ω => if dict1 ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if dict1 ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight (1 / 2 : ℝ)) (fun ω => if dict1 ω then (1 : ℝ) else 0) :=
  htl_kkl_logGain_half dict1

example (u v : ℝ) :
    ((1 - (3 / 4 : ℝ)) * u + (3 / 4) * v) ^ 2
        + (0 : ℝ) ^ 2 * ((3 / 4) * (1 - 3 / 4)) * (u - v) ^ 2
      ≤ ((1 - (3 / 4 : ℝ)) * |u| ^ (1 + (0 : ℝ) ^ 2) + (3 / 4) * |v| ^ (1 + (0 : ℝ) ^ 2))
          ^ (2 / (1 + (0 : ℝ) ^ 2)) :=
  htl_lib_rho_zero (by norm_num) (by norm_num) u v

/-! ## The degenerate window `q = 1/2` -/

/-- The window hypothesis for `q ≤ 1/2` holds because `(1/2, q)` is empty. -/
lemma lib_window_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) :
    ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ptn_RhoOptimise (1 / 2) := htl_rhoOptimise_of_lib (lib_window_of_le_half le_rfl)

example : kpb_PBiasedHC (1 / 2) :=
  htl_PBiasedHC_of_lib (by norm_num) (lib_window_of_le_half le_rfl)

/-- The dictator event `{ω | ω 0}` on `{0, 1}^{Fin 1}`. -/
def dictEvent1 : Set (ConfigSpace (Fin 1)) := {ω | ω 0 = true}

/-- Membership in `dictEvent1` is decidable. -/
instance : DecidablePred (· ∈ dictEvent1) := fun ω => inferInstanceAs (Decidable (ω 0 = true))

lemma dictEvent1_isIncreasing : IsIncreasing dictEvent1 := by
  intro ω ω' hle hω
  simp only [dictEvent1, Set.mem_ofPred_eq] at hω ⊢
  have := hle 0
  rw [hω] at this
  revert this; cases ω' 0 <;> simp

/-- A sum over the configurations of `{0, 1}^{Fin 1}`. -/
lemma sum_fin_one (f : ConfigSpace (Fin 1) → ℝ) :
    ∑ ω, f ω = f (fun _ => true) + f (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  rfl

lemma prob_dictEvent1 : StatMech.prob (1 / 2) dictEvent1 = 1 / 2 := by
  rw [StatMech.TwoDim.kklw_prob_eq_expect]
  simp [expect, weight, sum_fin_one, dictEvent1, bernoulliWeight, Set.indicator_apply]

example : 1 / 2 + (2 * 1 * 1) * ((1 / 2 : ℝ) - 1 / 2) ≤ StatMech.prob (1 / 2) dictEvent1 :=
  htl_sharpThreshold (by norm_num) (lib_window_of_le_half le_rfl) dictEvent1
    dictEvent1_isIncreasing le_rfl zero_le_one zero_le_one prob_dictEvent1 (by simp) (by simp)

end StatMechTest.BooleanFunctions.HCTensorLib
