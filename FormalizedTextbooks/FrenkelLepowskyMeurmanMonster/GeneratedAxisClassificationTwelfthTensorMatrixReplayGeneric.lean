/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSpatialTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Complete integer column replay gives the actual tensor action of any certified local fiber. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every complete column certificate and actual physical numerator
determine the full tensor action. -/
theorem generatedTwelfth_tensor_matrix_column_replay (f : localFiberSubgroup)
    (N : Matrix (Fin 24) (Fin 24) ℤ) (d : ℕ) (hd : d ≠ 0)
    (hphysical : (d : ℝ) • leechIsomMatrix f.val.2 = N.map (Int.castRingHom ℝ))
    (I O : Fin 4096 → Fin 24 → ℤ)
    (hspin : ∀ j : Fin 24,
      f.val.1.val (nortonUIntegerEmbed (fun n => ∑ k : Fin 24, N j k * I n k)) =
        nortonUIntegerEmbed (fun n => O n j)) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation f (fun u j => (I (nortonUIntegerLabel u) j : ℝ)) t i =
      (O (nortonUIntegerLabel t) i : ℝ) / d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hmat (j : Fin 24) : f.val.2.val (Pi.single j 1) i = (N i j : ℝ) / d := by
    have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i j) hphysical
    change (d : ℝ) * f.val.2.val (Pi.single j 1) i = (N i j : ℝ) at h
    apply (eq_div_iff hdR).mpr
    simpa only [mul_comm] using h
  have hcol : nortonUIntegerEmbed (fun n => ∑ k : Fin 24, N i k * I n k) =
      ∑ k : Fin 24, (N i k : ℝ) • nortonUIntegerEmbed (fun n => I n k) := by
    ext u
    simp only [nortonUIntegerEmbed, Int.cast_sum, Int.cast_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hs := congrFun (hspin i) t
  rw [hcol, map_sum] at hs
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed] at hs
  rw [generatedFourth_local_tensor_columns]
  simp only [hmat, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  exact congrArg (fun z : ℝ => z / d) hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
