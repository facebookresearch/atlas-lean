/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PathSignature.FactorialEstimate

open MathlibExt.Analysis.PathSignature

namespace MathlibExtTest.Analysis.PathSignature.FactorialEstimate

-- For 1 < p < 2 only level one is prescribed. A vanishing first level forces all
-- higher levels to vanish, even if their finite variation was witnessed by other controls.
example (Y : ℝ → ℝ → List (Fin 2) → ℝ)
    (hfirst : ∀ s t, s ≤ t → levelNorm (Y s t) 1 = 0)
    (hY : ∀ m, IsMultiplicativeFunctional m Y Set.univ ∧
      HasFinitePVariation (3 / 2) m Y Set.univ)
    {n : ℕ} (hn : 0 < n) {s t : ℝ} (hst : s ≤ t) : levelNorm (Y s t) n = 0 := by
  obtain ⟨β, _, h⟩ := ExtensionTheoremWanted.isControlledBy_extension (p := 3 / 2) (by norm_num)
  have hω : IsControl (fun _ _ => 0) Set.univ :=
    ⟨continuousOn_const, fun _ _ => rfl, fun _ _ _ _ _ => le_rfl, by simp⟩
  have hctl : IsControlledBy (3 / 2) β ⌊(3 / 2 : ℝ)⌋₊ Y (fun _ _ => 0) Set.univ := by
    intro i hi hin a _ b _ hab
    have hfloor : ⌊(3 / 2 : ℝ)⌋₊ = 1 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
    rw [hfloor] at hin
    obtain rfl : i = 1 := by omega
    rw [hfirst a b hab, Real.zero_rpow (by norm_num), zero_div]
  have hall := h (Fin 2) Set.ordConnected_univ _ hω β le_rfl Y Y (hY _).1 hctl
    (fun _ _ _ _ _ _ _ => rfl) hY
  have hle := hall n n hn le_rfl s trivial t trivial hst
  rw [Real.zero_rpow (by positivity), zero_div] at hle
  exact le_antisymm hle (Finset.sum_nonneg fun _ _ => abs_nonneg _)

end MathlibExtTest.Analysis.PathSignature.FactorialEstimate
