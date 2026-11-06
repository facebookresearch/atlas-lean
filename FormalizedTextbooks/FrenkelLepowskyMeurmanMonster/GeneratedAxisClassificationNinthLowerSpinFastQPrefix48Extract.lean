/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQPrefix03Data

/-! One exact full-prefix extraction avoids repeating the original long source-array lookup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every original25bit full-Q label in source prefix48, including all actual central bits. -/
def generatedNinthLowerSpinFastQPrefix48Array : Array ℕ := #[
  29525621, 31861946, 1988465, 8770374, 2768226, 33091690, 721408, 15887092,
  19087151, 23694885, 19056832, 22124544, 19730526, 23624837, 8085185, 19451013,
  5940443, 19607661, 17636534, 1507379, 21540511, 20011102, 19537078, 15262045
]

set_option maxHeartbeats 8000000 in
-- Normalize one original full-prefix slice through list drop and take exactly once.
/-- Extraction is precisely the original full source data, checked by the ordinary kernel. -/
theorem generatedNinth_lower_spin_fast_q_prefix48_extract :
    generatedNinthLowerSpinSourceQReplayPrefixWords00.extract 1152 1176 =
      generatedNinthLowerSpinFastQPrefix48Array := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract]
  rfl

private theorem getD_extract_of_bounds {α : Type} (xs : Array α)
    (start stop j : ℕ) (fallback : α) (hj : j < min stop xs.size - start) :
    (xs.extract start stop).getD j fallback = xs.getD (start + j) fallback := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, hj, ite_true]

/-- The exact slice certificate identifies the complete original prefix function. -/
theorem generatedNinth_lower_spin_fast_q_prefix48_extract_function :
    generatedNinthLowerSpinSourceQReplayWord 0 48 = generatedNinthLowerSpinFastQPrefix03 0 := by
  have hsize : generatedNinthLowerSpinSourceQReplayPrefixWords00.size = 4200 := rfl
  funext j
  change generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1152 + j.val) 0 =
    generatedNinthLowerSpinFastQPrefix03 0 j
  have hj : j.val < min 1176 generatedNinthLowerSpinSourceQReplayPrefixWords00.size - 1152 := by
    rw [hsize]
    have h := j.isLt
    omega
  calc
    generatedNinthLowerSpinSourceQReplayPrefixWords00.getD (1152 + j.val) 0 =
        generatedNinthLowerSpinFastQPrefix48Array.getD j.val 0 := by
      rw [← getD_extract_of_bounds _ 1152 1176 j.val 0 hj,
        generatedNinth_lower_spin_fast_q_prefix48_extract]
    _ = generatedNinthLowerSpinFastQPrefix03 0 j := by
      fin_cases j <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
