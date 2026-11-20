/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.OSSS.SharpnessUncond

open scoped BigOperators
open Real Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS.PottsSharpness

open StatMech.OSSS
open StatMech.OSSS.SharpnessFK






























theorem potts_subcritical_decay
    (q : ℝ) (hq : 2 ≤ q)
    (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate)
    (θ θ' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θ (θ' x) x)
    (hFKineq : ∀ x ∈ Icc a b, rate * θ x ≤ θ' x)
    (hθa : 0 ≤ θ a) (hθb : θ b ≤ 1)
    (pottsCorr : ℝ) (hES : pottsCorr = (q - 1) / q * θ a) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-(rate * (b - a)))
      ∧ Real.exp (-(rate * (b - a))) < 1 := by
  
  obtain ⟨hθa_nonneg, hθa_decay, hexp_lt_one⟩ :=
    osss_subcritical_decay_disch a b rate hab hrate θ θ' hd hFKineq hθa hθb
  
  obtain ⟨hpc_nonneg, hpc_decay⟩ :=
    potts_decay_of_fk q hq (rate * (b - a)) pottsCorr (θ a) hES hθa_nonneg hθa_decay
  exact ⟨hpc_nonneg, hpc_decay, hexp_lt_one⟩













theorem potts_subcritical_decay_box
    (q : ℝ) (hq : 2 ≤ q)
    (a b c : ℝ) (n : ℕ) (hab : a < b) (hc : 0 < c) (hn : 1 ≤ n)
    (θ θ' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt θ (θ' x) x)
    (hFKineq : ∀ x ∈ Icc a b, (c * n) * θ x ≤ θ' x)
    (hθa : 0 ≤ θ a) (hθb : θ b ≤ 1)
    (pottsCorr : ℝ) (hES : pottsCorr = (q - 1) / q * θ a) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-(c * n * (b - a))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hrate : 0 < c * (n : ℝ) := mul_pos hc hn0
  obtain ⟨h0, hle, _⟩ :=
    potts_subcritical_decay q hq a b (c * n) hab hrate θ θ' hd hFKineq hθa hθb
      pottsCorr hES
  exact ⟨h0, hle⟩

















theorem potts_corr_le_of_fk_decay
    (q : ℝ) (hq : 2 ≤ q) (c pottsCorr fkCross : ℝ)
    (hES : pottsCorr = (q - 1) / q * fkCross)
    (hfk_nonneg : 0 ≤ fkCross) (hfk_decay : fkCross ≤ Real.exp (-c)) :
    0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) :=
  potts_decay_of_fk q hq c pottsCorr fkCross hES hfk_nonneg hfk_decay

end OSSS.PottsSharpness
end StatMech
