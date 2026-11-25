/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPsiFChi

open MetaMathlibExt QPochhammer

-- At the center of the disk the theta sum has just its constant term.
example : ramanujanThetaRaw 0 0 = 1 := by
  simpa [qPochhammerInfRaw] using (ramanujan_psi_f_chi_eq_qPochhammer 0 (by simp)).1

-- Changing the sign of the nome exchanges the two odd-power products.
example {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfRaw (-q) (q ^ 2) =
      qPochhammerInfRaw (-q) (-q) / qPochhammerInfRaw (q ^ 2) (q ^ 2) := by
  simpa only [neg_sq] using
    (ramanujan_psi_f_chi_eq_qPochhammer (-q) (by simpa using hq)).2.2.2

#print axioms MetaMathlibExt.ramanujan_psi_f_chi_eq_qPochhammer
