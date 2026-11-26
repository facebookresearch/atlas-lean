/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.SlaterOrderEighteenThetaRamanujanThetaEtaQuotients
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.NonicProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanOneTwo
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProductDifference

/-!
# Tests for Ramanujan's eta-quotients

Each of the seven identities is specialized to the nonreal point `Complex.I / 2`
in the open unit disk.
-/

namespace MathlibExtTest.Combinatorics.Enumerative.Partition
namespace SlaterOrderEighteenThetaRamanujanThetaEtaQuotients

open MetaMathlibExt MetaMathlibExt.QPochhammer

local notation "q" => (Complex.I / 2)
local notation "f₁" => qPochhammerInfRaw q q
local notation "f₂" => qPochhammerInfRaw (q ^ 2) (q ^ 2)
local notation "f₄" => qPochhammerInfRaw (q ^ 4) (q ^ 4)

private lemma norm_half_I : ‖q‖ < 1 := by
  norm_num [norm_div]

example : ramanujanThetaRaw q q * (f₁ ^ 2 * f₄ ^ 2) = f₂ ^ 5 :=
  (ramanujanTheta_eta_quotients norm_half_I).1

example : ramanujanThetaRaw q (q ^ 3) * f₁ = f₂ ^ 2 :=
  (ramanujanTheta_eta_quotients norm_half_I).2.1

example : ramanujanThetaRaw (-q) (-q) * f₂ = f₁ ^ 2 :=
  (ramanujanTheta_eta_quotients norm_half_I).2.2.1

example : ramanujanThetaRaw (-q) (-q ^ 3) * f₂ = f₁ * f₄ :=
  (ramanujanTheta_eta_quotients norm_half_I).2.2.2.1

example : ramanujanThetaRaw q (-q ^ 2) * (f₁ * f₄) = f₂ ^ 3 :=
  (ramanujanTheta_eta_quotients norm_half_I).2.2.2.2.1

example : qPochhammerInfRaw (-q) (q ^ 2) * (f₁ * f₄) = f₂ ^ 2 :=
  (ramanujanTheta_eta_quotients norm_half_I).2.2.2.2.2.1

example : qPochhammerInfRaw q (q ^ 2) * f₂ = f₁ :=
  (ramanujanTheta_eta_quotients norm_half_I).2.2.2.2.2.2

end SlaterOrderEighteenThetaRamanujanThetaEtaQuotients
end MathlibExtTest.Combinatorics.Enumerative.Partition
