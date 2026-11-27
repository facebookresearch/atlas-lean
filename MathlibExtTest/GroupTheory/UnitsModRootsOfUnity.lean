/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.UnitsModRootsOfUnity
import Mathlib.Data.ZMod.Defs

-- The page's statement for an arbitrary field.
example (K : Type*) [Field K] :
    IsMulTorsionFree (Kˣ ⧸ CommGroup.torsion Kˣ) ∧
      ∀ (G : Type*) [Group G] [Finite G] (f : G →* Kˣ ⧸ CommGroup.torsion Kˣ), f = 1 :=
  units_quotient_torsion_isMulTorsionFree_and_eq_one K

-- A concrete instance: every homomorphism from the cyclic group of order 3 to
-- `ℚˣ / μ_∞(ℚ)` is trivial.
example (f : Multiplicative (ZMod 3) →* ℚˣ ⧸ CommGroup.torsion ℚˣ) : f = 1 :=
  MonoidHom.eq_one_of_finite_to_units_quotient_torsion f

-- `-1` is a root of unity of `ℚ`, so it lies in `μ_∞(ℚ)`.
example : (-1 : ℚˣ) ∈ CommGroup.torsion ℚˣ :=
  (mem_torsion_units_iff_exists_mem_rootsOfUnity (-1 : ℚˣ)).mpr
    ⟨2, by norm_num, by simp [mem_rootsOfUnity]⟩
