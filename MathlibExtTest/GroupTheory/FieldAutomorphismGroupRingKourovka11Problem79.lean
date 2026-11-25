/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GroupTheory.FieldAutomorphismGroupRingKourovka11Problem79
import Mathlib.Algebra.CharP.Basic

open MathlibExt.GroupTheory.FieldAutomorphismGroupRingKourovka11Problem79Wanted

-- The element 1 - σ has coefficient sum zero. Its powers are quotients x / σ(x),
-- so evaluating only on fixed elements would produce just 1.
example (p : ℕ) (F : Type) [Field F] [CharP F p] [Infinite F] (hp : p.Prime)
    (G : Subgroup (RingAut F)) (hG : (G : Set (RingAut F)).Finite)
    (σ : G) (hσ : σ ≠ 1) (K : Subfield F)
    (hK : ∀ x : F, x ≠ 0 → x / (σ : RingAut F) x ∈ K) :
    {y : F | y ∈ K ∧ ∀ g ∈ G, g y = y}.Infinite := by
  classical
  let ξ : G →₀ ℤ := Finsupp.single 1 1 + Finsupp.single σ (-1)
  apply subfieldContainsInfinitelyManyInvariants_holds p F hp inferInstance G hG ξ _ K
  · intro x hx
    have hne (g : G) : (g : RingAut F) x ≠ 0 := (g : RingAut F).map_ne_zero_iff.mpr hx
    rw [show ξ = Finsupp.single 1 1 + Finsupp.single σ (-1) from rfl,
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun g => zpow_add₀ (hne g)),
      Finsupp.prod_single_index (zpow_zero _), Finsupp.prod_single_index (zpow_zero _)]
    simpa [div_eq_mul_inv] using hK x hx
  · intro h
    have h1 : (p : ℤ) ∣ 1 := by simpa [ξ, hσ] using h (1 : G)
    exact hp.not_dvd_one (by exact_mod_cast h1)
