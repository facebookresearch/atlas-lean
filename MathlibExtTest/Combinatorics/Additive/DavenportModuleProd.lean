/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.DavenportModuleProd
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Nat

namespace MetaMathlibExt.davenport_prod_ge

private abbrev lengths (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] : Set ℕ :=
  {k : ℕ | 0 < k ∧ ∀ x : Fin k → M, ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → ZMod 2, (∀ i ∈ I, a i ∈ ({1} : Set (ZMod 2))) ∧ ∑ i ∈ I, a i • x i = 0}

private theorem factor_two : IsLeast (lengths (ZMod 2)) 2 := by
  refine ⟨by decide, ?_⟩
  intro k hk
  by_contra! hlt
  have hkpos := hk.1
  have : k = 1 := by omega
  subst k
  exact (by decide : 1 ∉ lengths (ZMod 2)) hk

/-- The product bound is attained on the two-dimensional vector space over `ZMod 2`. -/
example : IsLeast (lengths (ZMod 2 × ZMod 2)) 3 := by
  have hthree : 3 ∈ lengths (ZMod 2 × ZMod 2) := by decide
  classical
  have hne : (lengths (ZMod 2 × ZMod 2)).Nonempty := ⟨3, hthree⟩
  let d := Nat.find hne
  have hd : IsLeast (lengths (ZMod 2 × ZMod 2)) d := hne.isLeast_natFind
  have hge := davenport_prod_ge {1} factor_two factor_two hd
  have hle := hd.2 hthree
  exact (show d = 3 by omega) ▸ hd

/-- A zero-dimensional first factor contributes an empty zero-sum-free block. -/
example {d : ℕ} (h : IsLeast (lengths ((Fin 0 → ZMod 2) × ZMod 2)) d) : 2 ≤ d := by
  have htrivial : IsLeast (lengths (Fin 0 → ZMod 2)) 1 := ⟨by decide, fun _ hk => hk.1⟩
  exact davenport_prod_ge {1} htrivial factor_two h

end MetaMathlibExt.davenport_prod_ge

namespace MetaMathlibExt.davenport_prod_ring_ge

private abbrev productLengths : Set ℕ :=
  {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod 2 × ZMod 3, ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → ZMod 2 × ZMod 3, (∀ i ∈ I, a i ∈ ({1} : Set (ZMod 2)) ×ˢ {0}) ∧
      ∑ i ∈ I, ((a i).1 • (x i).1, (a i).2 • (x i).2) = 0}

/-- With weights `{1} ×ˢ {0}`, the second factor has constant one and the bound is sharp. -/
example : IsLeast productLengths 2 := by
  have hB : IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod 3, ∃ I : Finset (Fin k), I.Nonempty ∧
      ∃ a : Fin k → ZMod 3, (∀ i ∈ I, a i ∈ ({0} : Set (ZMod 3))) ∧ ∑ i ∈ I, a i • x i = 0} 1 :=
    ⟨by decide, fun _ hk => hk.1⟩
  have htwo : 2 ∈ productLengths := by decide
  classical
  have hne : productLengths.Nonempty := ⟨2, htwo⟩
  have hd := hne.isLeast_natFind
  have hge := davenport_prod_ring_ge {1} {0} davenport_prod_ge.factor_two hB hd
  have hle := hd.2 htwo
  exact (show Nat.find hne = 2 by omega) ▸ hd

end MetaMathlibExt.davenport_prod_ring_ge
