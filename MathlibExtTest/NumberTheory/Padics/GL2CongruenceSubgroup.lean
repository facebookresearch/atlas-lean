/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.GL2CongruenceSubgroup

@[expose] public section

/-- Source-shaped consumer: the original binders, in the original form. -/
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCompact ((Padic.gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) :=
  Padic.isCompact_coe_gl2CongruenceSubgroup p n

/-- Boundary: at level zero the congruence subgroup is the whole integral
subgroup, so compactness there is compactness of `GL(2, ℤ_[p])` itself. -/
example (p : ℕ) [Fact p.Prime] :
    Padic.gl2CongruenceSubgroup p 0 = Padic.integralSubgroup ℤ_[p] ℚ_[p] :=
  Padic.gl2CongruenceSubgroup_zero_eq_integralSubgroup p

/-- The congruence subgroups decrease with the level. -/
example (p : ℕ) [Fact p.Prime] {m n : ℕ} (h : m ≤ n) :
    Padic.gl2CongruenceSubgroup p n ≤ Padic.gl2CongruenceSubgroup p m :=
  Padic.gl2CongruenceSubgroup_antitone p h
