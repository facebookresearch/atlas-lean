/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.RamificationBounds

namespace MetaMathlibExt

@[expose] public section

/-- Over `ℤ` itself, the ramification index, inertia degree, and number of
primes above a maximal ideal are all `1`. -/
example (p : Ideal ℤ) [p.IsMaximal] (q : Ideal ℤ) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx ℤ = 1 ∧ q.inertiaDeg ℤ = 1 ∧ (p.primesOver ℤ).ncard = 1 := by
  have hfin : Module.finrank ℤ ℤ = 1 := by simp
  have h := Ideal.ramification_inertia_card_mem_Icc p q
  rw [hfin] at h
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp h.1
  obtain ⟨h3, h4⟩ := Set.mem_Icc.mp h.2.1
  obtain ⟨h5, h6⟩ := Set.mem_Icc.mp h.2.2
  exact ⟨Nat.le_antisymm h2 h1, Nat.le_antisymm h4 h3, Nat.le_antisymm h6 h5⟩

/-- The individual `e`-bound on `ℤ` over itself. -/
example (p : Ideal ℤ) [p.IsMaximal] (q : Ideal ℤ) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx ℤ ∈ Set.Icc 1 1 := by
  have hfin : Module.finrank ℤ ℤ = 1 := by simp
  have h := Ideal.ramificationIdx_mem_Icc p q
  rwa [hfin] at h

/-- The fraction-field form on `ℤ` over itself, with fraction fields `ℚ`. -/
example (p : Ideal ℤ) [p.IsMaximal] (q : Ideal ℤ) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx ℤ = 1 ∧ q.inertiaDeg ℤ = 1 ∧ (p.primesOver ℤ).ncard = 1 := by
  have hfin : Module.finrank ℚ ℚ = 1 := by simp
  have h := Ideal.ramification_inertia_card_mem_Icc_of_isFractionRing (R := ℤ) (S := ℤ)
    ℚ ℚ p q
  rw [hfin] at h
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp h.1
  obtain ⟨h3, h4⟩ := Set.mem_Icc.mp h.2.1
  obtain ⟨h5, h6⟩ := Set.mem_Icc.mp h.2.2
  exact ⟨Nat.le_antisymm h2 h1, Nat.le_antisymm h4 h3, Nat.le_antisymm h6 h5⟩

/-- The zero maximal ideal over `ℚ` satisfies all three module-rank bounds. -/
example : (⊥ : Ideal ℚ).ramificationIdx ℚ ∈ Set.Icc 1 1 ∧
    (⊥ : Ideal ℚ).inertiaDeg ℚ ∈ Set.Icc 1 1 ∧
    ((⊥ : Ideal ℚ).primesOver ℚ).ncard ∈ Set.Icc 1 1 := by
  simpa using Ideal.ramification_inertia_card_mem_Icc
    (R := ℚ) (S := ℚ) (⊥ : Ideal ℚ) (⊥ : Ideal ℚ)

/-- The fraction-field package also covers `ℚ` over itself at the zero prime. -/
example : (⊥ : Ideal ℚ).ramificationIdx ℚ ∈ Set.Icc 1 1 ∧
    (⊥ : Ideal ℚ).inertiaDeg ℚ ∈ Set.Icc 1 1 ∧
    ((⊥ : Ideal ℚ).primesOver ℚ).ncard ∈ Set.Icc 1 1 := by
  simpa using Ideal.ramification_inertia_card_mem_Icc_of_isFractionRing
    (R := ℚ) (S := ℚ) ℚ ℚ (⊥ : Ideal ℚ) (⊥ : Ideal ℚ)

end

end MetaMathlibExt
