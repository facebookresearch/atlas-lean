/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspFormIntegralLattice

@[expose] public section

open UpperHalfPlane

/-- exactSource consumer: the original binders apply verbatim. -/
example (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.intLattice N k).FG :=
  CuspForm.intLattice_fg N k

/-- The zero cusp form lies in the integral lattice. -/
example (N : ℕ) (k : ℤ) :
    (0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) ∈ CuspForm.intLattice N k :=
  (CuspForm.mem_intLattice_iff 0).mpr fun n ↦
    ⟨0, by simp [UpperHalfPlane.qExpansion_zero]⟩

/-- Boundary: integrality of the coefficients cannot be dropped in the
characterisation. The coefficient at `n` of a form in the lattice is
an integer, so a coefficient value of `1 / 2` is excluded. -/
example (N : ℕ) (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ)
    (h : (qExpansion 1 (f : ℍ → ℂ)).coeff n = (2 : ℂ)⁻¹) :
    f ∉ CuspForm.intLattice N k := by
  intro hf
  obtain ⟨m, hm⟩ := (CuspForm.mem_intLattice_iff f).mp hf n
  rw [h] at hm
  have hcast : ((2 * m : ℤ) : ℂ) = 1 := by
    push_cast
    rw [← hm]
    simp
  have hodd : 2 * m = 1 := by exact_mod_cast hcast
  omega

/-- exactSource consumer: the original binders apply verbatim. -/
example (N : ℕ) (k : ℤ) :
    CuspForm.HasIntegralStructure N k ↔
      Submodule.span ℂ
        ((CuspForm.intLattice N k :
          Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
          Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) = ⊤ :=
  CuspForm.hasIntegralStructure_iff N k

/-- The integral lattice is contained in its complex span, so under an
integral structure every cusp form lies in that span. -/
example (N : ℕ) (k : ℤ) (h : CuspForm.HasIntegralStructure N k)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    f ∈ Submodule.span ℂ
      ((CuspForm.intLattice N k :
        Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :
        Set (CuspForm (CongruenceSubgroup.Gamma0 N) k)) := by
  rw [h]
  exact Submodule.mem_top
