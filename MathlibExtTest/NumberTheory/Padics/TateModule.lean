/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.TateModule

@[expose] public section

namespace MathlibExtTest.NumberTheory.Padics.TateModule

universe u v

/-- Consumer with the original binders (`M : Type`), restated over `Type*`. -/
theorem exactSource (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ d) :
    Module.Finite ℤ_[ℓ] (TateModule ℓ M) ∧ Module.Free ℤ_[ℓ] (TateModule ℓ M) ∧
      Module.finrank ℤ_[ℓ] (TateModule ℓ M) = d ∧
      Module.finrank ℚ_[ℓ] (TateModule.RationalTateModule ℓ M) = d :=
  TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq ℓ M d hcard

/-- Higher-universe consumer. -/
example (ℓ : ℕ) [Fact ℓ.Prime] (M : Type (u + 1)) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ d) :
    Module.Finite ℤ_[ℓ] (TateModule ℓ M) ∧ Module.Free ℤ_[ℓ] (TateModule ℓ M) ∧
      Module.finrank ℤ_[ℓ] (TateModule ℓ M) = d ∧
      Module.finrank ℚ_[ℓ] (TateModule.RationalTateModule ℓ M) = d :=
  TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq ℓ M d hcard

/-- Boundary case `d = 0`: the trivial group has exactly one `ℓ ^ n`-torsion
element for every `n`, and both Tate modules have rank `0`. -/
example (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank ℤ_[ℓ] (TateModule ℓ PUnit.{1}) = 0 ∧
      Module.finrank ℚ_[ℓ] (TateModule.RationalTateModule ℓ PUnit.{1}) = 0 := by
  have hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ PUnit.{1} ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ 0 := by
    intro n
    rw [pow_zero, Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, ⟨0⟩⟩
  obtain ⟨-, -, h1, h2⟩ :=
    TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq ℓ PUnit.{1} 0 hcard
  exact ⟨h1, h2⟩

/-- The all-`n` hypothesis matters: for `M = ℤ ⧸ ℓ` only the `n = 0, 1`
counts match the rank-one prediction; at `n = 2` the count stays `ℓ`
rather than `ℓ ^ 2`, so no single `d` satisfies the hypothesis. -/
example (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 1 < ℓ) :
    Nat.card (Submodule.torsionBy ℤ (ZMod ℓ) ((ℓ ^ 2 : ℕ) : ℤ)) ≠ (ℓ ^ 2) ^ 1 := by
  have h : Submodule.torsionBy ℤ (ZMod ℓ) ((ℓ ^ 2 : ℕ) : ℤ) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_torsionBy_iff]
    have hx : ((ℓ : ℤ)) • x = 0 := by
      have : ((ℓ : ℤ)) • x = (ℓ : ZMod ℓ) * x := by simp [zsmul_eq_mul]
      rw [this, ZMod.natCast_self, zero_mul]
    calc ((ℓ ^ 2 : ℕ) : ℤ) • x = ((ℓ : ℤ) * (ℓ : ℤ)) • x := by push_cast; ring
      _ = (ℓ : ℤ) • ((ℓ : ℤ) • x) := mul_smul _ _ _
      _ = 0 := by rw [hx, smul_zero]
  rw [h, pow_one]
  have hcard : Nat.card (⊤ : Submodule ℤ (ZMod ℓ)) = ℓ :=
    Nat.card_congr (Submodule.topEquiv).toEquiv |>.trans (Nat.card_zmod ℓ)
  rw [hcard]
  have hlt : ℓ < ℓ ^ 2 := by
    rw [pow_two]
    exact lt_mul_of_one_lt_right (by omega) hℓ
  exact ne_of_lt hlt

/-- Consumer with the original binders for the basis statement: a prime
`p`, a genus `g`, and torsion counts `p ^ (2 * g * n)`, restated over an
arbitrary additive commutative group `M` in place of the Jacobian. -/
theorem exactSourceBasis (p g : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = p ^ (2 * g * n)) :
    Nonempty (Module.Basis (Fin (2 * g)) ℤ_[p] (TateModule p M)) :=
  TateModule.nonempty_basis_of_natCard_torsionBy_pow_eq p M (2 * g)
    (fun n => (hcard n).trans (pow_mul' p (2 * g) n))

/-- Higher-universe consumer for the basis statement. -/
example (p : ℕ) [Fact p.Prime] (M : Type (u + 1)) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Nonempty (Module.Basis (Fin d) ℤ_[p] (TateModule p M)) :=
  TateModule.nonempty_basis_of_natCard_torsionBy_pow_eq p M d hcard

/-- Boundary case `g = 0`: the trivial group has a `Fin 0` basis. -/
example (p : ℕ) [Fact p.Prime] :
    Nonempty (Module.Basis (Fin (2 * 0)) ℤ_[p] (TateModule p PUnit.{1})) := by
  refine exactSourceBasis p 0 PUnit.{1} (fun n => ?_)
  simp only [mul_zero, zero_mul, pow_zero]
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨0⟩⟩

end MathlibExtTest.NumberTheory.Padics.TateModule
