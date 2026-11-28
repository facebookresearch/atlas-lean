/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.HomothetyClasses
public import MathlibExt.NumberTheory.ModularForms.LatticeDiscriminantEta
public import MathlibExt.NumberTheory.QuadraticForms.ProperIdealRootLattice

/-!
# The discriminant of a lattice is nonzero

For a period pair `L` with invariants `g₂`, `g₃`, the discriminant `g₂³ - 27 g₃²` is nonzero
(`PeriodPair.discriminant_ne_zero`). For the lattice `ℤ + ℤ τ` with `τ` in the upper half-plane the
lattice sums are the sums over `v : Fin 2 → ℤ` of `(v₀ τ + v₁)^{-k}`
(`PeriodPair.G_ofTau_eq_tsum`), so by Jacobi's product formula
(`MetaMathlibExt.lattice_discriminant_eq_eta_product`) the discriminant is `(2π)¹² η(τ)²⁴`
(`PeriodPair.discriminant_ofTau_eq_eta`), which is nonzero by Mathlib's `ModularForm.eta_ne_zero`.
Every period pair is homothetic to some `(1, τ)` (`PeriodPair.exists_isHomothetic_ofTau`), and a
homothety scales the discriminant by a nonzero factor
(`PeriodPair.discriminant_eq_of_lattice_eq_smul`).

## References

* J. S. Milne, *Elliptic Curves*, 2nd ed., author's version,
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter III, Lemma 3.6, p. 95.
-/

@[expose] public section

open scoped UpperHalfPlane

namespace PeriodPair

/-- **The lattice sums of `(1, τ)` over `ℤ²`.** For `τ` in the upper half-plane and `k ∈ ℕ`, the
lattice sum `G_k = ∑_{ω ∈ Λ} ω^{-k}` of the period pair `(1, τ)` (`PeriodPair.G`, a sum over the
lattice) equals `∑_{v ∈ ℤ²} (v₀ τ + v₁)^{-k}` (for `k ≥ 1`, the term at `v = 0` is `0` in both
sums). The lattice is indexed through `PeriodPair.latticeEquivProd`. -/
theorem G_ofTau_eq_tsum (τ : ℍ) (k : ℕ) :
    (ofTau τ τ.im_pos.ne').G k = ∑' v : Fin 2 → ℤ, (((v 0 : ℂ) * τ + v 1) ^ k)⁻¹ := by
  set L := ofTau τ τ.im_pos.ne'
  let e : (Fin 2 → ℤ) ≃ L.lattice :=
    ((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans L.latticeEquivProd.symm.toEquiv
  rw [G, ← e.tsum_eq]
  congr 1
  funext v
  have hv : ((e v : L.lattice) : ℂ) = (v 0 : ℂ) * τ + v 1 := by
    simp only [e, Equiv.trans_apply, LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply]
    simp [L, ofTau, add_comm]
  rw [hv]

/-- **The discriminant of `ℤ + ℤ τ` through Dedekind's `η`.** For `τ` in the upper half-plane,
`g₂(τ)³ - 27 g₃(τ)² = (2π)¹² η(τ)²⁴` for the period pair `(1, τ)`, from Jacobi's product formula
`MetaMathlibExt.lattice_discriminant_eq_eta_product` and `PeriodPair.G_ofTau_eq_tsum`. -/
theorem discriminant_ofTau_eq_eta (τ : ℍ) :
    (ofTau τ τ.im_pos.ne').g₂ ^ 3 - 27 * (ofTau τ τ.im_pos.ne').g₃ ^ 2 =
      (2 * (Real.pi : ℂ)) ^ 12 * ModularForm.eta τ ^ 24 := by
  have h := (MetaMathlibExt.lattice_discriminant_eq_eta_product τ).1
  rw [g₂, g₃, G_ofTau_eq_tsum, G_ofTau_eq_tsum]
  exact h

/-- **The discriminant of a lattice is nonzero.** For every period pair `L`,
`g₂(L)³ - 27 g₃(L)² ≠ 0`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., author's version, Chapter III, Lemma 3.6,
p. 95. -/
theorem discriminant_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  obtain ⟨τ, c, hc, h⟩ := L.exists_isHomothetic_ofTau
  rw [discriminant_eq_of_lattice_eq_smul hc h, discriminant_ofTau_eq_eta]
  refine mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) (mul_ne_zero ?_ ?_)
  · exact pow_ne_zero _ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact pow_ne_zero _ (ModularForm.eta_ne_zero τ.im_pos)

end PeriodPair
