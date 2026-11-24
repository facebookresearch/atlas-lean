/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.MvFormalGroupRescaledLog

@[expose] public section

namespace MetaMathlibExt

open MvPowerSeries

universe u

/-- Consumer with the original binders, restated verbatim. -/
theorem exactSource {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),
      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧
      (∀ i, (Fp i).constantCoeff = 0) ∧
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
        (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :=
  MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F

/-- The statement also applies in a higher universe. -/
example {𝓞 : Type (u + 1)} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞, MvFormalGroup.linearPart φ = 1 := by
  obtain ⟨-, φ, -, -, -, h, -⟩ := MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F
  exact ⟨φ, h⟩

/-- The additive formal group law is commutative, so it has such a logarithm. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ) :
    ∃ φ : Fin d → MvPowerSeries (Fin d) 𝓞,
      (∀ i, (φ i).constantCoeff = 0) ∧ MvFormalGroup.linearPart φ = 1 := by
  obtain ⟨-, φ, -, -, h0, h1, -⟩ :=
    MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp (MvFormalGroup.addMv d 𝓞)
  exact ⟨φ, h0, h1⟩

end MetaMathlibExt
