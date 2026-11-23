/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusGenerators
import MathlibExt.RingTheory.Frobenius.Restriction
import Mathlib.FieldTheory.Galois.Abelian

/-!
# Restriction of unramified Frobenius values in a tower (ATLAS N402, Stage C2b)

This file ports frozen ATLAS source declaration
`restrictNormalHom_frobeniusAutomorphism` at source lines `731--753` in
[`RayClassFields.lean` at commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L731-L753):
in a tower `M / L / K` with `L / K` abelian Galois, the restriction of the
chosen Frobenius at `p` on `M` equals the chosen Frobenius at `p` on `L`.

## Source-to-API mapping

Source declaration `restrictNormalHom_frobeniusAutomorphism` at source lines
`731--753` maps to public API `Modulus.restrictNormalHom_frobeniusAtCoprimePrime`.

The ATLAS source works with unconditional hidden prime choices. Here the
unramifiedness witnesses `hL` and `hM` are explicit arguments, so each chosen
Frobenius is known to sit at an unramified prime with finite residue field.
Source lines `755--801` (the Artin-map wrapper and the final proposition) are
not ported here; they are deferred to a later stage.
-/

@[expose] public noncomputable section

namespace NumberField
namespace Modulus

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsAbelianGalois K L] [IsGalois K M]

open scoped IsMulCommutative in
/-- **Restriction of Frobenius elements in a tower.** Let $K \subseteq L \subseteq M$ be a tower
of number fields with $L/K$ abelian Galois and $M/K$ Galois, and let $\mathfrak m$ be a modulus
of $K$ such that $L$ and $M$ are both unramified outside $\mathfrak m$. For every finite prime
$\mathfrak p$ of $K$ not dividing the finite part of $\mathfrak m$, the restriction to $L$ of the
chosen Frobenius element of $\mathfrak p$ in $\mathrm{Gal}(M/K)$ equals the chosen Frobenius
element of $\mathfrak p$ in $\mathrm{Gal}(L/K)$.

The abelianity of $L/K$ is used only to make conjugation of the Frobenius element in
$\mathrm{Gal}(L/K)$ trivial. -/
theorem restrictNormalHom_frobeniusAtCoprimePrime
    (m : Modulus K) (hL : m.IsUnramifiedOutside L)
    (hM : m.IsUnramifiedOutside M) (p : m.CoprimePrimes) :
    AlgEquiv.restrictNormalHom L
        (m.frobeniusAtCoprimePrime (L := M) hM p) =
      m.frobeniusAtCoprimePrime (L := L) hL p := by
  obtain ⟨Q_M, hfinM, -, -, hFrobM⟩ :=
    m.frobeniusAtCoprimePrime_spec (L := M) hM p
  obtain ⟨Q_L', -, -, -, hFrobL⟩ :=
    m.frobeniusAtCoprimePrime_spec (L := L) hL p
  let : Finite (NumberField.RingOfIntegers M ⧸ Q_M.1) := hfinM
  let Q_L : Ideal (NumberField.RingOfIntegers L) :=
    Q_M.1.under (NumberField.RingOfIntegers L)
  let : Q_L.IsPrime := by dsimp [Q_L]; infer_instance
  let : Q_M.1.LiesOver Q_L := by dsimp [Q_L]; infer_instance
  let : Q_L.LiesOver p.val.asIdeal :=
    Ideal.LiesOver.tower_bot Q_M.1 Q_L p.val.asIdeal
  let : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q_L :=
    (hL p.val p.property) Q_L inferInstance inferInstance
  have hUnder : Q_L'.1.under (NumberField.RingOfIntegers K) =
      Q_L.under (NumberField.RingOfIntegers K) := by
    rw [← Ideal.LiesOver.over (P := Q_L'.1) (p := p.val.asIdeal),
      ← Ideal.LiesOver.over (P := Q_L) (p := p.val.asIdeal)]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
    (L ≃ₐ[K] L) Q_L'.1 Q_L hUnder
  have hFrobL_at_QL : IsArithFrobAt (NumberField.RingOfIntegers K)
      (m.frobeniusAtCoprimePrime (L := L) hL p) Q_L := by
    have hc := hFrobL.conj g
    have hconj : g * m.frobeniusAtCoprimePrime (L := L) hL p * g⁻¹ =
        m.frobeniusAtCoprimePrime (L := L) hL p := by
      rw [mul_comm' g, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj, ← hg] at hc
    exact hc
  exact restrictNormalHom_eq_of_isArithFrobAt Q_L Q_M.1
    (m.frobeniusAtCoprimePrime (L := M) hM p)
    (m.frobeniusAtCoprimePrime (L := L) hL p) hFrobM hFrobL_at_QL

end Modulus

end NumberField
