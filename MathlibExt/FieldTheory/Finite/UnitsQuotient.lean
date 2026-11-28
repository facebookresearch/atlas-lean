/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index

/-!
# Units of a quadratic extension of finite fields modulo the units of the base

Let `K ⊆ F` be finite fields with `#K = q` and `#F = q²`. Then `Fˣ / Kˣ` is cyclic of order
`q + 1` (`FiniteField.isCyclic_units_quotient_and_natCard_eq`). For `K = ℤ/ℓℤ` and `F` the
residue field of an imaginary quadratic field at an inert prime `ℓ`, this is Gross's description
of the Galois groups `G_ℓ ≃ F_λˣ / F_ℓˣ` in the ring class field tower.

## Proof

`Fˣ` is cyclic, being the unit group of a finite field, so its quotient is cyclic. The image of
`Kˣ` has `q - 1` elements, so the quotient has `(q² - 1) / (q - 1) = q + 1` elements.

## References

* B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic*
  (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
  235–256: §3, p. 239.
-/

@[expose] public section

namespace FiniteField

/-- **`F_{q²}ˣ / F_qˣ` is cyclic of order `q + 1`.** Let `K` and `F` be fields with `F` finite and
`F` a `K`-algebra, with `#K = q` and `#F = q²`. Then the quotient of `Fˣ` by the image of `Kˣ`
under `algebraMap K F` is cyclic of order `q + 1`. -/
theorem isCyclic_units_quotient_and_natCard_eq {K F : Type*} [Field K] [Field F] [Finite F]
    [Algebra K F] {q : ℕ} (hK : Nat.card K = q) (hF : Nat.card F = q ^ 2) :
    IsCyclic (Fˣ ⧸ (Units.map (algebraMap K F : K →* F)).range) ∧
      Nat.card (Fˣ ⧸ (Units.map (algebraMap K F : K →* F)).range) = q + 1 := by
  set H := (Units.map (algebraMap K F : K →* F)).range with hH
  have hinj : Function.Injective (Units.map (algebraMap K F : K →* F)) :=
    Units.map_injective (algebraMap K F).injective
  have : Finite K := Finite.of_injective _ (algebraMap K F).injective
  have hq : 1 < q := hK ▸ Finite.one_lt_card
  refine ⟨isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H), ?_⟩
  have hHcard : Nat.card H = q - 1 := by
    rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hK]
  have hmul := H.card_mul_index
  rw [hHcard, Nat.card_units, hF] at hmul
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hsq] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

end FiniteField

end
