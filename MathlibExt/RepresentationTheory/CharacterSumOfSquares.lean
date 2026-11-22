/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Sum-of-squares formulas for characters and Wedderburn block sizes

Two sum-of-squares formulas from the character theory of finite groups:

* **Parseval for characters.** If a class function `χ` is a combination
  `χ = ∑ i, n i • χ_i` of the characters of pairwise non-equivalent
  irreducible representations, then its self-pairing is the sum of the
  squares of the coefficients:
  `|G|⁻¹ ∑ g, χ g * χ g⁻¹ = ∑ i, (n i) ^ 2`.
  This is the first half of the v1 `character_selfInnerProduct_corollary`;
  its second half (the character criterion for irreducibility) was ported
  separately.

* **Sum of squares of Wedderburn block sizes.** The Wedderburn–Artin
  decomposition of the group algebra exhibits nonzero block sizes `d i` with
  `∑ i, (d i) ^ 2 = |G|`. This is the dimension-count part of the v1
  `mainTheorem`: the v1 full `mainTheorem` also asserted that the
  Wedderburn blocks give irreducible representations, which is unproved
  there and is NOT ported here.

Source: `v1/Atlas/AlgebraNotes/code/Characters.lean` (theorems
`CharacterTheory.character_selfInnerProduct_eq_sum_sq_aux` and
`CharacterTheory.mainTheorem_sum_sq_eq_card`). Neither formula is in
Mathlib: Mathlib has character orthogonality
(`Representation.char_orthonormal`) and the Wedderburn–Artin theorem
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`), but no
statement of either sum-of-squares consequence.
-/

@[expose] public section

namespace CharacterTheory

universe u

/-- **Parseval / sum-of-squares for characters.** If `χ` is a combination
of the characters of pairwise non-equivalent irreducible representations
with coefficients `n i`, then the self-pairing of `χ` is the sum of the
squares of the coefficients. In particular, for a single irreducible
`ρ`, taking `χ = χ_ρ` gives self-pairing `1`, and for the regular
character the formula recovers `∑ (dim ρ_i) ^ 2 = |G|` once the regular
character is expanded in irreducibles. -/
theorem character_selfPairing_eq_sum_sq
    {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    [Invertible (Nat.card G : k)] [IsAlgClosed k]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible]
    (h_pairwise : ∀ i j, i ≠ j → ¬Nonempty (Representation.Equiv (ρ i) (ρ j)))
    (n : ι → ℕ)
    (χ : G → k)
    (hχ : ∀ g : G, χ g = ∑ i, (n i : k) * (ρ i).character g) :
    (Nat.card G : k)⁻¹ * ∑ g : G, χ g * χ g⁻¹ = ∑ i, ((n i : k) ^ 2) := by
  have hexp : (Nat.card G : k)⁻¹ * ∑ g : G, χ g * χ g⁻¹ =
      ∑ i, ∑ j, (n i : k) * (n j : k) *
        ((Nat.card G : k)⁻¹ * ∑ g : G, (ρ i).character g * (ρ j).character g⁻¹) := by
    rw [Finset.mul_sum]
    simp_rw [hχ]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext g
    rw [Finset.sum_comm]
    congr 1; ext i
    congr 1; ext j
    ring
  rw [hexp]
  congr 1; ext i
  have h_ortho : ∀ j, (n i : k) * (n j : k) *
      ((Nat.card G : k)⁻¹ * ∑ g : G, (ρ i).character g * (ρ j).character g⁻¹) =
      if j = i then (n i : k) ^ 2 else 0 := by
    intro j
    rw [Representation.char_orthonormal (ρ i) (ρ j)]
    by_cases hij : i = j
    · subst hij
      have hself : Nonempty ((ρ i).Equiv (ρ i)) := ⟨Representation.Equiv.refl _⟩
      simp only [hself, ite_true, mul_one, ite_true]
      ring
    · have hne : ¬Nonempty ((ρ j).Equiv (ρ i)) := by
        intro ⟨e⟩; exact h_pairwise i j hij ⟨e.symm⟩
      simp only [hne, ite_false, mul_zero, show ¬(j = i) from fun h => hij h.symm,
        ite_false]
  simp_rw [h_ortho]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- **Sum of squares of the Wedderburn block sizes.** If `|G|` is nonzero in
an algebraically closed field, the group algebra of a finite group is a product
of matrix algebras with nonzero block sizes whose squares sum to `|G|`. -/
theorem wedderburn_sum_sq_eq_card
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      (∑ i, (d i) ^ 2 = Nat.card G) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k
    (MonoidAlgebra k G)
  refine ⟨n, d, hd, ?_, ⟨e⟩⟩
  have hdim : Module.finrank k (MonoidAlgebra k G) =
      Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) :=
    LinearEquiv.finrank_eq e.toLinearEquiv
  rw [show Module.finrank k (MonoidAlgebra k G) = Nat.card G from by
    -- In current Mathlib `MonoidAlgebra` is a structure wrapping `G →₀ k`,
    -- not a definitional unfolding of it, so the v1 `change` to `G →₀ k`
    -- fails; go through the coefficient linear equivalence instead.
    rw [LinearEquiv.finrank_eq (MonoidAlgebra.coeffLinearEquiv (R := k) (M := G))]
    rw [Module.finrank_finsupp, Module.finrank_self, mul_one,
      Nat.card_eq_fintype_card]] at hdim
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] at hdim
  rw [hdim]; congr 1; funext i; ring

end CharacterTheory
