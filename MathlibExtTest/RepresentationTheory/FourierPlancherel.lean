/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.FourierPlancherel
public import MathlibExt.GroupTheory.AbelianRepresentation

@[expose] public section

open scoped BigOperators
open CategoryTheory
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup
open MathlibExt.RepresentationTheory.FourierPlancherel

namespace MathlibExtTest.RepresentationTheory.FourierPlancherel

/-- Plancherel at the point mass at the identity gives `∑_i d_i² = |G|`. -/
example {G : Type} [Group G] [Fintype G] [DecidableEq G] {ι : Type} [Fintype ι]
    (V : ι → FDRep ℂ G) [∀ i, Simple (V i)]
    (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hsurj : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∑ i, (Module.finrank ℂ (V i) : ℂ) ^ 2 = Fintype.card G := by
  have h := plancherel V hinj hsurj (fun s => if s = 1 then 1 else 0)
  have hδ : ∀ i, fourier (V i).ρ (fun s => if s = 1 then (1 : ℂ) else 0) = 1 := fun i => by
    simp [fourier]
  have hδ' : ∀ i, fourier (V i).ρ (fun s => (starRingEnd ℂ) (if s⁻¹ = 1 then (1 : ℂ) else 0)) =
      1 := fun i => by
    simp [fourier, inv_eq_one]
  simp only [hδ, hδ', mul_one, LinearMap.trace_one] at h
  have hN : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hl : ((∑ s : G, ‖(if s = 1 then (1 : ℂ) else 0)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Finset.sum_eq_single (1 : G)] <;> simp_all
  rw [hl, eq_inv_mul_iff_mul_eq₀ hN, mul_one] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => sq _

/-- The character of the regular representation vanishes off the identity. -/
example {G : Type} [Group G] [Fintype G] [DecidableEq G] {ι : Type} [Fintype ι]
    (V : ι → FDRep ℂ G) [∀ i, Simple (V i)]
    (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hsurj : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i)) (g : G) (hg : g ≠ 1) :
    ∑ i, (Module.finrank ℂ (V i) : ℂ) * (V i).character g = 0 := by
  rw [sum_finrank_mul_character V hinj hsurj]
  simp [hg]

/-- The complete-set hypotheses of `plancherel` and `upper_bound_lemma` are satisfiable: the
trivial representation is a complete set of irreducibles for the trivial group. -/
example : ∃ (V : Unit → FDRep ℂ Unit) (_ : ∀ i, Simple (V i)),
    (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep ℂ Unit, Simple W → ∃ i, Nonempty (W ≅ V i)) := by
  refine ⟨fun _ => FDRep.ofMonoidHom (1 : Unit →* ℂ), fun _ => FDRep.ofMonoidHom_simple _,
    fun _ _ _ => rfl, fun W hW => ⟨(), ?_⟩⟩
  by_contra h
  have : Invertible (Nat.card Unit : ℂ) := invertibleOfNonzero (by simp)
  have := FDRep.ofMonoidHom_simple (1 : Unit →* ℂ)
  have ho := FDRep.char_orthonormal W (FDRep.ofMonoidHom (1 : Unit →* ℂ))
  simp only [h, ite_false] at ho
  have h1 := FDRep.finrank_eq_one_of_isMulCommutative W
  simp at ho
  rw [show (PUnit.unit : Unit) = 1 from rfl, FDRep.char_one, h1] at ho
  simp at ho

end MathlibExtTest.RepresentationTheory.FourierPlancherel
