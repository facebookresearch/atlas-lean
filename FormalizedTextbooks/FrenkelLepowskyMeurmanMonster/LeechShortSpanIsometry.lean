/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! A signed action on the actual finite short catalogue preserves the Leech lattice.
No lattice-preservation assumption is used to recognize the ambient map. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A signed forward action on short representatives forces a signed inverse action. -/
theorem leechShort_signed_inverse
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (he : ∀ r : GriessShortIndex, ∃ s : GriessShortIndex,
      e (griessShortVector r) = griessShortVector s ∨
      e (griessShortVector r) = -griessShortVector s) :
    ∀ s : GriessShortIndex, ∃ r : GriessShortIndex,
      e.symm (griessShortVector s) = griessShortVector r ∨
      e.symm (griessShortVector s) = -griessShortVector r := by
  classical
  choose σ hσ using he
  have hi : Function.Injective σ := by
    intro r t hrt
    have hs : e (griessShortVector t) = griessShortVector (σ r) ∨
        e (griessShortVector t) = -griessShortVector (σ r) := by
      simpa only [hrt] using hσ t
    have hpair : e (griessShortVector r) = e (griessShortVector t) ∨
        e (griessShortVector r) = -e (griessShortVector t) := by
      rcases hσ r with hr | hr <;> rcases hs with ht | ht <;> simp [hr, ht]
    apply centralizer_shortVector_sign_unique
    rcases hpair with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective (by simpa only [map_neg] using h))
  have hsurj := Finite.surjective_of_injective hi
  intro s
  obtain ⟨r, hr⟩ := hsurj s
  refine ⟨r, ?_⟩
  have h := hσ r
  rw [hr] at h
  rcases h with h | h
  · left
    apply e.injective
    simpa only [e.apply_symm_apply] using h.symm
  · right
    apply e.injective
    simp only [e.apply_symm_apply, map_neg, h, neg_neg]

/-- Mapping each actual short representative to a signed representative maps
the whole actual lattice into itself. -/
theorem leechShort_signed_preserves_lattice
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (he : ∀ r : GriessShortIndex, ∃ s : GriessShortIndex,
      e (griessShortVector r) = griessShortVector s ∨
      e (griessShortVector r) = -griessShortVector s)
    (u : Fin 24 → ℝ) (hu : u ∈ LeechLattice) : e u ∈ LeechLattice := by
  rw [leechLattice_eq_short_span] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, hs | hs⟩ := he r
    · rw [hs]
      exact griessShortVector_mem_leechLattice s
    · rw [hs]
      exact LeechLattice.neg_mem (griessShortVector_mem_leechLattice s)
  | zero => simpa only [map_zero] using LeechLattice.zero_mem
  | add x y _ _ hx hy =>
    simpa only [map_add] using LeechLattice.add_mem hx hy
  | smul a x _ hx =>
    simpa only [map_zsmul] using LeechLattice.smul_mem a hx

/-- A signed forward action on actual short vectors gives full lattice membership equivalence. -/
theorem leechShort_signed_lattice_iff
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (he : ∀ r : GriessShortIndex, ∃ s : GriessShortIndex,
      e (griessShortVector r) = griessShortVector s ∨
      e (griessShortVector r) = -griessShortVector s)
    (u : Fin 24 → ℝ) : u ∈ LeechLattice ↔ e u ∈ LeechLattice := by
  constructor
  · exact leechShort_signed_preserves_lattice e he u
  · intro hu
    have h := leechShort_signed_preserves_lattice e.symm
      (leechShort_signed_inverse e he) (e u) hu
    simpa only [e.symm_apply_apply] using h

/-- Recognition as an actual Leech isometry from pairing preservation and the short action. -/
theorem leechShort_signed_mem_isometry
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hp : ∀ u v, stdPairingFun (e u) (e v) = stdPairingFun u v)
    (he : ∀ r : GriessShortIndex, ∃ s : GriessShortIndex,
      e (griessShortVector r) = griessShortVector s ∨
      e (griessShortVector r) = -griessShortVector s) : e ∈ leechIsomSubgroup :=
  ⟨hp, leechShort_signed_lattice_iff e he⟩

/-- Orthogonality forces the scalar on a short line to be a sign. -/
theorem leechShort_orthogonal_scalar_sign
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hp : ∀ u v, stdPairingFun (e u) (e v) = stdPairingFun u v)
    (r s : GriessShortIndex) (t : ℝ)
    (h : e (griessShortVector r) = t • griessShortVector s) : t = 1 ∨ t = -1 := by
  have hn := hp (griessShortVector r) (griessShortVector r)
  change (∑ i, e (griessShortVector r) i * e (griessShortVector r) i) =
    ∑ i, griessShortVector r i * griessShortVector r i at hn
  rw [griessShortVector_norm_sq] at hn
  simp only [h, Pi.smul_apply, smul_eq_mul] at hn
  have he (i : Fin 24) :
      (t * griessShortVector s i) * (t * griessShortVector s i) =
        t ^ 2 * (griessShortVector s i * griessShortVector s i) := by ring
  simp_rw [he] at hn
  rw [← Finset.mul_sum, griessShortVector_norm_sq] at hn
  have ht : t ^ 2 = 1 := by nlinarith
  exact sq_eq_one_iff.mp ht

/-- An orthogonal ambient equivalence mapping actual short lines to short lines
is an actual lattice isometry. The inverse action follows from finiteness. -/
theorem leechShort_lines_mem_isometry
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ))
    (hp : ∀ u v, stdPairingFun (e u) (e v) = stdPairingFun u v)
    (he : ∀ r : GriessShortIndex, ∃ s : GriessShortIndex, ∃ t : ℝ,
      e (griessShortVector r) = t • griessShortVector s) : e ∈ leechIsomSubgroup := by
  apply leechShort_signed_mem_isometry e hp
  intro r
  obtain ⟨s, t, h⟩ := he r
  refine ⟨s, ?_⟩
  rcases leechShort_orthogonal_scalar_sign e hp r s t h with ht | ht
  · exact Or.inl (by simpa only [ht, one_smul] using h)
  · exact Or.inr (by simpa only [ht, neg_one_smul] using h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
