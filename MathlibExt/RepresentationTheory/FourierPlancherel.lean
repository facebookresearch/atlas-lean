/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.FourierTransformFiniteGroup
public import Mathlib.RepresentationTheory.FDRep
public import MathlibExt.GroupTheory.IrreducibleCharacterBasis

import Mathlib.Analysis.Complex.Basic

/-!
# Plancherel formula on a finite group

Let `V : ι → FDRep ℂ G` be a *complete set of irreducible representations* of a finite group `G`:
simple objects, pairwise non-isomorphic, such that every simple object is isomorphic to some
`V i`. Write `d_i` for the dimension of `V i` and `χ_i` for its character.

* `sum_finrank_mul_character`: `∑_i d_i χ_i(g) = |G|` if `g = 1` and `0` otherwise (the character
  of the regular representation);
* `trace_fourier_mul_fourier`: `Tr(P̂(ρ) Q̂(ρ)) = ∑_{s,t} P(s) Q(t) χ_ρ(s t)`;
* `plancherel`: `∑_s |P(s)|² = (1/|G|) ∑_i d_i Tr(P̂(V_i) P̂(V_i)*)`, with
  `P̂(ρ)* = ∑_s conj(P(s)) ρ(s⁻¹)` the transform of `s ↦ conj(P(s⁻¹))` (the adjoint of `P̂(ρ)` when
  `ρ` is unitary, as the sources assume).

Sources: P. Diaconis and M. Shahshahani, *Generating a random permutation with random
transpositions*, Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, Lemma 2; P. Diaconis, *Applications
of non-commutative Fourier analysis to probability problems*, École d'Été de Probabilités de
Saint-Flour XV–XVII, Lecture Notes in Math. 1362 (1988) 51–100, Theorem 4.1 and its proof.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory

namespace MathlibExt.RepresentationTheory.FourierPlancherel

open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (fourier)

variable {G : Type} [Group G] [Fintype G]

/-- **Trace of a product of Fourier transforms.** For every representation `ρ` with character
`χ_ρ = Tr ∘ ρ`, `Tr(P̂(ρ) Q̂(ρ)) = ∑_s ∑_t P(s) Q(t) χ_ρ(s t)`, by linearity of the trace (Mathlib's
`LinearMap.trace` is `0` on infinite-dimensional spaces, where both sides vanish). A direct
computation from the definitions of the transform and of the character in Diaconis and
Shahshahani 1981, Section 2; it is the first step of the proof of `plancherel`. -/
theorem trace_fourier_mul_fourier {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (P Q : G → ℂ) :
    LinearMap.trace ℂ V (fourier ρ P * fourier ρ Q) =
      ∑ s, ∑ t, P s * Q t * ρ.character (s * t) := by
  simp only [fourier, Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_smul, map_smul,
    smul_eq_mul, ← map_mul, Representation.character]
  exact Finset.sum_comm

private noncomputable instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- **Character of the regular representation.** For a complete set `V : ι → FDRep ℂ G` of
irreducible complex representations of the finite group `G`, of dimensions `d_i` and characters
`χ_i`, `∑_i d_i χ_i(g) = |G|` if `g = 1` and `0` otherwise: the regular representation contains
each irreducible `d_i` times and its character is `|G| δ_1` (Diaconis, Saint-Flour notes 1988,
proof of Theorem 4.1(a), citing Serre). Proved here from the completeness and orthonormality of
irreducible characters. -/
theorem sum_finrank_mul_character [DecidableEq G] {ι : Type} [Fintype ι] (V : ι → FDRep ℂ G)
    [∀ i, Simple (V i)] (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hsurj : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i)) (g : G) :
    ∑ i, (Module.finrank ℂ (V i) : ℂ) * (V i).character g =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  set δ : G → ℂ := fun g => if g = 1 then (Fintype.card G : ℂ) else 0 with hδ
  have hclass : ∀ g h : G, δ (h * g * h⁻¹) = δ g := fun g h => by
    have e : h * g * h⁻¹ = 1 ↔ g = 1 := by
      rw [mul_inv_eq_one]
      constructor
      · intro e; simpa using congrArg (h⁻¹ * ·) e
      · rintro rfl; simp
    simp only [hδ, e]
  have hspan :=
    MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted.mem_span_irrCharacters_of_isClassFunction
      G δ hclass
  have hle : Submodule.span ℂ {χ : G → ℂ | ∃ W : FDRep ℂ G, Simple W ∧ W.character = χ} ≤
      Submodule.span ℂ (Set.range fun i => (V i).character) := by
    rw [Submodule.span_le]
    rintro χ ⟨W, hW, rfl⟩
    obtain ⟨i, ⟨e⟩⟩ := hsurj W hW
    exact Submodule.subset_span ⟨i, (FDRep.char_iso e).symm⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hle hspan)
  -- Pair both sides with `χ_j(g⁻¹)`.
  have hcoef : ∀ j, c j = (Module.finrank ℂ (V j) : ℂ) := fun j => by
    have hN : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have h1 : (Nat.card G : ℂ)⁻¹ * ∑ g, δ g * (V j).character g⁻¹ =
        (Module.finrank ℂ (V j) : ℂ) := by
      rw [Finset.sum_eq_single (1 : G)]
      · simp only [hδ, ite_true, inv_one, FDRep.char_one, Nat.card_eq_fintype_card]
        field_simp
      · intro b _ hb; simp [hδ, hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : (Nat.card G : ℂ)⁻¹ * ∑ g, δ g * (V j).character g⁻¹ = c j := by
      have hexp : ∀ g, δ g * (V j).character g⁻¹ =
          ∑ i, c i * (V i).character g * (V j).character g⁻¹ := fun g => by
        rw [← hc]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      simp only [hexp]
      rw [Finset.sum_comm, Finset.mul_sum]
      have : ∀ i, (Nat.card G : ℂ)⁻¹ * ∑ g, c i * (V i).character g * (V j).character g⁻¹ =
          if i = j then c i else 0 := fun i => by
        have ho := FDRep.char_orthonormal (V i) (V j)
        have e : ∑ g, c i * (V i).character g * (V j).character g⁻¹ =
            c i * ∑ g, (V i).character g * (V j).character g⁻¹ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by ring
        rw [e, mul_left_comm, ho]
        by_cases hij : i = j
        · subst hij; simp
        · have : ¬ Nonempty (V i ≅ V j) := fun h => hij (hinj i j h)
          simp [hij, this]
      rw [Finset.sum_congr rfl fun i _ => this i]
      simp
    rw [← h2, h1]
  have := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoef] at this
  rw [this]

/-- **Plancherel formula on a finite group.** Let `V : ι → FDRep ℂ G` be a complete set of
irreducible complex representations of the finite group `G` (pairwise non-isomorphic simple
objects, every simple object isomorphic to one of them), of dimensions `d_i`. For every
`P : G → ℂ`, `∑_s |P(s)|² = (1/|G|) ∑_i d_i Tr(P̂(V_i) P̂(V_i)*)` (Diaconis and Shahshahani 1981,
Lemma 2, equation (2.1), citing Serre, *Linear representations of finite groups*, Section 6.2;
Diaconis, Saint-Flour notes 1988, Theorem 4.1(b)). The sources take `ρ` unitary; then
`P̂(ρ)* = ∑_s conj(P(s)) ρ(s⁻¹)` is the transform of `s ↦ conj(P(s⁻¹))`, which is how the
statement writes `Tr(P̂(ρ) P̂(ρ)*)` without choosing an inner product. -/
theorem plancherel {ι : Type} [Fintype ι] (V : ι → FDRep ℂ G) [∀ i, Simple (V i)]
    (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hsurj : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i))
    (P : G → ℂ) :
    ((∑ s, ‖P s‖ ^ 2 : ℝ) : ℂ) = ((Fintype.card G : ℂ))⁻¹ *
      ∑ i, (Module.finrank ℂ (V i) : ℂ) *
        LinearMap.trace ℂ (V i)
          (fourier (V i).ρ P * fourier (V i).ρ (fun s => (starRingEnd ℂ) (P s⁻¹))) := by
  classical
  have hN : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hswap : (∑ i, (Module.finrank ℂ (V i) : ℂ) *
      LinearMap.trace ℂ (V i)
        (fourier (V i).ρ P * fourier (V i).ρ (fun s => (starRingEnd ℂ) (P s⁻¹)))) =
      ∑ s, ∑ t, P s * (starRingEnd ℂ) (P t⁻¹) *
        ∑ i, (Module.finrank ℂ (V i) : ℂ) * (V i).character (s * t) := by
    simp only [trace_fourier_mul_fourier, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [FDRep.character, Representation.character]
    ring
  rw [hswap]
  simp only [sum_finrank_mul_character V hinj hsurj]
  have hst : ∀ s : G, ∑ t, P s * (starRingEnd ℂ) (P t⁻¹) *
      (if s * t = 1 then (Fintype.card G : ℂ) else 0) =
        P s * (starRingEnd ℂ) (P s) * (Fintype.card G : ℂ) := fun s => by
    rw [Finset.sum_eq_single s⁻¹]
    · simp
    · intro b _ hb
      have : s * b ≠ 1 := fun h => hb (eq_inv_of_mul_eq_one_right h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hst, ← Finset.sum_mul]
  push_cast
  rw [mul_comm, mul_assoc, mul_inv_cancel₀ hN, mul_one]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.mul_conj']

end MathlibExt.RepresentationTheory.FourierPlancherel
