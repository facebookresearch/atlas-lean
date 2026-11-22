/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.CharacterSumOfSquares
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace MathlibExtTest.RepresentationTheory.CharacterSumOfSquares

set_option linter.style.haveILetI false

open CharacterTheory

universe u

/-- Every one-dimensional representation is irreducible: its subrepresentations
are the submodules of a one-dimensional space, hence only `⊥` and `⊤`. -/
theorem one_dim_rep_irreducible {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] (ρ : Representation k G k) :
    ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine (isSimpleModule_iff _ _).mpr ?_
  have h : Module.finrank k ρ.asModule = 1 := Module.finrank_self k
  exact is_simple_module_of_finrank_eq_one h

/-- The sign representation of `S₃`: a permutation `g` acts on `ℂ` by
multiplication by `sign g`. -/
noncomputable def signRep : Representation ℂ (Equiv.Perm (Fin 3)) ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℂ) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    rw [Equiv.Perm.sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
    ring

/-- The sign representation of `S₃` is not equivalent to the trivial
representation: their characters differ at a transposition (`-1` vs `1`). -/
theorem signRep_not_equiv_trivial :
    ¬Nonempty (Representation.Equiv (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ)
      signRep) := by
  rintro ⟨e⟩
  have hchar := congr_fun (Representation.char_iso e) (Equiv.swap (0 : Fin 3) 1)
  have hsign : signRep.character (Equiv.swap (0 : Fin 3) 1) = -1 := by
    have hfun : ∀ x : ℂ, signRep (Equiv.swap (0 : Fin 3) 1) x = (-1 : ℂ) * x := by
      intro x
      change ((Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) : ℤ) : ℂ) * x = -1 * x
      rw [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]
      norm_num
    rw [Representation.character,
      show signRep (Equiv.swap (0 : Fin 3) 1) = (-1 : ℂ) • LinearMap.id from
        LinearMap.ext fun x => by
          rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]; exact hfun x,
      LinearMap.map_smul_of_tower, LinearMap.trace_id, smul_eq_mul]
    simp
  have htriv : (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ).character
      (Equiv.swap (0 : Fin 3) 1) = 1 := by
    show LinearMap.trace ℂ ℂ
        ((Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ) (Equiv.swap (0 : Fin 3) 1)) = 1
    rw [show (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ) (Equiv.swap (0 : Fin 3) 1) =
      LinearMap.id from rfl, LinearMap.trace_id]
    simp
  rw [htriv, hsign] at hchar
  norm_num at hchar

/-- The two one-dimensional representations of `S₃` used below, indexed by
`Bool`: trivial (`true`) and sign (`false`). -/
noncomputable def s3TwoReps : Bool → Representation ℂ (Equiv.Perm (Fin 3)) ℂ
  | true => Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ
  | false => signRep

/-- Parseval, one plus one: the character `χ_triv + χ_sign` of `S₃` has
self-pairing `1 ^ 2 + 1 ^ 2 = 2`. -/
example :
    (Nat.card (Equiv.Perm (Fin 3)) : ℂ)⁻¹ *
      ∑ g : Equiv.Perm (Fin 3),
        ((s3TwoReps true).character g + (s3TwoReps false).character g) *
        ((s3TwoReps true).character g⁻¹ + (s3TwoReps false).character g⁻¹) = 2 := by
  haveI : Invertible (Nat.card (Equiv.Perm (Fin 3)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  haveI : ∀ b, (s3TwoReps b).IsIrreducible := by
    intro b
    cases b <;> exact one_dim_rep_irreducible _
  have h := character_selfPairing_eq_sum_sq
    (ρ := s3TwoReps)
    (h_pairwise := by
      intro i j hij
      cases i <;> cases j
      · exact absurd rfl hij
      · rintro ⟨e⟩
        exact signRep_not_equiv_trivial ⟨e.symm⟩
      · rintro ⟨e⟩
        exact signRep_not_equiv_trivial ⟨e⟩
      · exact absurd rfl hij)
    (n := fun _ : Bool => 1)
    (χ := fun g => (s3TwoReps true).character g + (s3TwoReps false).character g)
    (hχ := by
      intro g
      rw [Fintype.sum_bool]
      simp [add_comm])
  simpa [Fintype.sum_bool] using h

/-- Parseval, two copies: the character `2 * χ_triv` has self-pairing
`2 ^ 2 = 4`. -/
example {G : Type} [Group G] [Fintype G] :
    (Nat.card G : ℂ)⁻¹ * ∑ _g : G, (2 : ℂ) * (2 : ℂ) = 4 := by
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne'))
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := one_dim_rep_irreducible _
  have hchar : ∀ g : G, (Representation.trivial ℂ G ℂ).character g = 1 := by
    intro g
    have hρ : (Representation.trivial ℂ G ℂ) g = LinearMap.id := rfl
    rw [show (Representation.trivial ℂ G ℂ).character g =
        LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) g) from rfl,
      hρ, LinearMap.trace_id]
    simp
  have h := character_selfPairing_eq_sum_sq
    (ρ := fun _ : PUnit => Representation.trivial ℂ G ℂ)
    (h_pairwise := fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (n := fun _ : PUnit => 2)
    (χ := fun _ : G => (2 : ℂ))
    (hχ := by
      intro g
      simp [hchar g])
  rw [h]
  simp
  norm_num

/-- Wedderburn block sizes for `S₃`: there are nonzero block sizes with
`∑ (d i) ^ 2 = |S₃| = 6`. -/
example :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, 1 ≤ d i) ∧ ∑ i, (d i) ^ 2 = 6 := by
  haveI : NeZero (Nat.card (Equiv.Perm (Fin 3)) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos.ne')⟩
  obtain ⟨n, d, hd, hsum, -⟩ := wedderburn_sum_sq_eq_card ℂ (Equiv.Perm (Fin 3))
  refine ⟨n, d, fun i => Nat.pos_of_ne_zero (NeZero.ne (d i)), ?_⟩
  rw [hsum]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- Wedderburn block sizes for `S₂`: there are nonzero block sizes with
`∑ (d i) ^ 2 = |S₂| = 2`. -/
example :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, 1 ≤ d i) ∧ ∑ i, (d i) ^ 2 = 2 := by
  haveI : NeZero (Nat.card (Equiv.Perm (Fin 2)) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.card_pos.ne')⟩
  obtain ⟨n, d, hd, hsum, -⟩ := wedderburn_sum_sq_eq_card ℂ (Equiv.Perm (Fin 2))
  refine ⟨n, d, fun i => Nat.pos_of_ne_zero (NeZero.ne (d i)), ?_⟩
  rw [hsum]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

end MathlibExtTest.RepresentationTheory.CharacterSumOfSquares
