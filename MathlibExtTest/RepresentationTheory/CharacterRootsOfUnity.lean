/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.CharacterRootsOfUnity
import Mathlib.Tactic

namespace MathlibExtTest.RepresentationTheory.CharacterRootsOfUnity

open CharacterTheory

/-- The sign function: the nontrivial element of `ZMod 2` acts by `-1`. -/
noncomputable def signFn (g : Multiplicative (ZMod 2)) : ℂ →ₗ[ℂ] ℂ :=
  if Multiplicative.toAdd g = 0 then LinearMap.id else (-1 : ℂ) • LinearMap.id

/-- The sign representation of `ZMod 2` on `ℂ`: the nontrivial element acts
by multiplication by `-1`. -/
noncomputable def signRep : Representation ℂ (Multiplicative (ZMod 2)) ℂ where
  toFun := signFn
  map_one' := by
    ext
    simp [signFn]
  map_mul' a b := by
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases h2 (Multiplicative.toAdd a) with ha | ha <;>
      rcases h2 (Multiplicative.toAdd b) with hb | hb <;>
      ext <;>
      simp [signFn, ha, hb, h11]

/-- The nontrivial element of the sign representation has eigenvalue `-1`. -/
theorem signRep_hasEigenvalue_neg_one :
    Module.End.HasEigenvalue
      (signRep (Multiplicative.ofAdd 1)) (-1 : ℂ) := by
  have hsg : signRep (Multiplicative.ofAdd 1) = (-1 : ℂ) • LinearMap.id := by
    simp [signRep, signFn]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : ℂ))
  refine ⟨?_, one_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff, hsg]
  simp

/-- The eigenvalue `-1` satisfies `(-1) ^ orderOf g = 1`. -/
example : (-1 : ℂ) ^ orderOf (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 :=
  hasEigenvalue_pow_orderOf_eq_one signRep _ signRep_hasEigenvalue_neg_one

/-- The eigenvalue `-1` satisfies `(-1) ^ |G| = 1`. -/
example : (-1 : ℂ) ^ Fintype.card (Multiplicative (ZMod 2)) = 1 :=
  hasEigenvalue_pow_card_eq_one signRep _ signRep_hasEigenvalue_neg_one

/-- `-1` is a root of the characteristic polynomial of the sign-representation
operator, and the charpoly-roots theorem gives `(-1) ^ |G| = 1`. -/
example : (-1 : ℂ) ^ Fintype.card (Multiplicative (ZMod 2)) = 1 := by
  have hmem : (-1 : ℂ) ∈ ((LinearMap.toMatrix (Module.finBasis ℂ ℂ) (Module.finBasis ℂ ℂ)
      (signRep (Multiplicative.ofAdd 1))).charpoly.roots) := by
    rw [Polynomial.mem_roots ((Matrix.charpoly_monic _).ne_zero),
      LinearMap.charpoly_toMatrix, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact signRep_hasEigenvalue_neg_one
  exact char_charpoly_roots_pow_eq_one signRep _
    (-1) hmem

/-- The trivial representation has eigenvalue `1`, so `1 ^ orderOf g = 1`
and `1 ^ |G| = 1` by the same theorems. -/
example {G : Type} [Group G] [Fintype G] (g : G) :
    (1 : ℂ) ^ orderOf g = 1 ∧ (1 : ℂ) ^ Fintype.card G = 1 := by
  have hρ : (Representation.trivial ℂ G ℂ) g = LinearMap.id := rfl
  have hev : Module.End.HasEigenvalue ((Representation.trivial ℂ G ℂ) g) (1 : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : ℂ))
    refine ⟨?_, one_ne_zero⟩
    rw [Module.End.mem_eigenspace_iff, hρ]
    simp
  exact ⟨hasEigenvalue_pow_orderOf_eq_one _ _ hev,
    hasEigenvalue_pow_card_eq_one _ _ hev⟩

end MathlibExtTest.RepresentationTheory.CharacterRootsOfUnity
