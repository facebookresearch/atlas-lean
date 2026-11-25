/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests for Cartier-linear maps, their images and compatible ideals

On `ZMod p` the identity is `p^{-e}`-linear for every `e`, since `a ^ (p ^ e) = a`; its stable
image and the infimum of its nonzero compatible ideals are the unit ideal, which is then the least
nonzero compatible ideal. A family containing
the zero map has zero stable image, and on the quotient by a compatible ideal the induced map
acts on residues by the original map.
-/

open MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals

variable (p : ℕ) [Fact p.Prime]

/-- The identity of `ZMod p`, which is `p^{-e}`-linear for every `e`. -/
def idTrace (e : ℕ) : CartierTrace (ZMod p) p e where
  toAddMonoidHom := AddMonoidHom.id _
  scalar a b := by simp [ZMod.pow_card_pow]

/-- The zero map, which is `p^{-e}`-linear for every ring and degree. -/
def zeroTrace (R : Type) [CommRing R] (e : ℕ) : CartierTrace R p e where
  toAddMonoidHom := 0
  scalar a b := by simp

example : indexedStableTraceImage (R := ZMod p) (p := p) id (idTrace p) = ⊤ := by
  refine eq_top_iff.mpr fun a _ ↦ Submodule.mem_iInf _ |>.mpr fun e ↦ ?_
  exact mem_imageIdeal.mpr ⟨a, rfl⟩

/-- In a field the only nonzero ideal is the unit ideal, so the infimum is not zero there. -/
example : indexedCompatibleIdealInfimum (R := ZMod p) (p := p) id (idTrace p) = ⊤ := by
  refine eq_top_iff.mpr (le_sInf fun I hI ↦ ?_)
  rcases Ideal.eq_bot_or_top I with h | h
  · exact absurd h hI.1
  · exact h.ge

/-- One zero map in the family forces the stable image to be zero. -/
example (R : Type) [CommRing R] :
    indexedStableTraceImage (p := p) (fun b : Bool ↦ if b then 1 else 2)
      (fun _ ↦ zeroTrace p R _) = ⊥ := by
  refine eq_bot_iff.mpr fun a ha ↦ ?_
  obtain ⟨x, hx⟩ := mem_imageIdeal.mp ((Submodule.mem_iInf _).mp ha true)
  simpa [zeroTrace, eq_comm] using hx

example (R : Type) [CommRing R] (e : ℕ) (c : CartierTrace R p e) (I : Ideal R)
    (hI : IsCompatible c I) (a : R) :
    (quotient c I hI).toAddMonoidHom (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (c.toAddMonoidHom a) := by
  simp

example (R : Type) [CommRing R] (e : ℕ) (c : CartierTrace R p e) :
    IsCompatible c ⊥ ∧ IsCompatible c ⊤ :=
  ⟨isCompatible_bot c, isCompatible_top c⟩

/-- A nonzero infimum is the least nonzero compatible ideal; in a field it is the unit ideal. -/
example : IsLeast {I : Ideal (ZMod p) | I ≠ ⊥ ∧ ∀ e, IsCompatible (idTrace p e) I}
    (indexedCompatibleIdealInfimum (R := ZMod p) (p := p) id (idTrace p)) := by
  refine isLeast_indexedCompatibleIdealInfimum id (idTrace p) fun h ↦ ?_
  have htop : (⊤ : Ideal (ZMod p)) ≤
      indexedCompatibleIdealInfimum (R := ZMod p) (p := p) id (idTrace p) :=
    le_sInf fun I hI ↦ ((Ideal.eq_bot_or_top I).resolve_left hI.1).ge
  exact top_ne_bot (eq_bot_iff.mpr (h ▸ htop))
