/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`TauCeti/RingTheory/Frobenius/Splitting.lean` (TauCetiProject/TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors

Adapted portions: the structure of a Frobenius-linear additive map (`FrobeniusSplitting`,
generalized here to `p^e`-linear maps without the normalization at one), compatibility of an
ideal (`IsCompatible`) and the descent to a compatible quotient (`quotient`, `quotient_mk`).
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Cartier-linear maps, their images and compatible ideals

A `CartierTrace R p e` is an additive map `φ : R → R` with `φ (a ^ (p ^ e) * b) = a * φ b`,
that is, an `R`-linear map `F^e_* R → R` when `R` has characteristic `p` (in other
characteristics such maps are degenerate). Unlike a Frobenius splitting, `φ 1 = 1` is not
required, so no radicality of compatible ideals is claimed.

For a family of such maps indexed by admissible degrees, `indexedStableTraceImage` is the
intersection of their images and `indexedCompatibleIdealInfimum` the infimum of the nonzero
ideals compatible with all of them. The family matters: for the iterates of the normalized trace
map of a pair (unique up to units, Hacon--Xu §2.3) these are the non-F-pure ideal and the
candidate test ideal, whereas an arbitrary family need not give them (the zero map alone makes
the intersection of images zero). That they are nonzero or minimal, and their agreement with the
geometric sheaves, needs F-finiteness and localization and is not asserted here.

Sources: Schwede, arXiv0901.1154v4, Definition 2.12 and Theorem 5.2;
Hacon--Xu arXiv1302.0298v2, §2.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals

variable (R : Type) [CommRing R] (p e : ℕ)

/-- An additive map `φ : R → R` with `φ (a ^ (p ^ e) * b) = a * φ b`: a `p^{-e}`-linear map.
It need not satisfy `φ 1 = 1`. -/
structure CartierTrace extends R →+ R where
  scalar : ∀ a b : R, toAddMonoidHom (a^(p^e) * b) = a * toAddMonoidHom b

variable {R p e}

/-- An ideal `I` is compatible with `φ` when `φ I ⊆ I`. -/
def IsCompatible (c : CartierTrace R p e) (I : Ideal R) : Prop :=
  ∀ a : R, a ∈ I → c.toAddMonoidHom a ∈ I

/-- The image of `φ`, an ideal by Cartier-linearity: `a * φ x = φ (a ^ (p ^ e) * x)`. -/
def imageIdeal (c : CartierTrace R p e) : Ideal R where
  carrier := Set.range c.toAddMonoidHom
  zero_mem' := ⟨0, c.toAddMonoidHom.map_zero⟩
  add_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x+y, c.toAddMonoidHom.map_add x y⟩
  smul_mem' := by
    rintro a b ⟨x, rfl⟩
    exact ⟨a^(p^e)*x, c.scalar a x⟩

/-- The map induced by `φ` on the quotient by a compatible ideal. -/
def quotient (c : CartierTrace R p e) (I : Ideal R) (hI : IsCompatible c I) :
    CartierTrace (R ⧸ I) p e where
  toAddMonoidHom := QuotientAddGroup.map I.toAddSubgroup I.toAddSubgroup c.toAddMonoidHom hI
  scalar a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact congrArg (Ideal.Quotient.mk I) (c.scalar a b)

@[simp]
theorem quotient_mk (c : CartierTrace R p e) (I : Ideal R) (hI : IsCompatible c I) (a : R) :
    (quotient c I hI).toAddMonoidHom (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (c.toAddMonoidHom a) := rfl

theorem mem_imageIdeal {c : CartierTrace R p e} {a : R} :
    a ∈ imageIdeal c ↔ ∃ x, c.toAddMonoidHom x = a := Iff.rfl

theorem isCompatible_bot (c : CartierTrace R p e) : IsCompatible c ⊥ := by
  intro a ha
  rw [Ideal.mem_bot] at ha ⊢
  rw [ha, map_zero]

theorem isCompatible_top (c : CartierTrace R p e) : IsCompatible c ⊤ :=
  fun _ _ ↦ Submodule.mem_top

/-- An intersection of compatible ideals is compatible. -/
theorem isCompatible_sInf (c : CartierTrace R p e) {S : Set (Ideal R)}
    (h : ∀ I ∈ S, IsCompatible c I) : IsCompatible c (sInf S) := by
  intro a ha
  rw [Submodule.mem_sInf] at ha ⊢
  exact fun I hI ↦ h I hI a (ha I hI)

/-- The intersection of the images of a family of maps of the given degrees. -/
def indexedStableTraceImage {ι : Type} (degree : ι → ℕ)
    (c : ∀ i, CartierTrace R p (degree i)) : Ideal R :=
  ⨅ i, imageIdeal (c i)

/-- The infimum of the nonzero ideals compatible with every map of the family. It is not
claimed to be nonzero. The degrees are given by an explicit index, so no zero maps need to be
supplied at inadmissible exponents. -/
def indexedCompatibleIdealInfimum {ι : Type} (degree : ι → ℕ)
    (c : ∀ i, CartierTrace R p (degree i)) : Ideal R :=
  sInf {I : Ideal R | I ≠ ⊥ ∧ ∀ i, IsCompatible (c i) I}

/-- The infimum is compatible with every map of the family; when it is nonzero it is therefore
the least nonzero compatible ideal. -/
theorem isLeast_indexedCompatibleIdealInfimum {ι : Type} (degree : ι → ℕ)
    (c : ∀ i, CartierTrace R p (degree i)) (h : indexedCompatibleIdealInfimum degree c ≠ ⊥) :
    IsLeast {I : Ideal R | I ≠ ⊥ ∧ ∀ i, IsCompatible (c i) I}
      (indexedCompatibleIdealInfimum degree c) :=
  ⟨⟨h, fun i ↦ isCompatible_sInf (c i) fun _ hI ↦ hI.2 i⟩, fun _ hI ↦ sInf_le hI⟩

end MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals
