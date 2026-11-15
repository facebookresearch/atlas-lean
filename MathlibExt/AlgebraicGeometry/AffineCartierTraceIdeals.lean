/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0; Authors: The Tau Ceti contributors.
Adapted from TauCetiProject/TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/RingTheory/Frobenius/Splitting.lean (additive Cartier-linearity
and compatible quotient construction). Modification: permit arbitrary
prime-power Cartier-linear traces without the splitting-at-one axiom;
compute actual trace-image and compatible-ideal infima.
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Actual affine Cartier-linear trace images and compatible quotients

These are actual additive maps with the Frobenius scalar formula.
The quotient map is the native additive-quotient map and is proved.
No radicality claim is made for a trace that is not a splitting.

Stable trace images and the infimum of nonzero compatible ideals are
computed ideal operations. Nonzero/minimality and equality with geometric
big-test/non-F-pure sheaves require the geometric normalized trace system,
F-finiteness and localization; those are separate provider boundaries.

Sources: Schwede, arXiv0901.1154v4, Definition 2.12 and Theorem 5.2;
Hacon--Xu arXiv1302.0298v2, §2.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals

variable (R : Type) [CommRing R] (p e : ℕ)

/-- Actual additive Frobenius-linear trace, with no false splitting-at-one condition. -/
structure CartierTrace extends R →+ R where
  scalar : ∀ a b : R, toAddMonoidHom (a^(p^e) * b) = a * toAddMonoidHom b

variable {R p e}

/-- Literal compatibility with the actual trace map. -/
def IsCompatible (c : CartierTrace R p e) (I : Ideal R) : Prop :=
  ∀ a : R, a ∈ I → c.toAddMonoidHom a ∈ I

/-- The actual trace image is an ideal by Cartier-linearity. -/
def imageIdeal (c : CartierTrace R p e) : Ideal R where
  carrier := Set.range c.toAddMonoidHom
  zero_mem' := ⟨0, c.toAddMonoidHom.map_zero⟩
  add_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x+y, c.toAddMonoidHom.map_add x y⟩
  smul_mem' := by
    rintro a b ⟨x, rfl⟩
    exact ⟨a^(p^e)*x, c.scalar a x⟩

/-- Compatible quotient trace, computed on the actual additive quotient. -/
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

/-- Actual intersection of a prescribed iterated normalized trace family's images. -/
def stableTraceImage (c : ∀ e : ℕ, CartierTrace R p e) : Ideal R :=
  ⨅ e : ℕ, imageIdeal (c e)

/-- Computed infimum of nonzero ideals compatible with every trace in the prescribed family.
Existence of a nonzero least element is not assumed by this definition. -/
def compatibleIdealInfimum (c : ∀ e : ℕ, CartierTrace R p e) : Ideal R :=
  sInf {I : Ideal R | I ≠ ⊥ ∧ ∀ e, IsCompatible (c e) I}


/-- Intersection of actual trace images indexed by the prescribed admissible degrees. -/
def indexedStableTraceImage {ι : Type} (degree : ι → ℕ)
    (c : ∀ i, CartierTrace R p (degree i)) : Ideal R :=
  ⨅ i, imageIdeal (c i)

/-- Infimum of nonzero ideals compatible with every actual admissible trace.
The degree index is explicit and not filled by zero maps at inadmissible exponents. -/
def indexedCompatibleIdealInfimum {ι : Type} (degree : ι → ℕ)
    (c : ∀ i, CartierTrace R p (degree i)) : Ideal R :=
  sInf {I : Ideal R | I ≠ ⊥ ∧ ∀ i, IsCompatible (c i) I}

end MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals

