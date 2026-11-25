/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Perfection
public import Mathlib.RingTheory.WittVector.Compare

/-!
# The universal PD envelope of the original semiperfect Witt surjection

The input ring is the actual inverse Frobenius limit. Its Witt map to R
is the original zeroth-coordinate map, with its entire kernel retained.
An envelope is an initial object among PD algebras receiving that Witt
ring and its kernel. Every divided power is required to preserve the
canonical divided powers on (p) in Z_p. Neither p-torsionfreeness nor a
finitely generated kernel is assumed.

The initial-object type records the universal PD hull; its construction
is deferred separately. Completion and B_cris⁺ use this hull literally.

Source: Scholze--Weinstein, arXiv:1211.6357v2, Proposition 4.1.3,
pp. 29--30. The integral and rational full-faithfulness scopes in
Theorem 4.1.4 and Corollary 4.1.12 are distinct.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.RingTheory.SemiperfectWittPDEnvelopes

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]

/-- The original inverse Frobenius limit, including every coefficient. -/
abbrev InversePerfection := Perfection R p

/-- The actual Witt coefficient ring in Fontaine's construction. -/
abbrev WittRing := WittVector p (InversePerfection p R)

/-- The displayed original surjection W(R^flat) to R. -/
def reduction : WittRing p R →+* R :=
  (Perfection.coeff R p 0).comp WittVector.constantCoeff

/-- The full original kernel; it is not replaced by a principal ideal. -/
def reductionIdeal : Ideal (WittRing p R) := RingHom.ker (reduction p R)

/-- Semiperfectness is surjectivity of the actual Frobenius. -/
def IsSemiperfect : Prop := Function.Surjective (frobenius R p)

/-- The canonical Z_p coefficients through the native Witt-vector equivalence. -/
def padicScalars : PadicInt p →+* WittRing p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (InversePerfection p R))).comp
    (WittVector.fromPadicInt p)

/-- A PD algebra under the actual Witt ring and its actual reduction kernel. -/
structure PDAlgebra where
  ring : CommRingCat.{0}
  scalars : WittRing p R →+* ring
  ideal : Ideal ring
  dividedPowers : DividedPowers ideal
  kernel_mem : (reductionIdeal p R).map scalars ≤ ideal
  padicCompatible : DividedPowers.IsDPMorphism (PadicInt.dividedPowers p)
    dividedPowers (scalars.comp (padicScalars p R))

variable {p R}

/-- All maps preserve the original coefficients and every divided power. -/
@[ext] structure PDHom (A B : PDAlgebra p R) where
  hom : A.ring →+* B.ring
  scalars : hom.comp A.scalars = B.scalars
  dividedPowers : DividedPowers.IsDPMorphism A.dividedPowers B.dividedPowers hom

instance : Category (PDAlgebra p R) where
  Hom := PDHom
  id A :=
    { hom := RingHom.id A.ring
      scalars := RingHom.id_comp _
      dividedPowers := (DividedPowers.DPMorphism.id A.dividedPowers).isDPMorphism }
  comp f g :=
    { hom := g.hom.comp f.hom
      scalars := by rw [RingHom.comp_assoc, f.scalars, g.scalars]
      dividedPowers := g.dividedPowers.comp _ f.dividedPowers }
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

variable (p R)

/-- The source universal PD hull, with universal maps on the complete PD category. -/
structure UniversalEnvelope where
  algebra : PDAlgebra p R
  initial : IsInitial algebra

variable {p R}

/-- The unique original-coefficient-preserving map to any PD target. -/
def UniversalEnvelope.to (A : UniversalEnvelope p R) (B : PDAlgebra p R) :
    A.algebra ⟶ B := A.initial.to B

/-- The source hull map is unique, including its original scalar map. -/
theorem UniversalEnvelope.to_unique (A : UniversalEnvelope p R)
    (B : PDAlgebra p R) (f : A.algebra ⟶ B) : f = A.to B :=
  A.initial.hom_ext f (A.to B)

/-- The residue dictionary is fixed on every original Witt coefficient. -/
structure ResidueIdentification (A : UniversalEnvelope p R) where
  equiv : (A.algebra.ring ⧸ A.algebra.ideal) ≃+* R
  coefficients : ∀ x : WittRing p R,
    equiv (Ideal.Quotient.mk A.algebra.ideal (A.algebra.scalars x)) = reduction p R x

end MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
