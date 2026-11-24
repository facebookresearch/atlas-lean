/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import MathlibExt.AlgebraicGeometry.FrobeniusGeometry

/-!
# Geometric F/V and actual torsion fibres of an abelian variety

The variety is an actual commutative group scheme over the prime field.
Multiplication uses its internal group law; Frobenius is the actual scheme
Frobenius. A Verschiebung is normalized by both composites being [p], and
its finite-flat degree is measured by the actual scheme rank function.

The torsion and F/V kernels are scheme-theoretic fibres at the actual group
identity. Their maps below are induced by the concrete factorization.
Verschiebung construction in higher dimension remains a Wanted request.

Reference: Mumford, *Abelian Varieties*, §15; Tate's F/V theory.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AbelianVerschiebung

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj _root_.AlgebraicGeometry
open FrobeniusGeometry

variable (p : ℕ) [Fact p.Prime]

/-- Schemes over the actual prime field. -/
abbrev PrimeFieldScheme := Over (Spec (CommRingCat.of.{0} (ZMod p)))

variable {p} (A : PrimeFieldScheme p) [GrpObj A] [IsCommMonObj A]

/-- Multiplication by n uses the actual pointwise internal group law. -/
def multiplication (n : ℕ) : A ⟶ A := by
  letI : CommGroup (A ⟶ A) := CategoryTheory.Hom.commGroup
  exact (𝟙 A) ^ n

omit [Fact p.Prime] [IsCommMonObj A] in
/-- Multiplication acts by the nth group power on every test-scheme point. -/
theorem multiplication_test (n : ℕ) (T : PrimeFieldScheme p) (f : T ⟶ A) :
    f ≫ multiplication A n = f ^ n := by
  simpa [multiplication] using (MonObj.comp_pow (𝟙 A) n f)

/-- The actual identity section of the group scheme. -/
abbrev identitySection : (𝟙_ (PrimeFieldScheme p)).left ⟶ A.left :=
  (η[A]).left

/-- Actual n-torsion as the fibre of multiplication at the group identity. -/
abbrev torsion (n : ℕ) : Scheme.{0} :=
  pullback (multiplication A n).left (identitySection A)

/-- Frobenius kernel as its actual scheme-theoretic identity fibre. -/
abbrev frobeniusKernel : Scheme.{0} :=
  pullback (primeFieldFrobenius p A).left (identitySection A)

/-- Actual finite-flat Verschiebung with both F/V normalization equations. -/
structure VerschiebungData (g : ℕ) where
  /-- The geometric V morphism over the actual prime field. -/
  hom : A ⟶ A
  /-- V respects the internal group operations. -/
  [groupHom : IsMonHom hom]
  /-- F followed by V is actual group multiplication by p. -/
  frobenius_then : primeFieldFrobenius p A ≫ hom = multiplication A p
  /-- V followed by F is the same actual multiplication. -/
  then_frobenius : hom ≫ primeFieldFrobenius p A = multiplication A p
  /-- V is finite. -/
  [finite : IsFinite hom.left]
  /-- V is flat. -/
  [flat : Flat hom.left]
  /-- Its rank is the geometric degree p^g at every actual scheme point. -/
  degree : ∀ x : A.left, hom.left.finrank x = p ^ g

attribute [instance] VerschiebungData.groupHom VerschiebungData.finite
  VerschiebungData.flat

namespace VerschiebungData

variable {A} {g : ℕ} (V : VerschiebungData A g)

/-- The actual identity fibre of V. -/
abbrev kernel : Scheme.{0} := pullback V.hom.left (identitySection A)

/-- The factorization sends actual p-torsion into the V-kernel. -/
def torsionToKernel : torsion A p ⟶ V.kernel :=
  pullback.lift
    (pullback.fst (multiplication A p).left (identitySection A) ≫
      (primeFieldFrobenius p A).left)
    (pullback.snd (multiplication A p).left (identitySection A)) (by
      rw [Category.assoc,
        ← Over.comp_left, V.frobenius_then]
      exact pullback.condition)

omit [IsCommMonObj A] in
/-- On the ambient variety this is precisely the geometric Frobenius map. -/
theorem torsionToKernel_fst :
    V.torsionToKernel ≫ pullback.fst V.hom.left (identitySection A) =
      pullback.fst (multiplication A p).left (identitySection A) ≫
        (primeFieldFrobenius p A).left :=
  pullback.lift_fst _ _ _

omit [IsCommMonObj A] in
/-- The normalized V is unique whenever the actual Frobenius is epimorphic. -/
theorem hom_unique (W : VerschiebungData A g)
    [Epi (primeFieldFrobenius p A)] : V.hom = W.hom :=
  (cancel_epi (primeFieldFrobenius p A)).mp
    (V.frobenius_then.trans W.frobenius_then.symm)

end VerschiebungData

end MathlibExt.AlgebraicGeometry.AbelianVerschiebung
