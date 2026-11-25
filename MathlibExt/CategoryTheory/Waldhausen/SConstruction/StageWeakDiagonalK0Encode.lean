/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Decode
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalFundamentalCommutativity

/-!
# Combinatorial Waldhausen K-zero encode

The based weak-diagonal fundamental group is commutative by an explicit
theorem, without a global commutative-group instance.  A named non-instance
`AddCommGroup` witness on its additive type tag lets the universal property of
Waldhausen K-zero map an object class to its canonical object-edge generator.
Weak-equivalence and cofiber relations come from the landed object-edge
simplices, with the reversed categorical-endomorphism factor order corrected
explicitly before applying `K0.lift`.

This file defines only the additive encode and its generator formula.  It
makes no inverse, equivalence, realization, topology, additivity, spectrum,
or Q/S claim and installs no global algebraic instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Explicit additive commutative-group structure on the additive type tag of
the based fundamental group.  This declaration is deliberately not an
installed typeclass; consumers opt in locally. -/
@[instance_reducible]
noncomputable def stageWeakDiagonalFundamentalAddCommGroup :
    AddCommGroup (Additive (stageWeakDiagonalFundamentalGroup C)) :=
  { (inferInstance :
      AddGroup (Additive (stageWeakDiagonalFundamentalGroup C))) with
    add_comm := fun f g => by
      change f.toMul * g.toMul = g.toMul * f.toMul
      exact stageWeakDiagonalFundamentalGroup_mul_comm C f.toMul g.toMul }

/-- Additive object generator attached to a canonical skeleton
representative. -/
noncomputable def stageWeakDiagonalK0EncodeGenerator
    (s : Skeleton C) : Additive (stageWeakDiagonalFundamentalGroup C) :=
  Additive.ofMul
    (stageWeakDiagonalObjectGenerator C ((fromSkeleton C).obj s))

/-- A canonical skeleton representative gives the same object generator as
the represented object. -/
@[simp]
theorem stageWeakDiagonalK0EncodeGenerator_toSkeleton (X : C) :
    stageWeakDiagonalK0EncodeGenerator C (toSkeleton X) =
      Additive.ofMul (stageWeakDiagonalObjectGenerator C X) := by
  let e := fromSkeletonToSkeletonIso X
  have he : IsWeakEquivalence e.hom :=
    (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso e.hom
  change stageWeakDiagonalObjectGenerator C
      ((fromSkeleton C).obj (toSkeleton X)) =
    stageWeakDiagonalObjectGenerator C X
  apply CategoryTheory.End.ext
  simpa only [stageWeakDiagonalObjectGenerator] using
      (stageWeakDiagonalObjectEdge_homMk_eq_of_weakEquivalence C e.hom he)

/-- The skeleton-representative generator is invariant under weak
equivalences.  This is the weak relation supplied to `K0.lift`. -/
theorem stageWeakDiagonalK0Encode_weak
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    stageWeakDiagonalK0EncodeGenerator C (toSkeleton X) =
      stageWeakDiagonalK0EncodeGenerator C (toSkeleton Y) := by
  rw [stageWeakDiagonalK0EncodeGenerator_toSkeleton,
    stageWeakDiagonalK0EncodeGenerator_toSkeleton]
  change stageWeakDiagonalObjectGenerator C X =
    stageWeakDiagonalObjectGenerator C Y
  apply CategoryTheory.End.ext
  simpa only [stageWeakDiagonalObjectGenerator] using
    (stageWeakDiagonalObjectEdge_homMk_eq_of_weakEquivalence C f hf)

/-- The skeleton-representative generator is additive on cofiber sequences.
The proof explicitly corrects the reversed categorical-endomorphism order. -/
theorem stageWeakDiagonalK0Encode_cofiber
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    stageWeakDiagonalK0EncodeGenerator C (toSkeleton Y) =
      stageWeakDiagonalK0EncodeGenerator C (toSkeleton X) +
        stageWeakDiagonalK0EncodeGenerator C (toSkeleton Z) := by
  rw [stageWeakDiagonalK0EncodeGenerator_toSkeleton,
    stageWeakDiagonalK0EncodeGenerator_toSkeleton,
    stageWeakDiagonalK0EncodeGenerator_toSkeleton]
  change stageWeakDiagonalObjectGenerator C Y =
    stageWeakDiagonalObjectGenerator C X *
      stageWeakDiagonalObjectGenerator C Z
  exact
    (stageWeakDiagonalObjectGenerator_quotient_mul_source C f g hSeq).symm.trans
      (stageWeakDiagonalObjectGenerator_comm C Z X)

/-- Additive encode from Waldhausen K-zero to the combinatorial based
fundamental group. -/
noncomputable def stageWeakDiagonalK0Encode :
    WaldhausenKTheory.K0 C →+
      Additive (stageWeakDiagonalFundamentalGroup C) := by
  letI : AddCommGroup (Additive (stageWeakDiagonalFundamentalGroup C)) :=
    stageWeakDiagonalFundamentalAddCommGroup C
  exact WaldhausenKTheory.K0.lift
    (stageWeakDiagonalK0EncodeGenerator C)
    (stageWeakDiagonalK0Encode_weak C)
    (stageWeakDiagonalK0Encode_cofiber C)

/-- The encode sends the K-zero class of an object to its canonical
weak-diagonal object-edge generator. -/
@[simp]
theorem stageWeakDiagonalK0Encode_mk (X : C) :
    stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk X) =
      Additive.ofMul (stageWeakDiagonalObjectGenerator C X) := by
  let _ : AddCommGroup (Additive (stageWeakDiagonalFundamentalGroup C)) :=
    stageWeakDiagonalFundamentalAddCommGroup C
  change WaldhausenKTheory.K0.lift
      (stageWeakDiagonalK0EncodeGenerator C)
      (stageWeakDiagonalK0Encode_weak C)
      (stageWeakDiagonalK0Encode_cofiber C)
      (WaldhausenKTheory.K0.mk X) = _
  rw [WaldhausenKTheory.K0.lift_mk]
  exact stageWeakDiagonalK0EncodeGenerator_toSkeleton C X

end CategoryTheory.Waldhausen.SConstruction

end
