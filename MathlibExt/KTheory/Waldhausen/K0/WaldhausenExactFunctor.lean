/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import MathlibExt.KTheory.Waldhausen.K0.Basic

/-!
# Waldhausen-exact functoriality of Waldhausen K0

A Waldhausen-exact functor between arbitrary Waldhausen categories induces an
abelian-group homomorphism on Waldhausen `K₀`.  The construction uses the
universal map `WaldhausenKTheory.K0.lift`: weak-equivalence relations are
preserved directly, and cofibration-sequence relations are preserved by
`Functor.IsWaldhausenExact.map_cofibrationSequence`.

The name `mapOfWaldhausenExact` distinguishes this general construction from
the pre-existing `K0.map`, whose interface is specialized to additive exact
functors between standard exact-category Waldhausen structures.

## Main definitions

* `WaldhausenKTheory.K0.mapOfWaldhausenExact`
* `WaldhausenKTheory.K0.mapOfWaldhausenExactGenerator`
* `WaldhausenKTheory.K0.mapOfWaldhausenExact_mk`
* `WaldhausenKTheory.K0.mapOfWaldhausenExact_id`
* `WaldhausenKTheory.K0.mapOfWaldhausenExact_comp`
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace WaldhausenKTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategory C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategory D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [WaldhausenCategory E]

/-- The map on skeleton objects used to construct the map on Waldhausen
`K₀`. -/
noncomputable def K0.mapOfWaldhausenExactGenerator (F : C ⥤ D) :
    Skeleton C → K0 D :=
  fun s ↦ K0.mk (F.obj ((fromSkeleton C).obj s))

/-- The generator map is invariant under weak equivalences. -/
theorem K0.mapOfWaldhausenExactGenerator_weakEquivalence
    (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence (C := C) f) :
    K0.mapOfWaldhausenExactGenerator F (toSkeleton X) =
      K0.mapOfWaldhausenExactGenerator F (toSkeleton Y) := by
  calc
    K0.mapOfWaldhausenExactGenerator F (toSkeleton X) = K0.mk (F.obj X) :=
      K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso X))
    _ = K0.mk (F.obj Y) :=
      K0.mk_eq_of_weakEquivalence (F.map f) (hF.map_weakEquivalence f hf)
    _ = K0.mapOfWaldhausenExactGenerator F (toSkeleton Y) :=
      (K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso Y))).symm

/-- The generator map is additive on cofibration sequences. -/
theorem K0.mapOfWaldhausenExactGenerator_cofibrationSequence
    (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {X Y Z : C} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) i p) :
    K0.mapOfWaldhausenExactGenerator F (toSkeleton Y) =
      K0.mapOfWaldhausenExactGenerator F (toSkeleton X) +
        K0.mapOfWaldhausenExactGenerator F (toSkeleton Z) := by
  calc
    K0.mapOfWaldhausenExactGenerator F (toSkeleton Y) = K0.mk (F.obj Y) :=
      K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso Y))
    _ = K0.mk (F.obj X) + K0.mk (F.obj Z) :=
      K0.mk_eq_of_cofibrationSequence (hF.map_cofibrationSequence hSeq)
    _ = K0.mapOfWaldhausenExactGenerator F (toSkeleton X) +
        K0.mapOfWaldhausenExactGenerator F (toSkeleton Z) :=
      congrArg₂ (· + ·)
        (K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso X))).symm
        (K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso Z))).symm

/-- The group homomorphism on Waldhausen `K₀` induced by a
Waldhausen-exact functor. -/
noncomputable def K0.mapOfWaldhausenExact (F : C ⥤ D)
    (hF : F.IsWaldhausenExact) : K0 C →+ K0 D :=
  K0.lift (K0.mapOfWaldhausenExactGenerator F)
    (K0.mapOfWaldhausenExactGenerator_weakEquivalence F hF)
    (K0.mapOfWaldhausenExactGenerator_cofibrationSequence F hF)

/-- A Waldhausen-exact functor sends the class of an object to the class of
its image. -/
@[simp]
theorem K0.mapOfWaldhausenExact_mk (F : C ⥤ D)
    (hF : F.IsWaldhausenExact) (X : C) :
    K0.mapOfWaldhausenExact F hF (K0.mk X) = K0.mk (F.obj X) := by
  rw [K0.mapOfWaldhausenExact, K0.lift_mk]
  exact K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso X))

/-- The identity functor induces the identity map on Waldhausen `K₀`. -/
@[simp]
theorem K0.mapOfWaldhausenExact_id :
    K0.mapOfWaldhausenExact (Functor.id C) Functor.IsWaldhausenExact.id =
      AddMonoidHom.id (K0 C) := by
  apply K0.hom_ext
  intro X
  simp

/-- Functor composition induces composition of the corresponding maps on
Waldhausen `K₀`, in functor-composition order. -/
theorem K0.mapOfWaldhausenExact_comp (F : C ⥤ D) (G : D ⥤ E)
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    K0.mapOfWaldhausenExact (F ⋙ G) (hF.comp hG) =
      (K0.mapOfWaldhausenExact G hG).comp
        (K0.mapOfWaldhausenExact F hF) := by
  apply K0.hom_ext
  intro X
  simp

end WaldhausenKTheory
