/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FourierMukai
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual geometric data for global derived self-intersection formality

The object is Li* Ri_* O_X for an actual closed immersion. Its conormal
sheaf is the actual pullback of the kernel O_Y → i_* O_X. A first
infinitesimal neighborhood is pinned by its actual local ring maps and
the square of the kernel ideal, and extension means an actual vector
bundle with an actual reduction isomorphism. The formal target is the
complex of the object's actual cohomology sheaves, with zero differential.

Source: Arinkin--Căldăraru, *When is the self-intersection of a subvariety
a fibration?*, https://arxiv.org/abs/1007.1671, Theorem 0.7. This packet
asks its underlying derived-object implication. It does not claim a
multiplicative dg/E-infinity comparison. Generic Koszul/exterior Tor
computations and single-degree formality are already covered in Axiom's
regular-sequence and LocallyConcentratedFormality source.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSelfIntersections

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries CurveVectorBundles

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The actual ideal module of a closed immersion. -/
abbrev idealModule {X Y : Scheme.{u}} (i : X ⟶ Y) : Y.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/-- The actual conormal I/I², computed as i*I. -/
abbrev conormalModule {X Y : Scheme.{u}} (i : X ⟶ Y) : X.Modules :=
  (Scheme.Modules.pullback i).obj (idealModule i)

/-- A literal first infinitesimal neighborhood, with the stalk ideals pinned to I². -/
structure FirstNeighborhood {X Y : Scheme.{u}} (i : X ⟶ Y) where
  thickening : Scheme.{u}
  inclusion : thickening ⟶ Y
  reduction : X ⟶ thickening
  [closed_inclusion : IsClosedImmersion inclusion]
  [closed_reduction : IsClosedImmersion reduction]
  reduction_surjective : Function.Surjective reduction
  factorization : reduction ≫ inclusion = i
  kernel_square : ∀ x : X,
    RingHom.ker
      (((Y.presheaf.stalkCongr (.of_eq
        (by simpa using congrArg (fun f : X ⟶ Y ↦ f x) factorization.symm))).hom ≫
          inclusion.stalkMap (reduction x)).hom) =
      RingHom.ker (i.stalkMap x).hom ^ 2

/-- Actual extension of the conormal bundle over that first neighborhood. -/
structure ConormalExtension {X Y : Scheme.{u}} (i : X ⟶ Y) (r : ℕ) where
  neighborhood : FirstNeighborhood i
  bundle : neighborhood.thickening.Modules
  locallyFree : IsVectorBundle bundle r
  restriction : (Scheme.Modules.pullback neighborhood.reduction).obj bundle ≅ conormalModule i

variable [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}]

/-- The actual derived self-intersection structure module. -/
def selfIntersection {X Y : Scheme.{u}} (i : X ⟶ Y) : D X :=
  (derivedPullback i).obj ((derivedPushforward i).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)))

/-- The actual cohomology sheaves of a derived object, assembled with zero differential. -/
def formalCohomologyComplex {X : Scheme.{u}} (M : D X) : CochainComplex X.Modules ℤ where
  X n := (DerivedCategory.homologyFunctor X.Modules n).obj M
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Formality compares to the computed cohomology, not to a free object named a normal model. -/
def IsFormal {X : Scheme.{u}} (M : D X) : Prop :=
  Nonempty (M ≅ DerivedCategory.Q.obj (formalCohomologyComplex M))

end MathlibExt.AlgebraicGeometry.DerivedSelfIntersections
