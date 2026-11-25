/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FourierMukai
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual geometric data for global derived self-intersection formality

The object is Li* Ri_* O_X for an actual closed immersion. Its conormal
sheaf is the actual pullback of the kernel O_Y → i_* O_X. A first
infinitesimal neighborhood is pinned by its actual local ring maps and
the square of the kernel ideal, and extension means an actual finite
locally free sheaf (Mathlib's `IsLocallyFree` and `IsFiniteType`) with an
actual reduction isomorphism. The formal target is the
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
open FourierMukai

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The actual ideal sheaf `I` of a closed immersion: the kernel of `𝒪_Y ⟶ i_* 𝒪_X`. -/
abbrev idealModule {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] : Y.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)

/-- The actual conormal sheaf `I/I²` of a closed immersion, computed as `i* I`. -/
abbrev conormalModule {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] : X.Modules :=
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

/-- Actual extension of the conormal sheaf over that first neighborhood: a finite locally
free sheaf on the thickening whose restriction to `X` is the conormal sheaf. (The conormal
sheaf is then itself finite locally free.) -/
structure ConormalExtension {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] where
  /-- The first infinitesimal neighborhood. -/
  neighborhood : FirstNeighborhood i
  /-- The extending sheaf on the thickening. -/
  bundle : neighborhood.thickening.Modules
  /-- It is locally free. -/
  locallyFree : SheafOfModules.IsLocallyFree.{u} (R := neighborhood.thickening.ringCatSheaf) bundle
  /-- It is of finite type. -/
  finiteType : SheafOfModules.IsFiniteType.{u} (R := neighborhood.thickening.ringCatSheaf) bundle
  /-- Its restriction to `X` is the conormal sheaf. -/
  restriction : (Scheme.Modules.pullback neighborhood.reduction).obj bundle ≅ conormalModule i

variable [HasDerivedPullbacks.{u}] [HasDerivedPushforwards.{u}]

/-- The actual derived self-intersection structure module `Li^* Ri_* 𝒪_X` of a closed
immersion (`𝒪_X` is `SheafOfModules.unit X.ringCatSheaf`). -/
def selfIntersection {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] : D X :=
  (derivedPullback i).obj ((derivedPushforward i).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)))

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
