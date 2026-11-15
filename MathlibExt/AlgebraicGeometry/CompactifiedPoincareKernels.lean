/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import MathlibExt.AlgebraicGeometry.FourierMukai
public import MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

@[expose] public noncomputable section

/-!
# Normalized compactified Poincaré kernels

This interface specifies the line-bundle locus by the actual universal
curve sheaf, fixes the open Poincaré family through a Picard-zero
representative, and records its extension, depth, factor flatness, dual
and two inverse-kernel identities. Derived operators are explicit
canonically characterized inputs. The identities concern actual coherent
kernel objects, and assert no equivalence on arbitrary non-QCoh sheaves.

Sources: Arinkin, *Autoduality of compactified Jacobians for curves with
plane singularities*, Theorems A--C; Melo--Rapagnetta--Viviani, *Fourier--
Mukai and autoduality for compactified Jacobians II*, §§4--6.
-/

namespace MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry Opposite
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open _root_.MathlibExt.AlgebraicGeometry.PointedPicardFamilies
open _root_.MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The actual ordinary tensor map, via presheaf tensor and sheafification. -/
def moduleTensorMap {X : Scheme.{u}} {L L' M M' : X.Modules}
    (f : L ⟶ L') (g : M ⟶ M') : moduleTensor X L M ⟶ moduleTensor X L' M' :=
  let P := PresheafOfModulesOfCommRing.{u} X.sheaf.obj
  let U := SheafOfModules.forget X.ringCatSheaf
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (((curriedTensor P).map (U.map f)).app (U.obj M) ≫
      ((curriedTensor P).obj (U.obj L')).map (U.map g))

/-- Internal Hom into the structure sheaf, fixed by its actual evaluation. -/
structure SheafDual {X : Scheme.{u}} (P : X.Modules) where
  dual : X.Modules
  evaluation : moduleTensor X P dual ⟶ structureModule X
  universal : ∀ (N : X.Modules) (f : moduleTensor X P N ⟶ structureModule X),
    ∃! g : N ⟶ dual, moduleTensorMap (𝟙 P) g ≫ evaluation = f

/-- The closed-point maximal Cohen--Macaulay depth condition on affine charts. -/
def IsClosedPointMCM {X : Scheme.{u}} (P : X.Modules) : Prop :=
  IsCoherent P ∧ ∀ (U : X.Opens), IsAffineOpen U →
    ∀ (p : Ideal Γ(X, U)) (hp : p.IsMaximal),
      letI : p.IsMaximal := hp
      (p.depth (ModuleCat.of Γ(X, U) Γ(P, U)) : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime p)

/-- Actual factorization of a parameter point through an open subscheme. -/
def FactorsThrough {k : Type u} [Field k] (J : Over (Spec (.of k)))
    (U : J.left.Opens) (x : 𝟙_ (Over (Spec (.of k))) ⟶ J) : Prop :=
  ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk (U.ι ≫ J.hom),
    y ≫ Over.homMk U.ι = x

/-- The union where at least one parameter represents a line bundle. -/
def bigOpen {k : Type u} [Field k] (J : Over (Spec (.of k)))
    (U : J.left.Opens) : (prod J J).left.Opens :=
  (prod.fst : prod J J ⟶ J).left ⁻¹ᵁ U ⊔
    (prod.snd : prod J J ⟶ J).left ⁻¹ᵁ U

/-- Transport an actual sheaf to the scheme fiber-product kernel category. -/
def kernelOfSheaf {k : Type u} [Field k] (J : Over (Spec (.of k)))
    (e : (prod J J).left ≅ pullback J.hom J.hom) (P : (prod J J).left.Modules) :
    FourierMukai.D (pullback J.hom J.hom) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((Scheme.Modules.pullback e.inv).obj P)

/-- The actual relative diagonal structure-sheaf kernel. -/
def diagonalKernel {k : Type u} [Field k] (J : Over (Spec (.of k))) :
    FourierMukai.D (pullback J.hom J.hom) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((Scheme.Modules.pushforward (pullback.lift (𝟙 J.left) (𝟙 J.left) rfl)).obj
      (structureModule J.left))

variable [FourierMukai.HasDerivedPullbacks.{u}]
  [FourierMukai.HasDerivedPushforwards.{u}] [FourierMukai.HasDerivedTensors.{u}]

/-- A normalized extension together with the requested inverse-kernel proofs. -/
structure PoincareKernelModel {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [TorsionFreeRestrictions C.left]
    (q : Polarization C.left) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) where
  /-- The canonical product/fiber-product comparison is pinned on projections. -/
  productComparison : (prod M.J M.J).left ≅ pullback M.J.hom M.J.hom
  fstComparison : productComparison.hom ≫ pullback.fst M.J.hom M.J.hom =
    (prod.fst : prod M.J M.J ⟶ M.J).left
  sndComparison : productComparison.hom ≫ pullback.snd M.J.hom M.J.hom =
    (prod.snd : prod M.J M.J ⟶ M.J).left
  origin : 𝟙_ (Over (Spec (.of k))) ⟶ M.J
  originSheaf :
    Nonempty ((Scheme.Modules.pullback (pointSection C M.J origin).left).obj M.F ≅
      structureModule C.left)
  lineOpen : M.J.left.Opens
  lineLocus : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ M.J,
    FactorsThrough M.J lineOpen x ↔
      IsLineBundle ((Scheme.Modules.pullback (pointSection C M.J x).left).obj M.F)
  dense : Dense (lineOpen : Set M.J.left)
  /-- Picard zero of the compactified Jacobian, with its actual universal family. -/
  picard : PicardZeroModel M.J origin
  beta : Over.mk (lineOpen.ι ≫ M.J.hom) ⟶ picard.J
  [betaIso : IsIso beta]
  P : (prod M.J M.J).left.Modules
  normalized : IsNormalized M.J M.J origin P
  symmetric : Nonempty
    ((Scheme.Modules.pullback
      (prod.lift (prod.snd : prod M.J M.J ⟶ M.J)
        (prod.fst : prod M.J M.J ⟶ M.J)).left).obj P ≅ P)
  /-- The open family is identified with the representing Picard family. -/
  openFamily : Nonempty
    ((Scheme.Modules.pullback
      (prod.map (𝟙 M.J) (Over.homMk lineOpen.ι)).left).obj P ≅
      familyPullback M.J picard.J (Over.mk (lineOpen.ι ≫ M.J.hom)) picard.P beta)
  bigLineBundle : IsLineBundle ((Scheme.Modules.pullback (bigOpen M.J lineOpen).ι).obj P)
  extension : Nonempty
    (P ≅ (Scheme.Modules.pushforward (bigOpen M.J lineOpen).ι).obj
      ((Scheme.Modules.pullback (bigOpen M.J lineOpen).ι).obj P))
  mcm : IsClosedPointMCM P
  flatFirst : IsFlatOver (prod.fst : prod M.J M.J ⟶ M.J).left P
  flatSecond : IsFlatOver (prod.snd : prod M.J M.J ⟶ M.J).left P
  dual : SheafDual P
  /-- These inverse identities are goals carried by the requested constructor. -/
  inverseLeft : Nonempty
    (FourierMukai.convolution M.J.hom M.J.hom M.J.hom
      (kernelOfSheaf M.J productComparison P)
      ((kernelOfSheaf M.J productComparison dual.dual)⟦(genus C.hom : ℤ)⟧) ≅
        diagonalKernel M.J)
  inverseRight : Nonempty
    (FourierMukai.convolution M.J.hom M.J.hom M.J.hom
      ((kernelOfSheaf M.J productComparison dual.dual)⟦(genus C.hom : ℤ)⟧)
      (kernelOfSheaf M.J productComparison P) ≅ diagonalKernel M.J)

end MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels
