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
# Candidate compactified Poincaré kernels

`PoincareKernelCandidate` collects the data of a normalized Poincaré-type sheaf `P`
on `J̄ × J̄` for a fine compactified Jacobian `J̄`: its line-bundle locus is
determined at every geometric point by the universal curve sheaf, `P` is
given on `J̄ × J` (`J` the line-bundle locus) by the universal family of a
Picard-zero representative of `J̄` along a classifying map `beta`, it is
symmetric, invertible on `(J̄ × J) ∪ (J × J̄)`, and it is the pushforward of its
restriction there.

These conditions do **not** determine `P`: they do not fix which family of line
bundles on `J̄` corresponds to a line bundle on the curve. For instance, on a
smooth elliptic curve the constant `beta` with `P = 𝒪` satisfies all of them.
The canonical Poincaré sheaf is the candidate whose restriction to `J × J̄` is
Arinkin's determinant-of-cohomology family [Arinkin, (1.1)]
`P_{(L, F)} = det RΓ(L ⊗ F) ⊗ det RΓ(𝒪_C) ⊗ det RΓ(L)⁻¹ ⊗ det RΓ(F)⁻¹`;
that normalization needs relative determinants of cohomology and is not
encoded here. Statements about the Poincaré sheaf should therefore assert the
existence of a candidate with the properties below, not properties of every
candidate.

Arinkin's theorems are separate predicates:
`PoincareKernelCandidate.Properties` (density of the line-bundle locus, the
autoduality isomorphism `J ≅ Pic⁰(J̄)`, depth and flatness over both factors)
and `PoincareKernelCandidate.IsAutodual` (the two inverse-kernel identities).
Derived operators are explicit canonically characterized inputs. The
identities concern actual coherent kernel objects, and assert no equivalence
on arbitrary non-QCoh sheaves.

Sources: Arinkin, *Autoduality of compactified Jacobians for curves with
plane singularities*, (1.1) and Theorems A--C; Melo--Rapagnetta--Viviani,
*Fourier--Mukai and autoduality for compactified Jacobians II*, §§4--6;
Esteves--Gagné--Kleiman, *Autoduality of the compactified Jacobian*.
-/

namespace MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry Opposite
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open _root_.MathlibExt.AlgebraicGeometry.PointedPicardFamilies
open _root_.MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

universe u

attribute [local instance] HasDerivedCategory.standard FineCompactifiedJacobian.proper

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
  IsFiniteTypeQuasicoherent P ∧ ∀ (U : X.Opens), IsAffineOpen U →
    ∀ (p : Ideal Γ(X, U)) (hp : p.IsMaximal),
      letI : p.IsMaximal := hp
      (p.depth (ModuleCat.of Γ(X, U) Γ(P, U)) : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime p)

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

/-- Candidate data for the normalized compactified Poincaré sheaf on `J̄ × J̄`:
its line-bundle locus, an open family classified by a map to Picard zero of
`J̄`, symmetry and extension from the big open. These data do not single out
Arinkin's sheaf (see the module docstring); its geometric properties and the
autoduality identities are the separate predicates `Properties` and
`IsAutodual`. -/
structure PoincareKernelCandidate {k : Type u} [Field k] [IsAlgClosed k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    [TorsionFreeRestrictions C.left] (q : Polarization C.left) (s : SmoothMarking C)
    (M : FineCompactifiedJacobian C q s) where
  /-- The canonical product/fiber-product comparison is pinned on projections. -/
  productComparison : (prod M.J M.J).left ≅ pullback M.J.hom M.J.hom
  fstComparison : productComparison.hom ≫ pullback.fst M.J.hom M.J.hom =
    (prod.fst : prod M.J M.J ⟶ M.J).left
  sndComparison : productComparison.hom ≫ pullback.snd M.J.hom M.J.hom =
    (prod.snd : prod M.J M.J ⟶ M.J).left
  /-- The point of `J̄` parametrizing the structure sheaf of the curve. -/
  origin : 𝟙_ (Over (Spec (.of k))) ⟶ M.J
  originSheaf :
    Nonempty ((Scheme.Modules.pullback (pointSection C M.J origin).left).obj M.F ≅
      structureModule C.left)
  /-- The line-bundle locus. A geometric point lies in it exactly when the
  universal sheaf restricted to the curve fibre over that point is
  invertible; since every point of `J̄` underlies a geometric point, this
  determines the open set. -/
  lineOpen : M.J.left.Opens
  lineLocus : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ M.J.left),
    p ⁻¹ᵁ lineOpen = ⊤ ↔
      IsLineBundle ((Scheme.Modules.pullback
        (pullback.fst (prod.snd : prod C M.J ⟶ M.J).left p)).obj M.F)
  /-- `H⁰(J̄, 𝒪) = k`, so that `J̄` has a Picard-zero model. -/
  [constantSections : HasConstantGlobalSections M.J.hom]
  /-- Picard zero of the compactified Jacobian, with its actual universal family. -/
  picard : PicardZeroModel M.J origin
  /-- The classifying map of the restricted family; `Properties.betaIso`
  states that it is an isomorphism. -/
  beta : Over.mk (lineOpen.ι ≫ M.J.hom) ⟶ picard.J
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
  /-- The internal dual of `P`, fixed by its universal property. -/
  dual : SheafDual P

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Over (Spec (.of k))}
  [IsProperCurve C.hom] [HasConstantGlobalSections C.hom] [TorsionFreeRestrictions C.left]
  {q : Polarization C.left} {s : SmoothMarking C} {M : FineCompactifiedJacobian C q s}

/-- Arinkin's geometric properties of the Poincaré sheaf, for a candidate: the
line-bundle locus is dense and identified with `Pic⁰(J̄)` by `beta`, and `P` is
maximal Cohen--Macaulay and flat over both factors (Arinkin, Theorem A;
Esteves--Gagné--Kleiman). Not every candidate has them. -/
structure PoincareKernelCandidate.Properties (K : PoincareKernelCandidate C q s M) : Prop where
  dense : Dense (K.lineOpen : Set M.J.left)
  betaIso : IsIso K.beta
  mcm : IsClosedPointMCM K.P
  flatFirst : IsFlatOver (prod.fst : prod M.J M.J ⟶ M.J).left K.P
  flatSecond : IsFlatOver (prod.snd : prod M.J M.J ⟶ M.J).left K.P

variable [FourierMukai.HasDerivedPullbacks.{u}]
  [FourierMukai.HasDerivedPushforwards.{u}] [FourierMukai.HasDerivedTensors.{u}]

/-- Fourier--Mukai autoduality of a candidate: `P` and `P^∨[g]` are mutually
inverse kernels (Arinkin, Theorem C, for the Poincaré sheaf). -/
def PoincareKernelCandidate.IsAutodual (K : PoincareKernelCandidate C q s M) : Prop :=
  Nonempty
    (FourierMukai.convolution M.J.hom M.J.hom M.J.hom
      (kernelOfSheaf M.J K.productComparison K.P)
      ((kernelOfSheaf M.J K.productComparison K.dual.dual)⟦(genus C.hom : ℤ)⟧) ≅
        diagonalKernel M.J) ∧
  Nonempty
    (FourierMukai.convolution M.J.hom M.J.hom M.J.hom
      ((kernelOfSheaf M.J K.productComparison K.dual.dual)⟦(genus C.hom : ℤ)⟧)
      (kernelOfSheaf M.J K.productComparison K.P) ≅ diagonalKernel M.J)

end MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels
