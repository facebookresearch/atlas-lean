/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CriticalHessianModels
public import MathlibExt.AlgebraicGeometry.SheafExteriorSectionModels
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Reduced critical-chart normal sequences and determinant coefficients

The reduction is the actual radical-zero subscheme, restricted to the
actual chart open. Cotangent maps and the pulled Hessian pairing use
native pullback composition and unit maps. Normal reindexing is fixed
by evaluation and the actual cokernel projection. The conormal injection
is the dual of that same projection, on every sheaf section.

The transition coefficient below is det(q) times the square of the
ordered exact-sequence wedge determinant. It uses actual cotangent and
normal frames, rather than a freely chosen transition function.
Reference: Joyce, arXiv:1304.4508v3, Definitions 2.26 and Theorem 2.28.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ReducedCriticalHessianModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Module
open _root_.AlgebraicGeometry
open CriticalSchemeCharts CriticalFunctionSheafModels CriticalHessianModels
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies
open BundleTrace NormalizedModuleTensorMaps GenericSectionMaps
open FiniteCoverLocalComparison SheafExteriorSectionModels

variable {k : Type} [Field k] {X : Over (Spec (.of k))}

def reducedOpen (E : AffineEmbedding X) : (reduction X.left).Opens :=
  reductionMap X.left ⁻¹ᵁ E.domain

def toDomain (E : AffineEmbedding X) : (reducedOpen E).toScheme ⟶ E.domain.toScheme :=
  (reductionMap X.left).resLE E.domain (reducedOpen E) le_rfl

def toAmbient (E : AffineEmbedding X) : (reducedOpen E).toScheme ⟶ (ambient E).left :=
  toDomain E ≫ E.inclusion.left

abbrev smallCotangent (E : AffineEmbedding X) :=
  (Scheme.Modules.pullback (toAmbient E)).obj (forms k (ambient E) 1)

variable {E F : AffineCriticalChart X} (r : CriticalAffineRefinement E F)
  (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))

abbrev largeCotangent :=
  (Scheme.Modules.pullback (toAmbient E.toAffineEmbedding ≫ (ambientMap r).left)).obj
    (forms k (ambient F.toAffineEmbedding) 1)

def smallComparison :
    (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).obj (chartCotangent (E := E)) ≅
      smallCotangent E.toAffineEmbedding :=
  (Scheme.Modules.pullbackComp (toDomain E.toAffineEmbedding) E.inclusion.left).app
    (forms k (ambient E.toAffineEmbedding) 1)

def largeComparison :
    (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).obj (largerCotangent r) ≅
      largeCotangent r :=
  (Scheme.Modules.pullbackComp (toDomain E.toAffineEmbedding)
    (E.inclusion.left ≫ (ambientMap r).left)).app
      (forms k (ambient F.toAffineEmbedding) 1)

/-- The reduced derivative is the pullback of the same native chart derivative. -/
def cotangentMap : largeCotangent r ⟶ smallCotangent E.toAffineEmbedding :=
  (largeComparison r).inv ≫
    (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).map (chartCotangentMap r D) ≫
      (smallComparison (E := E)).hom

abbrev largeTangent := homSheaf (reducedOpen E.toAffineEmbedding).toScheme
  (largeCotangent r) (structureModule (reducedOpen E.toAffineEmbedding).toScheme)

abbrev normal (P : DualPrecomposition (cotangentMap r D)) := cokernel P.map

def projection (P : DualPrecomposition (cotangentMap r D)) :
    largeTangent r ⟶ normal r D P := cokernel.π P.map

/-- The normal comparison has full dual evaluation and cokernel normalization. -/
structure NormalReindex (P : DualPrecomposition (chartCotangentMap r D))
    (P' : DualPrecomposition (cotangentMap r D)) where
  tangent : (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).obj (largerTangent r) ≅
    largeTangent r
  evaluation : ∀ (U : E.domain.toScheme.Opens)
    (W : (reducedOpen E.toAffineEmbedding).toScheme.Opens)
    (h : W ≤ toDomain E.toAffineEmbedding ⁻¹ᵁ U)
    (a : Γ(largerTangent r,U)) (b : Γ(largerCotangent r,U)),
    dualValue (largeCotangent r) W
      (tangent.hom.app W (localPullbackSection (toDomain E.toAffineEmbedding)
        (largerTangent r) U W h a))
      ((largeComparison r).hom.app W (localPullbackSection (toDomain E.toAffineEmbedding)
        (largerCotangent r) U W h b)) =
    ((toDomain E.toAffineEmbedding).appLE U W h).hom (dualValue (largerCotangent r) U a b)
  comparison : (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).obj
    (normalModule r D P) ≅ normal r D P'
  projection_square : tangent.hom ≫ projection r D P' =
    (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).map (normalProjection r D P) ≫
      comparison.hom

/-- The reduced pairing is the actual pullback of the half-Hessian. -/
def pulledPairing {P : DualPrecomposition (chartCotangentMap r D)} (Q : HessianForm r D P)
    {P' : DualPrecomposition (cotangentMap r D)} (N : NormalReindex r D P P')
    (T : PullbackTensor (toDomain E.toAffineEmbedding)) :
    moduleTensor (reducedOpen E.toAffineEmbedding).toScheme (normal r D P') (normal r D P') ⟶
      structureModule (reducedOpen E.toAffineEmbedding).toScheme :=
  LineBundleTaskContracts.tensorMap N.comparison.inv N.comparison.inv ≫
    (T.comparison (normalModule r D P) (normalModule r D P)).inv ≫
      (Scheme.Modules.pullback (toDomain E.toAffineEmbedding)).map Q.pairing ≫
        (pullbackStructureIso (toDomain E.toAffineEmbedding)).hom

abbrev normalDual (P' : DualPrecomposition (cotangentMap r D)) :=
  homSheaf (reducedOpen E.toAffineEmbedding).toScheme (normal r D P')
    (structureModule (reducedOpen E.toAffineEmbedding).toScheme)

/-- The exact conormal injection is the dual of the fixed normal projection. -/
structure ConormalData (P' : DualPrecomposition (cotangentMap r D)) where
  inclusion : normalDual r D P' ⟶ largeCotangent r
  dual_projection : ∀ (W : (reducedOpen E.toAffineEmbedding).toScheme.Opens)
    (b : Γ(normalDual r D P',W)) (v : Γ(largeTangent r,W)),
    dualValue (largeCotangent r) W v (inclusion.app W b) =
      dualValue (normal r D P') W b ((projection r D P').app W v)
  annihilated : inclusion ≫ cotangentMap r D = 0
  [quotient : Epi (cotangentMap r D)]
  [kernel : IsIso (kernel.lift (cotangentMap r D) inclusion annihilated)]

/-- Actual frames of the normal exact sequence; the lift need not split globally. -/
structure DeterminantFrame {P' : DualPrecomposition (cotangentMap r D)}
    (C : ConormalData r D P') (m n : ℕ)
    (W : (reducedOpen E.toAffineEmbedding).toScheme.Opens) where
  small : Basis (Fin m) Γ((reducedOpen E.toAffineEmbedding).toScheme,W)
    Γ(smallCotangent E.toAffineEmbedding,W)
  large : Basis (Fin (m + n)) Γ((reducedOpen E.toAffineEmbedding).toScheme,W)
    Γ(largeCotangent r,W)
  normalBasis : Basis (Fin n) Γ((reducedOpen E.toAffineEmbedding).toScheme,W) Γ(normal r D P',W)
  conormalBasis : Basis (Fin n) Γ((reducedOpen E.toAffineEmbedding).toScheme,W)
    Γ(normalDual r D P',W)
  dual : ∀ i j, dualValue (normal r D P') W (conormalBasis i) (normalBasis j) =
    if i = j then 1 else 0
  lift : Fin m → Γ(largeCotangent r,W)
  lift_eq : ∀ i, (cotangentMap r D).app W (lift i) = small i

def wedgeMatrix {P' : DualPrecomposition (cotangentMap r D)} {C : ConormalData r D P'}
    {m n : ℕ} {W : (reducedOpen E.toAffineEmbedding).toScheme.Opens}
    (F' : DeterminantFrame r D C m n W) :
    Matrix (Fin (m + n)) (Fin (m + n)) Γ((reducedOpen E.toAffineEmbedding).toScheme,W) :=
  fun i j => F'.large.repr
    (Fin.addCases F'.lift (fun a => C.inclusion.app W (F'.conormalBasis a)) j) i

/-- The coefficient of (2.27): det(q) times the squared exact-wedge coefficient. -/
def transitionCoefficient {P : DualPrecomposition (chartCotangentMap r D)}
    (Q : HessianForm r D P) {P' : DualPrecomposition (cotangentMap r D)}
    (N : NormalReindex r D P P') (T : PullbackTensor (toDomain E.toAffineEmbedding))
    {C : ConormalData r D P'} {m n : ℕ}
    {W : (reducedOpen E.toAffineEmbedding).toScheme.Opens}
    (F' : DeterminantFrame r D C m n W) : Γ((reducedOpen E.toAffineEmbedding).toScheme,W) :=
  Matrix.det (fun i j : Fin n =>
    (show Γ((reducedOpen E.toAffineEmbedding).toScheme,W) from
      (pulledPairing r D Q N T).app W
        (pureTensorSection _ _ _ W (F'.normalBasis i) (F'.normalBasis j)))) *
      Matrix.det (wedgeMatrix r D F') ^ 2

end MathlibExt.AlgebraicGeometry.ReducedCriticalHessianModels
