/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ReducedCriticalHessianModels
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles

/-!
# Hessian-normalized canonical-line candidates on the actual reduction

The local target is literally i* K_U squared, with K_U the exterior
power of the actual cotangent sheaf. The source's determinant transition
is fixed on all affine frames by det(q) times the squared exact-sequence
wedge coefficient. The global line comparisons use the actual open
pullbacks and their native composition maps.

These result types assume no chart-gluing or canonical-line existence
theorem. Construction, independence, gluing and uniqueness are Wanted
outputs. All constant-rank smooth affine refinements are tested; arbitrary
smooth charts are covered by those Zariski refinements.

Reference: Joyce, arXiv:1304.4508v3, Definition 2.26, Theorem 2.28
and Definition 2.31. The algebraic field has characteristic different
from two, without a characteristic-zero requirement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CriticalCanonicalLineModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Module
open _root_.AlgebraicGeometry
open CriticalSchemeCharts CriticalFunctionSheafModels CriticalHessianModels
open ReducedCriticalHessianModels SheafExteriorSectionModels
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks
open CoherentCurveLinearSeries CurveVectorBundles AlgebraicLineBundleFamilies
open LineBundleTaskContracts NormalizedModuleTensorMaps GenericSectionMaps

variable {k : Type} [Field k] {X : Over (Spec (.of k))}

def CotangentRank (E : AffineEmbedding X) (m : ℕ) : Prop :=
  IsVectorBundle (forms k (ambient E) 1) m

def ambientCanonical (E : AffineEmbedding X) (m : ℕ) :=
  exteriorSheaf (forms k (ambient E) 1) m

/-- The local target is the literal pullback of K_U squared. -/
def localCanonical (E : AffineEmbedding X) (m : ℕ) :=
  (Scheme.Modules.pullback (toAmbient E)).obj (power (ambientCanonical E m) 2)

variable {E F : AffineCriticalChart X} (r : CriticalAffineRefinement E F)

def largerCanonical (m : ℕ) :=
  (Scheme.Modules.pullback (toAmbient E.toAffineEmbedding ≫ (ambientMap r).left)).obj
    (power (ambientCanonical F.toAffineEmbedding m) 2)

/-- The actual comparison to exterior powers of the pulled cotangent bundle. -/
def squareExteriorView {T U : Scheme.{0}} (f : T ⟶ U) (M : U.Modules) (m : ℕ)
    (V : PullbackExterior f) (P : PullbackPowers f) :
    (Scheme.Modules.pullback f).obj (power (exteriorSheaf M m) 2) ≅
      power (exteriorSheaf ((Scheme.Modules.pullback f).obj M) m) 2 :=
  (P.comparison 2).app (exteriorSheaf M m) ≪≫
    (powerFunctor T 2).mapIso (V.comparison M m)

/-- The local squared wedge uses the actual unit and recursive tensor power. -/
def squareSection {T : Scheme.{0}} (M : T.Modules) (W : T.Opens) (a : Γ(M,W)) :
    Γ(power M 2,W) :=
  pureTensorSection T (power M 1) M W
    (pureTensorSection T (structureModule T) M W (1 : Γ(T,W)) a) a

variable (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))
  (P : DualPrecomposition (chartCotangentMap r D)) (Q : HessianForm r D P)
  (m n : ℕ)

/-- A transition is fixed on every actual exact-sequence frame by (2.27). -/
structure HessianTransition where
  reducedDual : DualPrecomposition (cotangentMap r D)
  normal : NormalReindex r D P reducedDual
  tensor : PullbackTensor (toDomain E.toAffineEmbedding)
  conormal : ConormalData r D reducedDual
  normal_rank : IsVectorBundle (ReducedCriticalHessianModels.normal r D reducedDual) n
  sourceExterior : PullbackExterior (toAmbient E.toAffineEmbedding)
  sourcePowers : PullbackPowers (toAmbient E.toAffineEmbedding)
  targetExterior : PullbackExterior (toAmbient E.toAffineEmbedding ≫ (ambientMap r).left)
  targetPowers : PullbackPowers (toAmbient E.toAffineEmbedding ≫ (ambientMap r).left)
  iso : localCanonical E.toAffineEmbedding m ≅ largerCanonical r (m + n)
  normalized : ∀ (W : (reducedOpen E.toAffineEmbedding).toScheme.Opens)
    (_affine : IsAffineOpen W) (C : DeterminantFrame r D conormal m n W),
    iso.hom.app W
      ((squareExteriorView (toAmbient E.toAffineEmbedding)
        (forms k (ambient E.toAffineEmbedding) 1) m sourceExterior sourcePowers).inv.app W
        (squareSection (exteriorSheaf (smallCotangent E.toAffineEmbedding) m) W
          (wedgeSection (smallCotangent E.toAffineEmbedding) m W C.small))) =
    transitionCoefficient r D Q normal tensor C •
      ((squareExteriorView (toAmbient E.toAffineEmbedding ≫ (ambientMap r).left)
        (forms k (ambient F.toAffineEmbedding) 1) (m + n) targetExterior targetPowers).inv.app W
        (squareSection (exteriorSheaf (largeCotangent r) (m + n)) W
          (wedgeSection (largeCotangent r) (m + n) W C.large)))

theorem reducedLe (r : CriticalAffineRefinement E F) :
    reducedOpen E.toAffineEmbedding ≤ reducedOpen F.toAffineEmbedding := by
  intro x hx
  exact r.domain_le hx

def reducedMap : (reducedOpen E.toAffineEmbedding).toScheme ⟶
    (reducedOpen F.toAffineEmbedding).toScheme :=
  (reduction X.left).homOfLE (reducedLe r)

theorem reducedMap_toDomain : reducedMap r ≫ toDomain F.toAffineEmbedding =
    toDomain E.toAffineEmbedding ≫ X.left.homOfLE r.domain_le := by
  apply (cancel_mono F.domain.ι).mp
  dsimp only [toDomain, reducedMap]
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

theorem reducedMap_toAmbient : reducedMap r ≫ toAmbient F.toAffineEmbedding =
    toAmbient E.toAffineEmbedding ≫ (ambientMap r).left := by
  dsimp only [toAmbient]
  rw [← Category.assoc, reducedMap_toDomain, Category.assoc, ← r.embedding_square]
  exact (Category.assoc _ _ _).symm

/-- Restricting the other chart comparison uses only the native pullback compositions. -/
def restrictedComparison (L : (reduction X.left).Modules) (d : ℕ)
    (c : (Scheme.Modules.pullback (reducedOpen F.toAffineEmbedding).ι).obj L ≅
      localCanonical F.toAffineEmbedding d) :
    (Scheme.Modules.pullback (reducedOpen E.toAffineEmbedding).ι).obj L ⟶ largerCanonical r d :=
  (Scheme.Modules.pullbackCongr ((reduction X.left).homOfLE_ι (reducedLe r))).inv.app L ≫
    (Scheme.Modules.pullbackComp (reducedMap r) (reducedOpen F.toAffineEmbedding).ι).inv.app L ≫
      (Scheme.Modules.pullback (reducedMap r)).map c.hom ≫
        (Scheme.Modules.pullbackComp (reducedMap r) (toAmbient F.toAffineEmbedding)).hom.app
          (power (ambientCanonical F.toAffineEmbedding d) 2) ≫
        (Scheme.Modules.pullbackCongr (reducedMap_toAmbient r)).hom.app
          (power (ambientCanonical F.toAffineEmbedding d) 2)

variable {B : CriticalSheafModel X} {R : FunctionRestriction (reductionArrow X)}
  {Z : ZeroCriticalSheafModel B R} (S : DCriticalStructure B R Z)

/-- The global line is characterized by the actual chart squares and fixed Hessian maps.
No internal chart-transition coherence is assumed as background. -/
structure CanonicalLineCandidate where
  line : (reduction X.left).Modules
  isLine : IsLineBundle line
  comparison : ∀ (E : AffineCriticalChart X) (_compatible : CompatibleChart S E)
    (m : ℕ) (_rank : CotangentRank E.toAffineEmbedding m),
    (Scheme.Modules.pullback (reducedOpen E.toAffineEmbedding).ι).obj line ≅
      localCanonical E.toAffineEmbedding m
  transition : ∀ (E F : AffineCriticalChart X)
    (hE : CompatibleChart S E) (hF : CompatibleChart S F) (m n : ℕ)
    (rankE : CotangentRank E.toAffineEmbedding m)
    (rankF : CotangentRank F.toAffineEmbedding (m + n)) (r : CriticalAffineRefinement E F),
    ∃ (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))
      (P : DualPrecomposition (chartCotangentMap r D)) (Q : HessianForm r D P)
      (J : HessianTransition r D P Q m n),
      (comparison E hE m rankE).hom ≫ J.iso.hom =
        restrictedComparison r line (m + n) (comparison F hF (m + n) rankF)

/-- The canonical isomorphism preserves the full chart comparison, not only fibres. -/
structure CanonicalLineIso (A C : CanonicalLineCandidate S) where
  iso : A.line ≅ C.line
  comparison : ∀ (E : AffineCriticalChart X) (hE : CompatibleChart S E)
    (m : ℕ) (rank : CotangentRank E.toAffineEmbedding m),
    (Scheme.Modules.pullback (reducedOpen E.toAffineEmbedding).ι).map iso.hom ≫
      (C.comparison E hE m rank).hom = (A.comparison E hE m rank).hom

/-- Every scheme-valued fibre comparison is pulled from the same full chart isomorphism. -/
def chartFibreComparison (C : CanonicalLineCandidate S) (E : AffineCriticalChart X)
    (hE : CompatibleChart S E) (m : ℕ) (rank : CotangentRank E.toAffineEmbedding m)
    {T : Scheme.{0}} (x : T ⟶ (reducedOpen E.toAffineEmbedding).toScheme) :
    (Scheme.Modules.pullback (x ≫ (reducedOpen E.toAffineEmbedding).ι)).obj C.line ≅
      (Scheme.Modules.pullback (x ≫ toAmbient E.toAffineEmbedding)).obj
        (power (ambientCanonical E.toAffineEmbedding m) 2) :=
  ((Scheme.Modules.pullbackComp x (reducedOpen E.toAffineEmbedding).ι).app C.line).symm ≪≫
    (Scheme.Modules.pullback x).mapIso (C.comparison E hE m rank) ≪≫
      (Scheme.Modules.pullbackComp x (toAmbient E.toAffineEmbedding)).app
        (power (ambientCanonical E.toAffineEmbedding m) 2)

/-- Orientation is a square root of this particular canonical line on Xred. -/
structure Orientation (C : CanonicalLineCandidate S) where
  line : (reduction X.left).Modules
  isLine : IsLineBundle line
  square : power line 2 ≅ C.line

end MathlibExt.AlgebraicGeometry.CriticalCanonicalLineModels
