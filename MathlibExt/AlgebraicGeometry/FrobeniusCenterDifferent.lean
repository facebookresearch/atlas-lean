/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
public import MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
public import MathlibExt.AlgebraicGeometry.LogResidueDifferent

/-!
# Actual compatible-center descent and computed F-different

The quotient trace is pinned by the actual ordinary Frobenius base-change
mate and the actual upstairs boundary trace. Epimorphy makes that descended
map unique. The adjoint trace element is computed by the prescribed native
derived adjunction, not supplied as a divisor or functional.

Its rational multiplier is normalized on every section through the actual
O(D) inclusion and Cartier generators. The F-different is then the actual
coefficient formula (D_0-D_N+div(r))/(p^e-1). Canonical data use fixed
dualizing-module references, so no Kähler/separability restriction is hidden.

Compatible quotient construction, finite duality and Cartier/rationalization
are source-complete integration inputs. Recovering/gluing the same boundary
across admissible exponents and comparison to geometric F-purity remain
separate provider/proof boundaries.

Source: Schwede arXiv0901.1154v4, §3, Theorem 5.2 and Corollary 6.9;
Tau compatible quotients and Axiom finite duality at the cited pinned
revisions in the supporting completed modules.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.RationalFunctionModules
open MathlibExt.AlgebraicGeometry.LogResidueDifferent

attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] {n d : ℕ}
  {V : NormalVariety k n} {W : NormalVariety k d}
  [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
  [∀ q : PrimePoint W, IsDiscreteValuationRing (LocalRing W q.val)]
  [HasDerivedPushforwards.{0}]
  (C : CanonicalWeilReference V) (D : RealWeil V) (p e : ℕ) [Fact p.Prime]
  (hV : IsInCharacteristic V.X.left p) (hW : IsInCharacteristic W.X.left p)
  [(derivedPushforward (iterated V.X.left p hV e)).IsLeftAdjoint]
  [(derivedPushforward (iterated W.X.left p hW e)).IsLeftAdjoint]
  (F : FrobeniusIdentification V C p e hV) (I : BoundaryIndex V C p e D)
  (i : W.X ⟶ V.X)
  (comm : i.left ≫ iterated V.X.left p hV e = iterated W.X.left p hW e ≫ i.left)

abbrev sourceModule :=
  DivisorialModuleSheaves.sheaf V (boundaryTwist V C D p e)

/-- Descent of the boundary trace to $W$. Let $V$ and $W$ be normal varieties over $k$ in
characteristic $p$, with $p$ prime and with local rings at points of codimension one that are
discrete valuation rings; let $F^e$ be the $e$-th iterate of absolute Frobenius, with derived direct
image along $F^e$ (for the derived direct images given by `HasDerivedPushforwards`) having a right
adjoint on $V$ and on $W$; and let $i : W \to V$ be a $k$-morphism with
$F^e_V \circ i = i \circ F^e_W$. Let $\mathcal{M}$ be the divisorial sheaf
$\mathcal{O}_V(\lfloor (1 - p^e)(K_V + D) \rfloor)$ (`sourceModule`), for the chosen canonical
divisor $K_V$ (`C`) and the boundary $D$, and $F^e_{V*}\mathcal{M} \to \mathcal{O}_V$ the boundary
trace (`boundaryTrace`, for the chosen Frobenius identification `F` and index `I`). The data is a
map $\phi : F^e_{W*}\, i^*\mathcal{M} \to \mathcal{O}_W$ such that the base-change map
$i^* F^e_{V*}\mathcal{M} \to F^e_{W*}\, i^*\mathcal{M}$ is an epimorphism and its composite with
$\phi$ is $i^*$ of the boundary trace followed by $i^*\mathcal{O}_V \cong \mathcal{O}_W$. -/
structure CenterDescent where
  map : (Scheme.Modules.pushforward (iterated W.X.left p hW e)).obj
    ((Scheme.Modules.pullback i.left).obj (sourceModule C D p e)) ⟶ structureModule W.X.left
  [epi : Epi (ordinaryBaseChangeMap i.left (iterated W.X.left p hW e)
    (iterated V.X.left p hV e) i.left comm (sourceModule C D p e))]
  normalized : ordinaryBaseChangeMap i.left (iterated W.X.left p hW e)
    (iterated V.X.left p hV e) i.left comm (sourceModule C D p e) ≫ map =
      (Scheme.Modules.pullback i.left).map
        (DualizingFrobeniusInterfaces.boundaryTrace V C p e hV D F I) ≫
          (MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison.pullbackStructureIso i.left).hom

/-- Genuine Cartesian line representation of the actual restricted boundary source. -/
structure CenterLine where
  cartier : CartierLine W
  comparison : cartier.line.val ≅ (Scheme.Modules.pullback i.left).obj (sourceModule C D p e)
  rationalization : CartierRationalization cartier

/-- The actual descended trace after the prescribed line comparison. -/
def centerTrace (Q : CenterDescent C D p e hV hW F I i comm)
    (N : CenterLine C D p e i) :
    (Scheme.Modules.pushforward (iterated W.X.left p hW e)).obj N.cartier.line.val ⟶
      structureModule W.X.left :=
  (Scheme.Modules.pushforward (iterated W.X.left p hW e)).map N.comparison.hom ≫ Q.map

/-- The adjoint trace element is the actual derived adjunction transpose followed by H0. -/
def adjointTraceElement {X : Scheme.{0}} (f : X ⟶ X)
    [(derivedPushforward f).IsLeftAdjoint] (M : X.Modules)
    (σ : (Scheme.Modules.pushforward f).obj M ⟶ structureModule X)
    (h : IsIso (sheafPushforwardUnit f M)) : M ⟶ relativeCanonicalModule f 0 := by
  letI := h
  let φ := ((Adjunction.ofIsLeftAdjoint (derivedPushforward f)).homEquiv _ _)
    (inv (sheafPushforwardUnit f M) ≫ (DerivedCategory.singleFunctor X.Modules 0).map σ)
  exact (singleHomologyIso X M).inv ≫ (DerivedCategory.homologyFunctor X.Modules 0).map φ

/-- Rational multiplier of the actual adjoint element, fixed on every actual local section. -/
structure TraceMultiplier (Q : CenterDescent C D p e hV hW F I i comm)
    (N : CenterLine C D p e i) (CW : CanonicalWeilReference W)
    (FW : FrobeniusIdentification W CW p e hW)
    (h : IsIso (sheafPushforwardUnit (iterated W.X.left p hW e) N.cartier.line.val)) where
  multiplier : (FunctionField W)ˣ
  finite : (Function.support (fun q : PrimePoint W =>
    W.X.left.ord (multiplier : FunctionField W) q.val)).Finite
  normalized : ∀ (U : W.X.left.Opens) [Nonempty U] (s : Γ(N.cartier.line.val,U)),
    rationalFunctionsEquiv U
      ((DivisorialModuleSheaves.inclusion W (canonicalTwist W CW p e)).app U
        ((adjointTraceElement (iterated W.X.left p hW e) N.cartier.line.val
          (centerTrace C D p e hV hW F I i comm Q N) h ≫ FW.comparison.inv).app U s)) =
    (multiplier : FunctionField W) *
      rationalFunctionsEquiv U (N.rationalization.map.app U s)

/-- Literal principal divisor of the fixed rational multiplier. -/
def multiplierDivisor {Q : CenterDescent C D p e hV hW F I i comm}
    {N : CenterLine C D p e i} {CW : CanonicalWeilReference W}
    {FW : FrobeniusIdentification W CW p e hW}
    {h : IsIso (sheafPushforwardUnit (iterated W.X.left p hW e) N.cartier.line.val)}
    (R : TraceMultiplier C D p e hV hW F I i comm Q N CW FW h) : IntegerWeil W :=
  Finsupp.ofSupportFinite (fun q => W.X.left.ord (R.multiplier : FunctionField W) q.val) R.finite

/-- Actual center boundary, with no freely supplied different coefficients. -/
def fDifferent {Q : CenterDescent C D p e hV hW F I i comm}
    {N : CenterLine C D p e i} {CW : CanonicalWeilReference W}
    {FW : FrobeniusIdentification W CW p e hW}
    {h : IsIso (sheafPushforwardUnit (iterated W.X.left p hW e) N.cartier.line.val)}
    (R : TraceMultiplier C D p e hV hW F I i comm Q N CW FW h) : RealWeil W :=
  (1/((p^e : ℝ)-1)) •
    (realCast (canonicalTwist W CW p e) - realCast N.cartier.divisor +
      realCast (multiplierDivisor C D p e hV hW F I i comm R))

end MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent
