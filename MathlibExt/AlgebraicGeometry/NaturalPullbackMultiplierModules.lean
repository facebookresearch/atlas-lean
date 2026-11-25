/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
public import MathlibExt.AlgebraicGeometry.NormalCrossingsModels
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import MathlibExt.AlgebraicGeometry.LogResidueDifferent
public import MathlibExt.AlgebraicGeometry.CartierIdealModels

/-!
# Natural divisor pullback and limiting multiplier candidates

No Q-Gorenstein hypothesis is imposed on the normal base. The natural
pullback coefficient is the minimum of orders of the actual local
sections of O(-D) transported by the actual generic-point field map.
The ideal order uses the actual scheme ideal sheaf after pullback.

The limiting relative canonical divisor, its round-up and the pushed
O(round-up) candidate are computed. An ideal presentation must have
exactly the image of that fixed pushforward map, with the map normalized
by the actual rational functions. Local limiting ideals are literal
suprema of those ideals. No multiplier-ideal assignment is supplied.

Finite-support/coherence, resolved/SNC models and comparison of different
models remain explicit source-integration/provider boundaries.
Source: de Fernex--Hacon, arXiv0805.1767v2, Definitions 2.6/3.1,
the multiplier-ideal formula after Definition 4.3 and Theorem 1.1.
The completed Tau O(D) construction is reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RationalFunctionModules

variable {k : Type} [Field k] {n : ℕ}
  (V : NormalVariety k n) (C : CanonicalData V)

/-- A normalized proper birational canonical model, without an R-Cartier base adjoint. -/
structure CanonicalModel where
  variety : NormalVariety k n
  map : variety.X ⟶ V.X
  [proper : IsProper map.left]
  birational : MathlibExt.AlgebraicGeometry.BirationalResolution.IsBirationalMorphism map.left
  generic : map.left (genericPoint variety.X.left) = genericPoint V.X.left
  fieldIso :
    letI := fractionAlgebra V
    letI := fractionAlgebra variety
    FunctionField V ≃ₐ[k] FunctionField variety
  fieldNormalized : fieldIso.toRingHom = (genericMap map generic).hom
  canonical : CanonicalData variety
  canonicalNormalized :
    letI := fractionAlgebra V
    letI := fractionAlgebra variety
    canonical.form = rationalTopMap fieldIso.toAlgHom C.form
  [dvr : ∀ p : PrimePoint variety, IsDiscreteValuationRing (LocalRing variety p.val)]

variable [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]

/-- Actual natural-pullback order of the fractional module O(-D). -/
def naturalCoefficient (M : CanonicalModel V C) (D : IntegerWeil V)
    (p : PrimePoint M.variety) : ℤ :=
  sInf {a | ∃ (U : V.X.left.Opens) (_hU : IsAffineOpen U) (hp : M.map.left p.val ∈ U),
    letI : Nonempty U := ⟨⟨M.map.left p.val, hp⟩⟩
    ∃ s : Γ(DivisorialModuleSheaves.sheaf V (-D), U),
      let r := rationalFunctionsEquiv U
        ((DivisorialModuleSheaves.inclusion V (-D)).app U s)
      r ≠ 0 ∧ a = M.variety.X.left.ord (M.fieldIso r) p.val}

/-- Finite support is a proof on the fixed actual coefficient function. -/
structure NaturalSupport (M : CanonicalModel V C) (D : IntegerWeil V) : Prop where
  finite : (Function.support (naturalCoefficient V C M D)).Finite

def naturalDivisor (M : CanonicalModel V C) (D : IntegerWeil V) (h : NaturalSupport V C M D) :
    IntegerWeil M.variety :=
  Finsupp.ofSupportFinite (naturalCoefficient V C M D) h.finite

/-- Actual order of the pulled-back ideal at a prime: the least order at `p` of a nonzero local
section of the pulled-back ideal on an affine open containing `p`. Such orders are nonnegative.
For a nonzero ideal on the integral base the set of orders is nonempty, since the model maps
birationally onto the base; for the zero ideal it is empty and the value is the `sInf ∅ = 0`
convention, not an order, which is why `IdealSupport` requires a nonzero ideal. -/
def idealCoefficient (M : CanonicalModel V C) (I : V.X.left.IdealSheafData)
    (p : PrimePoint M.variety) : ℤ :=
  sInf {a | ∃ (U : M.variety.X.left.Opens) (hU : IsAffineOpen U) (hp : p.val ∈ U),
    letI : Nonempty U := ⟨⟨p.val, hp⟩⟩
    ∃ s : Γ(M.variety.X.left,U), s ≠ 0 ∧
      s ∈ (I.comap M.map.left).ideal ⟨U,hU⟩ ∧
      a = M.variety.X.left.ord (M.variety.X.left.germToFunctionField U s) p.val}

/-- The ideal is nonzero, so that `idealCoefficient` is its actual order, and its coefficient
function has finite support. -/
structure IdealSupport (M : CanonicalModel V C) (I : V.X.left.IdealSheafData) : Prop where
  nonzero : I ≠ ⊥
  finite : (Function.support (idealCoefficient V C M I)).Finite

def idealDivisor (M : CanonicalModel V C) (I : V.X.left.IdealSheafData)
    (h : IdealSupport V C M I) : IntegerWeil M.variety :=
  Finsupp.ofSupportFinite (idealCoefficient V C M I) h.finite

/-- The actual `m`-limiting relative canonical divisor `K_Y - (1/m) f^♮(m K_X)`, for a positive
index `m` (de Fernex--Hacon, Definition 3.1). -/
def limitingRelativeCanonical (M : CanonicalModel V C) (m : ℕ+)
    (h : NaturalSupport V C M (((m : ℕ) : ℤ) • canonicalDivisor C)) : RealWeil M.variety :=
  realCast (canonicalDivisor M.canonical) -
    (1/((m : ℕ) : ℝ)) • realCast (naturalDivisor V C M (((m : ℕ) : ℤ) • canonicalDivisor C) h)

/-- The literal round-up divisor defining the multiplier candidate. -/
def multiplierDivisor (M : CanonicalModel V C) (I : V.X.left.IdealSheafData)
    (m : ℕ+) (c : ℝ) (h : NaturalSupport V C M (((m : ℕ) : ℤ) • canonicalDivisor C))
    (hI : IdealSupport V C M I) : IntegerWeil M.variety :=
  Finsupp.mapRange Int.ceil (by simp)
    (limitingRelativeCanonical V C M m h - c • realCast (idealDivisor V C M I hI))

/-- The actual pushed divisor module, without an arbitrary multiplier-ideal carrier. -/
def multiplierCandidate (M : CanonicalModel V C) (I : V.X.left.IdealSheafData)
    (m : ℕ+) (c : ℝ) (h : NaturalSupport V C M (((m : ℕ) : ℤ) • canonicalDivisor C))
    (hI : IdealSupport V C M I) : V.X.left.Modules := by
  letI := M.dvr
  exact (Scheme.Modules.pushforward M.map.left).obj
    (DivisorialModuleSheaves.sheaf M.variety (multiplierDivisor V C M I m c h hI))

/-- A multiplier ideal presentation is pinned on every affine section
to the exact candidate image. -/
structure CandidateImage (M : CanonicalModel V C) (I : V.X.left.IdealSheafData)
    (m : ℕ+) (c : ℝ) (h : NaturalSupport V C M (((m : ℕ) : ℤ) • canonicalDivisor C))
    (hI : IdealSupport V C M I) where
  map : multiplierCandidate V C M I m c h hI ⟶
    CoherentCurveLinearSeries.structureModule V.X.left
  ideal : V.X.left.IdealSheafData
  image : ∀ U : V.X.left.affineOpens, ∀ a : Γ(V.X.left,U.val),
    a ∈ ideal.ideal U ↔ ∃ s, map.app U.val s = a
  rationalNormalized : ∀ (U : V.X.left.Opens) [Nonempty U]
    (s : Γ(multiplierCandidate V C M I m c h hI,U)),
    letI := M.dvr
    letI := fractionAlgebra V
    letI := fractionAlgebra M.variety
    letI : Nonempty (M.map.left ⁻¹ᵁ U) :=
      ⟨⟨genericPoint M.variety.X.left, by
        change M.map.left (genericPoint M.variety.X.left) ∈ U
        rw [M.generic]
        exact genericPoint_mem U⟩⟩
    V.X.left.germToFunctionField U (map.app U s) =
      M.fieldIso.symm
        (rationalFunctionsEquiv (M.map.left ⁻¹ᵁ U)
          ((DivisorialModuleSheaves.inclusion M.variety
            (multiplierDivisor V C M I m c h hI)).app (M.map.left ⁻¹ᵁ U) s))


/-- Actual open locus where the birational map is an isomorphism. -/
def isomorphismOpen (M : CanonicalModel V C) : V.X.left.Opens :=
  sSup {U | IsIso (M.map.left.resLE U (M.map.left ⁻¹ᵁ U) le_rfl)}

/-- Actual closed support of a finite divisor. -/
def divisorSupport {W : NormalVariety k n} (D : IntegerWeil W) :
    TopologicalSpace.Closeds W.X.left :=
  ⨆ p : D.support, ⟨closure ({p.val.val} : Set W.X.left), isClosed_closure⟩

/-- For a normal variety $V$ over a perfect field $k$, with canonical data $C$ and with local rings
at codimension-one points that are discrete valuation rings, a normal proper birational model
$f : Y → V$ carrying canonical data compatible with $C$ (`CanonicalModel V C`) and a Weil divisor
$D$ on $V$ whose natural pullback $f^\natural D$ has finite support: a map from the pullback along
$f$ of the divisorial sheaf $\mathcal{O}_V(-D)$ to the sheaf of rational functions on $Y$ that sends
the pullback of each local section to the same rational function, transported by the identification
of function fields of the model, and whose image on every affine open of $Y$ is exactly the sections
of $\mathcal{O}_Y(-f^\natural D)$; moreover $\mathcal{O}_Y(-f^\natural D)$ is a line bundle. -/
structure FractionalPullback (M : CanonicalModel V C) (D : IntegerWeil V)
    (hD : NaturalSupport V C M D) where
  map : (Scheme.Modules.pullback M.map.left).obj (DivisorialModuleSheaves.sheaf V (-D)) ⟶
    rationalFunctions M.variety.X.left
  normalized : ∀ (U : V.X.left.Opens) (W : M.variety.X.left.Opens)
    [Nonempty U] [Nonempty W] (h : W ≤ M.map.left ⁻¹ᵁ U)
    (s : Γ(DivisorialModuleSheaves.sheaf V (-D),U)),
    rationalFunctionsEquiv W
      (map.app W (LogResidueDifferent.pullOpenSection M.map
        (DivisorialModuleSheaves.sheaf V (-D)) U W h s)) =
      M.fieldIso (rationalFunctionsEquiv U ((DivisorialModuleSheaves.inclusion V (-D)).app U s))
  image : ∀ U : M.variety.X.left.affineOpens,
    letI := M.dvr
    Set.range (map.app U.val) =
      {s | s ∈ DivisorialModuleSheaves.sections M.variety
        (-naturalDivisor V C M D hD) U.val}
  principal :
    letI := M.dvr
    CoherentCurveLinearSeries.IsLineBundle
      (DivisorialModuleSheaves.sheaf M.variety (-naturalDivisor V C M D hD))

/-- Exact smooth/SNC resolution input for the actual fractional and ideal pullbacks. -/
structure ResolvedMultiplierModel (I : V.X.left.IdealSheafData) (m : ℕ+) where
  model : CanonicalModel V C
  [smooth : Smooth model.variety.X.hom]
  naturalSupport : NaturalSupport V C model (((m : ℕ) : ℤ) • canonicalDivisor C)
  idealSupport : IdealSupport V C model I
  fractional : FractionalPullback V C model (((m : ℕ) : ℤ) • canonicalDivisor C) naturalSupport
  idealPrincipal : CartierIdealModels.IsEffectiveCartier (I.comap model.map.left)
  crossings : NormalCrossingsModels.IsStrictNormalCrossings model.variety.X
    (Scheme.IdealSheafData.vanishingIdeal
      ((model.map.left ⁻¹ᵁ isomorphismOpen V C model).compl ⊔
        divisorSupport
          (naturalDivisor V C model (((m : ℕ) : ℤ) • canonicalDivisor C) naturalSupport) ⊔
          (I.comap model.map.left).support))

/-- Actual selected resolved models and exact candidate images for every positive degree. -/
structure LimitingFamily (I : V.X.left.IdealSheafData) (c : ℝ) where
  model : ∀ m : PNat, ResolvedMultiplierModel V C I m
  image : ∀ m : PNat,
    CandidateImage V C (model m).model I m c (model m).naturalSupport (model m).idealSupport

/-- The local limiting multiplier ideal is the literal supremum of the fixed candidate images. -/
def localLimitingIdeal {I : V.X.left.IdealSheafData} {c : ℝ}
    (F : LimitingFamily V C I c) (U : V.X.left.affineOpens) : Ideal Γ(V.X.left,U.val) :=
  ⨆ m : PNat, (F.image m).ideal.ideal U

end MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
