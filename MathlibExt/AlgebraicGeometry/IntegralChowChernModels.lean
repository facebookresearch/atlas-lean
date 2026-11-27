/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import MathlibExt.AlgebraicGeometry.GeometricChowOperators
public import MathlibExt.AlgebraicGeometry.IntegralOperationalChow
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

/-!
# Integral cycle maps and source-normalized Chern construction models

Proper push is the literal residue-degree sum. Smooth pull uses the
actual scheme-theoretic inverse image of each integral point closure,
with generic local-ring lengths. The quotient adapters contain only
relation-descent and homotopy-invariance proofs for these fixed maps.

The first Chern operation is zero-section push followed by the inverse
of the actual line-bundle pullback. Generic projective models retain all
quotient-line families over arbitrary, possibly singular and nonproper,
base schemes.

Sources: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Chow/GenuineChern/Classes.lean, BivariantChernClass.lean,
Chow/Bivariant/TotalChernClass.lean, Apache 2.0; Stacks 02U6/0B7H.
The generic integral source operators are completed there; native
comparison and construction proofs are recorded separately.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralChowChernModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open IntegerSchemeChow StackCycleGeometry
open CoherentCurveLinearSeries AlgebraicBundleGeometry

abbrev SchemeData := FieldScheme ℂ
abbrev Chow (X : SchemeData) (d : ℤ) := IntegerSchemeChow.ChowGroup X d

variable {X Y : SchemeData}

/-- The actual proper push of a single generic point, with its dimension filter. -/
def pushBasis (f : X.scheme ⟶ Y.scheme) (d : ℤ) (x : X.scheme.left) :
    IntegerSchemeChow.CycleGroup Y.scheme.left d := by
  classical
  exact IntegerSchemeChow.dimensionPart Y.scheme.left d
    (Function.locallyFinsuppWithin.single (f.left x) (f.left.residueDegree x : ℤ))

def cyclePush (f : X.scheme ⟶ Y.scheme) (d : ℤ) :
    IntegerSchemeChow.CycleGroup X.scheme.left d →+
      IntegerSchemeChow.CycleGroup Y.scheme.left d :=
  (Finsupp.linearCombination ℤ (pushBasis f d) ∘ₗ
    _root_.AlgebraicGeometry.IntegralOperationalChow.cycleCoordinates X.scheme.left ∘ₗ
      (IntegerSchemeChow.cyclesOfDimension X.scheme.left d).subtype.toIntLinearMap).toAddMonoidHom

/-- Properness and descent concern the fixed residue-degree map. -/
structure ProperPushDescent (f : X.scheme ⟶ Y.scheme) : Prop where
  [proper : IsProper f.left]
  preserves : ∀ d : ℤ, rationalEquivalences X.scheme.left d ≤
    (rationalEquivalences Y.scheme.left d).comap (cyclePush f d)

/-- Pure relative dimension is geometric here, not a freely chosen dimension selector. -/
structure SmoothPullDescent (f : Y.scheme ⟶ X.scheme) (r : ℕ) : Prop where
  [smooth : SmoothOfRelativeDimension r f.left]
  preserves : ∀ d : ℤ, rationalEquivalences X.scheme.left d ≤
    (rationalEquivalences Y.scheme.left (d+r)).comap
      (_root_.AlgebraicGeometry.IntegralOperationalChow.flatCycleMap f d r).toAddMonoidHom

def properPush {f : X.scheme ⟶ Y.scheme} (D : ProperPushDescent f) (d : ℤ) :
    Chow X d →+ Chow Y d :=
  QuotientAddGroup.map _ _ (cyclePush f d) (D.preserves d)

def smoothPull {f : Y.scheme ⟶ X.scheme} {r : ℕ} (D : SmoothPullDescent f r) (d : ℤ) :
    Chow X d →+ Chow Y (d+r) :=
  QuotientAddGroup.map _ _
    (_root_.AlgebraicGeometry.IntegralOperationalChow.flatCycleMap f d r).toAddMonoidHom
    (D.preserves d)

def chowCast (X : SchemeData) {d e : ℤ} (h : d = e) : Chow X d →+ Chow X e := by
  cases h
  exact AddMonoidHom.id _

@[simp] theorem chowCast_rfl (X : SchemeData) (d : ℤ) :
    chowCast X (d := d) rfl = AddMonoidHom.id (Chow X d) := rfl

/-- Generic actual line-bundle total space, without smooth/proper base restrictions. -/
structure LineTotalModel (X : SchemeData) (L : X.scheme.left.Modules) where
  isLine : IsLine L
  total : SchemeData
  projection : total.scheme ⟶ X.scheme
  [relativeSmooth : SmoothOfRelativeDimension 1 projection.left]
  universalSection :
    LineBundleTaskContracts.Section ((Scheme.Modules.pullback projection.left).obj L)
  universal : ∀ (T : Over (Spec (.of ℂ))) (f : T ⟶ X.scheme)
    (s : LineBundleTaskContracts.Section ((Scheme.Modules.pullback f.left).obj L)),
    ∃! g : T ⟶ total.scheme, ∃ h : g ≫ projection = f,
      s = AlgebraicBundleGeometry.pulledCompositeSection L projection universalSection f g h
  zero : X.scheme ⟶ total.scheme
  zero_projection : zero ≫ projection = 𝟙 X.scheme
  zero_section :
    AlgebraicBundleGeometry.pulledCompositeSection L projection universalSection
      (𝟙 X.scheme) zero zero_projection = 0
  [closedZero : IsClosedImmersion zero.left]

/-- The only comparisons are proofs for the actual zero and projection maps. -/
structure LineChowComparison {X : SchemeData} {L : X.scheme.left.Modules}
    (V : LineTotalModel X L) where
  pull : SmoothPullDescent V.projection 1
  bijective : ∀ d : ℤ, Function.Bijective (smoothPull pull d)
  zeroPush : ProperPushDescent V.zero

/-- The integral first Chern cap is the actual zero-section push and homotopy inverse. -/
def firstChern {X : SchemeData} {L : X.scheme.left.Modules}
    (V : LineTotalModel X L) (D : LineChowComparison V) (d : ℤ) :
    Chow X d →+ Chow X (d-1) :=
  ((AddEquiv.ofBijective (smoothPull D.pull (d-1)) (D.bijective (d-1))).symm.toAddMonoidHom).comp
    ((chowCast V.total (show d=(d-1)+1 by omega)).comp (properPush D.zeroPush d))

/-- The projective quotient-line model over every actual test scheme. -/
structure ProjectiveModel (X : SchemeData) (E : X.scheme.left.Modules) (r : ℕ) where
  positive : 0 < r
  isBundle : IsBundle E r
  total : SchemeData
  projection : total.scheme ⟶ X.scheme
  [proper : IsProper projection.left]
  [relativeSmooth : SmoothOfRelativeDimension (r-1) projection.left]
  tautological : total.scheme.left.Modules
  isLine : IsLine tautological
  quotient : (Scheme.Modules.pullback projection.left).obj E ⟶ tautological
  [epi : Epi quotient]
  universal : ∀ (T : Over (Spec (.of ℂ))) (f : T ⟶ X.scheme) (L : T.left.Modules)
    (_hL : IsLine L) (q : (Scheme.Modules.pullback f.left).obj E ⟶ L) (_hq : Epi q),
    ∃! g : T ⟶ total.scheme, ∃ (h : g ≫ projection = f)
      (e : (Scheme.Modules.pullback g.left).obj tautological ≅ L),
      q = AlgebraicBundleGeometry.pulledQuotient E tautological projection quotient f g h L e

/-- All projective Chern inputs are actual geometric models and proofs for fixed cycle maps. -/
structure ProjectiveChernData (X : SchemeData) (E : X.scheme.left.Modules) (r : ℕ) where
  projective : ProjectiveModel X E r
  pull : SmoothPullDescent projective.projection (r-1)
  push : ProperPushDescent projective.projection
  hyperplane : LineTotalModel projective.total projective.tautological
  hyperplaneChow : LineChowComparison hyperplane

/-- Powers of the actual first-Chern cap, retaining their signed dimension shift. -/
def firstChernPower {X : SchemeData} {L : X.scheme.left.Modules}
    (V : LineTotalModel X L) (D : LineChowComparison V) :
    ∀ (n : ℕ) (d : ℤ), Chow X d →+ Chow X (d-n)
  | 0,d => chowCast X (by simp)
  | n+1,d =>
    (chowCast X (by omega)).comp
      ((firstChern V D (d-n)).comp (firstChernPower V D n d))

/-- The quotient convention's projective Segre operation p_*(ξ^(r-1+n) p^*(-)). -/
def projectiveSegre {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}
    (D : ProjectiveChernData X E r) (n : ℕ) (d : ℤ) : Chow X d →+ Chow X (d-n) := by
  let a := smoothPull D.pull d
  let b := firstChernPower D.hyperplane D.hyperplaneChow ((r-1)+n) (d+((r-1 : ℕ) : ℤ))
  let c : Chow D.projective.total (d+((r-1 : ℕ) : ℤ)-((r-1)+n : ℕ)) →+
      Chow D.projective.total (d-n) := chowCast D.projective.total (by omega)
  exact (properPush D.push (d-n)).comp (c.comp (b.comp a))

/-- Coefficients of the inverse of the signed projective-Segre series.
The sign corrects the quotient convention, so rank-one c_1 is ξ. -/
def chernRec {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}
    (D : ProjectiveChernData X E r) :
    ∀ (n : ℕ) (d : ℤ), Chow X d →+ Chow X (d-n)
  | 0,d => chowCast X (by simp)
  | n+1,d =>
    -∑ j : Fin (n+1), (Int.negOnePow (j.val+1)).val •
      (let a := chernRec D (n-j.val) d
       let b := projectiveSegre D (j.val+1) (d-((n-j.val : ℕ) : ℤ))
       let c : Chow X (d-((n-j.val : ℕ) : ℤ)-(j.val+1)) →+
           Chow X (d-(n+1)) := chowCast X (by omega)
       c.comp (b.comp a))
termination_by n _ => n
decreasing_by omega

/-- The construction covers rank zero without requesting an empty projective bundle. -/
structure ChernConstruction (X : SchemeData) (E : X.scheme.left.Modules) (r : ℕ) where
  isBundle : IsBundle E r
  projective : 0 < r → ProjectiveChernData X E r

/-- The actual all-rank integral Chern cap: c_0=id and c_i=0 above the rank. -/
def chernCap {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}
    (D : ChernConstruction X E r) (n : ℕ) (d : ℤ) : Chow X d →+ Chow X (d-n) :=
  if hn : n=0 then chowCast X (by simp [hn])
  else if hr : n≤r then chernRec (D.projective (by omega)) n d
  else 0

end MathlibExt.AlgebraicGeometry.IntegralChowChernModels
