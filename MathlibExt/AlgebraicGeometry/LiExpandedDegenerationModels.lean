/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DegenerationParameterModels
public import MathlibExt.AlgebraicGeometry.RelativeMapGluingGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective one-parameter degenerations and their standard expansions

The original input is a native projective family over a pointed smooth
curve with an etale coordinate to A1 and a specified transverse central
fibre Y1 union_D Y2. Standard expansions are output models with the actual
successive blowups, native contractions and polynomial node charts.
Every coefficient algebra is an arbitrary smooth finitely presented
k-algebra; actual etale chart maps retain localizations and nilpotents.

The standard local chart is t_i=u_i*v_i, x=productEarlier*u_i,
y=v_i*productLater. The adjacent overlap is (a,z,b)->(az,z^-1,zb).
The ordered original components are Y1=(y=0) and Y2=(x=0), so that the
successive centre Y1 times the new last-parameter zero has this chart.
Our index n has n+1 parameters and n inserted ruled components: it is
W[n+1] in math/0009097v1 and W[n] in math/0110113v1.
All expanded families have one projection to the base and one contraction
to the original W, independent of the number of source components.

Sources: Jun Li arXiv:math/0110113v1, introduction pp1--4, Section1.1
pp6--9 and Section3.1; arXiv:math/0009097v1, Section1, equation(1.7)
and Lemma1.2. The printed divided transition is normalized by the base
and contraction equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiExpandedDegenerationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedTargetGluingModels ExpansionParameterModels DegenerationParameterModels
open scoped BigOperators

variable {k : Type} [Field k]

/-- A genuine relative closed projective embedding over the given curve. -/
def IsProjectiveOver {X C : Over (Spec (.of k))} (p : X ⟶ C) : Prop :=
  ∃ n : ℕ, ∃ i : X ⟶ prod (ProjectiveSpace.projectiveSpace k n) C,
    IsClosedImmersion i.left ∧ i ≫ prod.snd = p

def coefficientStructure (B : Type) [CommRing B] [Algebra k B] : Spec (.of B) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k B))

def coefficientLine (B : Type) [CommRing B] [Algebra k B] :
    smoothingBase (B := B) ⟶ (affineLine k).left :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k B)))

def axisHom (B : Type) [CommRing B] (i : Fin 2) : NodeRing B →ₐ[B] Polynomial B :=
  MvPolynomial.aeval (fun j => if j = i then 0 else Polynomial.X)

def axis (B : Type) [CommRing B] (i : Fin 2) :
    Spec (.of (Polynomial B)) ⟶ nodeScheme (B := B) :=
  Spec.map (CommRingCat.ofHom (axisHom B i).toRingHom)

/-- Original transverse node charts, including the actual two component ideals. -/
structure OriginalNodeChart {X C Y Z : Over (Spec (.of k))}
    (p : X ⟶ C) (coordinate : C ⟶ affineLine k) (left : Y ⟶ X) (right : Z ⟶ X) (x : X.left) where
  coefficient : Type
  [ring : CommRing coefficient]
  [algebra : Algebra k coefficient]
  smooth : Smooth (coefficientStructure (k := k) coefficient)
  finitePresentation : LocallyOfFinitePresentation (coefficientStructure (k := k) coefficient)
  neighborhood : Scheme.{0}
  map : neighborhood ⟶ X.left
  etale : Etale map
  contains : x ∈ Set.range map
  coordinates : neighborhood ⟶ nodeScheme (B := coefficient)
  coordinateEtale : Etale coordinates
  base : coordinates ≫ nodeSmoothing ≫ coefficientLine coefficient = map ≫ p.left ≫ coordinate.left
  leftIdeal : left.left.ker.comap map = (axis coefficient 1).ker.comap coordinates
  rightIdeal : right.left.ker.comap map = (axis coefficient 0).ker.comap coordinates

attribute [instance] OriginalNodeChart.ring OriginalNodeChart.algebra

variable (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)

structure OneParameter where
  curve : Over (Spec (.of k))
  smoothCurve : Smooth curve.hom
  zero : 𝟙_ (Over (Spec (.of k))) ⟶ curve
  coordinate : curve ⟶ affineLine k
  coordinateEtale : Etale coordinate.left
  zeroCoordinate : zero ≫ coordinate = zeroPoint k
  zeroFibre : IsPullback (𝟙 _) zero (zeroPoint k) coordinate
  total : Over (Spec (.of k))
  projection : total ⟶ curve
  projective : IsProjectiveOver projection
  proper : IsProper projection.left
  flat : Flat projection.left
  smoothTotal : Smooth total.hom
  leftIrreducible : IrreducibleSpace P.target.left
  rightIrreducible : IrreducibleSpace Q.target.left
  smoothGeneral : ∀ (Ω : Type) [Field Ω] (t : Spec (.of Ω) ⟶ curve.left),
    (¬ ∃ z : Spec (.of Ω) ⟶ (𝟙_ (Over (Spec (.of k)))).left, z ≫ zero.left = t) →
      Smooth (pullback.snd projection.left t)
  central : W0.scheme ≅ pullback projection zero
  node : ∀ x : W0.scheme.left, x ∈ Set.range (P.inclusion ≫ W0.left).left →
    OriginalNodeChart projection coordinate
      (W0.left ≫ central.hom ≫ pullback.fst projection zero)
      (W0.right ≫ central.hom ≫ pullback.fst projection zero)
      ((central.hom ≫ pullback.fst projection zero).left x)

variable {P Q W0}

def parameterObject (n : ℕ) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (ParameterRing k n))))

def parameterProductMap (n : ℕ) : parameterObject (k := k) n ⟶ affineLine k :=
  Over.homMk (parameterProduct (B := k) (n := n)) (by
    change Spec.map (CommRingCat.ofHom (productHom (B := k) (n := n)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (ParameterRing k n)))
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp [productHom])

def base (W : OneParameter P Q W0) (n : ℕ) : Over (Spec (.of k)) :=
  pullback W.coordinate (parameterProductMap n)

def baseToCurve (W : OneParameter P Q W0) (n : ℕ) : base W n ⟶ W.curve := pullback.fst _ _
def baseToParameters (W : OneParameter P Q W0) (n : ℕ) : base W n ⟶ parameterObject n :=
  pullback.snd _ _

def parameterOriginHom (n : ℕ) : ParameterRing k n →ₐ[k] k := MvPolynomial.aeval (fun _ => 0)

def parameterOrigin (n : ℕ) : 𝟙_ (Over (Spec (.of k))) ⟶ parameterObject (k := k) n :=
  Over.homMk (Spec.map (CommRingCat.ofHom (parameterOriginHom n).toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (ParameterRing k n))) = 𝟙 _
    rw [← Spec.map_comp]
    rw [show CommRingCat.ofHom (algebraMap k (ParameterRing k n)) ≫
      CommRingCat.ofHom (parameterOriginHom n).toRingHom = 𝟙 (CommRingCat.of k) by
        ext a; simp [parameterOriginHom]]
    exact Spec.map_id _)

theorem parameterOrigin_product (n : ℕ) :
    parameterOrigin (k := k) n ≫ parameterProductMap n = zeroPoint k := by
  ext1
  simp only [Over.comp_left, parameterOrigin, parameterProductMap, zeroPoint, Over.homMk_left,
    parameterProduct, ← Spec.map_comp]
  congr 1
  ext a
  · simp [parameterOriginHom, productHom]
  · simp [parameterOriginHom, productHom, map_prod, Fin.prod_univ_succ]

def baseOrigin (W : OneParameter P Q W0) (n : ℕ) : 𝟙_ (Over (Spec (.of k))) ⟶ base W n :=
  pullback.lift W.zero (parameterOrigin n) (by rw [W.zeroCoordinate, parameterOrigin_product])

def parameterSection (n : ℕ) (i : Fin (n + 1)) : Γ((parameterObject (k := k) n).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (ParameterRing k n))).inv.hom (MvPolynomial.X i)

def originalLeft (W : OneParameter P Q W0) : P.target ⟶ W.total :=
  W0.left ≫ W.central.hom ≫ pullback.fst W.projection W.zero

def otherParameters (n : ℕ) : Γ((parameterObject (k := k) n).left, ⊤) :=
  ∏ i : Fin (n + 1), if i.val = 0 then 1 else parameterSection n i

/-- The open inverse image of Y1 away from all the other parameter hyperplanes. -/
def genericLeftMap (W : OneParameter P Q W0) (n : ℕ) {X : Over (Spec (.of k))}
    (p : X ⟶ base W n) (c : X ⟶ W.total) :
    ((pullback (originalLeft W) c).left.basicOpen
      ((pullback.snd (originalLeft W) c ≫ p ≫ baseToParameters W n).left.appTop.hom (otherParameters n)) :
        Scheme.{0}) ⟶
      X.left :=
  ((pullback (originalLeft W) c).left.basicOpen
    ((pullback.snd (originalLeft W) c ≫ p ≫ baseToParameters W n).left.appTop.hom (otherParameters n))).ι ≫
      (pullback.snd (originalLeft W) c).left

structure StandardChart (W : OneParameter P Q W0) (n : ℕ) where
  scheme : Over (Spec (.of k))
  projection : scheme ⟶ base W n
  contraction : scheme ⟶ W.total
  over : contraction ≫ W.projection = projection ≫ baseToCurve W n
  projective : IsProjectiveOver projection
  extreme : Over (Spec (.of k))
  extremeMap : extreme ⟶ scheme
  extremeClosed : IsClosedImmersion extremeMap.left
  extremeCartier : CartierIdealModels.IsEffectiveCartier extremeMap.left.ker
  /-- The whole inverse-image divisor, including its ruled components.
  This is the divisor that resolves the new last node after base change. -/
  extremeClosure : extremeMap.left.ker = (originalLeft W).left.ker.comap contraction.left
  extremePullback : extreme ≅ pullback (originalLeft W) contraction
  extremePullbackMap : extremePullback.hom ≫ pullback.snd (originalLeft W) contraction = extremeMap

def lastParameterMap (n : ℕ) : parameterObject (k := k) (n + 1) ⟶ affineLine k :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (MvPolynomial.X (Fin.last (n + 1)) : ParameterRing k (n + 1))).toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (ParameterRing k (n + 1))))
    rw [← Spec.map_comp]
    congr 1
    ext a
    simp)

def newParameterZero (W : OneParameter P Q W0) (n : ℕ) : Over (Spec (.of k)) :=
  pullback (baseToParameters W (n + 1) ≫ lastParameterMap n) (zeroPoint k)

/-- The actual centre inside the base-changed preceding expansion. -/
def stepCenter {W : OneParameter P Q W0} {n : ℕ} (U : StandardChart W n)
    (split : base W (n + 1) ⟶ base W n) :
    pullback
      (pullback.snd U.extremeMap (pullback.fst U.projection split) ≫ pullback.snd U.projection split)
      (pullback.fst (baseToParameters W (n + 1) ≫ lastParameterMap n) (zeroPoint k)) ⟶
      pullback U.projection split :=
  pullback.fst _ _ ≫ pullback.snd U.extremeMap (pullback.fst U.projection split)

structure StandardStep {W : OneParameter P Q W0} {n : ℕ}
    (U : StandardChart W n) (V : StandardChart W (n + 1)) where
  split : base W (n + 1) ⟶ base W n
  splitCurve : split ≫ baseToCurve W n = baseToCurve W (n + 1)
  splitCoordinates : ∀ i : Fin (n + 1),
    (split ≫ baseToParameters W n).left.appTop.hom (parameterSection n i) =
      (baseToParameters W (n + 1)).left.appTop.hom
        (parameterSection (n + 1) i.castSucc) *
      (if i = Fin.last n then (baseToParameters W (n + 1)).left.appTop.hom
        (parameterSection (n + 1) (Fin.last (n + 1))) else 1)
  blowup : BlowupAlong (pullback U.projection split) (stepCenter U split).left.ker
  identifies : V.scheme ≅ blowup.scheme
  contraction : identifies.hom ≫ blowup.map ≫ pullback.fst U.projection split ≫ U.contraction = V.contraction
  projection : identifies.hom ≫ blowup.map ≫ pullback.snd U.projection split = V.projection
  transform : V.extreme ⟶ U.extreme
  transformSquare : V.extremeMap ≫ identifies.hom ≫ blowup.map ≫ pullback.fst U.projection split =
    transform ≫ U.extremeMap

def parameterCoefficient (B : Type) [CommRing B] [Algebra k B] (n : ℕ) :
    parameterScheme (B := B) n ⟶ parameterScheme (B := k) n :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap k B)))

def coordinateSection (B : Type) [CommRing B] {n : ℕ} (i : Fin (n + 1))
    (f : ChartRing B i) : Γ(chartScheme (B := B) i, ⊤) :=
  (Scheme.ΓSpecIso (.of (ChartRing B i))).inv.hom f

/-- Local charts use the original node chart's coefficient algebra and contraction. -/
structure LocalStandardChart {W : OneParameter P Q W0} {n : ℕ} (U : StandardChart W n)
    (x : U.scheme.left) where
  original : OriginalNodeChart W.projection W.coordinate
    (W0.left ≫ W.central.hom ≫ pullback.fst W.projection W.zero)
    (W0.right ≫ W.central.hom ≫ pullback.fst W.projection W.zero) (U.contraction.left x)
  index : Fin (n + 1)
  neighborhood : Scheme.{0}
  map : neighborhood ⟶ U.scheme.left
  etale : Etale map
  contains : x ∈ Set.range map
  coordinates : neighborhood ⟶ chartScheme (B := original.coefficient) index
  coordinateEtale : Etale coordinates
  originalLift : neighborhood ⟶ original.neighborhood
  contraction : coordinates ≫ chartContraction index = originalLift ≫ original.coordinates
  originalSquare : originalLift ≫ original.map = map ≫ U.contraction.left
  parameters : coordinates ≫ chartParameter index ≫ parameterCoefficient original.coefficient n =
    map ≫ U.projection.left ≫ (baseToParameters W n).left

/-- The corrected adjacent transition is an equality of actual regular sections. -/
structure AdjacentTransition (B : Type) [CommRing B] {n : ℕ}
    (i j : Fin (n + 1)) (next : j.val = i.val + 1) where
  overlap : Scheme.{0}
  left : overlap ⟶ chartScheme (B := B) i
  right : overlap ⟶ chartScheme (B := B) j
  leftEtale : Etale left
  rightEtale : Etale right
  leftOpen : overlap ≅ (chartScheme (B := B) i).basicOpen (coordinateSection B i (vCoordinate i))
  leftOpenMap : leftOpen.hom ≫
    ((chartScheme (B := B) i).basicOpen (coordinateSection B i (vCoordinate i))).ι = left
  rightOpen : overlap ≅ (chartScheme (B := B) j).basicOpen (coordinateSection B j (uCoordinate j))
  rightOpenMap : rightOpen.hom ≫
    ((chartScheme (B := B) j).basicOpen (coordinateSection B j (uCoordinate j))).ι = right
  z : Γ(overlap, ⊤)ˣ
  zCoordinate : (z : Γ(overlap, ⊤)) = left.appTop.hom (coordinateSection B i (vCoordinate i))
  previousParameter : right.appTop.hom (coordinateSection B j (parameterValue j i)) =
    left.appTop.hom (coordinateSection B i (uCoordinate i)) * (z : Γ(overlap, ⊤))
  uCoordinate : right.appTop.hom (coordinateSection B j (DegenerationParameterModels.uCoordinate j)) =
    (z⁻¹ : Γ(overlap, ⊤)ˣ)
  vCoordinate : right.appTop.hom (coordinateSection B j (DegenerationParameterModels.vCoordinate j)) =
    (z : Γ(overlap, ⊤)) * left.appTop.hom (coordinateSection B i (parameterValue i j))
  remaining : ∀ l : Fin (n + 1), l ≠ i → l ≠ j →
    right.appTop.hom (coordinateSection B j (parameterValue j l)) =
      left.appTop.hom (coordinateSection B i (parameterValue i l))
  over : left ≫ chartParameter i = right ≫ chartParameter j
  contraction : left ≫ chartContraction i = right ≫ chartContraction j

/-- Coordinate formula on every ring, with the genuine inverse of the unit. -/
def transition {A : Type*} [CommRing A] (a : A) (z : Aˣ) (b : A) : A × Aˣ × A :=
  (a * z, z⁻¹, z * b)

@[simp] theorem transition_twice {A : Type*} [CommRing A] (a : A) (z : Aˣ) (b : A) :
    transition (transition a z b).1 (transition a z b).2.1 (transition a z b).2.2 = (a, z, b) := by
  simp [transition]

def edgeUnit {A : Type*} [CommRing A] {n : ℕ} (u : Fin n → Aˣ) (j : ℕ) : Aˣ :=
  if h : 0 < j ∧ j ≤ n then u ⟨j - 1, by omega⟩ else 1

def parameterWeight {A : Type*} [CommRing A] {n : ℕ}
    (u : Fin n → Aˣ) (i : Fin (n + 1)) : Aˣ := edgeUnit u (i.val + 1) / edgeUnit u i.val

theorem parameterWeight_product {A : Type*} [CommRing A] {n : ℕ} (u : Fin n → Aˣ) :
    ∏ i : Fin (n + 1), parameterWeight u i = 1 := by
  change (∏ i : Fin (n + 1), edgeUnit u ((i : ℕ) + 1) / edgeUnit u (i : ℕ)) = 1
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => edgeUnit u (j + 1) / edgeUnit u j) (n + 1)]
  rw [Finset.prod_range_div]
  simp [edgeUnit]

structure ScalingData {W : OneParameter P Q W0} {n : ℕ}
    (U : StandardChart W n) (H : TorusTheory k n) where
  parameter : letI := H.group; ModObj (torusScheme k n) (base W n)
  standard : letI := H.group; ModObj (torusScheme k n) U.scheme
  coordinates : letI := H.group; letI := parameter;
    ∀ (T : Over (Spec (.of k))) (g : T ⟶ torusScheme k n) (t : T ⟶ base W n) (i : Fin (n + 1)),
      (CartesianMonoidalCategory.lift g t ≫ γ[torusScheme k n,base W n] ≫
        baseToParameters W n).left.appTop.hom (parameterSection n i) =
      (parameterWeight (H.units T g) i : Γ(T.left, ⊤)) *
        (t ≫ baseToParameters W n).left.appTop.hom (parameterSection n i)
  curveFixed : letI := H.group; letI := parameter;
    γ[torusScheme k n,base W n] ≫ baseToCurve W n =
      CartesianMonoidalCategory.snd _ _ ≫ baseToCurve W n
  projection : letI := H.group; letI := parameter; letI := standard;
    γ[torusScheme k n,U.scheme] ≫ U.projection =
      (torusScheme k n ◁ U.projection) ≫ γ[torusScheme k n,base W n]
  contraction : letI := H.group; letI := standard;
    γ[torusScheme k n,U.scheme] ≫ U.contraction =
      CartesianMonoidalCategory.snd _ _ ≫ U.contraction

structure CentralChain (P Q : RelativePair (k := k)) (W0 : SingularTarget P Q)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (n : ℕ) where
  chain : ExpandedSpecialFibre P R n
  scheme : Over (Spec (.of k))
  left : chain.scheme ⟶ scheme
  right : Q.target ⟶ scheme
  boundary : chain.boundary ≫ left = W0.divisor.hom ≫ Q.inclusion ≫ right
  contraction : scheme ⟶ W0.scheme
  leftContraction : left ≫ contraction = chain.contraction ≫ W0.left
  rightContraction : right ≫ contraction = W0.right
  universal : ∀ (Z : Over (Spec (.of k))) (f : chain.scheme ⟶ Z) (h : Q.target ⟶ Z),
    chain.boundary ≫ f = W0.divisor.hom ≫ Q.inclusion ≫ h →
      ∃! q : scheme ⟶ Z, left ≫ q = f ∧ right ≫ q = h

structure StandardSystem (W : OneParameter P Q W0) where
  chart : ∀ n : ℕ, StandardChart W n
  seed : (chart 0).scheme ≅ W.total
  seedContraction : seed.hom = (chart 0).contraction
  seedExtreme : (chart 0).extreme ≅ P.target
  seedExtremeMap : seedExtreme.hom ≫ W0.left ≫ W.central.hom ≫
    pullback.fst W.projection W.zero = (chart 0).extremeMap ≫ seed.hom
  step : ∀ n, StandardStep (chart n) (chart (n + 1))
  nodeChart : ∀ n (x : (chart n).scheme.left),
    RelativeExpandedMapFamilies.IsRelativeNode ((chart n).projection.left) x → LocalStandardChart (chart n) x
  overlap : ∀ (n : ℕ) (B : Type) [CommRing B] (i j : Fin (n + 1)) (h : j.val = i.val + 1),
    AdjacentTransition B i j h
  torus : ∀ n, TorusTheory k n
  scaling : ∀ n, ScalingData (chart n) (torus n)
  ruled : ProjectiveLine P.divisor.left (normalLineModule P)
  centralChain : ∀ n, CentralChain P Q W0 ruled n
  centralIso : ∀ n, (centralChain n).scheme ≅ pullback (chart n).projection (baseOrigin W n)
  centralContraction : ∀ n,
    (centralIso n).hom ≫ pullback.fst (chart n).projection (baseOrigin W n) ≫ (chart n).contraction =
      (centralChain n).contraction ≫ W.central.hom ≫ pullback.fst W.projection W.zero

variable (W : OneParameter P Q W0) (S : StandardSystem W)

structure LocalPresentation {T : Over (Spec (.of k))} (b : T ⟶ W.curve)
    {X : Over (Spec (.of k))} (p : X ⟶ T) (c : X ⟶ W.total) (t : T.left) where
  neighborhood : Over (Spec (.of k))
  map : neighborhood ⟶ T
  etale : Etale map.left
  contains : t ∈ Set.range map.left
  length : ℕ
  parameter : neighborhood ⟶ base W length
  parameterOver : parameter ≫ baseToCurve W length = map ≫ b
  comparison : pullback p map ≅ pullback (S.chart length).projection parameter
  projection : comparison.hom ≫ pullback.snd (S.chart length).projection parameter = pullback.snd p map
  contraction : comparison.hom ≫ pullback.fst (S.chart length).projection parameter ≫
    (S.chart length).contraction = pullback.fst p map ≫ c

structure ExpandedFamily (T : Over (Spec (.of k))) (b : T ⟶ W.curve) where
  scheme : Over (Spec (.of k))
  projection : scheme ⟶ T
  contraction : scheme ⟶ W.total
  over : contraction ≫ W.projection = projection ≫ b
  presentation : ∀ t : T.left, LocalPresentation W S b projection contraction t

structure ExpandedIso {T : Over (Spec (.of k))} {b : T ⟶ W.curve}
    (F H : ExpandedFamily W S T b) where
  iso : F.scheme ≅ H.scheme
  over : iso.hom ≫ H.projection = F.projection
  contraction : iso.hom ≫ H.contraction = F.contraction

@[ext] theorem ExpandedIso.ext {T : Over (Spec (.of k))} {b : T ⟶ W.curve}
    {F H : ExpandedFamily W S T b} (f h : ExpandedIso W S F H)
    (iso : f.iso = h.iso) : f = h := by cases f; cases h; cases iso; rfl

instance expandedGroupoid (T : Over (Spec (.of k))) (b : T ⟶ W.curve) :
    Groupoid (ExpandedFamily W S T b) where
  Hom F H := ExpandedIso W S F H
  id F := ⟨Iso.refl _, by simp, by simp⟩
  comp f h := ⟨f.iso ≪≫ h.iso, by simp [Category.assoc, h.over, f.over],
    by simp [Category.assoc, h.contraction, f.contraction]⟩
  inv f := ⟨f.iso.symm, by rw [← f.over]; simp, by rw [← f.contraction]; simp⟩
  id_comp f := by apply ExpandedIso.ext; ext; simp
  comp_id f := by apply ExpandedIso.ext; ext; simp
  assoc f h j := by apply ExpandedIso.ext; ext; simp
  inv_comp f := by apply ExpandedIso.ext; ext; simp
  comp_inv f := by apply ExpandedIso.ext; ext; simp

end MathlibExt.AlgebraicGeometry.LiExpandedDegenerationModels
