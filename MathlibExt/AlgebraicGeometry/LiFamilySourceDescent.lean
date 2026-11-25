/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiFamilyDeformationMaps
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Full family and atlas descent of Li source complexes

Local maps are fixed on every actual Cech tuple and coefficient module.
Each derivation/log value is realized by two genuine target lifts; their
comparison is a map of the entire expanded target families, preserving
the signed boundary and both lifted maps. Thus changing a standard frame
retains its unit logarithmic derivatives and node branch permutations.
Only preserving the map to the parameter space would not suffice.

The global comparison uses the actual affine-point module presheaf. All
stack arrows are tested after a common etale source refinement. Its two
source maps retain the actual marked extensions, dual trivialization,
coface maps and torus quotient. This excludes a line twist which is
trivial on each individual atlas chart.

Sources: Jun Li, arXiv:math/0110113v1, equations 1.18--1.25,
Definition 2.1 and Theorems 2.2--2.3, printed pages 15--23; JPPZ,
arXiv:1602.04705v2, Section 0.2.4. Native presheaves, tensor maps,
derived quotients and Cech operations are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0).
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiFamilySourceDescent

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels ExpandedRelativeFamilies RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry StackAffineModules StackFibreModels StackBundleCones
open LiFamilyDeformationMaps LiAffineMapCharts LiCechChartModules LiLocalLiftDifferences
open LiFiniteComplexPresentations LiUniversalSourceExtensions
open scoped TensorProduct Simplicial ChangeOfRings

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm
  LiMarkedCurveExtensions.oppositeTower HasDerivedCategory.standard

variable {k : Type} [Field k]
  {O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k)))}
  {P : RelativePair (k := k)} {D : OriginalRubberPair O P}
  {R : ProjectiveLine P.divisor.left (normalLineModule P)} {S : StandardSystem P R}
  {g n : ℕ} {a : Fin n → ℤ} {B : RubberModuliModel O P D R S (g := g) a}

def localChart (C : LiFamilyDeformationMaps.Point O P D R S a B)
    (z : SimplexCategory) (t : Fin (z.len + 1) → Fin C.chart.cover.count) :=
  C.chart.geometry.chart z t

def localValue (C : LiFamilyDeformationMaps.Point O P D R S a B)
    (I : ModuleCat.{0} C.ring) (z : SimplexCategory)
    (t : Fin (z.len + 1) → Fin C.chart.cover.count) : ModuleCat.{0} C.ring :=
  LiCechChartModules.value (S.chart C.chart.length).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S C.chart.length)
    (RubberLieQuotientComplexes.parameters P R S C.chart.length) I (C.chart.geometry.mode z t)

def logCochains (C : LiFamilyDeformationMaps.Point O P D R S a B)
    (I : ModuleCat.{0} C.ring) :=
  (C.chart.coefficients.localModel I).cochains

def sourceComplex (C : LiFamilyDeformationMaps.Point O P D R S a B)
    (I : ModuleCat.{0} C.ring) : CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  LiCechObstructionComplexes.integerComplex (C.chart.system.complex I)

def quotientComplex (C : LiFamilyDeformationMaps.Point O P D R S a B) :=
  RubberPOTSourceCharts.complex O P D R S a B C.chart

variable (C : LiFamilyDeformationMaps.Point O P D R S a B)
  (I : ModuleCat.{0} C.ring) (z : SimplexCategory)
  (t : Fin (z.len + 1) → Fin C.chart.cover.count)

/-- A local value is fixed by the actual regular and logarithmic lift differences. -/
structure DifferencePair (x : localValue C I z t) where
  extension : LocalExtension (localChart C z t) I
  pair : Pair (RubberLieQuotientComplexes.parameters P R S C.chart.length)
    (localChart C z t) I extension
  ratios : Ratios (S.chart C.chart.length).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S C.chart.length)
    (RubberLieQuotientComplexes.parameters P R S C.chart.length)
    (localChart C z t) I extension pair (C.chart.geometry.mode z t)
  normalized : Normalized (S.chart C.chart.length).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S C.chart.length)
    (RubberLieQuotientComplexes.parameters P R S C.chart.length)
    (localChart C z t) I extension pair (C.chart.geometry.mode z t) ratios x

def extensionBase {x : localValue C I z t} (F : DifferencePair C I z t x) :
    Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap C.ring F.extension.extension.ring).comp (algebraMap k C.ring))))

def reductionBase : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k (localChart C z t).source)

def reductionBaseMap : reductionBase C z t ⟶ C.spec :=
  Over.homMk (Spec.algebraMap C.ring (localChart C z t).source)
    (by
      change Spec.map (CommRingCat.ofHom (algebraMap C.ring (localChart C z t).source)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k C.ring)) =
          Spec.map (CommRingCat.ofHom (algebraMap k (localChart C z t).source))
      rw [← Spec.map_comp]
      congr 1
      ext b
      exact (IsScalarTower.algebraMap_apply k C.ring (localChart C z t).source b).symm)

/-- An actual standard-frame atlas for a full expanded target family. -/
structure TargetTemplate (m : ℕ) where
  base : Over (Spec (.of k))
  family : ExpandedFamily P R S base
  parameter : base ⟶ ExpansionParameterModels.ParameterSpace k m
  frame : StandardFamilyIdentification P R S family m parameter

/-- The actual reduced target over a source tuple. -/
structure ReducedTarget where
  family : ExpandedFamily P R S (reductionBase C z t)
  original : family.scheme ⟶ C.family.rubber.target.scheme
  original_cartesian : IsPullback original family.projection C.family.rubber.target.projection
    (reductionBaseMap C z t)
  original_zero : zeroIdeal O P D R S family =
    C.family.rubber.target.zero.comap original.left
  original_infinity : family.boundary.left.ker =
    C.family.rubber.target.boundary.left.ker.comap original.left
  sectionMap : Spec (.of (localChart C z t).source) ⟶ family.scheme.left
  section_over : sectionMap ≫ family.projection.left = 𝟙 _
  section_original : sectionMap ≫ original.left =
    (localChart C z t).sourceMap ≫ C.family.rubber.map

/-- One target lift, including its full standard frame and actual reduction. -/
structure TargetLift {x : localValue C I z t} (F : DifferencePair C I z t x)
    (V : ReducedTarget C z t) (h : (localChart C z t).target →+* F.extension.extension.ring) where
  target : ExpandedFamily P R S (extensionBase C I z t F)
  parameter : extensionBase C I z t F ⟶ ExpansionParameterModels.ParameterSpace k C.chart.length
  frame : StandardFamilyIdentification P R S target C.chart.length parameter
  map : Spec (.of F.extension.extension.ring) ⟶ target.scheme.left
  over : map ≫ target.projection.left = 𝟙 _
  in_frame : map ≫ (frame.comparison.hom ≫
      pullback.fst (S.chart C.chart.length).projection parameter).left =
    Spec.map (CommRingCat.ofHom h) ≫ (localChart C z t).targetMap
  reduction : V.family.scheme.left ⟶ target.scheme.left
  reduction_cartesian : IsPullback reduction V.family.projection.left target.projection.left
    (Spec.map (CommRingCat.ofHom F.extension.extension.projection.toRingHom))
  zero : zeroIdeal O P D R S V.family = (zeroIdeal O P D R S target).comap reduction
  infinity : V.family.boundary.left.ker = target.boundary.left.ker.comap reduction
  reduction_map : Spec.map (CommRingCat.ofHom F.extension.extension.projection.toRingHom) ≫
    map = V.sectionMap ≫ reduction

/-- The two parameters may differ. Ordinary log cochains can deform the
smoothing parameters, so the lifts must not be forced into one target fibre. -/
structure FullDifferencePair {x : localValue C I z t} (F : DifferencePair C I z t x) where
  reduced : ReducedTarget C z t
  first : TargetLift C I z t F reduced F.pair.first
  second : TargetLift C I z t F reduced F.pair.second

variable {C I z t} {E : LiFamilyDeformationMaps.Point O P D R S a B} (f : Arrow C E)

/-- One actual change of target-frame atlas, used for both members of every
lift pair and for all coefficient modules. This is a map of full universal
families over an actual scheme map, rather than an unrelated log operator. -/
structure TemplateChange where
  left : TargetTemplate (P := P) (R := R) (S := S) C.chart.length
  right : TargetTemplate (P := P) (R := R) (S := S) E.chart.length
  base : right.base ⟶ left.base
  target : right.family.scheme ⟶ left.family.scheme
  cartesian : IsPullback target right.family.projection left.family.projection base
  zero : zeroIdeal O P D R S right.family = (zeroIdeal O P D R S left.family).comap target.left
  infinity : right.family.boundary.left.ker = left.family.boundary.left.ker.comap target.left
  leftPoint : C.spec ⟶ left.base
  rightPoint : E.spec ⟶ right.base
  points : rightPoint ≫ base = f.hom.base ≫ leftPoint
  leftTarget : C.family.rubber.target.scheme ⟶ left.family.scheme
  rightTarget : E.family.rubber.target.scheme ⟶ right.family.scheme
  left_cartesian : IsPullback leftTarget C.family.rubber.target.projection left.family.projection leftPoint
  right_cartesian : IsPullback rightTarget E.family.rubber.target.projection right.family.projection rightPoint
  normalized : rightTarget ≫ target = targetArrow f ≫ leftTarget

variable {f}

/-- The given target lift is the actual pullback of its common atlas template. -/
structure TemplateLift (T : TargetTemplate (P := P) (R := R) (S := S) C.chart.length)
    {I : ModuleCat.{0} C.ring} {z : SimplexCategory}
    {t : Fin (z.len + 1) → Fin C.chart.cover.count} {x : localValue C I z t}
    {F : DifferencePair C I z t x} {V : ReducedTarget C z t}
    {h : (localChart C z t).target →+* F.extension.extension.ring}
    (L : TargetLift C I z t F V h) where
  point : extensionBase C I z t F ⟶ T.base
  map : L.target.scheme ⟶ T.family.scheme
  cartesian : IsPullback map L.target.projection T.family.projection point
  parameter : L.parameter = point ≫ T.parameter
  frame : map ≫ (T.frame.comparison.hom ≫
      pullback.fst (S.chart C.chart.length).projection T.parameter) =
    L.frame.comparison.hom ≫ pullback.fst (S.chart C.chart.length).projection L.parameter

variable (f) (T : TemplateChange f)
  (N : ModuleCat.{0} E.ring) (u : I →ₛₗ[scalar f] N)
  (v : Fin (z.len + 1) → Fin E.chart.cover.count)
  {x : localValue C I z t} {y : localValue E N z v}
  (F : DifferencePair C I z t x) (H : DifferencePair E N z v y)
  (V : FullDifferencePair C I z t F) (W : FullDifferencePair E N z v H)

/-- Full geometric comparison of a pair of differences. It fixes both
lifted maps, the actual target-family map and its original reduction. -/
structure FullPairMap where
  scalar : (localChart C z t).source →ₛₗ[LiFamilyDeformationMaps.scalar f]
    (localChart E z v).source
  sourceRing : (localChart C z t).source →+* (localChart E z v).source
  source_ring : ∀ b, scalar b = sourceRing b
  source_geometric : Spec.map (CommRingCat.ofHom sourceRing) ≫ (localChart C z t).sourceMap =
    (localChart E z v).sourceMap ≫ sourceArrow f
  extension : F.extension.extension.ring →+* H.extension.extension.ring
  reduction : ∀ b, H.extension.extension.projection (extension b) =
    sourceRing (F.extension.extension.projection b)
  coefficientMap : sourceCoefficient (localChart C z t) I →ₛₗ[LiFamilyDeformationMaps.scalar f]
    sourceCoefficient (localChart E z v) N
  coefficient_tensor : ∀ b w, coefficientMap (b ⊗ₜ[C.ring] w) = sourceRing b ⊗ₜ[E.ring] u w
  coefficient_normalized : ∀ b : F.extension.extension.coefficient,
    H.extension.coefficient.hom
      (H.extension.extension.kernel
        ⟨extension ((F.extension.extension.kernel.symm b).val), by
          change H.extension.extension.projection (extension _) = 0
          rw [reduction]
          have hb := (F.extension.extension.kernel.symm b).property
          change F.extension.extension.projection ((F.extension.extension.kernel.symm b).val) = 0 at hb
          rw [hb, map_zero]⟩) =
      coefficientMap (F.extension.coefficient.hom b)
  leftFirst : TemplateLift T.left V.first
  leftSecond : TemplateLift T.left V.second
  rightFirst : TemplateLift T.right W.first
  rightSecond : TemplateLift T.right W.second
  extensionBaseMap : extensionBase E N z v H ⟶ extensionBase C I z t F
  extension_base : extensionBaseMap.left = Spec.map (CommRingCat.ofHom extension)
  firstPoint : rightFirst.point ≫ T.base = extensionBaseMap ≫ leftFirst.point
  secondPoint : rightSecond.point ≫ T.base = extensionBaseMap ≫ leftSecond.point
  firstTarget : W.first.target.scheme.left ⟶ V.first.target.scheme.left
  secondTarget : W.second.target.scheme.left ⟶ V.second.target.scheme.left
  first_over : firstTarget ≫ V.first.target.projection.left =
    W.first.target.projection.left ≫ Spec.map (CommRingCat.ofHom extension)
  second_over : secondTarget ≫ V.second.target.projection.left =
    W.second.target.projection.left ≫ Spec.map (CommRingCat.ofHom extension)
  first_template : firstTarget ≫ leftFirst.map.left = rightFirst.map.left ≫ T.target.left
  second_template : secondTarget ≫ leftSecond.map.left = rightSecond.map.left ≫ T.target.left
  first : W.first.map ≫ firstTarget = Spec.map (CommRingCat.ofHom extension) ≫ V.first.map
  second : W.second.map ≫ secondTarget = Spec.map (CommRingCat.ofHom extension) ≫ V.second.map
  reduced : W.reduced.family.scheme.left ⟶ V.reduced.family.scheme.left
  reduced_original : reduced ≫ V.reduced.original.left =
    W.reduced.original.left ≫ (targetArrow f).left
  first_square : reduced ≫ V.first.reduction = W.first.reduction ≫ firstTarget
  second_square : reduced ≫ V.second.reduction = W.second.reduction ≫ secondTarget
  reduced_section : W.reduced.sectionMap ≫ reduced =
    Spec.map (CommRingCat.ofHom sourceRing) ≫ V.reduced.sectionMap

section Refinements

variable {C₀ E₀ : LiFamilyDeformationMaps.Point O P D R S a B} (f₀ : Arrow C₀ E₀)

/-- The actual source-tuple maps of a refinement, with every coface and
degeneracy. The index map is independent of the coefficient and value. -/
structure CechGeometry where
  index : Fin E₀.chart.cover.count → Fin C₀.chart.cover.count
  source : ∀ (z : SimplexCategory) (v : Fin (z.len + 1) → Fin E₀.chart.cover.count),
    (localChart C₀ z (index ∘ v)).source →+* (localChart E₀ z v).source
  scalar : ∀ z v (r : C₀.ring), source z v (algebraMap C₀.ring _ r) =
    algebraMap E₀.ring _ (LiFamilyDeformationMaps.scalar f₀ r)
  geometric : ∀ z v, Spec.map (CommRingCat.ofHom (source z v)) ≫
    (localChart C₀ z (index ∘ v)).sourceMap = (localChart E₀ z v).sourceMap ≫ sourceArrow f₀
  cofaces : ∀ {z w : SimplexCategory} (s : z ⟶ w)
    (v : Fin (w.len + 1) → Fin E₀.chart.cover.count) (b : (localChart C₀ z (index ∘ v ∘ s.toOrderHom)).source),
      source w v ((C₀.chart.geometry.restriction s (index ∘ v)).source b) =
        (E₀.chart.geometry.restriction s v).source (source z (v ∘ s.toOrderHom) b)

variable (G : CechGeometry f₀) (T₀ : TemplateChange f₀)
  (I₀ : ModuleCat.{0} C₀.ring) (N₀ : ModuleCat.{0} E₀.ring)
  (u₀ : I₀ →ₛₗ[scalar f₀] N₀)

/-- An actual Cech map is fixed on every local value by full target-pair
transport. Its native naturality retains all simplicial operators. -/
structure CechMap where
  map : logCochains C₀ I₀ ⟶ logCochains E₀ N₀ ⋙ ModuleCat.restrictScalars (scalar f₀)
  localMap : ∀ (z : SimplexCategory) (v : Fin (z.len + 1) → Fin E₀.chart.cover.count),
    localValue C₀ I₀ z (G.index ∘ v) →ₛₗ[scalar f₀] localValue E₀ N₀ z v
  normalized : ∀ z v (x : (logCochains C₀ I₀).obj z),
    ((E₀.chart.coefficients.localModel N₀).comparison z).hom (map.app z x) v =
      localMap z v (((C₀.chart.coefficients.localModel I₀).comparison z).hom x (G.index ∘ v))
  leftPair : ∀ z v x, DifferencePair C₀ I₀ z (G.index ∘ v) x
  leftFull : ∀ z v x, FullDifferencePair C₀ I₀ z (G.index ∘ v) (leftPair z v x)
  rightPair : ∀ z v x, DifferencePair E₀ N₀ z v (localMap z v x)
  rightFull : ∀ z v x, FullDifferencePair E₀ N₀ z v (rightPair z v x)
  transport : ∀ z v x, FullPairMap f₀ T₀ N₀ u₀ v (leftPair z v x) (rightPair z v x)
    (leftFull z v x) (rightFull z v x)
  source_normalized : ∀ z v x, (transport z v x).sourceRing = G.source z v

def termIso (C : LiFamilyDeformationMaps.Point O P D R S a B)
    (I : ModuleCat.{0} C.ring) (j : ℕ) :
    (sourceComplex C I).X (j : ℤ) ≅ LiCechObstructionComplexes.term (C.chart.system.complex I) j :=
  (LiCechObstructionComplexes.complex (C.chart.system.complex I)).extendXIso
    (ComplexShape.embeddingUpIntGE 0) (i := j) (by simp)

def restrictionComplex {A T : Type} [CommRing A] [CommRing T] (φ : A →+* T) :=
  (ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)

variable {G T₀ I₀ N₀ u₀}

/-- The change of universal target lifts is an actual zero-cochain.
Its two maps come from the new lifts and the old lifts transported along
the fixed universal-curve/dual and full target-template comparisons.
This is the off-diagonal correction in a general source refinement. -/
structure UniversalLiftDifferences (G : CechGeometry f₀) (T : TemplateChange f₀)
    {F : ResolutionMap f₀} (V : DualComparison f₀ F) where
  cochain : (logCochains E₀ (rightDual E₀.chart.source.matrix)).obj ⦋0⦌
  pair : ∀ j : Fin E₀.chart.cover.count,
    DifferencePair E₀ (rightDual E₀.chart.source.matrix) ⦋0⦌ (fun _ => j)
      (((E₀.chart.coefficients.localModel (rightDual E₀.chart.source.matrix)).comparison ⦋0⦌).hom
        cochain (fun _ => j))
  full : ∀ j, FullDifferencePair E₀ (rightDual E₀.chart.source.matrix) ⦋0⦌ (fun _ => j) (pair j)
  globalBase : ∀ j, TrivSqZeroExt E₀.ring (rightDual E₀.chart.source.matrix) →+*
    (pair j).extension.extension.ring
  global_scalar : ∀ j r, globalBase j (TrivSqZeroExt.inl r) =
    algebraMap E₀.ring (pair j).extension.extension.ring r
  global_coefficient : ∀ j α, globalBase j (TrivSqZeroExt.inr α) =
    (pair j).extension.baseMap (TrivSqZeroExt.inr (1 ⊗ₜ[E₀.ring] α))
  universal : ∀ j, Spec (.of (pair j).extension.extension.ring) ⟶ E₀.chart.universal.universal.curve.X
  over : ∀ j, universal j ≫ E₀.chart.universal.universal.curve.π =
    Spec.map (CommRingCat.ofHom (globalBase j))
  cartesian : ∀ j, IsPullback
    (Spec.map (CommRingCat.ofHom (pair j).extension.extension.projection.toRingHom))
    (localChart E₀ ⦋0⦌ (fun _ => j)).sourceMap (universal j) E₀.chart.universal.universal.reduction
  newMap : ∀ j, (E₀.chart.lifts j).extensionData.extension.ring →+*
    (pair j).extension.extension.ring
  oldMap : ∀ j, (C₀.chart.lifts (G.index j)).extensionData.extension.ring →+*
    (pair j).extension.extension.ring
  new_source : ∀ j, Spec.map (CommRingCat.ofHom (newMap j)) ≫ (E₀.chart.lifts j).source = universal j
  old_source : ∀ j, Spec.map (CommRingCat.ofHom (oldMap j)) ≫ (C₀.chart.lifts (G.index j)).source =
    universal j ≫ V.universal.inv.iso.hom ≫ V.rightTransport.map C₀.chart.universal.universal
  new_scalar : ∀ j x, newMap j ((E₀.chart.lifts j).globalBase x) = globalBase j x
  old_scalar : ∀ j x, oldMap j ((C₀.chart.lifts (G.index j)).globalBase x) =
    globalBase j (V.rightTransport.split.map x)
  new_reduction : ∀ j,
    Spec.map (CommRingCat.ofHom (pair j).extension.extension.projection.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (newMap j)) =
    (E₀.chart.geometry.source ⦋0⦌ (fun _ => j)).hom ≫ WidePullback.π _ 0 ≫
      Spec.map (CommRingCat.ofHom (E₀.chart.lifts j).extensionData.extension.projection.toRingHom)
  old_reduction : ∀ j,
    Spec.map (CommRingCat.ofHom (pair j).extension.extension.projection.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (oldMap j)) =
    Spec.map (CommRingCat.ofHom (G.source ⦋0⦌ (fun _ => j))) ≫
      (C₀.chart.geometry.source ⦋0⦌ (fun _ => G.index j)).hom ≫ WidePullback.π _ 0 ≫
      Spec.map (CommRingCat.ofHom (C₀.chart.lifts (G.index j)).extensionData.extension.projection.toRingHom)
  first : ∀ j,
    Spec.map (CommRingCat.ofHom (pair j).pair.first) ≫ (localChart E₀ ⦋0⦌ (fun _ => j)).targetMap =
      Spec.map (CommRingCat.ofHom (newMap j)) ≫ (E₀.chart.lifts j).target
  firstTemplate : ∀ j, TemplateLift T.right (full j).first
  secondTemplate : ∀ j, TemplateLift T.right (full j).second
  second : ∀ j,
    (full j).second.map ≫ (secondTemplate j).map.left ≫ T.target.left ≫
      (T.left.frame.comparison.hom ≫
        pullback.fst (S.chart C₀.chart.length).projection T.left.parameter).left =
      Spec.map (CommRingCat.ofHom (oldMap j)) ≫ (C₀.chart.lifts (G.index j)).target

/-- Evaluate the actual universal lift-difference cochain by the native
finite tensor-dual pairing and the fixed coefficient Cech transport. -/
def correctionValue {G : CechGeometry f₀} {T : TemplateChange f₀} {F : ResolutionMap f₀}
    {V : DualComparison f₀ F} (H : UniversalLiftDifferences f₀ G T V)
    (N : ModuleCat.{0} E₀.ring) (x : rightCoefficient E₀.chart.source.matrix N) :
    (logCochains E₀ N).obj ⦋0⦌ :=
  (LiCechCoefficientModels.transport
    (g := (S.chart E₀.chart.length).projection.left)
    (J := RubberLieQuotientComplexes.boundaries O P D R S E₀.chart.length)
    (t := RubberLieQuotientComplexes.parameters P R S E₀.chart.length)
    (L := E₀.chart.cover) (G := E₀.chart.geometry)
    (u := ModuleCat.ofHom
      (LiTensorEvaluation.evaluation E₀.ring (LiFiniteComplexPresentations.right E₀.chart.source.matrix) N x))
    E₀.chart.coefficients).app ⦋0⦌ H.cochain

/-- A single source refinement fixes its full raw cochain map by the
source matrix, the actual delta and every Cech component. -/
structure SourceRefinement where
  family : FamilyMap f₀
  resolution : ResolutionMap f₀
  dual : DualComparison f₀ resolution
  template : TemplateChange f₀
  geometry : CechGeometry f₀
  differences : UniversalLiftDifferences f₀ geometry template dual
  curve : ∀ (I : ModuleCat.{0} C₀.ring) (N : ModuleCat.{0} E₀.ring)
    (u : I →ₛₗ[scalar f₀] N), CurveTransport f₀ I N u
  coefficients : ∀ (I : ModuleCat.{0} C₀.ring) (N : ModuleCat.{0} E₀.ring)
    (u : I →ₛₗ[scalar f₀] N), SourceCoefficientMap f₀ I N u resolution
  source : ∀ (I : ModuleCat.{0} C₀.ring) (N : ModuleCat.{0} E₀.ring)
    (u : I →ₛₗ[scalar f₀] N), SourceComparison f₀ I N u (curve I N u) (coefficients I N u)
  cech : ∀ (I : ModuleCat.{0} C₀.ring) (N : ModuleCat.{0} E₀.ring)
    (u : I →ₛₗ[scalar f₀] N), CechMap f₀ geometry template I N u
  raw : ∀ (I : ModuleCat.{0} C₀.ring) (N : ModuleCat.{0} E₀.ring)
    (_u : I →ₛₗ[scalar f₀] N), sourceComplex C₀ I ⟶
      (restrictionComplex (scalar f₀)).obj (sourceComplex E₀ N)
  zero : ∀ I N u x,
    (termIso E₀ N 0).hom ((raw I N u).f 0 x) =
      (E₀.chart.system.source N).zero.inv
        ((coefficients I N u).left ((C₀.chart.system.source I).zero.hom ((termIso C₀ I 0).hom x)))
  one : ∀ I N u x,
    (termIso E₀ N 1).hom ((raw I N u).f 1 x) =
      ((E₀.chart.system.source N).one.inv
        ((coefficients I N u).right
          ((C₀.chart.system.source I).one.hom (((termIso C₀ I 1).hom x).1))),
      (E₀.chart.system.log N).inv.app ⦋0⦌
        ((show (logCochains E₀ N).obj ⦋0⦌ from
          (cech I N u).map.app ⦋0⦌
            ((C₀.chart.system.log I).hom.app ⦋0⦌ (((termIso C₀ I 1).hom x).2))) -
        correctionValue f₀ differences N
          ((coefficients I N u).right
            ((C₀.chart.system.source I).one.hom (((termIso C₀ I 1).hom x).1)))))
  higher : ∀ I N u (j : ℕ) x,
    (termIso E₀ N (j + 2)).hom ((raw I N u).f (j + 2 : ℕ) x) =
      (E₀.chart.system.log N).inv.app ⦋j + 1⦌
        ((cech I N u).map.app ⦋j + 1⦌
          ((C₀.chart.system.log I).hom.app ⦋j + 1⦌ ((termIso C₀ I (j + 2)).hom x)))
  torusMap : MonoidalCategoryStruct.tensorObj E₀.spec
      (ExpansionParameterModels.torusScheme k (C₀.chart.length + 1)) ⟶
    ExpansionParameterModels.torusScheme k (E₀.chart.length + 1)
  lieCoefficient : Fin (C₀.chart.length + 1) → Fin (E₀.chart.length + 1) → E₀.ring
  torus_normalized : ∀ j : Fin (C₀.chart.length + 1),
    E₀.chart.torus.units (TorusInfinitesimalPoints.doubled E₀.ring)
      (CartesianMonoidalCategory.lift
        (TorusInfinitesimalPoints.projection E₀.ring)
        (TorusInfinitesimalPoints.point C₀.chart.torus E₀.ring j) ≫ torusMap) =
      fun i => Units.map (Scheme.ΓSpecIso (.of (TrivSqZeroExt E₀.ring E₀.ring))).inv.hom.toMonoidHom
        (TorusInfinitesimalPoints.unit E₀.ring (lieCoefficient j i))
  lie : RubberLieQuotientComplexes.lieComplex (A := C₀.ring) C₀.chart.length ⟶
    (restrictionComplex (scalar f₀)).obj
      (RubberLieQuotientComplexes.lieComplex (A := E₀.ring) E₀.chart.length)
  lie_normalized : ∀ j : Fin (C₀.chart.length + 1),
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
      (ModuleCat.of E₀.ring (Fin (E₀.chart.length + 1) → E₀.ring))).hom)
        (lie.f 1 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
          (ModuleCat.of C₀.ring (Fin (C₀.chart.length + 1) → C₀.ring))).inv (Pi.single j 1))) =
      lieCoefficient j
  action : C₀.chart.lie.map ≫ raw (ModuleCat.of C₀.ring C₀.ring)
      (ModuleCat.of E₀.ring E₀.ring) (scalar f₀).toSemilinearMap =
    lie ≫ (restrictionComplex (scalar f₀)).map E₀.chart.lie.map

/-- The quotient transition is the actual cone map for the computed
raw source and torus arrows, followed by the native scalar-restriction comparison. -/
def quotientMap (F : SourceRefinement f₀) :
    quotientComplex C₀ ⟶ (restrictionComplex (scalar f₀)).obj (quotientComplex E₀) :=
  CochainComplex.mappingCone.map C₀.chart.lie.map
    ((restrictionComplex (scalar f₀)).map E₀.chart.lie.map) F.lie
    (F.raw (ModuleCat.of C₀.ring C₀.ring) (ModuleCat.of E₀.ring E₀.ring)
      (scalar f₀).toSemilinearMap) F.action ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso E₀.chart.lie.map
      (ModuleCat.restrictScalars (scalar f₀))).inv

end Refinements

section Global

/-- The genuine module-presheaf cochain category on every affine stack point. -/
abbrev GlobalComplex := CochainComplex (ModulePresheaf B.stack) ℤ

def evaluatePoint (L : GlobalComplex (B := B)) (p : AffinePoint B.stack) :
    CochainComplex (ModuleCat.{0} ((rings B.stack).obj (op p))) ℤ :=
  ((PresheafOfModules.evaluation (rings B.stack ⋙ forget₂ CommRingCat RingCat) (op p)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L

/-- The affine presentation is transported by the actual Gamma-Spec isomorphism. -/
def evaluateChart (L : GlobalComplex (B := B)) (C : LiFamilyDeformationMaps.Point O P D R S a B) :
    CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  (restrictionComplex (Scheme.ΓSpecIso (.of C.ring)).inv.hom).obj (evaluatePoint L C.native)

/-- Projective cofibrancy in the genuine cochain model: lifting against
every degreewise surjective quasi-isomorphism. It ensures that the
displayed ordinary tensor computes derived scalar extension. -/
def IsCofibrantComplex {A : Type} [CommRing A] (K : CochainComplex (ModuleCat.{0} A) ℤ) : Prop :=
  ∀ (L M : CochainComplex (ModuleCat.{0} A) ℤ) (p : L ⟶ M),
    QuasiIso p → (∀ j : ℤ, Function.Surjective ((p.f j).hom)) →
      ∀ f : K ⟶ M, ∃ g : K ⟶ L, g ≫ p = f

/-- The actual global restriction. Every component is the native
presheaf map on the actual stack arrow; the scalar square follows from
the Gamma-Spec definition of scalar. -/
def globalRestriction (L : GlobalComplex (B := B))
    {C E : LiFamilyDeformationMaps.Point O P D R S a B} (f : Arrow C E) :
    evaluateChart L C ⟶ (restrictionComplex (scalar f)).obj (evaluateChart L E) where
  f j := by
    letI : Module C.ring ((evaluatePoint L C.native).X j) := ((evaluateChart L C).X j).isModule
    letI : Module E.ring ((evaluatePoint L E.native).X j) := ((evaluateChart L E).X j).isModule
    letI : Module ((rings B.stack).obj (op C.native)) ((evaluateChart L C).X j) :=
      ((evaluatePoint L C.native).X j).isModule
    letI : Module ((rings B.stack).obj (op E.native)) ((evaluateChart L E).X j) :=
      ((evaluatePoint L E.native).X j).isModule
    letI : Module C.ring ((evaluateChart L E).X j) :=
      (((restrictionComplex (scalar f)).obj (evaluateChart L E)).X j).isModule
    exact ModuleCat.ofHom (show (evaluateChart L C).X j →ₗ[C.ring]
      ((restrictionComplex (scalar f)).obj (evaluateChart L E)).X j from
      { toFun := fun x => (L.X j).map f.op x
        map_add' := fun x y => map_add ((L.X j).map f.op).hom x y
        map_smul' := by
          intro r x
          change (L.X j).map f.op
              ((show (rings B.stack).obj (op C.native) from
                (Scheme.ΓSpecIso (.of C.ring)).inv.hom r) • x) =
            (show (rings B.stack).obj (op E.native) from
              (Scheme.ΓSpecIso (.of E.ring)).inv.hom (scalar f r)) • (L.X j).map f.op x
          rw [PresheafOfModules.map_smul]
          congr 1
          change f.hom.base.left.appTop.hom ((Scheme.ΓSpecIso (.of C.ring)).inv.hom r) =
            (Scheme.ΓSpecIso (.of E.ring)).inv.hom (scalar f r)
          (simp [LiFamilyDeformationMaps.scalar, RingHom.comp_apply]; rfl) })
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom ((L.d i j).naturality f.op) x

/-- A common source refinement is genuinely covering over the second
chart. Its two actual arrows give the same composite stack arrow. -/
structure RefinementSpan {C E : LiFamilyDeformationMaps.Point O P D R S a B} (f : Arrow C E) where
  point : LiFamilyDeformationMaps.Point O P D R S a B
  left : Arrow C point
  right : Arrow E point
  composite : right ≫ f = left
  etale : Etale right.hom.base.left
  covering : Function.Surjective right.hom.base.left
  leftSource : SourceRefinement left
  rightSource : SourceRefinement right

/-- An étale cover of an affine point `p` of the rubber moduli stack by a chart: a chart point
`point` (`LiFamilyDeformationMaps.Point`) and a morphism `arrow` from its affine stack point to `p`
whose underlying morphism of schemes is étale (`etale`) and surjective (`covering`). -/
structure SourceCover (p : AffinePoint B.stack) where
  point : LiFamilyDeformationMaps.Point O P D R S a B
  arrow : point.native ⟶ p
  etale : Etale arrow.hom.base.left
  covering : Function.Surjective arrow.hom.base.left

/-- Actual derived scalar extension on every affine test arrow. The
balanced tensor map is fixed on every pure tensor by native restriction. -/
structure BaseChange (L : GlobalComplex (B := B)) {p q : AffinePoint B.stack} (f : p ⟶ q) where
  map : ((ModuleCat.extendScalars ((rings B.stack).map f.op).hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (evaluatePoint L q) ⟶ evaluatePoint L p
  normalized : ∀ j (r : (rings B.stack).obj (op p)) (x : (evaluatePoint L q).X j),
    map.f j (r ⊗ₜ[(rings B.stack).obj (op q), ((rings B.stack).map f.op).hom] x) =
      r • (L.X j).map f.op x
  quasi : QuasiIso map

/-- The global source object and all its maps are fixed by actual
cochain augmentations. Native presheaf functor laws supply the triple
cocycle; the two displayed homotopies bind every actual overlap and
frame change to the source construction after a covering refinement. -/
structure Descent where
  complex : GlobalComplex (B := B)
  cofibrant : ∀ p : AffinePoint B.stack, IsCofibrantComplex (evaluatePoint complex p)
  cover : ∀ p : AffinePoint B.stack, IsNoetherian p.obj.base.left →
    LocallyOfFiniteType p.obj.base.hom → SourceCover p
  baseChange : ∀ {p q : AffinePoint B.stack} (f : p ⟶ q), BaseChange complex f
  augmentation : ∀ C : LiFamilyDeformationMaps.Point O P D R S a B,
    evaluateChart complex C ⟶ quotientComplex C
  quasi : ∀ C, QuasiIso (augmentation C)
  refinement : ∀ {C E : LiFamilyDeformationMaps.Point O P D R S a B} (f : Arrow C E),
    RefinementSpan f
  left : ∀ {C E : LiFamilyDeformationMaps.Point O P D R S a B} (f : Arrow C E),
    Homotopy
      (augmentation C ≫ quotientMap (refinement f).left (refinement f).leftSource)
      (globalRestriction complex (refinement f).left ≫
        (restrictionComplex (scalar (refinement f).left)).map (augmentation (refinement f).point))
  right : ∀ {C E : LiFamilyDeformationMaps.Point O P D R S a B} (f : Arrow C E),
    Homotopy
      (augmentation E ≫ quotientMap (refinement f).right (refinement f).rightSource)
      (globalRestriction complex (refinement f).right ≫
        (restrictionComplex (scalar (refinement f).right)).map (augmentation (refinement f).point))

/-- The actual affine-point restriction before a Gamma-Spec frame is chosen. -/
def pointRestriction (L : GlobalComplex (B := B)) {p q : AffinePoint B.stack} (f : p ⟶ q) :
    evaluatePoint L q ⟶ (restrictionComplex ((rings B.stack).map f.op).hom).obj (evaluatePoint L p) where
  f j := (L.X j).map f.op
  comm' i j _ := (L.d i j).naturality f.op

variable (E : VectorBundleStack B.stack)

/-- The tangent-obstruction differential of the actual global bundle-stack diagram. -/
def bundleArrow (p : AffinePoint B.stack) :=
  (CochainComplex.singleFunctor (ModuleCat.{0} ((rings B.stack).obj (op p))) 2).map
    (E.linear.diagram.modules p).differential

def bundleComplex (p : AffinePoint B.stack) :=
  CochainComplex.mappingCone (bundleArrow E p)

/-- Native two-term restriction maps are fixed on both displayed module blocks. -/
structure BundleTransition {p q : AffinePoint B.stack} (f : p ⟶ q) where
  first :
    (CochainComplex.singleFunctor (ModuleCat.{0} ((rings B.stack).obj (op q))) 2).obj
      (E.linear.diagram.modules q).degreeZero ⟶
    (restrictionComplex ((rings B.stack).map f.op).hom).obj
      ((CochainComplex.singleFunctor (ModuleCat.{0} ((rings B.stack).obj (op p))) 2).obj
        (E.linear.diagram.modules p).degreeZero)
  second :
    (CochainComplex.singleFunctor (ModuleCat.{0} ((rings B.stack).obj (op q))) 2).obj
      (E.linear.diagram.modules q).degreeOne ⟶
    (restrictionComplex ((rings B.stack).map f.op).hom).obj
      ((CochainComplex.singleFunctor (ModuleCat.{0} ((rings B.stack).obj (op p))) 2).obj
        (E.linear.diagram.modules p).degreeOne)
  first_normalized : ∀ x : (E.linear.diagram.modules q).degreeZero,
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 2
      (E.linear.diagram.modules p).degreeZero).hom
        (first.f 2 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 2
          (E.linear.diagram.modules q).degreeZero).inv x)) =
      (E.linear.diagram.restriction f).degreeZero x
  second_normalized : ∀ x : (E.linear.diagram.modules q).degreeOne,
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 2
      (E.linear.diagram.modules p).degreeOne).hom
        (second.f 2 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 2
          (E.linear.diagram.modules q).degreeOne).inv x)) =
      (E.linear.diagram.restriction f).degreeOne x
  differential : bundleArrow E q ≫ second =
    first ≫ (restrictionComplex ((rings B.stack).map f.op).hom).map (bundleArrow E p)

/-- The actual native cone transition for these two fixed module maps. -/
def bundleTransition {p q : AffinePoint B.stack} {f : p ⟶ q} (T : BundleTransition E f) :
    bundleComplex E q ⟶
      (restrictionComplex ((rings B.stack).map f.op).hom).obj (bundleComplex E p) :=
  CochainComplex.mappingCone.map (bundleArrow E q)
    ((restrictionComplex ((rings B.stack).map f.op).hom).map (bundleArrow E p))
    T.first T.second T.differential ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso (bundleArrow E p)
        (ModuleCat.restrictScalars ((rings B.stack).map f.op).hom)).inv

/-- Strict cochain realization of the bundle diagram, objectwise and arrow by arrow.
The value and every arrow are normalized on the original two module blocks, and each restriction
arrow has its own comparison homotopy. These homotopies are not required to be compatible with
the diagram's unit and composition cells (`mapId`, `mapComp`), so this is weaker than a
realization of the homotopy-coherent diagram (a pseudonatural equivalence carrying those cells).
This is an ordinary source realization input, independent of the Li theorem. -/
structure BundleRealization where
  complex : GlobalComplex (B := B)
  value : ∀ p : AffinePoint B.stack, evaluatePoint complex p ⟶ bundleComplex E p
  quasi : ∀ p, QuasiIso (value p)
  transition : ∀ {p q : AffinePoint B.stack} (f : p ⟶ q), BundleTransition E f
  naturality : ∀ {p q : AffinePoint B.stack} (f : p ⟶ q),
    Homotopy (value q ≫ bundleTransition E (transition f))
      (pointRestriction complex f ≫
        (restrictionComplex ((rings B.stack).map f.op).hom).map (value p))

/-- One global cochain map identifies the actual Li source with the actual
bundle-stack diagram. Objectwise atlas isomorphisms cannot replace this map.

This identifies the underlying complexes only: compatibility with the obstruction assignment
(the square-zero obstruction classes of Li, math/0110113v1, Thm. 1.22, as pulled back in
Behrend–Fantechi, Thm. 4.5) is not required, so for instance the negative of a comparison also
qualifies. -/
structure BundleBinding (L : Descent (O := O) (P := P) (D := D) (R := R) (S := S) (a := a) (B := B)) where
  realization : BundleRealization E
  comparison : L.complex ⟶ realization.complex
  quasi : ∀ p : AffinePoint B.stack,
    QuasiIso (((PresheafOfModules.evaluation (rings B.stack ⋙ forget₂ CommRingCat RingCat) (op p)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map comparison)

end Global

end MathlibExt.AlgebraicGeometry.LiFamilySourceDescent
