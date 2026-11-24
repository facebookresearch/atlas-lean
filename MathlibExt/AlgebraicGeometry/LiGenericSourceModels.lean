/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiLiftedSourceCechModels
public import MathlibExt.AlgebraicGeometry.RelativeMapGluingGeometry
public import MathlibExt.AlgebraicGeometry.LiSharedTargetCechModels

/-!
# Relative and central Li sources with a shared target

The source may have any finite number of connected marked components,
including zero. All components map to one actual target over one actual
parameter. A first-order target parameter is one scheme morphism; the
local lifts on every component use this same morphism.

The finite marked-curve extension groupoid is represented on every
coefficient module, including its actual arrows and Cartesian transports.
Its identity tensors determine the universal extension and the
`d`-dual trivialization. The local maps and their differences are genuine
scheme and ring maps on these extensions. Their ordinary, boundary and
node values are the existing native Li Cech modules, with actual tensor
coefficients, normal equations and coordinate changes.

This is a construction target, rather than an assumed final obstruction
bundle. The relative/central source and its finite presentation may be
constructed by direct Wanted commands. No finite-type condition is imposed
on a coefficient algebra here.

Source: Jun Li, arXiv:math/0110113v1, (1.15)--(1.25), Theorems 2.2--2.3
and Proposition 2.4; arXiv:math/0009097v1, Sections 2 and 4. The pinned GW
PDF has SHA256 70b4202f5882ae4c0dcc0e80879f043146e84e57dbf3c7c9fa193e5a741dd14b.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGenericSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.Opposite MarkedCurveStabilization StackBundleCones
open LiAffineMapCharts LiCechChartModules LiFiniteComplexPresentations
open LiMarkedCurveExtensions LiUniversalSourceExtensions LiLocalLiftDifferences
open scoped Simplicial TensorProduct BigOperators

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm
  LiMarkedCurveExtensions.oppositeTower

variable {k A : Type} [Field k] [CommRing A] [Algebra k A]

/-- Actual finite curves over the same coefficient scheme and one common target. -/
structure MapFamily (k A : Type) [Field k] [CommRing A] [Algebra k A] where
  components : ℕ
  markings : Fin components → ℕ
  genus : Fin components → ℕ
  curve : ∀ v, MarkedFamily (Spec (.of A)) (markings v) (genus v)
  target : Scheme.{0}
  structural : target ⟶ Spec (.of k)
  parameterBase : Scheme.{0}
  parameterStructural : parameterBase ⟶ Spec (.of k)
  projection : target ⟶ parameterBase
  projection_structural : projection ≫ parameterStructural = structural
  parameter : Spec (.of A) ⟶ parameterBase
  parameter_structural : parameter ≫ parameterStructural = Spec.algebraMap k A
  map : ∀ v, (curve v).X ⟶ target
  map_structural : ∀ v, map v ≫ structural = (curve v).π ≫ Spec.algebraMap k A
  over : ∀ v, map v ≫ projection = (curve v).π ≫ parameter
  relative : ∀ v, (curve v).X ⟶ pullback projection parameter
  relative_target : ∀ v, relative v ≫ pullback.fst projection parameter = map v
  relative_base : ∀ v, relative v ≫ pullback.snd projection parameter = (curve v).π
  predeformable : ∀ v, RelativeExpandedMapFamilies.IsPredeformable
    (curve v).π (pullback.snd projection parameter) (relative v) (relative_base v)
  boundaryCount : ℕ
  boundary : Fin boundaryCount → target.IdealSheafData
  root : ∀ v, Fin (markings v) → Option (Fin boundaryCount)
  order : ∀ v, Fin (markings v) → ℕ
  positive : ∀ v i j, root v i = some j → 0 < order v i
  contact : ∀ v j (U : (curve v).X.affineOpens),
    ((boundary j).comap (map v)).ideal U =
      ∏ i : {i : Fin (markings v) // root v i = some j},
        ((curve v).marking i.val).ker.ideal U ^ order v i.val
  parameterCount : ℕ
  parameterBaseFunction : Fin parameterCount → Γ(parameterBase, ⊤)
  parameterFunction : Fin parameterCount → Γ(target, ⊤)
  parameter_function : ∀ i, projection.appTop.hom (parameterBaseFunction i) = parameterFunction i

variable (F : MapFamily k A)

/-- A genuine extension of every component over the same split square-zero base. -/
structure CurveExtension (I : ModuleCat.{0} A) where
  component : ∀ v : Fin F.components, LiMarkedCurveExtensions.Family (F.curve v) I

instance curveExtensionGroupoid (I : ModuleCat.{0} A) : Groupoid (CurveExtension F I) where
  Hom E H := ∀ v, E.component v ⟶ H.component v
  id E v := 𝟙 (E.component v)
  comp e h v := e v ≫ h v
  inv e v := Groupoid.inv (e v)
  id_comp e := by funext v; exact Category.id_comp (e v)
  comp_id e := by funext v; exact Category.comp_id (e v)
  assoc e h j := by funext v; exact Category.assoc (e v) (h v) (j v)
  inv_comp e := by funext v; exact Groupoid.inv_comp (e v)
  comp_inv e := by funext v; exact Groupoid.comp_inv (e v)

structure CurveBaseChange {I N : ModuleCat.{0} A} (u : I ⟶ N)
    (E : CurveExtension F I) (H : CurveExtension F N) where
  component : ∀ v, LiMarkedCurveExtensions.BaseChange (F.curve v) u (E.component v) (H.component v)

/-- One source resolution presents the whole finite extension groupoid. -/
structure Classification where
  matrix : Matrix A
  functor : ∀ I : ModuleCat.{0} A,
    CurveExtension F I ⥤ AdditiveQuotient (tensorDifferential matrix I).hom
  equivalence : ∀ I, (functor I).IsEquivalence
  reindex : ∀ {I N : ModuleCat.{0} A}, (I ⟶ N) → (CurveExtension F I ⥤ CurveExtension F N)
  baseChange : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) (E : CurveExtension F I),
    CurveBaseChange F u E ((reindex u).obj E)
  arrows : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N)
    {E H : CurveExtension F I} (e : E ⟶ H) v,
    ((reindex u).map e v).iso.hom ≫ ((baseChange u H).component v).map =
      ((baseChange u E).component v).map ≫ (e v).iso.hom
  naturality : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    reindex u ⋙ functor N ≅ functor I ⋙ LiMarkedCurveExtensions.quotientReindex matrix u
  identity : ∀ I : ModuleCat.{0} A, reindex (𝟙 I) ≅ 𝟭 (CurveExtension F I)
  composition : ∀ {I N Q : ModuleCat.{0} A} (u : I ⟶ N) (v : N ⟶ Q),
    reindex u ⋙ reindex v ≅ reindex (u ≫ v)

variable (C : Classification F)

def trivialExtension
    (T : ∀ v, LiUniversalSourceExtensions.Trivial (F.curve v) (leftDual C.matrix)) :
    CurveExtension F (leftDual C.matrix) := ⟨fun v => (T v).family⟩

/-- The identity tensor and negative identity translation fix the actual universal curves. -/
structure Universal where
  extension : CurveExtension F (rightDual C.matrix)
  universalClass : (C.functor (rightDual C.matrix)).obj extension ≅
    (⟨rightIdentity C.matrix⟩ : AdditiveQuotient (tensorDifferential C.matrix (rightDual C.matrix)).hom)
  trivial : ∀ v, LiUniversalSourceExtensions.Trivial (F.curve v) (leftDual C.matrix)
  trivialClass : (C.functor (leftDual C.matrix)).obj (trivialExtension F C trivial) ≅
    (⟨0⟩ : AdditiveQuotient (tensorDifferential C.matrix (leftDual C.matrix)).hom)
  trivialization : (C.reindex (dualMap C.matrix)).obj extension ≅ trivialExtension F C trivial
  translation :
    (((LiMarkedCurveExtensions.quotientReindex C.matrix (dualMap C.matrix)).map universalClass.inv ≫
      (C.naturality (dualMap C.matrix)).inv.app extension ≫
      (C.functor (leftDual C.matrix)).map trivialization.hom ≫ trivialClass.hom).translation) =
      -leftIdentity C.matrix

/-- A single target deformation is used on every disconnected source component. -/
structure SharedParameter (I : ModuleCat.{0} A) where
  map : Spec (.of (TrivSqZeroExt A I)) ⟶ F.parameterBase
  reduction : LiMarkedCurveExtensions.reduction A I ≫ map = F.parameter
  structural : map ≫ F.parameterStructural =
    Spec.algebraMap A (TrivSqZeroExt A I) ≫ Spec.algebraMap k A

/-- A global first-order map extension has exactly ONE target deformation. -/
structure MapExtension (I : ModuleCat.{0} A) where
  curve : CurveExtension F I
  parameter : SharedParameter F I
  map : ∀ v, (curve.component v).curve.X ⟶ F.target
  structural : ∀ v, map v ≫ F.structural = (curve.component v).curve.π ≫
    Spec.algebraMap A (TrivSqZeroExt A I) ≫ Spec.algebraMap k A
  over : ∀ v, map v ≫ F.projection = (curve.component v).curve.π ≫ parameter.map
  reduction : ∀ v, (curve.component v).reduction ≫ map v = F.map v
  relative : ∀ v, (curve.component v).curve.X ⟶ pullback F.projection parameter.map
  relative_target : ∀ v, relative v ≫ pullback.fst F.projection parameter.map = map v
  relative_base : ∀ v, relative v ≫ pullback.snd F.projection parameter.map = (curve.component v).curve.π
  predeformable : ∀ v, RelativeExpandedMapFamilies.IsPredeformable
    (curve.component v).curve.π (pullback.snd F.projection parameter.map)
    (relative v) (relative_base v)
  contact : ∀ v j (W : (curve.component v).curve.X.affineOpens),
    ((F.boundary j).comap (map v)).ideal W =
      ∏ s : {s : Fin (F.markings v) // F.root v s = some j},
        ((curve.component v).curve.marking s.val).ker.ideal W ^ F.order v s.val

structure MapExtensionIso {I : ModuleCat.{0} A} (E H : MapExtension F I) where
  curve : E.curve ⟶ H.curve
  parameter : E.parameter.map = H.parameter.map
  map : ∀ v, (curve v).iso.hom ≫ H.map v = E.map v

def reduceTarget {I : ModuleCat.{0} A} (T : SharedParameter F I) :
    pullback F.projection F.parameter ⟶ pullback F.projection T.map :=
  pullback.lift (pullback.fst F.projection F.parameter)
    (pullback.snd F.projection F.parameter ≫ LiMarkedCurveExtensions.reduction A I)
    (by rw [Category.assoc, T.reduction]; exact pullback.condition)

@[ext] theorem MapExtensionIso.ext {I : ModuleCat.{0} A} {E H : MapExtension F I}
    (e h : MapExtensionIso F E H) (same : e.curve = h.curve) : e = h := by
  cases e
  cases h
  cases same
  rfl

instance mapExtensionGroupoid (I : ModuleCat.{0} A) : Groupoid (MapExtension F I) where
  Hom E H := MapExtensionIso F E H
  id E := ⟨𝟙 E.curve, rfl, by
    intro v
    change (𝟙 _) ≫ E.map v = E.map v
    exact Category.id_comp _⟩
  comp e h := ⟨e.curve ≫ h.curve, e.parameter.trans h.parameter, by
    intro v
    change ((e.curve v).iso.hom ≫ (h.curve v).iso.hom) ≫ _ = _
    rw [Category.assoc, h.map, e.map]⟩
  inv e := ⟨Groupoid.inv e.curve, e.parameter.symm, by
    intro v
    change (e.curve v).iso.inv ≫ _ = _
    rw [← e.map v]
    simp⟩
  id_comp e := by apply MapExtensionIso.ext; exact Category.id_comp e.curve
  comp_id e := by apply MapExtensionIso.ext; exact Category.comp_id e.curve
  assoc e h j := by apply MapExtensionIso.ext; exact Category.assoc e.curve h.curve j.curve
  inv_comp e := by apply MapExtensionIso.ext; exact Groupoid.inv_comp e.curve
  comp_inv e := by apply MapExtensionIso.ext; exact Groupoid.comp_inv e.curve

variable {F}

def SharedParameter.value {I : ModuleCat.{0} A} (T : SharedParameter F I)
    (i : Fin F.parameterCount) : I :=
  ((Scheme.ΓSpecIso (.of (TrivSqZeroExt A I))).hom.hom
    (T.map.appTop.hom (F.parameterBaseFunction i))).snd

variable (F)

/-- Both infinitesimal parameters belong to the same actual square-zero source ring. -/
theorem epsilon_mul_epsilon0 (I : ModuleCat.{0} A) (epsilon epsilon0 : I) :
    (TrivSqZeroExt.inr epsilon : TrivSqZeroExt A I) * TrivSqZeroExt.inr epsilon0 = 0 :=
  TrivSqZeroExt.inr_mul_inr A epsilon epsilon0

/-- The relation remains zero after the actual local source-ring map. -/
theorem mapped_epsilon_mul_epsilon0 (I : ModuleCat.{0} A) {B : Type} [CommRing B]
    (u : TrivSqZeroExt A I →+* B) (epsilon epsilon0 : I) :
    u (TrivSqZeroExt.inr epsilon) * u (TrivSqZeroExt.inr epsilon0) = 0 := by
  rw [← map_mul, epsilon_mul_epsilon0, map_zero]

abbrev Cover (v : Fin F.components) := LiGeometricCechModels.Cover
  (p := (F.curve v).π) (q := F.structural) (f := F.map v)

abbrev Geometry (v : Fin F.components) (L : Cover F v) :=
  LiGeometricCechModels.Geometry F.projection F.boundary F.parameterFunction L

abbrev Coefficients (v : Fin F.components) (L : Cover F v) (G : Geometry F v L) :=
  LiCechCoefficientModels.Model F.projection F.boundary F.parameterFunction L G

variable (U : Universal F C)
  {v : Fin F.components} (L : Cover F v)

/-- Local universal lifts retain their etale base parameters. Their differences
measure the failure to glue to the single global target of MapExtension. -/
structure Lift (i : Fin L.count) where
  extension : LocalExtension (L.charts i) (rightDual C.matrix)
  globalBase : TrivSqZeroExt A (rightDual C.matrix) →+* extension.extension.ring
  global_scalar : ∀ r : A, globalBase (TrivSqZeroExt.inl r) = algebraMap A extension.extension.ring r
  global_coefficient : ∀ x : rightDual C.matrix,
    globalBase (TrivSqZeroExt.inr x) = extension.baseMap (TrivSqZeroExt.inr (1 ⊗ₜ[A] x))
  source : Spec (.of extension.extension.ring) ⟶ (U.extension.component v).curve.X
  etale : Etale source
  over : source ≫ (U.extension.component v).curve.π = Spec.map (CommRingCat.ofHom globalBase)
  cartesian : IsPullback (Spec.map (CommRingCat.ofHom extension.extension.projection.toRingHom))
    (L.charts i).sourceMap source (U.extension.component v).reduction
  target : Spec (.of extension.extension.ring) ⟶ F.target
  target_scalar : target ≫ F.structural =
    Spec.algebraMap A extension.extension.ring ≫ Spec.algebraMap k A
  reduction : Spec.map (CommRingCat.ofHom extension.extension.projection.toRingHom) ≫ target =
    (L.charts i).sourceMap ≫ F.map v
  parameter : Spec (.of (TrivSqZeroExt (L.charts i).base
    (baseCoefficientObject (L.charts i) (rightDual C.matrix)))) ⟶ F.parameterBase
  parameter_structural : parameter ≫ F.parameterStructural =
    Spec.algebraMap (L.charts i).base
      (TrivSqZeroExt (L.charts i).base (baseCoefficientObject (L.charts i) (rightDual C.matrix))) ≫
      Spec.algebraMap A (L.charts i).base ≫ Spec.algebraMap k A
  parameter_square : target ≫ F.projection = Spec.map (CommRingCat.ofHom extension.baseMap) ≫ parameter
  relative : Spec (.of extension.extension.ring) ⟶ pullback F.projection parameter
  relative_target : relative ≫ pullback.fst F.projection parameter = target
  relative_base : relative ≫ pullback.snd F.projection parameter = Spec.map (CommRingCat.ofHom extension.baseMap)
  predeformable : RelativeExpandedMapFamilies.IsPredeformable
    (Spec.map (CommRingCat.ofHom extension.baseMap)) (pullback.snd F.projection parameter)
    relative relative_base
  contact : ∀ j (W : (Spec (.of extension.extension.ring)).affineOpens),
    ((F.boundary j).comap target).ideal W =
      ∏ s : {s : Fin (F.markings v) // F.root v s = some j},
        (((U.extension.component v).curve.marking s.val).ker.comap source).ideal W ^ F.order v s.val

variable (G : Geometry F v L) (V : Coefficients F v L G)
  (lift : ∀ i : Fin L.count, Lift F C U L i)

structure Overlap (a : Fin 2 → Fin L.count) where
  extension : LocalExtension (G.chart ⦋1⦌ a) (rightDual C.matrix)
  iso : Spec (.of extension.extension.ring) ≅ pullback (lift (a 0)).source (lift (a 1)).source
  left_reduction : Spec.map (CommRingCat.ofHom extension.extension.projection.toRingHom) ≫ iso.hom ≫
    pullback.fst (lift (a 0)).source (lift (a 1)).source =
    (G.source ⦋1⦌ a).hom ≫ WidePullback.π _ 0 ≫
      Spec.map (CommRingCat.ofHom (lift (a 0)).extension.extension.projection.toRingHom)
  right_reduction : Spec.map (CommRingCat.ofHom extension.extension.projection.toRingHom) ≫ iso.hom ≫
    pullback.snd (lift (a 0)).source (lift (a 1)).source =
    (G.source ⦋1⦌ a).hom ≫ WidePullback.π _ 1 ≫
      Spec.map (CommRingCat.ofHom (lift (a 1)).extension.extension.projection.toRingHom)
  pair : Pair F.parameterFunction (G.chart ⦋1⦌ a) (rightDual C.matrix) extension
  first : Spec.map (CommRingCat.ofHom pair.first) ≫ (G.chart ⦋1⦌ a).targetMap =
    iso.hom ≫ pullback.snd (lift (a 0)).source (lift (a 1)).source ≫ (lift (a 1)).target
  second : Spec.map (CommRingCat.ofHom pair.second) ≫ (G.chart ⦋1⦌ a).targetMap =
    iso.hom ≫ pullback.fst (lift (a 0)).source (lift (a 1)).source ≫ (lift (a 0)).target
  ratios : LiLocalLiftDifferences.Ratios F.projection F.boundary F.parameterFunction
    (G.chart ⦋1⦌ a) (rightDual C.matrix) extension pair (G.mode ⦋1⦌ a)

structure TrivialLift (i : Fin L.count) where
  extension : LocalExtension (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix)
  source : Spec (.of extension.extension.ring) ⟶ (U.trivial v).family.curve.X
  etale : Etale source
  cartesian : IsPullback (Spec.map (CommRingCat.ofHom extension.extension.projection.toRingHom))
    (G.chart ⦋0⦌ (fun _ => i)).sourceMap source (U.trivial v).family.reduction
  pull : Spec (.of extension.extension.ring) ⟶ Spec (.of (lift i).extension.extension.ring)
  pull_square : IsPullback pull source (lift i).source
    ((U.trivialization.inv v).iso.hom ≫
      ((C.baseChange (dualMap C.matrix) U.extension).component v).map)
  pair : Pair F.parameterFunction (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix) extension
  first : Spec.map (CommRingCat.ofHom pair.first) ≫ (G.chart ⦋0⦌ (fun _ => i)).targetMap =
    pull ≫ (lift i).target
  second : Spec.map (CommRingCat.ofHom pair.second) ≫ (G.chart ⦋0⦌ (fun _ => i)).targetMap =
    source ≫ (U.trivial v).iso.hom ≫ pullback.fst (F.curve v).π (trivialBase (leftDual C.matrix)) ≫ F.map v
  ratios : LiLocalLiftDifferences.Ratios F.projection F.boundary F.parameterFunction
    (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix) extension pair (G.mode ⦋0⦌ (fun _ => i))

/-- Native product cochains keep all components and every Cech restriction. -/
def productCochains {c : ℕ} (D : Fin c → CosimplicialObject (ModuleCat.{0} A)) :
    CosimplicialObject (ModuleCat.{0} A) where
  obj n := ModuleCat.of A (∀ v : Fin c, (D v).obj n)
  map f := ModuleCat.ofHom
    { toFun := fun x v => (D v).map f (x v)
      map_add' := by intros; funext v; exact map_add ((D v).map f).hom _ _
      map_smul' := by intros; funext v; exact map_smul ((D v).map f).hom _ _ }
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext v
    exact ConcreteCategory.congr_hom ((D v).map_id n) (x v)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext v
    exact ConcreteCategory.congr_hom ((D v).map_comp f g) (x v)

def productCochainsMap {c : ℕ} {D H : Fin c → CosimplicialObject (ModuleCat.{0} A)}
    (f : ∀ v, D v ⟶ H v) : productCochains D ⟶ productCochains H where
  app n := ModuleCat.ofHom
    { toFun := fun x v => (f v).app n (x v)
      map_add' := by intros; funext v; exact map_add ((f v).app n).hom _ _
      map_smul' := by intros; funext v; exact map_smul ((f v).app n).hom _ _ }
  naturality n m g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext v
    exact ConcreteCategory.congr_hom ((f v).naturality g) (x v)

/-- The actual first-order parameter value of a universal local lift. -/
def liftedParameter (i : Fin L.count) (Z : Lift F C U L i) (j : Fin F.parameterCount) :
    baseCoefficient (L.charts i) (rightDual C.matrix) :=
  ((Scheme.ΓSpecIso (.of (TrivSqZeroExt (L.charts i).base
    (baseCoefficientObject (L.charts i) (rightDual C.matrix))))).hom.hom
      (Z.parameter.appTop.hom (F.parameterBaseFunction j))).snd

def labelParameter
    (covers : ∀ v : Fin F.components, Cover F v)
    (geometry : ∀ v, Geometry F v (covers v))
    (coefficients : ∀ v, Coefficients F v (covers v) (geometry v))
    (H : LiSharedTargetCechModels.System
      (C := fun v => (F.curve v).X) (p := fun v => (F.curve v).π)
      (q := F.structural) (f := F.map)
      F.projection F.boundary F.parameterFunction covers geometry coefficients)
    (lifts : ∀ v i, Lift F C U (covers v) i)
    (a : LiSharedTargetCechModels.Label covers) (j : Fin F.parameterCount) :
    LiSharedTargetCechModels.labelRing covers a ⊗[A] rightDual C.matrix :=
  match a with
  | none => 0
  | some a => TensorProduct.map (H.sourceLabel a.1 a.2).algebra.toLinearMap LinearMap.id
      (liftedParameter F C U (covers a.1) a.2 (lifts a.1 a.2) j)

/-- The complete raw source is constructed from the actual universal lifts. -/
structure Source where
  classification : Classification F
  universal : Universal F classification
  cover : ∀ v : Fin F.components, Cover F v
  geometry : ∀ v, Geometry F v (cover v)
  coefficients : ∀ v, Coefficients F v (cover v) (geometry v)
  shared : LiSharedTargetCechModels.System
    (C := fun v => (F.curve v).X) (p := fun v => (F.curve v).π)
    (q := F.structural) (f := F.map)
    F.projection F.boundary F.parameterFunction cover geometry coefficients
  lifts : ∀ v i, Lift F classification universal (cover v) i
  overlap : ∀ v a, Overlap F classification universal (cover v) (geometry v) (lifts v) a
  trivial : ∀ v i, TrivialLift F classification universal (cover v) (geometry v) (lifts v) i
  differenceOne : (shared.model (rightDual classification.matrix)).cochains.obj ⦋1⦌
  differenceOne_normalized : ∀ v (a : Fin 2 → Fin (cover v).count),
    LiLocalLiftDifferences.Normalized F.projection F.boundary F.parameterFunction
      ((geometry v).chart ⦋1⦌ a) (rightDual classification.matrix)
      (overlap v a).extension (overlap v a).pair ((geometry v).mode ⦋1⦌ a) (overlap v a).ratios
      ((((coefficients v).localModel (rightDual classification.matrix)).comparison ⦋1⦌).hom
        ((((shared.model (rightDual classification.matrix)).comparison ⦋1⦌).hom differenceOne).val.1 v) a)
  differenceOne_parameters : ∀ (a : Fin 2 → LiSharedTargetCechModels.Label cover) j,
    ((((shared.model (rightDual classification.matrix)).comparison ⦋1⦌).hom differenceOne).val.2 a j) =
      TensorProduct.map (shared.labels ⦋1⦌ a 1).algebra.toLinearMap LinearMap.id
        (labelParameter F classification universal cover geometry coefficients shared lifts (a 1) j) -
      TensorProduct.map (shared.labels ⦋1⦌ a 0).algebra.toLinearMap LinearMap.id
        (labelParameter F classification universal cover geometry coefficients shared lifts (a 0) j)
  differenceZero : (shared.model (leftDual classification.matrix)).cochains.obj ⦋0⦌
  differenceZero_normalized : ∀ v (i : Fin (cover v).count),
    LiLocalLiftDifferences.Normalized F.projection F.boundary F.parameterFunction
      ((geometry v).chart ⦋0⦌ (fun _ => i)) (leftDual classification.matrix)
      (trivial v i).extension (trivial v i).pair ((geometry v).mode ⦋0⦌ (fun _ => i)) (trivial v i).ratios
      ((((coefficients v).localModel (leftDual classification.matrix)).comparison ⦋0⦌).hom
        ((((shared.model (leftDual classification.matrix)).comparison ⦋0⦌).hom differenceZero).val.1 v)
          (fun _ => i))
  differenceZero_parameters : ∀ (a : Fin 1 → LiSharedTargetCechModels.Label cover) j,
    ((((shared.model (leftDual classification.matrix)).comparison ⦋0⦌).hom differenceZero).val.2 a j) =
      TensorProduct.map (shared.labels ⦋0⦌ a 0).algebra.toLinearMap (dualMap classification.matrix).hom
        (labelParameter F classification universal cover geometry coefficients shared lifts (a 0) j)
  data : ∀ I : ModuleCat.{0} A, LiCechObstructionComplexes.Data A
  source : ∀ I : ModuleCat.{0} A,
    LiFiniteComplexPresentations.SourceBinding classification.matrix I (data I)
  log : ∀ I : ModuleCat.{0} A, (data I).logCochains ≅ (shared.model I).cochains
  deltaZero : ∀ (I : ModuleCat.{0} A) (x : (data I).zero),
    (log I).hom.app ⦋0⦌ ((data I).deltaZero x) =
      (LiSharedTargetCechModels.transport
        (g := F.projection) (J := F.boundary) (t := F.parameterFunction)
        (L := cover) (G := geometry) (V := coefficients)
        (u := ModuleCat.ofHom (LiTensorEvaluation.evaluation A (left classification.matrix) I
          ((source I).zero.hom x))) shared).app ⦋0⦌ differenceZero
  deltaOne : ∀ (I : ModuleCat.{0} A) (x : (data I).one),
    (log I).hom.app ⦋1⦌ ((data I).deltaOne x) =
      (LiSharedTargetCechModels.transport
        (g := F.projection) (J := F.boundary) (t := F.parameterFunction)
        (L := cover) (G := geometry) (V := coefficients)
        (u := ModuleCat.ofHom (LiTensorEvaluation.evaluation A (right classification.matrix) I
          ((source I).one.hom x))) shared).app ⦋1⦌ differenceOne

variable {F}

def Source.complex (Q : Source F) (I : ModuleCat.{0} A) : CochainComplex (ModuleCat.{0} A) ℤ :=
  LiCechObstructionComplexes.integerComplex (Q.data I)

def Source.termIso (Q : Source F) (I : ModuleCat.{0} A) (j : ℕ) :
    (Q.complex I).X (j : ℤ) ≅ LiCechObstructionComplexes.term (Q.data I) j :=
  (LiCechObstructionComplexes.complex (Q.data I)).extendXIso
    (ComplexShape.embeddingUpIntGE 0) (i := j) (by simp)

def Source.sourceLogValue (Q : Source F) (I : ModuleCat.{0} A) (z : SimplexCategory)
    (x : (Q.data I).logCochains.obj z) (v : Fin F.components) :
    ((Q.coefficients v).localModel I).cochains.obj z :=
  (((Q.shared.model I).comparison z).hom ((Q.log I).hom.app z x)).val.1 v

def Source.baseLogValue (Q : Source F) (I : ModuleCat.{0} A) (z : SimplexCategory)
    (x : (Q.data I).logCochains.obj z)
    (a : Fin (z.len + 1) → LiSharedTargetCechModels.Label Q.cover) (i : Fin F.parameterCount) :
    LiSharedTargetCechModels.baseRing Q.cover z a ⊗[A] I :=
  (((Q.shared.model I).comparison z).hom ((Q.log I).hom.app z x)).val.2 a i

/-- The identity base chart supplies the ONE global target parameter. -/
def Source.globalParameter (Q : Source F) (I : ModuleCat.{0} A)
    (x : (Q.data I).logCochains.obj ⦋0⦌) (i : Fin F.parameterCount) : I :=
  TensorProduct.lid A I
    (TensorProduct.map Q.shared.parent.algebra.toLinearMap LinearMap.id
      (Q.baseLogValue I ⦋0⦌ x (fun _ => none) i))

variable (F)

/-- Coefficient maps fix both source tensor blocks and the entire log diagram. -/
structure SourceCoefficientFunctor (Q : Source F) where
  functor : ModuleCat.{0} A ⥤ CochainComplex (ModuleCat.{0} A) ℤ
  [additive : functor.Additive]
  [linear : functor.Linear A]
  comparison : ∀ I, functor.obj I ≅ Q.complex I
  sourceZero : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    (Q.data I).zero ⟶ (Q.data N).zero
  sourceOne : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    (Q.data I).one ⟶ (Q.data N).one
  zero_tensor : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) x,
    (Q.source N).zero.hom (sourceZero u x) =
      leftCoefficientMap Q.classification.matrix I u.hom ((Q.source I).zero.hom x)
  one_tensor : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) x,
    (Q.source N).one.hom (sourceOne u x) =
      rightCoefficientMap Q.classification.matrix I u.hom ((Q.source I).one.hom x)
  logMap : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N), (Q.data I).logCochains ⟶ (Q.data N).logCochains
  log_normalized : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    logMap u ≫ (Q.log N).hom = (Q.log I).hom ≫
      LiSharedTargetCechModels.transport
        (g := F.projection) (J := F.boundary) (t := F.parameterFunction)
        (L := Q.cover) (G := Q.geometry) (V := Q.coefficients) u Q.shared
  delta_zero : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    (Q.data I).deltaZero ≫ (logMap u).app ⦋0⦌ = sourceZero u ≫ (Q.data N).deltaZero
  delta_one : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N),
    (Q.data I).deltaOne ≫ (logMap u).app ⦋1⦌ = sourceOne u ≫ (Q.data N).deltaOne
attribute [instance] SourceCoefficientFunctor.additive SourceCoefficientFunctor.linear

variable {F}

def SourceCoefficientFunctor.map {Q : Source F} (V : SourceCoefficientFunctor F Q)
    {I N : ModuleCat.{0} A} (u : I ⟶ N) : Q.complex I ⟶ Q.complex N :=
  (V.comparison I).inv ≫ V.functor.map u ≫ (V.comparison N).hom

variable (F)

/-- Every cochain block uses the same source tensor map and actual log transport. -/
structure SourceCoefficientNormalization {Q : Source F} (V : SourceCoefficientFunctor F Q) : Prop where
  zero : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) x,
    (Q.termIso N 0).hom ((V.map u).f 0 x) = V.sourceZero u ((Q.termIso I 0).hom x)
  one : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) x,
    (Q.termIso N 1).hom ((V.map u).f 1 x) =
      (V.sourceOne u (((Q.termIso I 1).hom x).1),
        (V.logMap u).app ⦋0⦌ (((Q.termIso I 1).hom x).2))
  higher : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) (j : ℕ) x,
    (Q.termIso N (j + 2)).hom ((V.map u).f (j + 2 : ℕ) x) =
      (V.logMap u).app ⦋j + 1⦌ ((Q.termIso I (j + 2)).hom x)

def cocycleModule (Q : Source F) (I : ModuleCat.{0} A) : ModuleCat.{0} A :=
  ModuleCat.of A (LinearMap.ker (LiCechObstructionComplexes.secondStep (Q.data I)).hom)

/-- The actual first differential lands in the actual second-differential kernel. -/
def cocycleDifferential (Q : Source F) (I : ModuleCat.{0} A) :
    (Q.data I).zero ⟶ cocycleModule F Q I :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨LiCechObstructionComplexes.firstStep (Q.data I) x, by
        exact ConcreteCategory.congr_hom (LiCechObstructionComplexes.first_second (Q.data I)) x⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }

def MapExtension.curves (I : ModuleCat.{0} A) : MapExtension F I ⥤ CurveExtension F I where
  obj E := E.curve
  map e := e.curve

/-- Coefficient transport has its actual Cartesian curve and one target-parameter square. -/
structure MapBaseChange {I N : ModuleCat.{0} A} (u : I ⟶ N)
    (E : MapExtension F I) (H : MapExtension F N) where
  curve : CurveBaseChange F u E.curve H.curve
  parameter : LiMarkedCurveExtensions.baseMap A u ≫ E.parameter.map = H.parameter.map
  map : ∀ v, (curve.component v).map ≫ E.map v = H.map v

/-- The full compatible map-extension groupoid is classified by Li's actual cocycles.
The target value is the ONE shared parameter of that global extension. -/
structure DeformationClassification (Q : Source F) where
  functor : ∀ I : ModuleCat.{0} A,
    MapExtension F I ⥤ AdditiveQuotient (cocycleDifferential F Q I).hom
  equivalence : ∀ I, (functor I).IsEquivalence
  curve : ∀ (I : ModuleCat.{0} A) (E : MapExtension F I),
    (Q.classification.functor I).obj E.curve ≅
      (⟨(Q.source I).one.hom (((functor I).obj E).value.val.1)⟩ :
        AdditiveQuotient (tensorDifferential Q.classification.matrix I).hom)
  curve_arrows : ∀ (I : ModuleCat.{0} A) {E H : MapExtension F I} (e : E ⟶ H),
    ((Q.classification.functor I).map e.curve).translation =
      (Q.source I).zero.hom (((functor I).map e).translation)
  target_normalized : ∀ (I : ModuleCat.{0} A) (E : MapExtension F I) i,
    Q.globalParameter I (((functor I).obj E).value.val.2) i = E.parameter.value i
  reindex : ∀ {I N : ModuleCat.{0} A}, (I ⟶ N) → (MapExtension F I ⥤ MapExtension F N)
  baseChange : ∀ {I N : ModuleCat.{0} A} (u : I ⟶ N) (E : MapExtension F I),
    MapBaseChange F u E ((reindex u).obj E)
  identity : ∀ I : ModuleCat.{0} A, reindex (𝟙 I) ≅ 𝟭 (MapExtension F I)
  composition : ∀ {I N P : ModuleCat.{0} A} (u : I ⟶ N) (v : N ⟶ P),
    reindex u ⋙ reindex v ≅ reindex (u ≫ v)

end MathlibExt.AlgebraicGeometry.LiGenericSourceModels
