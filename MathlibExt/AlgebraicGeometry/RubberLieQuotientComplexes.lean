/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RubberStandardScalingModels
public import MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints
public import MathlibExt.AlgebraicGeometry.LiGeometricCechModels
public import MathlibExt.AlgebraicGeometry.LiCechObstructionComplexes

/-!
# The actual torus Lie quotient of the framed Li complex

There are m+1 target-frame scalings. Each generator is the actual torus
point1 plus epsilon, acting on the fixed total standard target. Its local
derivative is fixed on every regular function and every retained normal
logarithm. The source-curve component is zero. The quotient complex is
the literal mapping cone of this normalized Lie action in degree1.

This retains the full infinitesimal quotient, including its differential
and possible stabilizer kernel, before any two-term replacement or
virtual-dimension calculation.
Source: JPPZ arXiv:1602.04705v2, Section0.2.4;
Jun Li arXiv:math/0110113v1, descended obstruction theory in Section2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RubberLieQuotientComplexes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels ExpansionParameterModels RubberMapFamilies
open RubberStandardScalingModels TorusInfinitesimalPoints LiAffineMapCharts LiCechChartModules
open scoped TensorProduct Simplicial

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  (m : ℕ) (H : TorusTheory k (m + 1)) (N : StandardAction O P D R S m H)

def boundaries : Fin 2 → (S.chart m).scheme.left.IdealSheafData :=
  fun i => if i = 0 then standardZeroIdeal O P D R S m else (S.chart m).boundary.left.ker

def parameters (i : Fin m) : Γ((S.chart m).scheme.left, ⊤) :=
  (S.chart m).projection.left.appTop.hom (parameterCoordinate k m i)

variable {A : Type} [CommRing A] [Algebra k A] {C : Scheme.{0}}
  {p : C ⟶ Spec (.of A)} {f : C ⟶ (S.chart m).scheme.left}

def targetPoint (a : Chart p (S.chart m).scheme.hom f) :
    Over.mk (Spec.algebraMap k a.target) ⟶ (S.chart m).scheme :=
  Over.homMk a.targetMap a.targetOver

abbrev LocalJet (a : Chart p (S.chart m).scheme.hom f) (j : Fin (m + 1)) :=
  EtaleJet H a.target (S.chart m).scheme N.standard (targetPoint P R S m a) j

structure BoundaryRatio {a : Chart p (S.chart m).scheme.hom f} {j : Fin (m + 1)}
    (T : LocalJet O P D R S m H N a j) (z : a.target) where
  unit : (TrivSqZeroExt a.target a.target)ˣ
  reduction : unit.val.fst = 1
  coordinate : T.map z = TrivSqZeroExt.inl z * (unit : TrivSqZeroExt a.target a.target)

structure NodeRatios {a : Chart p (S.chart m).scheme.hom f} {j : Fin (m + 1)}
    (T : LocalJet O P D R S m H N a j) (z : Fin 2 → a.target) where
  unit : Fin 2 → (TrivSqZeroExt a.target a.target)ˣ
  reduction : ∀ i, (unit i).val.fst = 1
  coordinate : ∀ i, T.map (z i) = TrivSqZeroExt.inl (z i) * (unit i : TrivSqZeroExt a.target a.target)

def Ratios {a : Chart p (S.chart m).scheme.hom f} {j : Fin (m + 1)}
    (T : LocalJet O P D R S m H N a j) :
    Mode (S.chart m).projection.left (boundaries O P D R S m) (parameters P R S m) a → Type
  | .ordinary _ _ _ _ => PUnit
  | .boundary _ z _ _ _ _ => BoundaryRatio O P D R S m H N T z.coordinate
  | .node z _ _ _ => NodeRatios O P D R S m H N T z.coordinate

def NormalizedLocal {a : Chart p (S.chart m).scheme.hom f} {j : Fin (m + 1)}
    (T : LocalJet O P D R S m H N a j)
    (o : Mode (S.chart m).projection.left (boundaries O P D R S m) (parameters P R S m) a)
    (u : Ratios O P D R S m H N T o)
    (x : value (S.chart m).projection.left (boundaries O P D R S m) (parameters P R S m) A o) : Prop :=
  (∀ b : a.target,
    derivative (S.chart m).projection.left (boundaries O P D R S m) (parameters P R S m) A o x b =
      algebraMap a.target a.source (functionDerivative H a.target (S.chart m).scheme N.standard
        (targetPoint P R S m a) T b) ⊗ₜ[A] (1 : A)) ∧
  match o, u, x with
  | .ordinary _ _ _ _, _, _ => True
  | .boundary _ z pr pt hp h, e, y =>
      boundaryLog (S.chart m).projection.left (boundaries O P D R S m) (parameters P R S m) A z pr pt hp h y =
        algebraMap a.target a.source e.unit.val.snd ⊗ₜ[A] (1 : A)
  | .node z pr pure h, e, y =>
      ∀ i : Fin 2, nodeLog (S.chart m).projection.left (boundaries O P D R S m) (parameters P R S m) A z pr pure h y i =
        algebraMap a.target a.source (e.unit i).val.snd ⊗ₜ[A] (1 : A)

def lieComplex : CochainComplex (ModuleCat.{0} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{0} A) 1).obj (ModuleCat.of A (Fin (m + 1) → A))

variable
  (L : LiGeometricCechModels.Cover (p := p) (q := (S.chart m).scheme.hom) (f := f))
  (G : LiGeometricCechModels.Geometry (S.chart m).projection.left
    (boundaries O P D R S m) (parameters P R S m) L)
  (V : LiGeometricCechModels.Model (S.chart m).projection.left
    (boundaries O P D R S m) (parameters P R S m) L G A)
  (E : LiCechObstructionComplexes.Data A)

structure LieAction where
  parameter : Spec (.of A) ⟶ (ParameterSpace k m).left
  parameter_square : f ≫ (S.chart m).projection.left = p ≫ parameter
  log : E.logCochains ≅ V.cochains
  map : lieComplex (A := A) m ⟶ LiCechObstructionComplexes.integerComplex E
  jets : ∀ (j : Fin (m + 1)) (a : Fin L.count),
    LocalJet O P D R S m H N (G.chart ⦋0⦌ (fun _ => a)) j
  ratios : ∀ (j : Fin (m + 1)) (a : Fin L.count),
    Ratios O P D R S m H N (jets j a) (G.mode ⦋0⦌ (fun _ => a))
  source_zero : ∀ j : Fin (m + 1),
    ((LiCechObstructionComplexes.degreeOneIso E).hom
      ((map.f 1) ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
        (ModuleCat.of A (Fin (m + 1) → A))).inv (Pi.single j 1)))).1 = 0
  normalized : ∀ (j : Fin (m + 1)) (a : Fin L.count),
    NormalizedLocal O P D R S m H N (jets j a) (G.mode ⦋0⦌ (fun _ => a)) (ratios j a)
      ((V.comparison ⦋0⦌).hom ((log.hom.app ⦋0⦌)
        (((LiCechObstructionComplexes.degreeOneIso E).hom
          ((map.f 1) ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
            (ModuleCat.of A (Fin (m + 1) → A))).inv (Pi.single j 1)))).2)) (fun _ => a))

def quotientComplex (Q : LieAction O P D R S m H N L G V E) : CochainComplex (ModuleCat.{0} A) ℤ :=
  CochainComplex.mappingCone Q.map

end MathlibExt.AlgebraicGeometry.RubberLieQuotientComplexes
