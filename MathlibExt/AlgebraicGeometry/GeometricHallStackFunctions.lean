/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackChowGroups
public import MathlibExt.AlgebraicGeometry.GeometricChow
public import MathlibExt.AlgebraicGeometry.StablePairParameterPullbacks
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual geometric stack-function generators and Lefschetz stages

Symbols are strong maps from finite-type Artin stacks with affine
geometric stabilizers. Relations are the actual disjoint-union,
complex-point geometric-bijection and Zariski-fibration relations.
Open/closed decompositions and local trivializations retain their full
fibred categories over every test scheme, including disconnected and
nonreduced tests.

Lefschetz inversion is represented by integer stages and the actual
product with the affine line. Every such geometric product model gives
the same relation; no formal variable is substituted for that product.

Reference: Bridgeland, arXiv:1002.4374v3, §4.1, (14)–(15), §5.1.
The native stack/fibre constructions and their source notices are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricHallStackFunctions

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackVectorBundles
open StablePairParameterPullbacks

abbrev base : Scheme := Spec (.of ℂ)
abbrev ComplexStack := Stack base
abbrev complexPoint : Over base := Over.mk (𝟙 base)

/-- Affine stabilizers represent the actual automorphism sheaves at every geometric point. -/
def AffineStabilizers (X : ComplexStack) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω]
    (x : X.Fibre (geometricParameter Ω)),
    ∃ U : Over (Spec (.of Ω)), IsAffine U.left ∧
      Nonempty (((geometricParameter Ω).iteratedSliceForward.op ⋙ yoneda.obj U) ≅
        X.toPseudofunctor.presheafHom x x)

/-- Locally finite type is tested on an actual smooth scheme atlas. -/
structure LocallyFiniteTypeStack where
  stack : ComplexStack
  diagonal : stack.HasRepresentableDiagonal
  atlas : stack.SmoothAtlas
  [locallyFiniteType : LocallyOfFiniteType atlas.U.hom]
  affineStabilizers : AffineStabilizers stack

/-- Finite type retains a quasi-compact actual atlas. -/
structure FiniteTypeStack extends LocallyFiniteTypeStack where
  [quasiCompact : QuasiCompact atlas.U.hom]

/-- A source is a scheme only with its complete represented category over the base. -/
structure SchemeSource (X : FiniteTypeStack) where
  scheme : Over base
  [locallyFiniteType : LocallyOfFiniteType scheme.hom]
  [quasiCompact : QuasiCompact scheme.hom]
  comparison : Total X.stack ≌ Over scheme.left
  overBase : comparison.functor ⋙ Over.map scheme.hom ≅
    Pseudofunctor.CoGrothendieck.forget X.stack.toPseudofunctor

/-- A genuine source symbol in the paper's K(St/M). -/
structure Generator (M : ComplexStack) where
  source : FiniteTypeStack
  map : StackHom source.stack M

/-- The ordinary complex linear span of the actual source symbols. -/
abbrev Formal (M : ComplexStack) := Generator M →₀ ℂ

def rawSymbol {M : ComplexStack} (g : Generator M) : Formal M := Finsupp.single g 1

/-- Products use the two actual stack projections and their computed comparison. -/
structure ProductModel (X Y : FiniteTypeStack) where
  apex : FiniteTypeStack
  fst : StackHom apex.stack X.stack
  snd : StackHom apex.stack Y.stack
  cartesian : ∀ T : Over base,
    ((StackCycleGeometry.component fst T).prod'
      (StackCycleGeometry.component snd T)).IsEquivalence

variable {M : ComplexStack}

/-- A disjoint union is an actual complementary open/closed cover in every scheme fibre. -/
structure DisjointUnionDiagram (a b c : Generator M) where
  first : StackHom a.source.stack c.source.stack
  second : StackHom b.source.stack c.source.stack
  firstOver : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp first c.map) a.map
  secondOver : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp second c.map) b.map
  firstFibre : ∀ (T : Over base) (x : c.source.stack.Fibre T), SchemeFibreModel first T x
  secondFibre : ∀ (T : Over base) (x : c.source.stack.Fibre T), SchemeFibreModel second T x
  firstOpen : ∀ T x, IsOpenImmersion (firstFibre T x).scheme.hom
  firstClosed : ∀ T x, IsClosedImmersion (firstFibre T x).scheme.hom
  secondOpen : ∀ T x, IsOpenImmersion (secondFibre T x).scheme.hom
  secondClosed : ∀ T x, IsClosedImmersion (secondFibre T x).scheme.hom
  disjoint : ∀ T x,
    Disjoint (Set.range (firstFibre T x).scheme.hom) (Set.range (secondFibre T x).scheme.hom)
  cover : ∀ T x,
    Set.range (firstFibre T x).scheme.hom ∪ Set.range (secondFibre T x).scheme.hom = Set.univ

/-- The geometric-bijection relation has precisely the paper's complex-point equivalence. -/
structure GeometricBijection (a b : Generator M) where
  map : StackHom a.source.stack b.source.stack
  overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map b.map) a.map
  complexPoints : (StackCycleGeometry.component map complexPoint).IsEquivalence

/-- The actual category of F-valued families over a specified scheme U. -/
abbrev FibreProductTotal (F : ComplexStack) (U : Over base) :=
  CostructuredArrow (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor) U

/-- The literal structural functor to schemes over U. -/
def fibreProductForget (F : ComplexStack) (U : Over base) :
    FibreProductTotal F U ⥤ Over U.left where
  obj q := Over.mk q.hom.left
  map {q r} a := Over.homMk a.left.base.left (by
    exact congrArg (fun f : q.left.base ⟶ U => f.left) a.w)
  map_id q := rfl
  map_comp a b := rfl

def coverScheme (T : Over base) (C : T.left.OpenCover.{0}) (i : C.I₀) : Over base :=
  Over.mk (C.f i ≫ T.hom)

def coverMap (T : Over base) (C : T.left.OpenCover.{0}) (i : C.I₀) : coverScheme T C i ⟶ T :=
  Over.homMk (C.f i) rfl

/-- The ordinary scheme pullback over an open of the test scheme. -/
def localScheme {T : Over base} (V : Over T.left) (C : T.left.OpenCover.{0})
    (i : C.I₀) : Over (coverScheme T C i).left :=
  Over.mk (pullback.snd V.hom (C.f i))

/-- The actual constant scheme fibre, with its projection to the open. -/
def constantFibreScheme (U F : Over base) : Over U.left :=
  Over.mk (pullback.fst U.hom F.hom)

/-- Both maps are represented, and locally are genuine scheme products
with the same fibre. Fibres may vary by open, as in Definition 2.4 of
Bridgeland arXiv:1002.4372v1. Definition 3.3 requires scheme fibres. -/
structure LocalFibrationPair {Y : ComplexStack} {A B : FiniteTypeStack}
    (a : StackHom A.stack Y) (b : StackHom B.stack Y)
    (T : Over base) (y : Y.Fibre T) where
  first : SchemeFibreModel a T y
  second : SchemeFibreModel b T y
  cover : T.left.OpenCover.{0}
  fibre : cover.I₀ → IntegerSchemeChow.FieldScheme ℂ
  firstComparison : ∀ i, localScheme first.scheme cover i ≅
    constantFibreScheme (coverScheme T cover i) (fibre i).scheme
  secondComparison : ∀ i, localScheme second.scheme cover i ≅
    constantFibreScheme (coverScheme T cover i) (fibre i).scheme

/-- Zariski local triviality and equal fibres on all actual scheme base changes. -/
structure ZariskiFibrationPair (a b : Generator M) where
  target : LocallyFiniteTypeStack
  map : StackHom target.stack M
  first : StackHom a.source.stack target.stack
  second : StackHom b.source.stack target.stack
  firstOver : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp first map) a.map
  secondOver : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp second map) b.map
  locallyTrivial : ∀ (T : Over base) (y : target.stack.Fibre T), LocalFibrationPair first second T y

/-- Exactly the three displayed geometric additive relations. -/
inductive GeometricRelation (M : ComplexStack) : Formal M → Prop
  | disjoint {a b c : Generator M} (D : DisjointUnionDiagram a b c) :
      GeometricRelation M (rawSymbol c - rawSymbol a - rawSymbol b)
  | bijection {a b : Generator M} (D : GeometricBijection a b) :
      GeometricRelation M (rawSymbol a - rawSymbol b)
  | fibration {a b : Generator M} (D : ZariskiFibrationPair a b) :
      GeometricRelation M (rawSymbol a - rawSymbol b)

def relations (M : ComplexStack) : Submodule ℂ (Formal M) :=
  Submodule.span ℂ {r | GeometricRelation M r}

/-- The actual geometric Grothendieck stack-function quotient. -/
abbrev StackFunctions (M : ComplexStack) := Formal M ⧸ relations M

def symbol {M : ComplexStack} (g : Generator M) : StackFunctions M :=
  (relations M).mkQ (rawSymbol g)

/-- Each denominator stage is a power of the actual affine-line product. -/
abbrev StagedFormal (M : ComplexStack) := (Generator M × ℕ) →₀ ℂ

def stageMap (M : ComplexStack) (n : ℕ) : Formal M →ₗ[ℂ] StagedFormal M :=
  Finsupp.linearCombination ℂ (fun g => Finsupp.single (g,n) 1)

def rawStage {M : ComplexStack} (g : Generator M) (n : ℕ) : StagedFormal M :=
  Finsupp.single (g,n) 1

/-- The line factor is an actual represented affine line, with the full product normalization. -/
structure LefschetzProduct (g : Generator M) where
  line : FiniteTypeStack
  lineModel : SchemeSource line
  line_normalized : lineModel.scheme = GeometricChow.affineLine
  product : ProductModel line g.source

def LefschetzProduct.generator {g : Generator M} (D : LefschetzProduct g) : Generator M :=
  ⟨D.product.apex,Pseudofunctor.StrongTrans.vcomp D.product.snd g.map⟩

/-- Geometric relations at every stage and the literal L-inverse refinement relation. -/
inductive StagedRelation (M : ComplexStack) : StagedFormal M → Prop
  | geometric {r : Formal M} (h : GeometricRelation M r) (n : ℕ) :
      StagedRelation M (stageMap M n r)
  | lefschetz {g : Generator M} (D : LefschetzProduct g) (n : ℕ) :
      StagedRelation M (rawStage D.generator (n+1) - rawStage g n)

def stagedRelations (M : ComplexStack) : Submodule ℂ (StagedFormal M) :=
  Submodule.span ℂ {r | StagedRelation M r}

/-- The actual stack-function presentation with Lefschetz powers inverted. -/
abbrev LefschetzStackFunctions (M : ComplexStack) := StagedFormal M ⧸ stagedRelations M

def stageSymbol {M : ComplexStack} (g : Generator M) (n : ℕ) : LefschetzStackFunctions M :=
  (stagedRelations M).mkQ (rawStage g n)

end MathlibExt.AlgebraicGeometry.GeometricHallStackFunctions
