/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallConvolutionOperations

/-!
# Actual infinite-type geometric Hall symbols for torsion-pair identities

The sources are actual locally finite-type stacks with affine
stabilizers. The geometric-bijection and representable scheme
Zariski-fibration relations remain. The disjoint-union relation is
deliberately absent, as required in the source to avoid the zero
group. Multiplication is the same actual exact-sequence two-fibre
correspondence, with locally finite-type output.

This is the source's H_infinity used in §4 torsion-pair identities.
The Laurent completion has its separate explicit support bounds.

Reference: Bridgeland, arXiv:1002.4374v3, Definition 4.2,
equation (15), Lemmas 4.1–4.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.InfiniteHallStackFunctions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open StackCycleGeometry StackFibreModels StackVectorBundles StackChowGroups
open GeometricHallStackFunctions HallFamilyStackModels

structure Generator (M : ComplexStack) where
  source : LocallyFiniteTypeStack
  map : StackHom source.stack M

abbrev Formal (M : ComplexStack) := Generator M →₀ ℂ

def rawSymbol {M : ComplexStack} (g : Generator M) : Formal M := Finsupp.single g 1

structure GeometricBijection {M : ComplexStack} (a b : Generator M) where
  map : StackHom a.source.stack b.source.stack
  overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map b.map) a.map
  complexPoints : (component map complexPoint).IsEquivalence

structure FibreScheme where
  scheme : Over base
  [finiteType : LocallyOfFiniteType scheme.hom]

structure LocalFibrationPair {A B Y : ComplexStack} (a : StackHom A Y) (b : StackHom B Y)
    (T : Over base) (y : Y.Fibre T) where
  first : SchemeFibreModel a T y
  second : SchemeFibreModel b T y
  cover : T.left.OpenCover.{0}
  fibre : cover.I₀ → FibreScheme
  firstComparison : ∀ i, GeometricHallStackFunctions.localScheme first.scheme cover i ≅
    constantFibreScheme (coverScheme T cover i) (fibre i).scheme
  secondComparison : ∀ i, GeometricHallStackFunctions.localScheme second.scheme cover i ≅
    constantFibreScheme (coverScheme T cover i) (fibre i).scheme

structure ZariskiFibrationPair {M : ComplexStack} (a b : Generator M) where
  target : LocallyFiniteTypeStack
  map : StackHom target.stack M
  first : StackHom a.source.stack target.stack
  second : StackHom b.source.stack target.stack
  firstOver : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp first map) a.map
  secondOver : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp second map) b.map
  locallyTrivial : ∀ (T : Over base) (y : target.stack.Fibre T),
    LocalFibrationPair first second T y

/-- Exactly the two remaining infinite-type geometric relations. -/
inductive Relation (M : ComplexStack) : Formal M → Prop
  | bijection {a b : Generator M} (D : GeometricBijection a b) :
      Relation M (rawSymbol a - rawSymbol b)
  | fibration {a b : Generator M} (D : ZariskiFibrationPair a b) :
      Relation M (rawSymbol a - rawSymbol b)

def relations (M : ComplexStack) : Submodule ℂ (Formal M) :=
  Submodule.span ℂ {r | Relation M r}

abbrev StackFunctions (M : ComplexStack) := Formal M ⧸ relations M

def symbol {M : ComplexStack} (g : Generator M) : StackFunctions M :=
  (relations M).mkQ (rawSymbol g)

structure LocallyFiniteTwoFibreModel {A B C : ComplexStack}
    (f : StackHom A C) (g : StackHom B C) where
  square : TwoCartesianSquare f g
  source : LocallyFiniteTypeStack
  apex_eq : square.apex=source.stack

def LocallyFiniteTwoFibreModel.fst {A B C : ComplexStack} {f : StackHom A C} {g : StackHom B C}
    (D : LocallyFiniteTwoFibreModel f g) : StackHom D.source.stack A := by
  rw [← D.apex_eq]
  exact D.square.fst

structure ConvolutionModel {X : Over base} (H : HallStacks X) (a b : Generator H.moduli) where
  first : TwoCartesianSquare H.subobject.map a.map
  second : LocallyFiniteTwoFibreModel
    (Pseudofunctor.StrongTrans.vcomp first.fst H.quotient.map) b.map

def ConvolutionModel.generator {X : Over base} {H : HallStacks X} {a b : Generator H.moduli}
    (D : ConvolutionModel H a b) : Generator H.moduli :=
  ⟨D.second.source,Pseudofunctor.StrongTrans.vcomp D.second.fst
    (Pseudofunctor.StrongTrans.vcomp D.first.fst H.middleTerm.map)⟩

abbrev ConvolutionModels {X : Over base} (H : HallStacks X) :=
  ∀ a b : Generator H.moduli, ConvolutionModel H a b

def rawConvolution {X : Over base} {H : HallStacks X} (D : ConvolutionModels H) :
    Formal H.moduli →ₗ[ℂ] Formal H.moduli →ₗ[ℂ] StackFunctions H.moduli :=
  Finsupp.linearCombination ℂ (fun a =>
    Finsupp.linearCombination ℂ (fun b => symbol (D a b).generator))

structure ConvolutionDescent {X : Over base} {H : HallStacks X} (D : ConvolutionModels H) : Prop where
  left : relations H.moduli ≤ (rawConvolution D).ker
  right : relations H.moduli ≤ (rawConvolution D).flip.ker

def convolution {X : Over base} {H : HallStacks X} {D : ConvolutionModels H}
    (h : ConvolutionDescent D) :
    StackFunctions H.moduli →ₗ[ℂ] StackFunctions H.moduli →ₗ[ℂ] StackFunctions H.moduli :=
  (rawConvolution D).liftQ₂ (relations H.moduli) (relations H.moduli) h.left h.right

end MathlibExt.AlgebraicGeometry.InfiniteHallStackFunctions
