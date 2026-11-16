/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallFamilyStackModels
public import MathlibExt.AlgebraicGeometry.HallProjectiveInverseModels
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Exact-sequence convolution and the regular Hall subspace

Each product generator is the iterated actual two-fibre product of
the subobject and quotient maps with its two source generators,
followed by the middle-term strong map. This is equation (15)'s
two-fibre product over M × M, retaining its comparison isomorphisms
and all arrows. Denominator stages add under multiplication.

The regular space contains actual scheme-source/Lefschetz symbols
and is closed under the actual inverse projective-space scalar
products, as required by the v3 correction in §7.3, equation (50).
Its Lefschetz operator is the actual affine-line product. The
semiclassical carrier is literally the quotient by the image of
that operator minus the identity.

Reference: Bridgeland, arXiv:1002.4374v3, equation (15), §5.1.
Descent, regular closure and algebra/Poisson laws are separate requests
about these specified maps, not inputs of an arbitrary Hall ring.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallConvolutionOperations

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackVectorBundles StackChowGroups
open GeometricHallStackFunctions HallFamilyStackModels
open HallProjectiveInverseModels

variable {X : Over (Spec (.of ℂ))}

/-- A finite-type source for the actual native two-Cartesian square. -/
structure FiniteTwoFibreModel {A B C : ComplexStack}
    (f : StackHom A C) (g : StackHom B C) where
  square : TwoCartesianSquare f g
  source : FiniteTypeStack
  apex_eq : square.apex = source.stack

namespace FiniteTwoFibreModel

def fst {A B C : ComplexStack} {f : StackHom A C} {g : StackHom B C}
    (D : FiniteTwoFibreModel f g) : StackHom D.source.stack A := by
  rw [← D.apex_eq]
  exact D.square.fst

def snd {A B C : ComplexStack} {f : StackHom A C} {g : StackHom B C}
    (D : FiniteTwoFibreModel f g) : StackHom D.source.stack B := by
  rw [← D.apex_eq]
  exact D.square.snd

end FiniteTwoFibreModel

/-- The two original sequence projections define the product fibre, in order. -/
structure ConvolutionModel (H : HallStacks X) (a b : Generator H.moduli) where
  first : TwoCartesianSquare H.subobject.map a.map
  second : FiniteTwoFibreModel
    (Pseudofunctor.StrongTrans.vcomp first.fst H.quotient.map) b.map

/-- The product's actual map is its lift to M^(2) followed by the middle term. -/
def ConvolutionModel.generator {H : HallStacks X} {a b : Generator H.moduli}
    (D : ConvolutionModel H a b) : Generator H.moduli :=
  ⟨D.second.source, Pseudofunctor.StrongTrans.vcomp D.second.fst
    (Pseudofunctor.StrongTrans.vcomp D.first.fst H.middleTerm.map)⟩

/-- All symbols use their actual geometric convolution square. -/
abbrev ConvolutionModels (H : HallStacks X) :=
  ∀ a b : Generator H.moduli, ConvolutionModel H a b

/-- The fixed bilinear map on the free staged presentation. -/
def rawConvolution {H : HallStacks X} (D : ConvolutionModels H) :
    StagedFormal H.moduli →ₗ[ℂ] StagedFormal H.moduli →ₗ[ℂ]
      LefschetzStackFunctions H.moduli :=
  Finsupp.linearCombination ℂ (fun a =>
    Finsupp.linearCombination ℂ (fun b =>
      stageSymbol (D a.1 b.1).generator (a.2+b.2)))

/-- Only preservation of the specified geometric and Lefschetz relations is requested. -/
structure ConvolutionDescent {H : HallStacks X} (D : ConvolutionModels H) : Prop where
  left : stagedRelations H.moduli ≤ (rawConvolution D).ker
  right : stagedRelations H.moduli ≤ (rawConvolution D).flip.ker

/-- Actual Hall multiplication on the geometric quotient. -/
def convolution {H : HallStacks X} {D : ConvolutionModels H} (h : ConvolutionDescent D) :
    LefschetzStackFunctions H.moduli →ₗ[ℂ] LefschetzStackFunctions H.moduli →ₗ[ℂ]
      LefschetzStackFunctions H.moduli :=
  (rawConvolution D).liftQ₂ (stagedRelations H.moduli) (stagedRelations H.moduli)
    h.left h.right

/-- On every source symbol, multiplication is the geometric correspondence. -/
theorem convolution_stageSymbol {H : HallStacks X} {D : ConvolutionModels H}
    (h : ConvolutionDescent D) (a b : Generator H.moduli) (n m : ℕ) :
    convolution h (stageSymbol a n) (stageSymbol b m) =
      stageSymbol (D a b).generator (n+m) := by
  simp [convolution, stageSymbol, rawStage, rawConvolution,
    Finsupp.linearCombination_single]

/-- A scalar acts by the actual geometric product with its source stack. -/
abbrev ScalarProductModels (M : ComplexStack) (A : FiniteTypeStack) :=
  ∀ g : Generator M, ProductModel A g.source

def scalarGenerator {M : ComplexStack} {A : FiniteTypeStack}
    (D : ScalarProductModels M A) (g : Generator M) : Generator M :=
  ⟨(D g).apex, Pseudofunctor.StrongTrans.vcomp (D g).snd g.map⟩

def rawScalar {M : ComplexStack} {A : FiniteTypeStack} (D : ScalarProductModels M A) :
    StagedFormal M →ₗ[ℂ] StagedFormal M :=
  Finsupp.linearCombination ℂ (fun a => rawStage (scalarGenerator D a.1) a.2)

def ScalarDescent {M : ComplexStack} {A : FiniteTypeStack} (D : ScalarProductModels M A) :
    Prop := stagedRelations M ≤ (stagedRelations M).comap (rawScalar D)

def scalarAction {M : ComplexStack} {A : FiniteTypeStack} {D : ScalarProductModels M A}
    (h : ScalarDescent D) : LefschetzStackFunctions M →ₗ[ℂ] LefschetzStackFunctions M :=
  (stagedRelations M).mapQ (stagedRelations M) (rawScalar D) h

/-- Scheme-source membership is the genuine represented-category comparison. -/
def IsRegularGenerator {M : ComplexStack} (g : Generator M) : Prop :=
  Nonempty (SchemeSource g.source)

def schemeLefschetzSubmodule (M : ComplexStack) : Submodule ℂ (LefschetzStackFunctions M) :=
  Submodule.span ℂ {a | ∃ (g : Generator M) (n : ℕ), IsRegularGenerator g ∧ a=stageSymbol g n}

/-- Stability under the actual inverse classes of all projective spaces. -/
def ProjectiveInverseStable {M : ComplexStack} (P : Submodule ℂ (LefschetzStackFunctions M)) :
    Prop := ∀ (k : ℕ) (J : ProjectiveInverseModel k)
      (D : ScalarProductModels M J.inverseStack) (h : ScalarDescent D),
    P ≤ P.comap (scalarAction h)

/-- The regular space over K(Var)[L^-1,[P^k]^-1], including the v3 correction. -/
def regularSubmodule (M : ComplexStack) : Submodule ℂ (LefschetzStackFunctions M) :=
  sInf {P | schemeLefschetzSubmodule M ≤ P ∧ ProjectiveInverseStable P}

/-- The source's H_reg, as its actual subspace in the geometric Hall group. -/
abbrev Regular (M : ComplexStack) := regularSubmodule M

def regularSymbol {M : ComplexStack} (g : Generator M) (S : SchemeSource g.source) (n : ℕ) :
    Regular M :=
  ⟨stageSymbol g n, Submodule.mem_sInf.mpr (fun _P hP =>
    hP.1 (Submodule.subset_span ⟨g,n,⟨S⟩,rfl⟩))⟩

/-- Projective-space inverse scalar multiplication preserves this corrected space. -/
theorem projectiveInverse_regular {M : ComplexStack} (k : ℕ) (J : ProjectiveInverseModel k)
    (D : ScalarProductModels M J.inverseStack) (h : ScalarDescent D) (a : Regular M) :
    scalarAction h a.val ∈ regularSubmodule M := by
  apply Submodule.mem_sInf.mpr
  intro P hP
  exact hP.2 k J D h (Submodule.mem_sInf.mp a.property P hP)

/-- The Lefschetz operator uses the actual affine-line product at every stage. -/
def rawLefschetz {M : ComplexStack} (D : ∀ g : Generator M, LefschetzProduct g) :
    StagedFormal M →ₗ[ℂ] StagedFormal M :=
  Finsupp.linearCombination ℂ (fun a => rawStage (D a.1).generator a.2)

def LefschetzDescent {M : ComplexStack} (D : ∀ g : Generator M, LefschetzProduct g) : Prop :=
  stagedRelations M ≤ (stagedRelations M).comap (rawLefschetz D)

def lefschetz {M : ComplexStack} {D : ∀ g : Generator M, LefschetzProduct g}
    (h : LefschetzDescent D) : LefschetzStackFunctions M →ₗ[ℂ] LefschetzStackFunctions M :=
  (stagedRelations M).mapQ (stagedRelations M) (rawLefschetz D) h

/-- These are closure proofs for the computed operations, without algebra laws. -/
structure RegularClosure {H : HallStacks X} {D : ConvolutionModels H}
    (h : ConvolutionDescent D) {L : ∀ g : Generator H.moduli, LefschetzProduct g}
    (hL : LefschetzDescent L) : Prop where
  multiplication : ∀ a b : Regular H.moduli,
    convolution h a.val b.val ∈ regularSubmodule H.moduli
  lefschetz : ∀ a : Regular H.moduli, lefschetz hL a.val ∈ regularSubmodule H.moduli

def regularMultiplication {H : HallStacks X} {D : ConvolutionModels H}
    {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
    {hL : LefschetzDescent L} (C : RegularClosure h hL) :
    Regular H.moduli →ₗ[ℂ] Regular H.moduli →ₗ[ℂ] Regular H.moduli :=
  LinearMap.mk₂ ℂ (fun a b => ⟨convolution h a.val b.val,C.multiplication a b⟩)
    (by intros; apply Subtype.ext; simp)
    (by intros; apply Subtype.ext; simp)
    (by intros; apply Subtype.ext; simp)
    (by intros; apply Subtype.ext; simp)

def regularLefschetz {H : HallStacks X} {D : ConvolutionModels H}
    {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
    {hL : LefschetzDescent L} (C : RegularClosure h hL) :
    Regular H.moduli →ₗ[ℂ] Regular H.moduli where
  toFun a := ⟨lefschetz hL a.val,C.lefschetz a⟩
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

/-- The actual ideal (L−1)H_reg, presented as the operator's range. -/
def semiclassicalRelations {H : HallStacks X} {D : ConvolutionModels H}
    {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
    {hL : LefschetzDescent L} (C : RegularClosure h hL) : Submodule ℂ (Regular H.moduli) :=
  LinearMap.range (regularLefschetz C - LinearMap.id)

/-- The source's H_sc is a quotient of this specific regular Hall subspace. -/
abbrev Semiclassical {H : HallStacks X} {D : ConvolutionModels H}
    {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
    {hL : LefschetzDescent L} (C : RegularClosure h hL) :=
  Regular H.moduli ⧸ semiclassicalRelations C

end MathlibExt.AlgebraicGeometry.HallConvolutionOperations
