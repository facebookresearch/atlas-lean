/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ValuedLineFibres
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.FunProp

/-!
# Norms fixed by actual integral-model line frames

The base is the actual norm-at-most-one subring of a nonarchimedean field.
A model has the actual generic-fibre pullback square and actual pullback
line isomorphism. Centres are actual valuative scheme maps and both their
base and generic maps are fixed. A local integral frame is a real module
section giving a stalk basis; its completed fibre basis is fixed to the
actual pullback germ. Its norm is then computed in those coordinates.

Centres, local frames and the ordinary fibre-basis comparison are source
integration inputs; generic valuative criteria and local freeness are not
requested again. Analytic continuity, model change and the adelic/Deligne
pairing comparisons are distinct geometric assertions.

Reference: Yuan--Zhang, arXiv:2105.13587v9, A.5.1, pp238-239. The model
frame has norm exactly one, fixing more than an arbitrary unit-ball rule.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.ModelLineMetrics

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open ValuedLineFibres
open scoped TensorProduct

/-- The actual integral subring of a nonarchimedean normed field. -/
def integerRing (K : Type) [NormedField K]
    (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖) : Subring K where
  carrier := {a | ‖a‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := (hK _ _).trans (max_le ha hb)
  neg_mem' {a} ha := by
    change ‖-a‖ ≤ 1
    change ‖a‖ ≤ 1 at ha
    simpa only [norm_neg] using ha
  mul_mem' {a b} ha hb := by
    change ‖a * b‖ ≤ 1
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg b)).trans
      (by simpa only [one_mul] using hb)

@[simp] theorem mem_integerRing (K : Type) [NormedField K]
    (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖) (a : K) :
    a ∈ integerRing K hK ↔ ‖a‖ ≤ 1 := Iff.rfl

variable (K : Type) [NormedField K]
  (X : Over (Spec (.of K)))

/-- The actual extension of base scalars into the completed residue field. -/
def completedScalar (p : Point K X) : K →+* CompletedResidue K X p :=
  (completionUnit K X p).comp
    (BerkovichAnalytification.scalarMap K X p.schemePoint)

/-- Base scalar norms survive the actual residue completion. -/
theorem completedScalar_norm (p : Point K X) (a : K) :
    ‖completedScalar K X p a‖ = ‖a‖ := by
  let b : Residue K X p := BerkovichAnalytification.scalarMap K X p.schemePoint a
  change ‖(UniformSpace.Completion.coeRingHom :
    Residue K X p →+* CompletedResidue K X p) b‖ = _
  exact (UniformSpace.Completion.norm_coe b).trans (p.extends_norm a)

/-- The actual completion retains the nonarchimedean inequality. -/
theorem completedUltrametric (p : NonArchPoint K X)
    (a b : CompletedResidue K X p.val) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  induction a, b using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
    simp only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
    exact p.property a b

/-- The actual integral subring of the completed residue field. -/
def residueIntegers (p : NonArchPoint K X) : Subring (CompletedResidue K X p.val) :=
  integerRing _ (completedUltrametric K X p)

variable (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖)

/-- The actual scalar map of valuation rings, fixed by completed residue scalars. -/
def integralScalar (p : NonArchPoint K X) :
    integerRing K hK →+* residueIntegers K X p where
  toFun a := ⟨completedScalar K X p.val a.val,
    by
      change ‖completedScalar K X p.val a.val‖ ≤ 1
      rw [completedScalar_norm]
      exact a.property⟩
  map_zero' := by ext; exact map_zero _
  map_one' := by ext; exact map_one _
  map_add' a b := by ext; exact map_add _ _ _
  map_mul' a b := by ext; exact map_mul _ _ _

variable (L : X.left.Modules)

/-- An actual proper flat finite-presentation integral model of the line. -/
structure Model where
  scheme : Scheme.{0}
  structureMap : scheme ⟶ Spec (.of (integerRing K hK))
  [proper : IsProper structureMap]
  [flat : Flat structureMap]
  [presentation : LocallyOfFinitePresentation structureMap]
  genericMap : X.left ⟶ scheme
  genericSquare : IsPullback genericMap X.hom structureMap
    (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))
  line : scheme.Modules
  isLine : CoherentCurveLinearSeries.IsLineBundle line
  genericLine : (Scheme.Modules.pullback genericMap).obj line ≅ L

attribute [instance] Model.proper Model.flat Model.presentation

variable {K X hK L} (M : Model K X hK L)

/-- A change of integral model, fixed on the actual generic line. -/
structure ModelMap (M' : Model K X hK L) where
  map : M'.scheme ⟶ M.scheme
  base : map ≫ M.structureMap = M'.structureMap
  generic : M'.genericMap ≫ map = M.genericMap
  line : (Scheme.Modules.pullback map).obj M.line ≅ M'.line
  line_generic :
    (Scheme.Modules.pullback M'.genericMap).map line.hom ≫ M'.genericLine.hom =
      (Scheme.Modules.pullbackComp M'.genericMap map).hom.app M.line ≫
        (Scheme.Modules.pullbackCongr generic).hom.app M.line ≫ M.genericLine.hom

/-- A centre is an actual valuative map, normalized on both base and generic fibre. -/
structure Centre (p : NonArchPoint K X) where
  map : Spec (.of (residueIntegers K X p)) ⟶ M.scheme
  base : map ≫ M.structureMap = Spec.map (CommRingCat.ofHom (integralScalar K X hK p))
  generic : Spec.map (CommRingCat.ofHom (residueIntegers K X p).subtype) ≫ map =
    Spec.map (CommRingCat.ofHom (completionUnit K X p.val)) ≫
      X.left.fromSpecResidueField p.val.schemePoint ≫ M.genericMap

/-- Pull an actual model section to the actual generic line by the native unit. -/
def pullbackModelSection {U : M.scheme.Opens} (s : M.line.val.obj (op U)) :
    L.val.obj (op (M.genericMap ⁻¹ᵁ U)) :=
  M.genericLine.hom.app (M.genericMap ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction M.genericMap).unit.app M.line).app
      U s)

/-- A real integral local frame whose completed basis is the fixed generic germ. -/
structure FrameAt (p : NonArchPoint K X) (C : Centre M p) where
  openSet : M.scheme.Opens
  centre_mem : ∀ z : Spec (.of (residueIntegers K X p)), C.map z ∈ openSet
  point_mem : M.genericMap p.val.schemePoint ∈ openSet
  localSection : M.line.val.obj (op openSet)
  stalkBasis : ∀ (y : M.scheme) (_hy : y ∈ openSet),
    Module.Basis Unit (M.scheme.presheaf.stalk y)
      (↑(TopCat.Presheaf.stalk M.line.val.presheaf y : AddCommGrpCat.{0}))
  stalkGenerator : ∀ (y : M.scheme) (hy : y ∈ openSet),
    stalkBasis y hy () =
      TopCat.Presheaf.germ M.line.val.presheaf openSet y hy localSection
  fibreBasis : Module.Basis Unit (CompletedResidue K X p.val) (Fibre K X L p.val)
  fibreGenerator : fibreBasis () =
    evaluateSection K X L (pullbackModelSection M localSection) p.val point_mem

/-- The exact norm in the completed fibre coordinates of the integral frame. -/
def frameNorm {p : NonArchPoint K X} {C : Centre M p} (F : FrameAt M p C)
    (v : Fibre K X L p.val) : ℝ := ‖F.fibreBasis.repr v ()‖

/-- Integral frame generators have norm exactly one. -/
theorem frameNorm_generator {p : NonArchPoint K X} {C : Centre M p}
    (F : FrameAt M p C) :
    frameNorm M F (evaluateSection K X L (pullbackModelSection M F.localSection)
      p.val F.point_mem) = 1 := by
  rw [← F.fibreGenerator]
  simp [frameNorm]

/-- The norm is genuine and cannot be replaced by a zero-valued model. -/
def frameFibreNorm {p : NonArchPoint K X} {C : Centre M p} (F : FrameAt M p C) :
    FibreNorm K X L p.val where
  norm := frameNorm M F
  nonnegative v := norm_nonneg _
  zero v := by
    rw [frameNorm, norm_eq_zero]
    constructor
    · intro h
      have hf : F.fibreBasis.repr v = 0 := by
        apply Finsupp.ext
        intro i
        cases i
        exact h
      exact F.fibreBasis.repr.injective (hf.trans F.fibreBasis.repr.map_zero.symm)
    · rintro rfl
      simp
  triangle v w := by
    change ‖F.fibreBasis.repr (v + w) ()‖ ≤
      ‖F.fibreBasis.repr v ()‖ + ‖F.fibreBasis.repr w ()‖
    rw [F.fibreBasis.repr.map_add, Finsupp.add_apply]
    exact norm_add_le _ _
  homogeneous a v := by
    change ‖F.fibreBasis.repr (a • v) ()‖ = ‖a‖ * ‖F.fibreBasis.repr v ()‖
    rw [F.fibreBasis.repr.map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]

/-- Local geometric integration inputs; all centres, frames and bases are normalized. -/
structure Frames where
  centre : ∀ p : NonArchPoint K X, Centre M p
  frame : ∀ p : NonArchPoint K X, FrameAt M p (centre p)

/-- The actual model norm family, computed from integral frame coordinates. -/
def modelNorm (F : Frames M) (p : NonArchPoint K X) : FibreNorm K X L p.val :=
  frameFibreNorm M (F.frame p)

/-- Analytic continuity is a separate assertion on the computed norms. -/
def IsContinuousModelNorm (F : Frames M) : Prop :=
  ∀ (U : X.left.Opens) (s : L.val.obj (op U)),
    Continuous (fun p : {p : NonArchPoint K X // p.val.schemePoint ∈ U} ↦
      (modelNorm M F p.val).norm
        (evaluateSection K X L s p.val.val p.property))

end MathlibExt.AlgebraicGeometry.ModelLineMetrics
