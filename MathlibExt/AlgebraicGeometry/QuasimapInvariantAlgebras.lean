/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` (Mathlib):
Copyright (c) 2024 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapSectionLengths
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The actual homogeneous invariant algebra of a character polarization

The algebra carrier is the direct sum of the actual invariant-section
coefficient subgroups, retaining the homogeneous degree. Its
multiplication is fixed on every pair of homogeneous generators by
ordinary multiplication of their regular functions. This construction
also covers a trivial or torsion character, when the same regular
function occurs in several degrees.

The GIT target is the native Proj of this particular graded algebra.
The affine quotient is Spec of the actual invariant regular-function
ring, and its proper projection is recorded as genuine scheme geometry.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2, §2.2.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open LinearizedLineBundles LineBundleTaskContracts CoherentCurveLinearSeries
open QuasimapBasepointDefects QuasimapSectionLengths

universe u
variable {S : Scheme.{u}} (G W : Over S) [GrpObj G] [ModObj G W]
variable (L : CharacterPolarization G W)

/-- The actual invariant coefficient subgroup in degree m. -/
def invariantPiece (m : ℕ) : AddSubgroup Γ(W.left, ⊤) :=
  AddSubgroup.closure {f | ∃ s : Section (power L.line.module m),
    IsInvariantPowerSection G W L.line.linearization L.actionPowers L.projectionPowers m s ∧
      invariantCoefficient L m s = f}

abbrev InvariantAlgebra := DirectSum ℕ (fun m => ↥(invariantPiece G W L m))

/-- The component-supported native homogeneous subgroup of the actual direct sum. -/
def invariantGrading (m : ℕ) : AddSubgroup (InvariantAlgebra G W L) where
  carrier := {x | ∀ n, n ≠ m → x n = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb n hn := by simp [ha n hn, hb n hn]
  neg_mem' {x} ha n hn := by
    change -(x n) = 0
    rw [ha n hn, neg_zero]

/-- Native ring and grading assembly, with its full homogeneous multiplication fixed. -/
class InvariantAlgebraModel where
  [products : SetLike.GradedMonoid (invariantPiece G W L)]
  [grading : GradedRing (invariantGrading G W L)]
  zeroComparison : invariantGrading G W L 0 ≃+* invariantRing G W
  zero_normalized : ∀ a : invariantGrading G W L 0,
    (zeroComparison a).val = (a.val 0).val

attribute [instance] InvariantAlgebraModel.products
attribute [instance_reducible] InvariantAlgebraModel.grading
attribute [instance] InvariantAlgebraModel.grading

/-- The actual projective GIT quotient of the chosen invariant algebra. -/
abbrev gitScheme [InvariantAlgebraModel G W L] := Proj (invariantGrading G W L)

/-- The actual affine invariant-function quotient. -/
abbrev affineQuotient := Spec (.of (invariantRing G W))

/-- The affine-quotient arrow is the native degree-zero Proj structure map. -/
def gitAffineProjection [A : InvariantAlgebraModel G W L] :
    gitScheme G W L ⟶ affineQuotient G W :=
  Proj.toSpecZero (invariantGrading G W L) ≫
    Spec.map (CommRingCat.ofHom A.zeroComparison.symm.toRingHom)

/-- The invariant-coefficient scalar action is the actual degree-zero inclusion. -/
def invariantScalarMap [A : InvariantAlgebraModel G W L] :
    invariantRing G W →+* InvariantAlgebra G W L :=
  (SetLike.GradeZero.subring (invariantGrading G W L)).subtype.comp
    A.zeroComparison.symm.toRingHom

instance invariantAlgebraScalars [InvariantAlgebraModel G W L] :
    Algebra (invariantRing G W) (InvariantAlgebra G W L) :=
  (invariantScalarMap G W L).toAlgebra

/-- Evaluate every homogeneous invariant at the actual stable open. -/
def gitEvaluation [InvariantAlgebraModel G W L] (U : W.left.Opens) :
    InvariantAlgebra G W L →+* Γ(U, ⊤) :=
  U.ι.appTop.hom.comp (DirectSum.coeRingHom (invariantPiece G W L))

section ProjCover

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))

/-- The basic opens of the images of the positive-degree homogeneous elements
cover `X`: the irrelevant ideal generates the unit ideal sheaf. Generating the
unit ideal of `Γ(X, ⊤)` implies this but is strictly stronger: for the scalar
action on `𝔸² ∖ {0}`, whose global section ring is `ℂ[x, y]`, the coordinates
cover but generate a proper ideal. -/
def IrrelevantCovers : Prop :=
  ⨆ ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i, X.basicOpen (f ir.2.1) = ⊤

/-- The open cover of `X` by the basic opens of positive-degree homogeneous elements. -/
def irrelevantOpenCover (h : IrrelevantCovers 𝒜 f) : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ X.basicOpen (f ir.2.1)) h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The morphism $X \to \operatorname{Proj} A$ defined by a ring map
$f : A \to \Gamma(X, \mathcal{O}_X)$ from an $\mathbb{N}$-graded ring $A$ such that the basic opens
$D(f(r))$, for $r$ homogeneous of positive degree, cover $X$: it is glued from the morphisms
$D(f(r)) \to D_+(r)$ induced by $f$. -/
def fromOfIrrelevantCover (h : IrrelevantCovers 𝒜 f) : X ⟶ Proj 𝒜 := by
  refine (irrelevantOpenCover 𝒜 f h).glueMorphisms
    (fun ri ↦ Proj.toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((irrelevantOpenCover 𝒜 f h).f x)
      ((irrelevantOpenCover 𝒜 f h).f y) ≅ (X.basicOpen (f (x.snd.fst * y.snd.fst))) :=
    (isPullback_opens_inf _ _).isoPullback.symm ≪≫ X.isoOfEq (by simp)
  rw [← cancel_epi e.inv]
  trans Proj.toBasicOpenOfGlobalSections 𝒜 f rfl (Nat.add_pos_left x.2.2.1 y.1)
    (SetLike.mul_mem_graded x.2.2.2 y.2.2.2) ≫ (Scheme.Opens.ι _)
  · simpa [e, irrelevantOpenCover, Scheme.isoOfEq_inv] using
      Proj.homOfLE_toBasicOpenOfGlobalSections_ι _ _ rfl rfl y.2.2.2
  · simpa [e, irrelevantOpenCover, Scheme.isoOfEq_inv] using
      (Proj.homOfLE_toBasicOpenOfGlobalSections_ι _ _ (mul_comm _ _) (add_comm _ _)
        x.2.2.2).symm

/-- Generating the unit ideal of the global sections implies the local condition. -/
theorem irrelevantCovers_of_map_eq_top
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) : IrrelevantCovers 𝒜 f := by
  classical
  have H : Ideal.span (Set.range fun x : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ x.2.1) =
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    apply le_antisymm
    · rw [Ideal.span_le, Set.range_subset_iff]
      rintro ⟨i, r, hi0, hri⟩
      simp [-ZeroMemClass.coe_eq_zero, DirectSum.decompose_of_mem_ne 𝒜 hri hi0.ne']
    · intro x hx
      rw [← DirectSum.sum_support_decompose 𝒜 x]
      refine Ideal.sum_mem _ fun c hc ↦ ?_
      have : c ≠ 0 := by contrapose hc; simpa [hc] using hx
      exact Ideal.subset_span ⟨⟨c, _, this.bot_lt, by simp⟩, rfl⟩
  unfold IrrelevantCovers
  ext1
  apply compl_injective
  simp only [TopologicalSpace.Opens.coe_iSup, Set.compl_iUnion, ← Scheme.zeroLocus_singleton,
    ← Scheme.zeroLocus_iUnion, Set.iUnion_singleton_eq_range, TopologicalSpace.Opens.coe_top,
    Set.compl_univ]
  rw [← Scheme.zeroLocus_span, Set.range_comp', ← Ideal.map_span, H, hf]
  simp

end ProjCover

/-- The canonical stable-locus map, glued from the native Proj charts over the
basic opens of the positive-degree invariants, which cover the stable open. -/
def gitOrbitMap [InvariantAlgebraModel G W L] (U : W.left.Opens)
    (h : IrrelevantCovers (invariantGrading G W L) (gitEvaluation G W L U)) :
    U.toScheme ⟶ gitScheme G W L :=
  fromOfIrrelevantCover (invariantGrading G W L) (gitEvaluation G W L U) h

end MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras
