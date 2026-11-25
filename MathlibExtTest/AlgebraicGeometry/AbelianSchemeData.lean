/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AbelianSchemeData

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.PointedPicardFamilies

/-- Consumer: the base as a pointed scheme over a field. -/
example {k : Type} [Field k] : GoodReductionJacobian.PointedRelativeScheme k :=
  GoodReductionJacobian.PointedRelativeScheme.trivial k

/-- Higher-universe consumer. -/
example {k : Type (u + 1)} [Field k] : GoodReductionJacobian.PointedRelativeScheme k :=
  GoodReductionJacobian.PointedRelativeScheme.trivial k

/-- Consumer assembling Jacobian scheme data from its core, over a proper
scheme with a rational point. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {J : Scheme.{0}}
    (f : J ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A,
      pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hdim : SmoothOfRelativeDimension g f) (hproper : IsProper f)
    (M : PicardZeroModel C p) (e : Over.mk f ≅ M.J)
    (he : letI := L.grpObjOverMk; letI := M.group; IsMonHom e.hom) :
    MilneJVScheme.JacobianSchemeData A C p g (𝟙 (Spec (CommRingCat.of k))) :=
  MilneJVScheme.JacobianSchemeData.ofCore A C p g f L pts pts_add hdim hproper M e he

/-- The identity point of the group law agrees with the bridge image of
zero. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (D : GoodReductionJacobian.PointedRelativeScheme k)
    (L : RelativeGroupLaw k D.toBase) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (B : GoodReductionJacobian.AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 :=
  B.law_one_eq_pts_zero

/-- The zero section is the identity section of the abelian scheme, for any
test scheme of the bridge, an empty one included. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (D : MilneJVScheme.JacobianSchemeData A C p g σ) :
    D.D.zeroSection = D.abelianScheme.zero.left := by
  rw [D.zeroSection_eq, ← D.L.one_overMk]
  rfl

/-- Jacobian scheme data gives an abelian scheme over `Spec k` in the shared
`AbelianScheme` API, whose model is the data's scheme, so its operations apply:
here, the fibre at a point. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (D : MilneJVScheme.JacobianSchemeData A C p g σ) (s : Spec (CommRingCat.of k)) :
    AbelianScheme (Spec ((Spec (CommRingCat.of k)).residueField s)) :=
  D.abelianScheme.fibre s

/-- The abelian scheme's model is the data's scheme, and multiplication of its
points is the data's group law. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (D : MilneJVScheme.JacobianSchemeData A C p g σ) {T' : Scheme.{0}}
    (t : T' ⟶ Spec (CommRingCat.of k)) (x y : Over.mk t ⟶ D.abelianScheme.model) :
    D.abelianScheme.model = Over.mk D.D.toBase ∧ x * y = D.L.mul t x y :=
  ⟨rfl, D.L.mul_overMk t x y⟩

/-- The fibres of the data's scheme are connected, as the abelian scheme is
geometrically connected. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (D : MilneJVScheme.JacobianSchemeData A C p g σ) (s : Spec (CommRingCat.of k)) :
    _root_.IsConnected (D.D.toBase.base ⁻¹' {s}) :=
  have : GeometricallyConnected D.D.toBase := D.abelianScheme.connected
  D.D.toBase.isConnected_preimage_singleton s

/-- The scheme of Jacobian scheme data classifies the line bundles on the
curve that are normalized along the rational point and algebraically trivial
on geometric fibres: it represents Picard zero of the curve. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (D : MilneJVScheme.JacobianSchemeData A C p g σ)
    (S : Over (Spec (CommRingCat.of k))) (L : (prod C S).left.Modules)
    (hL : IsLineBundle L) (hN : IsNormalized C S p L)
    (hP : IsFibrewiseAlgebraicallyTrivial (prod.snd : prod C S ⟶ S).left L) :
    ∃! φ : S ⟶ Over.mk D.D.toBase,
      Nonempty (familyPullback C D.picard.J S D.picard.P (φ ≫ D.picardIso.hom) ≅ L) := by
  obtain ⟨φ, hφ, huniq⟩ := D.picard.universal S L hL hN hP
  refine ⟨φ ≫ D.picardIso.inv, by simpa using hφ, fun ψ hψ => ?_⟩
  rw [← huniq _ hψ]
  simp

/-- Boundary: the dimension parameter is not free. It equals
`dim H¹(C, 𝒪_C)`, the dimension of the Picard-zero model and the genus of a
curve with `H⁰(C, 𝒪_C) = k`. -/
example {k : Type} [Field k] (A : Type*) [AddCommGroup A]
    (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (g : ℕ) {T : Scheme.{0}}
    (σ : T ⟶ Spec (CommRingCat.of k))
    (D : MilneJVScheme.JacobianSchemeData A C p g σ) :
    g = Module.finrank k (cohomology C.hom (structureModule C.left) 1) := by
  have hg := D.hDim
  have hJ := D.picard.smoothDimension
  have hw : D.picardIso.hom.left ≫ D.picard.J.hom = D.D.toBase := Over.w D.picardIso.hom
  have hiso : IsIso D.picardIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map D.picardIso.hom))
  have hcomp : SmoothOfRelativeDimension
      (0 + Module.finrank k (cohomology C.hom (structureModule C.left) 1)) D.D.toBase := by
    rw [← hw]
    infer_instance
  have : Nonempty D.D.P :=
    ⟨D.D.zeroSection.base (Classical.arbitrary (PrimeSpectrum k))⟩
  have h5 : (g : WithBot ℕ∞) = ((0 + Module.finrank k
      (cohomology C.hom (structureModule C.left) 1) : ℕ) : WithBot ℕ∞) :=
    le_antisymm
      ((SmoothOfRelativeDimension.le_topologicalKrullDim D.D.toBase g).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le D.D.toBase _))
      ((SmoothOfRelativeDimension.le_topologicalKrullDim D.D.toBase _).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le D.D.toBase g))
  have h6 : g = 0 + Module.finrank k (cohomology C.hom (structureModule C.left) 1) := by
    exact_mod_cast h5
  omega
