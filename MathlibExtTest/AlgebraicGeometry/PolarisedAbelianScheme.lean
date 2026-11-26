/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PolarisedAbelianScheme

/-!
# Tests for polarised abelian schemes with quaternion multiplication
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Polynomial
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
  (IsLineBundle isLineBundle_structureModule structureModule)
open MathlibExt.AlgebraicGeometry.SchemeModulesTensor (moduleTensor)

open scoped Quaternion

universe u

namespace AlgebraicGeometry.PolarisedAbelianScheme.QMStructure

/-- Consumer with the original binders: pullback along a composite is
the composite pullback. -/
theorem exactSource {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (χ : S' →+* S'')
    {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
    {X'' : PolarisedAbelianScheme 2 d m S''}
    {t : QMStructure Λ star β X} {t' : QMStructure Λ star β X'}
    {t'' : QMStructure Λ star β X''}
    (h : QMStructure.IsPullback φ t t') (h' : QMStructure.IsPullback χ t' t'') :
    QMStructure.IsPullback (χ.comp φ) t t'' :=
  QMStructure.IsPullback.trans φ χ h h'

/-- The polarisation of a quaternion multiplication structure is locally
the cube of a canonical polarisation. -/
example {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ}
    {β : Fin (2 * 2) → ↥Λ} {d m : ℕ} {S : Type u} [CommRing S]
    {X : PolarisedAbelianScheme 2 d m S} (s : QMStructure Λ star β X) :
    ∃ polE : X.A.Modules,
      QMCanonicalPol.CanonicalPolarizationData X.L s.act s.act_over star polE ∧
      QMCanonicalPol.LocIsoOnBase X.f X.pol
        (moduleTensor X.A polE (moduleTensor X.A polE polE)) :=
  s.pol_canonical

/-- The canonical polarisation of a quaternion multiplication structure is
symmetric, its Mumford kernel is the two-torsion, and it is Rosati
compatible with the action. -/
example {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ}
    {β : Fin (2 * 2) → ↥Λ} {d m : ℕ} {S : Type u} [CommRing S]
    {X : PolarisedAbelianScheme 2 d m S} (s : QMStructure Λ star β X) :
    ∃ polE : X.A.Modules, QMCanonicalPol.IsSymmetric X.L polE ∧
      QMCanonicalPol.KernelIsTwoTorsion X.L polE ∧
      QMCanonicalPol.RosatiCompatible X.L polE s.act s.act_over star := by
  obtain ⟨polE, h, -⟩ := s.pol_canonical
  exact ⟨polE, h.isSymmetric, h.kernelIsTwoTorsion, h.rosatiCompatible⟩

/-- The polarisation of a polarised abelian scheme is very ample: some
presentation of it by global sections maps the scheme to projective space
by a closed immersion. -/
example {g d n : ℕ} {S : Type u} [CommRing S] (X : PolarisedAbelianScheme g d n S) :
    ∃ (N : ℕ) (𝔓 : X.pol.ProjPresentation X.f N), IsClosedImmersion 𝔓.toProj :=
  X.pol_veryAmple

/-- A sheaf that is very ample relative to `f` makes `f` proper: `f` factors
through a closed immersion into projective space over the base. -/
private theorem isProper_of_closedImmersionBySections {R : Type u} [CommRing R]
    {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (CommRingCat.of R)}
    (h : M.ClosedImmersionBySections f) : IsProper f := by
  obtain ⟨N, 𝔓, h𝔓⟩ := h
  rw [← 𝔓.toProj_π]
  infer_instance

/-- An invertible sheaf need not be very ample: the structure sheaf of the
affine line over a field is invertible, but the affine line is not proper
over the field, so no presentation by global sections maps it to
projective space by a closed immersion. -/
example (K : Type u) [Field K] :
    IsLineBundle (structureModule (Spec (CommRingCat.of K[X]))) ∧
      ¬ (structureModule (Spec (CommRingCat.of K[X]))).ClosedImmersionBySections
        (Spec.map (CommRingCat.ofHom (algebraMap K K[X]))) := by
  refine ⟨isLineBundle_structureModule _, fun h => ?_⟩
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K K[X]))) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr
      ⟨isProper_of_closedImmersionBySections h, inferInstance⟩
  rw [IsFinite.SpecMap_iff] at hfin
  exact Polynomial.not_finite (RingHom.finite_algebraMap.mp hfin)

/-- `Λ` need not be an order: the zero submodule, which does not contain `1`,
gives a well-formed type of quaternion multiplication structures. -/
example {d m : ℕ} {S : Type u} [CommRing S] (X : PolarisedAbelianScheme 2 d m S) :
    Type (u + 1) :=
  QMStructure (⊥ : Submodule ℤ ℍ[ℚ, 1, 1]) id (fun _ => 0) X

/-- The zero submodule of `ℍ[ℚ, 1, 1]` does not contain `1`. -/
example : (1 : ℍ[ℚ, 1, 1]) ∉ (⊥ : Submodule ℤ ℍ[ℚ, 1, 1]) := by
  simp

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The ratio condition of a presentation is stated with `ProjSpace.ratio`, so
`ProjSpace.ratio_self` rewrites it: at `j = i` it reduces to `σ i = σ i`. -/
example {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ} (𝔓 : M.ProjPresentation f N)
    (i : Fin (N + 1)) : True := by
  have h := 𝔓.app_ratio_smul i i
  rw [ProjSpace.ratio_self, map_one, map_one, one_smul] at h
  trivial

end AlgebraicGeometry.PolarisedAbelianScheme.QMStructure
