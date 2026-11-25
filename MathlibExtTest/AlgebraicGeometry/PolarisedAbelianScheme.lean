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

open CategoryTheory AlgebraicGeometry
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

/-- Invertibility of a polarisation sheaf unpacks to local
trivialisations. -/
example {X : Scheme.{u}} (𝓛 : X.Modules)
    (h : Scheme.Modules.IsInvertible 𝓛) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  h.exists_trivialization x

/-- A canonical polarisation is symmetric, its Mumford kernel is the
two-torsion, and it is Rosati compatible with the action. -/
example {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    {L : RelativeGroupLaw S f} {I : Type} {act : I → (A ⟶ A)}
    {act_over : ∀ x : I, act x ≫ f = f} {star : I → I} {𝓛 : A.Modules}
    (h : IsCanonicalPolData f L act act_over star 𝓛) :
    Polarisation.IsSymmetric f L 𝓛 ∧ Polarisation.KernelIsTwoTorsion f L 𝓛 ∧
      Polarisation.RosatiCompatible f L 𝓛 act act_over star :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.2⟩

/-- The polarisation of a quaternion multiplication structure is locally
the cube of a canonical polarisation. -/
example {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ}
    {β : Fin (2 * 2) → ↥Λ} {d m : ℕ} {S : Type u} [CommRing S]
    {X : PolarisedAbelianScheme 2 d m S} (s : QMStructure Λ star β X) :
    ∃ polE : X.A.Modules, IsCanonicalPolData X.f X.L s.act s.act_over star polE ∧
      LocIsoOnBase X.f X.pol (moduleTensor X.A polE (moduleTensor X.A polE polE)) :=
  s.pol_canonical

/-- The polarisation of a polarised abelian scheme is very ample: some
presentation of it by global sections maps the scheme to projective space
by a closed immersion. -/
example {g d n : ℕ} {S : Type u} [CommRing S] (X : PolarisedAbelianScheme g d n S) :
    ∃ (N : ℕ) (𝔓 : X.pol.ProjPresentation X.f N), IsClosedImmersion 𝔓.toProj :=
  X.pol_veryAmple

end AlgebraicGeometry.PolarisedAbelianScheme.QMStructure
