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

end AlgebraicGeometry.PolarisedAbelianScheme.QMStructure
