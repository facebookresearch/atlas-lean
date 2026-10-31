/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Ext from the Koszul projective resolution (step A5, part 2: comparison)

Step A5 of the scoped Koszul/AB plan (A1–A6): Ext-vanishing via self-duality (part 1, separate
work) plus Ext-comparison (part 2, this file). This file bridges Mathlib's
`Ext` API to Koszul homology: it shows that `Ext^i(X, Y)` can be computed
from the Koszul chain complex once the augmentation is known to be a
quasi-isomorphism.

## Probe result: yes, the comparison exists in Mathlib (no gap)

Mathlib `v4.34.0` already contains the full "Ext from a given projective
resolution" API, in `Mathlib/CategoryTheory/Abelian/Projective/Ext.lean`
(literally titled "Computing `Ext` using a projective resolution"):

* `ProjectiveResolution.extEquivCohomologyClass` :
  `Ext X Y n ≃ CohomologyClass R.cochainComplex (single Y 0) n`.
* `ProjectiveResolution.extAddEquivCohomologyClass` : the additive form.
* `ProjectiveResolution.extMk` : builds `Ext X Y n` from a chain-level
  cocycle `f : R.complex.X n ⟶ Y` with `R.complex.d m n ≫ f = 0`.
* `ProjectiveResolution.extMk_eq_zero_iff` : `extMk f = 0 ↔
  ∃ g, R.complex.d n p ≫ g = f` (the vanishing criterion A5 consumes).
* `ProjectiveResolution.extMk_surjective` : every class is an `extMk`.
* `ProjectiveResolution.extMk_comp_mk₀` , `mk₀_comp_extMk`.

The underlying chain (all proved): `Ext` is `SmallShiftedHom` of single
complexes (`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`);
quasi-iso invariance is `SmallShiftedHom.precompEquiv`
(`Mathlib/CategoryTheory/Localization/SmallShiftedHom.lean`);
K-projective comparison is `CohomologyClass.equivOfIsKProjective`
(`Mathlib/Algebra/Homology/DerivedCategory/KProjective.lean`);
Hom-complex homology is `HomComplex.homologyAddEquiv`
(`Mathlib/Algebra/Homology/HomotopyCategory/HomComplexCohomology.lean`);
degreewise-projective `ChainComplex C ℕ` extends to a K-projective cochain
complex
(`Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean`,
an instance).

So this file is thin verified wrappers in the exact shape A5 needs:

* (§2) Koszul objects are degreewise projective: `koszulXd_projective`, from
  any basis of `M` via `Module.Basis.exteriorPower`
  (`LinearAlgebra/ExteriorPower/Basis.lean`) and
  `ModuleCat.projective_of_free`
  (`Algebra/Category/ModuleCat/Projective.lean`).
* (§3) `koszulProjectiveResolution` bundles `koszulChainComplex φ` into a
  `ProjectiveResolution X`, conditional on the augmentation quasi-iso.
* (§4) `koszulExtMk`, `koszulExtMk_eq_zero_iff`, `koszulExtMk_surjective`,
  `koszulExtAddEquiv`: the Ext-computation interface stated purely in terms
  of `koszulChainComplex φ` (chain level over `ℕ`), so A5 never touches
  cochain/`Cocycle`/`CohomologyClass` API.

## Residual (explicit hypothesis, not assumed)

The augmentation `π : koszulChainComplex φ ⟶ single₀ X` and its `QuasiIso`
proof are taken as explicit arguments of `koszulProjectiveResolution`.
Constructing them is step A4/R2 (exactness of `K(sop)`), budgeted inside
A4's lines — exactly the `KoszulConeSESResidual` pattern from A3. The
`OfSequence` bundling `koszulProjectiveResolutionOfSequence` is provided for
the sequence form A5 consumes (`X = residue field`, `Y = R_P` after A4).

## Contents

* (§1) Probe ledger (this docstring + `References` below): names with
  file:line for every Mathlib lemma consumed.
* (§2) `koszulXd_projective`: degreewise projectivity of Koszul objects.
* (§3) `koszulProjectiveResolution`, `koszulProjectiveResolutionOfSequence`.
* (§4) `koszulExtMk`, `koszulExtMk_eq_zero_iff`, `koszulExtMk_surjective`,
  `koszulExtAddEquiv`.

## References

Project (read-only): `Regularity/Koszul/KoszulComplex.lean` (A2 foundation:
`koszulChainComplex`, `koszulContractOfSequence`,
`koszulChainComplexOfSequence`, `koszulChainComplex_X`),
`Regularity/Unmixed/BabyAuslanderBuchsbaum.lean` (§1–§3: the length-2 AB equation this comparison
generalizes; its LES consumption is
`Abelian.Ext.covariant_sequence_exact₃'`,
`DerivedCategory/Ext/ExactSequences.lean`).

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `CategoryTheory/Preadditive/Projective/Resolution.lean`
  (`ProjectiveResolution` structure: `complex`, `projective`, `π`,
  `quasiIso`).
* `CategoryTheory/Abelian/Projective/Ext.lean` (`extEquivCohomologyClass`),
  (`extAddEquivCohomologyClass`) (`extMk`)
  (`extMk_eq_zero_iff`) (`extMk_surjective`).
* `Algebra/Category/ModuleCat/Ext/HasExt.lean`
  (`HasExt (ModuleCat.{v} R)` from `Small.{v} R`).
* `LinearAlgebra/ExteriorPower/Basis.lean`
  (`Module.Basis.exteriorPower`).
* `Algebra/Category/ModuleCat/Projective.lean` (`projective_of_free`).
* `Logic/Small/Defs.lean` (`small_self`, an instance).
* `Algebra/Homology/ShortComplex/Abelian.lean`
  (`categoryWithHomology_of_abelian`, filling `HasHomology`).

## Status

* §2 projectivity: unconditional (conditional only on the caller's basis).
* §3 resolution bundling: conditional-exact on `(π, QuasiIso π)` (A4/R2).
* §4 Ext wrappers: conditional-exact on the same `(π, QuasiIso π)` pair.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ExtComparison

open CategoryTheory HomologicalComplex KoszulComplex

universe u

/-! ## §2. Koszul objects are degreewise projective -/

/-- The `k`-th object of the Koszul chain complex is projective, from any
basis of `M`: exterior powers of a free module are free
(`Module.Basis.exteriorPower`), and free modules are projective
(`ModuleCat.projective_of_free`).
-/
theorem koszulXd_projective {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Type u} [LinearOrder I] (b : Module.Basis I R M)
    (k : ℕ) : Projective (ModuleCat.of R ↥(⋀[R]^k M)) :=
  ModuleCat.projective_of_free (M := ModuleCat.of R ↥(⋀[R]^k M))
    (b.exteriorPower k)

/-! ## §3. The Koszul complex as a `ProjectiveResolution` -/

/-- The Koszul chain complex bundled as a projective resolution of `X`,
conditional on the augmentation quasi-isomorphism (step A4/R2: exactness of
`K(sop)`). The `projective` field is §2; `hasHomology` is filled by
`categoryWithHomology_of_abelian` since `ModuleCat R` is abelian.

Conditional on exactly `(π, QuasiIso π)` (A4/R2 residual). -/
noncomputable def koszulProjectiveResolution {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Type u} [LinearOrder I]
    (b : Module.Basis I R M) (φ : M →ₗ[R] R) (X : ModuleCat.{u} R)
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) : ProjectiveResolution X where
  complex := koszulChainComplex φ
  projective := fun k => koszulXd_projective b k
  π := π
  quasiIso := hπ

/-- The sequence form A5 consumes: `φ` is the contraction functional of
`x : Fin n → R`, so `complex` is `koszulChainComplexOfSequence x` by `rfl`.

Conditional on exactly `(π, QuasiIso π)` (A4/R2 residual). -/
noncomputable def koszulProjectiveResolutionOfSequence {R : Type u} [CommRing R]
    {I : Type u} [LinearOrder I] {n : ℕ} (b : Module.Basis I R (Fin n → R))
    (x : Fin n → R) (X : ModuleCat.{u} R)
    (π : koszulChainComplexOfSequence x ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) : ProjectiveResolution X :=
  koszulProjectiveResolution b (koszulContractOfSequence x) X π hπ

/-! ## §4. Ext computed from the Koszul resolution -/

/-- Build `Ext X Y n` from a Koszul cocycle `f` (thin wrapper over
`ProjectiveResolution.extMk`, stated purely at chain level over `ℕ`).

Conditional on exactly `(π, QuasiIso π)` (A4/R2 residual). -/
noncomputable def koszulExtMk {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Type u} [LinearOrder I] (b : Module.Basis I R M)
    (φ : M →ₗ[R] R) {X Y : ModuleCat.{u} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) {n : ℕ} (f : (koszulChainComplex φ).X n ⟶ Y)
    (m : ℕ) (hm : n + 1 = m)
    (hf : (koszulChainComplex φ).d m n ≫ f = 0) : Abelian.Ext X Y n :=
  (koszulProjectiveResolution b φ X π hπ).extMk f m hm hf

/-- Vanishing criterion: a Koszul-built class is zero iff its cocycle is a
coboundary (thin wrapper over `ProjectiveResolution.extMk_eq_zero_iff`).
This is the lemma A5's vanishing argument consumes.

Conditional on exactly `(π, QuasiIso π)` (A4/R2 residual). -/
theorem koszulExtMk_eq_zero_iff {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Type u} [LinearOrder I] (b : Module.Basis I R M)
    (φ : M →ₗ[R] R) {X Y : ModuleCat.{u} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) {n : ℕ} (f : (koszulChainComplex φ).X n ⟶ Y)
    (m : ℕ) (hm : n + 1 = m)
    (hf : (koszulChainComplex φ).d m n ≫ f = 0)
    (p : ℕ) (hp : p + 1 = n) :
    koszulExtMk b φ π hπ f m hm hf = 0 ↔
      ∃ g : (koszulChainComplex φ).X p ⟶ Y,
        (koszulChainComplex φ).d n p ≫ g = f :=
  ProjectiveResolution.extMk_eq_zero_iff
    (koszulProjectiveResolution b φ X π hπ) f m hm hf p hp

/-- Every `Ext` class comes from a Koszul cocycle (thin wrapper over
`ProjectiveResolution.extMk_surjective`).

Conditional on exactly `(π, QuasiIso π)` (A4/R2 residual). -/
theorem koszulExtMk_surjective {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Type u} [LinearOrder I] (b : Module.Basis I R M)
    (φ : M →ₗ[R] R) {X Y : ModuleCat.{u} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) {n : ℕ} (α : Abelian.Ext X Y n) (m : ℕ)
    (hm : n + 1 = m) :
    ∃ (f : (koszulChainComplex φ).X n ⟶ Y)
      (hf : (koszulChainComplex φ).d m n ≫ f = 0),
      koszulExtMk b φ π hπ f m hm hf = α :=
  ProjectiveResolution.extMk_surjective
    (koszulProjectiveResolution b φ X π hπ) α m hm

/-- The full bridge: `Ext X Y n` as an additive group identifies with the
cohomology classes from the Koszul cochain complex (thin wrapper over
`ProjectiveResolution.extAddEquivCohomologyClass`).

Conditional on exactly `(π, QuasiIso π)` (A4/R2 residual). -/
noncomputable def koszulExtAddEquiv {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Type u} [LinearOrder I] (b : Module.Basis I R M)
    (φ : M →ₗ[R] R) {X Y : ModuleCat.{u} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) {n : ℕ} :
    Abelian.Ext X Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (koszulProjectiveResolution b φ X π hπ).cochainComplex
        ((CochainComplex.singleFunctor _ 0).obj Y) n :=
  (koszulProjectiveResolution b φ X π hπ).extAddEquivCohomologyClass

end ExtComparison
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
