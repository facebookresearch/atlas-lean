/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/SphereMonoid.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SymmetricSpectrum
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Comap

/-!
# The higher sphere monoids `S^(k)`

For a pointed simplicial set `X`, the symmetric sequence `n ↦ X^∧n` of smash powers is a
commutative monoid for the Day convolution product (`SymmetricSequence.smashPow X`), Hovey's
symmetric algebra `Sym(X)`, whose modules are the symmetric spectra based on `X`.

Taking `X` to be the simplicial `k`-sphere `S^k = (S¹)^∧k` gives the sphere monoid
`S^(k) = SymmetricSequence.sphereMonoid k`. Its `n`-th level is `(S^k)^∧n`, on which `Σ_n` acts
by permuting the `n` blocks of `k` circle coordinates, and its multiplication concatenates
blocks. Its modules, `SphereModule k`, are the symmetric spectra based on the `k`-sphere: the
structure maps have the form `(S^k)^∧p ∧ X_q → X_(p+q)`. They are the input of comparisons between
symmetric spectra indexed on different spheres, such as stabilization with respect to `S²`.

For `k = 1` the identification `(S¹)^∧1 ≅ S¹` of the single smash factor gives an isomorphism of
monoids `S^(1) ≅ S` with the sphere sequence (`SymmetricSequence.sphereMonoidOneIso`), so
restricting scalars identifies symmetric spectra with `S^(1)`-modules
(`SymmetricSpectrum.sphereModuleOneEquivalence`). The underlying symmetric sequences are not
changed: the chosen category of symmetric spectra is the `k = 1` instance of this family.

## Main definitions

* `SymmetricSequence.sphereMonoid k`: the sphere monoid `S^(k)`, `n ↦ (S^k)^∧n`.
* `SphereModule k`: the category of `S^(k)`-modules.
* `SymmetricSequence.sphereMonoidOneIso`: the isomorphism of monoids `S^(1) ≅ S`.
* `SymmetricSpectrum.sphereModuleOneEquivalence`: symmetric spectra are the `S^(1)`-modules.

## References

* M. Hovey, *Spectra and symmetric spectra in general model categories*, J. Pure Appl. Algebra
  165 (2001), 63–127.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource

open scoped DayFunctor

namespace SymmetricSequence

/-- The sphere monoid `S^(k)`: the symmetric sequence `n ↦ (S^k)^∧n` of smash powers of the
simplicial `k`-sphere `S^k = (S¹)^∧k`, on which `Σ_n` permutes the `n` blocks of `k` circle
coordinates. Block concatenation makes it a commutative monoid for the Day convolution product. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
noncomputable abbrev sphereMonoid (k : ℕ) : SymmetricSequence.{0} :=
  smashPow (PointedSSet.sphere k)

/- The sphere monoid `S^(k)` is a commutative monoid. -/
noncomputable example (k : ℕ) : IsCommMonObj (sphereMonoid k) := inferInstance

/-- The sphere monoid `S^(1)` is isomorphic, as a monoid, to the sphere sequence: in every level,
`((S¹)^∧1)^∧n ≅ (S¹)^∧n` identifies each block with its single circle coordinate. -/
noncomputable def sphereMonoidOneIso : sphereMonoid 1 ≅ sphere :=
  smashPowMapIso (PointedSSet.smashPowUniqueIso PointedSSet.circle (Fin 1))

/-- The isomorphism `S^(1) ≅ S` is an isomorphism of monoids. -/
instance : IsMonHom sphereMonoidOneIso.hom :=
  inferInstanceAs (IsMonHom (smashPowMapIso _).hom)

@[simp]
lemma sphereMonoidOneIso_hom :
    sphereMonoidOneIso.hom =
      smashPowMap (PointedSSet.smashPowUniqueIso PointedSSet.circle (Fin 1)).hom :=
  smashPowMapIso_hom _

@[simp]
lemma sphereMonoidOneIso_inv :
    sphereMonoidOneIso.inv =
      smashPowMap (PointedSSet.smashPowUniqueIso PointedSSet.circle (Fin 1)).inv :=
  smashPowMapIso_inv _

end SymmetricSequence

/-- The category of `S^(k)`-symmetric spectra: modules over the sphere monoid `S^(k)` for the Day
convolution product. -/
abbrev SphereModule (k : ℕ) := Mod SymmetricSequence.{0} (SymmetricSequence.sphereMonoid k)

/- Modules over each sphere monoid `S^(k)` form a monoidal category under the smash product over
`S^(k)`. -/
noncomputable example (k : ℕ) : MonoidalCategory (SphereModule k) := inferInstance

/- Function spectra are the internal hom for the smash product over each higher sphere monoid. -/
noncomputable example (k : ℕ) : MonoidalClosed (SphereModule k) := inferInstance

/- The smash product over each sphere monoid `S^(k)` is symmetric monoidal. -/
noncomputable example (k : ℕ) : SymmetricCategory (SphereModule k) := inferInstance

/-- Symmetric spectra are the `S^(1)`-modules: restricting scalars along the isomorphism of
monoids `S^(1) ≅ S` is an equivalence of categories, which does not change the underlying
symmetric sequences. -/
@[expose] noncomputable def SymmetricSpectrum.sphereModuleOneEquivalence :
    SymmetricSpectrum ≌ SphereModule 1 :=
  Mod.comapEquivalence SymmetricSequence.sphereMonoidOneIso

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_functor :
    sphereModuleOneEquivalence.functor = Mod.comap SymmetricSequence.sphereMonoidOneIso.hom :=
  Mod.comapEquivalence_functor _

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_inverse :
    sphereModuleOneEquivalence.inverse = Mod.comap SymmetricSequence.sphereMonoidOneIso.inv :=
  Mod.comapEquivalence_inverse _

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_unitIso_hom_app_hom (M : SymmetricSpectrum) :
    (sphereModuleOneEquivalence.unitIso.hom.app M).hom = 𝟙 M.X :=
  Mod.comapEquivalence_unitIso_hom_app_hom _ M

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_unitIso_inv_app_hom (M : SymmetricSpectrum) :
    (sphereModuleOneEquivalence.unitIso.inv.app M).hom = 𝟙 M.X :=
  Mod.comapEquivalence_unitIso_inv_app_hom _ M

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_counitIso_hom_app_hom (M : SphereModule 1) :
    (sphereModuleOneEquivalence.counitIso.hom.app M).hom = 𝟙 M.X :=
  Mod.comapEquivalence_counitIso_hom_app_hom _ M

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_counitIso_inv_app_hom (M : SphereModule 1) :
    (sphereModuleOneEquivalence.counitIso.inv.app M).hom = 𝟙 M.X :=
  Mod.comapEquivalence_counitIso_inv_app_hom _ M

end MathlibExt.SpectraSource
