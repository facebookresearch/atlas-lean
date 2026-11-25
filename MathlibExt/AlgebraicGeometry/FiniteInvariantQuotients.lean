/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
ported from `TauCeti/AlgebraicGeometry/Quotient/Affine.lean`,
`TauCeti/AlgebraicGeometry/Quotient/FiniteGroup/Affine.lean`,
`TauCeti/AlgebraicGeometry/Quotient/FiniteGroup/UniversalProperty.lean` in
TauCetiProject/TauCeti at revision 62bbc0596dc3539d488232e4e924a338548ea0a9. Consolidate the
complete affine, finite-group and arbitrary-target quotient proofs; replace project imports
by the listed completed local dependencies. No unresolved result is added.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.RingTheory.InvariantPointMaps
public import MathlibExt.RingTheory.InvariantLocalization
public import MathlibExt.AlgebraicGeometry.InvariantSchemeDescent

/-!
# Affine invariant quotients

For a monoid acting on a commutative ring `A`, the affine invariant quotient is `Spec (Aᴳ)`,
with projection induced by the inclusion of the fixed subring.
This file proves its universal property for affine target schemes. For group actions,
the contravariant spectrum maps are isomorphisms and act on prime ideals by the inverse element.

The first section proves the affine-target universal property for monoid actions.
The later finite-group sections prove integral/surjective/finite and orbit properties,
then `descOfFinite` and `existsUnique_desc_of_finite` give the universal property for
arbitrary scheme targets using the actual localization and glueing maps.

## Main definitions

* `quotient`: the spectrum of the fixed subring.
* `projection`: the invariant-spectrum projection.
* `specComap`: the contravariant spectrum map of an action element.
* `specAction`: for a group action, the induced action on `Spec A` by automorphisms.
* `actionMap`: the action graphs mapped into the kernel pair of the quotient projection.
* `desc`: descent of an invariant morphism to an affine target.

## Main results

* `existsUnique_desc` and `hom_ext`: the affine-target universal property.
* `projection_specAlgebraMap`: the projection lies over every invariant base ring.
* `specComap_base_apply`: the point map of a group element is the inverse spectrum action.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped Pointwise

namespace TauCeti.AffineInvariantQuotient

universe u v

section Monoid

variable (A : Type u) (G : Type v) [CommRing A] [Monoid G] [MulSemiringAction G A]

/-- The spectrum of the fixed subring, the affine invariant quotient of `Spec A`. -/
noncomputable abbrev quotient : Scheme.{u} :=
  Spec (CommRingCat.of (FixedPoints.subring A G))

/-- The quotient projection, induced by the inclusion of invariant functions. -/
noncomputable def projection : Spec (CommRingCat.of A) ⟶ quotient A G :=
  Spec.algebraMap (FixedPoints.subring A G) A

/-- The defining equation for the quotient projection. -/
theorem projection_def : projection A G = Spec.algebraMap (FixedPoints.subring A G) A := (rfl)

/-- The projection contracts prime ideals to the fixed subring. -/
@[simp]
theorem projection_base_apply (x : PrimeSpectrum A) :
    (projection A G).base x = PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) x := by
  rw [projection_def]
  exact Spec.map_apply (CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A)) x

/-- The quotient projection lies over every invariant base ring. -/
@[simp, reassoc]
theorem projection_specAlgebraMap (R : Type u) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] :
    projection A G ≫ Spec.algebraMap R (FixedPoints.subalgebra R A G) =
      Spec.algebraMap R A := by
  rw [projection_def]
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))
    (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A))).symm.trans (by
      rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

/-- The contravariant spectrum map induced by an element of the acting monoid. -/
noncomputable def specComap (g : G) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g))

/-- The defining equation for the contravariant spectrum map. -/
theorem specComap_def (g : G) :
    specComap A G g = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) := (rfl)

/-- Pullback on global sections recovers the ring homomorphism of the action element. -/
@[simp]
theorem preimage_specComap (g : G) :
    Spec.preimage (specComap A G g) =
      CommRingCat.ofHom (MulSemiringAction.toRingHom G A g) := by
  rw [specComap_def, Spec.preimage_map]

/-- The identity element pulls back to the identity morphism of the spectrum. -/
@[simp]
theorem specComap_one : specComap A G 1 = 𝟙 _ := by
  rw [specComap_def, ← Spec.map_id]
  exact congrArg Spec.map (by ext a; exact one_smul G a)

/-- Pullback reverses composition: these morphisms form a right action on the spectrum. -/
@[simp]
theorem specComap_mul (g h : G) :
    specComap A G (g * h) = specComap A G g ≫ specComap A G h := by
  rw [specComap_def, specComap_def, specComap_def, ← Spec.map_comp]
  exact congrArg Spec.map (by ext a; exact mul_smul g h a)

/-- The quotient projection is invariant under every element of the acting monoid. -/
@[reassoc (attr := simp)]
theorem specComap_projection (g : G) :
    specComap A G g ≫ projection A G = projection A G := by
  rw [specComap_def, projection_def, ← Spec.map_comp]
  exact congrArg Spec.map (by ext a; exact a.property g)

section ActionMap

variable [Small.{u} G]

/-- The action graphs over the invariant quotient. On the component indexed by `g`, the two
projections are the identity and `specComap A G g`, respectively. The latter is the right action
on spectra, induced contravariantly by `a ↦ g • a`. The assumption `Small.{u} G` ensures that
the coproduct exists in `Scheme.{u}`; it is automatic for finite `G`. -/
noncomputable def actionMap : (∐ fun _ : G ↦ Spec (CommRingCat.of A)) ⟶
    pullback (projection A G) (projection A G) :=
  Sigma.desc fun g ↦ pullback.lift (𝟙 _) (specComap A G g) (by simp)

/-- The restriction of the action map to one component is the graph of its action element. -/
@[reassoc (attr := simp)]
theorem ι_actionMap (g : G) :
    Sigma.ι (fun _ : G ↦ Spec (CommRingCat.of A)) g ≫ actionMap A G =
      pullback.lift (𝟙 _) (specComap A G g) (by simp) := by
  simp [actionMap]

/-- The first projection of the action relation forgets the group element. -/
@[reassoc (attr := simp)]
theorem actionMap_fst : actionMap A G ≫ pullback.fst _ _ =
    Sigma.desc (fun _ : G ↦ 𝟙 (Spec (CommRingCat.of A))) := by
  ext g
  simp

/-- The second projection of the action relation applies the action element. -/
@[reassoc (attr := simp)]
theorem actionMap_snd : actionMap A G ≫ pullback.snd _ _ =
    Sigma.desc (fun g : G ↦ specComap A G g) := by
  ext g
  simp

end ActionMap

variable {A G}

/-- An invariant morphism to an affine scheme pulls back functions to invariant functions. -/
private theorem preimage_mem_fixed {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) (a : Γ(Y, ⊤)) :
    (Spec.preimage (f ≫ Y.isoSpec.hom)).hom a ∈ FixedPoints.subring A G := by
  intro g
  have h := congrArg Spec.preimage (congrArg (fun k => k ≫ Y.isoSpec.hom) (hf g))
  simpa only [Category.assoc, Spec.preimage_comp, preimage_specComap, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom, RingHom.comp_apply, MulSemiringAction.toRingHom_apply] using
    congrArg (fun k => k.hom a) h

/-- Descend an invariant morphism to an affine target through the fixed-subring spectrum. -/
noncomputable def desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) : quotient A G ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
      (FixedPoints.subring A G) (preimage_mem_fixed f hf))) ≫ Y.isoSpec.inv

/-- The descended morphism factors the given invariant morphism. -/
@[reassoc (attr := simp)]
theorem projection_desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    projection A G ≫ desc f hf = f := by
  rw [desc, projection_def, ← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom
      ((Spec.preimage (f ≫ Y.isoSpec.hom)).hom.codRestrict
        (FixedPoints.subring A G) (preimage_mem_fixed f hf)) ≫
      CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A) =
      Spec.preimage (f ≫ Y.isoSpec.hom) := by
    ext a
    rfl
  rw [h, Spec.map_preimage]
  simp

/-- Morphisms from the invariant quotient to an affine target are determined by their
composition with the projection. -/
@[ext]
theorem hom_ext {Y : Scheme.{u}} [IsAffine Y] {f h : quotient A G ⟶ Y}
    (hfh : projection A G ≫ f = projection A G ≫ h) : f = h := by
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (FixedPoints.subring A G).subtype)
    Subtype.val_injective ⊤ (isAffineOpen_top Y) (by simp) (by simp)
  exact hfh

/-- The affine-target universal property: every invariant morphism factors uniquely through
the invariant quotient. -/
theorem existsUnique_desc {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (CommRingCat.of A) ⟶ Y)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃! h : quotient A G ⟶ Y, projection A G ≫ h = f :=
  ⟨desc f hf, projection_desc f hf, fun _ hh ↦ hom_ext (hh.trans (projection_desc f hf).symm)⟩

/-- Descending the pullback of an affine-target morphism recovers that morphism. -/
@[simp]
theorem desc_projection {Y : Scheme.{u}} [IsAffine Y] (f : quotient A G ⟶ Y) :
    desc (projection A G ≫ f) (fun g => by simp) = f :=
  hom_ext (projection_desc _ _)

end Monoid

section Group

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A]

/-- Every contravariant spectrum map of a group element is an isomorphism. -/
instance (g : G) : IsIso (specComap A G g) := by
  rw [specComap_def]
  exact isIso_SpecMap_iff.mpr (MulSemiringAction.toRingEquiv G A g).bijective

/-- The contravariant spectrum map of `g` is the standard spectrum action by `g⁻¹`. -/
@[simp]
theorem specComap_base_apply (g : G) (x : PrimeSpectrum A) :
    (specComap A G g).base x = g⁻¹ • x := by
  rw [specComap_def]
  refine (Spec.map_apply (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) x).trans ?_
  apply PrimeSpectrum.ext
  ext a
  simp [Ideal.mem_inv_pointwise_smul_iff]

/-- A group acting on `A` acts on `Spec A` by automorphisms: `g` acts by the spectrum map of
`g⁻¹`, so that it sends a prime ideal `𝔭` to `g • 𝔭` (`specAction_apply`). -/
noncomputable def specAction : G →* Aut (Spec (CommRingCat.of A)) where
  toFun g := .of (asIso (specComap A G g⁻¹))
  map_one' := by ext1; ext1; simp
  map_mul' g h := by ext1; ext1; simp

@[simp]
theorem specAction_asIso_hom (g : G) : (specAction A G g).asIso.hom = specComap A G g⁻¹ :=
  (rfl)

/-- The automorphism `specAction A G g` sends a prime ideal `𝔭` to `g • 𝔭`. -/
theorem specAction_apply (g : G) (x : PrimeSpectrum A) :
    (specAction A G g).asIso.hom x = g • x := by
  rw [specAction_asIso_hom, specComap_base_apply, inv_inv]

end Group

end TauCeti.AffineInvariantQuotient


/-!
# Affine invariant quotients by finite groups

For a finite group acting on a commutative ring `A`, the invariant-spectrum projection is
integral and surjective, and its topological fibres are precisely the orbits of prime ideals.
Likewise, two points of `Spec A` with values in a domain which have the same image in the quotient
differ by an element of the group.
If `A` is of finite type over its fixed subring, the projection is finite; in particular,
this holds when `A` is of finite type over an invariant base semiring `R`.
These results supplement the affine-target universal property in
`TauCeti.AlgebraicGeometry.Quotient.Affine`.

Neither flatness nor finite presentation of the quotient projection is asserted.

## Main results

* The projection is integral and surjective for finite groups.
* `isFinite_projection`: the projection is finite when `A` is of finite type over its
  fixed subring.
* `isFinite_projection_of_finiteType`: finiteness over an invariant base semiring suffices.
* `isQuotientMap_projection`: the projection is a topological quotient map.
* `projection_eq_iff_exists_smul`: its fibres are prime-ideal orbits.
* `exists_comp_specComap_eq`: points with values in a domain and the same image in the quotient
  differ by the action of a group element.

## References

* Formal sources: Mathlib's `Algebra.IsInvariant.isIntegral` and
  `Algebra.IsInvariant.exists_smul_of_under_eq`, and Tau Ceti's
  `TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq`.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace TauCeti.AffineInvariantQuotient

universe u v w

section Group

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- The invariant-spectrum projection is integral for a finite group action. -/
instance : IsIntegralHom (projection A G) := by
  rw [projection_def]
  exact IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (Algebra.IsInvariant.isIntegral _ _ G))

/-- The quotient projection is surjective for a finite group action. -/
instance : Surjective (projection A G) := by
  rw [projection_def]
  let := Algebra.IsInvariant.isIntegral (FixedPoints.subring A G) A G
  exact ⟨Algebra.IsIntegral.comap_surjective _ _⟩

/-- The quotient projection is finite when `A` is of finite type over its fixed subring. -/
theorem isFinite_projection [Algebra.FiniteType (FixedPoints.subring A G) A] :
    IsFinite (projection A G) := by
  rw [projection_def]
  let := Algebra.IsInvariant.isIntegral (FixedPoints.subring A G) A G
  exact IsFinite.SpecMap_iff _ |>.mpr (RingHom.finite_algebraMap.mpr Algebra.IsIntegral.finite)

/-- The quotient projection is finite when `A` is of finite type over an invariant base `R`. -/
theorem isFinite_projection_of_finiteType (R : Type w) [CommSemiring R] [Algebra R A]
    [SMulCommClass G R A] [Algebra.FiniteType R A] : IsFinite (projection A G) := by
  let : Algebra.FiniteType (FixedPoints.subring A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R A G) A
  exact isFinite_projection A G

/-- The projection is a quotient map of topological spaces. -/
theorem isQuotientMap_projection : Topology.IsQuotientMap (projection A G) :=
  (projection A G).isClosedMap.isQuotientMap
    (projection A G).continuous (Surjective.surj (f := projection A G))

/-- Two points have the same image exactly when they are in the same spectrum orbit. -/
theorem projection_eq_iff_exists_smul (x y : PrimeSpectrum A) :
    projection A G x = projection A G y ↔
      ∃ g : G, y = g • x := by
  simp only [projection_base_apply]
  -- Rewrite matching cannot reduce the carrier of `quotient` to `PrimeSpectrum`.
  -- Only the carrier changes here; `projection_base_apply` already identifies the point map.
  change PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) x =
    PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) y ↔ _
  rw [PrimeSpectrum.ext_iff]
  simp only [PrimeSpectrum.comap_asIdeal, ← Ideal.under_def]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
      (FixedPoints.subring A G) A G x.asIdeal y.asIdeal h
    exact ⟨g, PrimeSpectrum.ext hg⟩
  · rintro ⟨g, hg⟩
    simpa only [hg, PrimeSpectrum.asIdeal_smul] using
      (Ideal.under_smul (FixedPoints.subring A G) x.asIdeal g).symm

/-- **Points of the affine invariant quotient are orbits.** Two morphisms from the spectrum of a
domain to `Spec A` with the same image in the quotient differ by the action of an element of
`G`. -/
theorem exists_comp_specComap_eq {K : Type u} [CommRing K] [IsDomain K]
    {x₁ x₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A)}
    (h : x₁ ≫ projection A G = x₂ ≫ projection A G) :
    ∃ g : G, x₁ ≫ specComap A G g = x₂ := by
  -- Pass to the ring maps `A ⟶ K`, which agree on the fixed subring.
  have hφ : (CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A) ≫
      Spec.preimage x₁) = CommRingCat.ofHom (algebraMap (FixedPoints.subring A G) A) ≫
        Spec.preimage x₂ :=
    Spec.map_injective (by simpa [Spec.map_comp, projection_def] using h)
  obtain ⟨g, hg⟩ := TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq
    (FixedPoints.subring A G) G (Spec.preimage x₁).hom (Spec.preimage x₂).hom
    congr(($hφ).hom)
  refine ⟨g, ?_⟩
  rw [← Spec.map_preimage x₁, ← Spec.map_preimage x₂, specComap_def, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext hg)

end Group

end TauCeti.AffineInvariantQuotient


/-!
# The universal property of the affine invariant quotient by a finite group

Let a finite group `G` act on a commutative ring `A`. This file shows that the invariant-spectrum
projection `π : Spec A ⟶ Spec Aᴳ` is a categorical quotient in the category of all schemes: every
morphism `f : Spec A ⟶ X` to an arbitrary scheme `X` which is invariant under the action of `G`
factors uniquely through `π`. The case of an affine `X`, where only a monoid action is needed, is
`TauCeti.AffineInvariantQuotient.existsUnique_desc`.

Uniqueness holds because `π` is an epimorphism of schemes: it is surjective, and its stalk maps
`(Aᴳ)_P → A_Q` are injective (`TauCeti.FixedPoints.localRingHom_injective`).

For existence, `f` is constant on the fibres of `π`, which are the `G`-orbits, so it descends to a
continuous map `b : Spec Aᴳ → X` because `π` is a topological quotient map. Cover `Spec Aᴳ` by basic
opens `D(r)` with `r` invariant and `b(D(r))` inside an affine open `V` of `X`. Over `D(r)`, the
projection is the affine invariant quotient of the localization `A[1/r]`: invariants commute with
this localization (`TauCeti.FixedPoints.isLocalization`), so the square formed by
`Spec A[1/r] ⟶ Spec A`, the two projections and `Spec A[1/r]ᴳ ⟶ Spec Aᴳ` is a pullback square
(`TauCeti.AffineInvariantQuotient.isPullback_away`). The restriction of `f` to `Spec A[1/r]` lands
in `V`, so it descends by the affine universal property. The local descents agree on overlaps
because `π` remains an epimorphism over every open subscheme of `Spec Aᴳ`, and they glue
(`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_openCover`).

The construction follows the proof of Mathlib's
`AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine`, where flat descent plays the
role of the affine invariant quotient.

## Main definitions

* `TauCeti.AffineInvariantQuotient.descOfFinite`: the morphism `Spec Aᴳ ⟶ X` induced by an
  invariant morphism `Spec A ⟶ X`.

## Main results

* `TauCeti.AffineInvariantQuotient.stalkMap_projection_injective`: the stalk maps of the projection
  are injective.
* `TauCeti.AffineInvariantQuotient.instEpiProjection`: the projection is an epimorphism of schemes.
* `TauCeti.AffineInvariantQuotient.isPullback_away`: over the basic open `D(r)`, the projection is
  the projection of `A[1/r]`.
* `TauCeti.AffineInvariantQuotient.hom_ext_of_finite`: morphisms out of the quotient to an
  arbitrary scheme are determined by their composition with the projection.
* `TauCeti.AffineInvariantQuotient.existsUnique_desc_of_finite`: the universal property for
  arbitrary target schemes.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
* D. Mumford, *Abelian Varieties*, §7, Theorem 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AffineInvariantQuotient

universe u v

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- The stalk maps `(Aᴳ)_P → A_Q` of the invariant-spectrum projection are injective for a finite
group action. -/
theorem stalkMap_projection_injective (x : Spec (CommRingCat.of A)) :
    Function.Injective ((projection A G).stalkMap x) := by
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  have : Mono (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap (algebraMap (FixedPoints.subring A G) A) x).asIdeal x.asIdeal
      (algebraMap (FixedPoints.subring A G) A) rfl)) :=
    ConcreteCategory.mono_of_injective _ (FixedPoints.localRingHom_injective _ _ rfl)
  rw [projection_def]
  have hmono : Mono ((Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subring A G) A))).stalkMap x) :=
    ((MorphismProperty.monomorphisms CommRingCat).arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom
        (algebraMap (FixedPoints.subring A G) A)) x)).mpr this
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- The invariant-spectrum projection of a finite group action is an epimorphism of schemes. -/
instance instEpiProjection : Epi (projection A G) :=
  Scheme.Hom.epi_of_surjective_of_stalkMap_injective _ (stalkMap_projection_injective A G)

variable {A} in
/-- Over the basic open `D(r)` of an invariant `r`, the invariant-spectrum projection is the
projection of the localization `A[1/r]`: the square formed by the two projections and the maps
induced by `A → A[1/r]` and `Aᴳ → A[1/r]ᴳ` is a pullback square. -/
theorem isPullback_away (r : FixedPoints.subring A G) :
    IsPullback (Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))))
      (projection (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G) (projection A G)
      (Spec.algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) := by
  have : IsLocalization ((Submonoid.powers r).map (algebraMap (FixedPoints.subring A G) A))
      (Localization (Algebra.algebraMapSubmonoid A (.powers r))) :=
    Localization.isLocalization
  rw [projection_def, projection_def]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ <| CommRingCat.isPushout_of_isLocalization
    (algebraMap (FixedPoints.subring A G) A)
    (algebraMap (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)
      (Localization (Algebra.algebraMapSubmonoid A (.powers r))))
    rfl (Submonoid.powers r)

variable {A} in
/-- The map `Spec A[1/r]ᴳ ⟶ Spec Aᴳ` is an open immersion. -/
instance isOpenImmersion_away (r : FixedPoints.subring A G) :
    IsOpenImmersion (Spec.algebraMap (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) :=
  IsOpenImmersion.of_isLocalization r

variable {A} in
/-- The image of `Spec A[1/r]ᴳ ⟶ Spec Aᴳ` is the basic open `D(r)`. -/
theorem range_specAlgebraMap_away (r : FixedPoints.subring A G) :
    Set.range (Spec.algebraMap (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (FixedPoints.subring A G))) :=
  PrimeSpectrum.localization_away_comap_range _ r

omit [Finite G] in
variable {A G} in
/-- The map `Spec A[1/r] ⟶ Spec A` is equivariant. -/
@[reassoc]
theorem specComap_comp_specAlgebraMap_away (r : FixedPoints.subring A G) (g : G) :
    specComap (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G g ≫
        Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))) =
      Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))) ≫
        specComap A G g := by
  rw [specComap_def, specComap_def, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact FixedPoints.smul_algebraMap_localization _ g a

variable {A G}

/-- An invariant morphism is constant on the fibres of the projection, so it descends to a
continuous map on the invariant quotient. -/
private theorem exists_continuousMap_comp_projection {X : Scheme.{u}}
    (f : Spec (CommRingCat.of A) ⟶ X) (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃ b : C(quotient A G, X), ∀ x, b (projection A G x) = f x := by
  have hfac : Function.FactorsThrough f.base.hom (projection A G) := fun x y hxy ↦ by
    obtain ⟨g, rfl⟩ := (projection_eq_iff_exists_smul A G x y).mp hxy
    have h := congrArg (fun k : Spec (CommRingCat.of A) ⟶ X ↦ k x) (hf g⁻¹)
    have h2 := specComap_base_apply A G g⁻¹ x
    rw [inv_inv] at h2
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm.trans (congrArg _ h2)
  refine ⟨(isQuotientMap_projection A G).lift _ hfac, fun x ↦ ?_⟩
  exact DFunLike.congr_fun ((isQuotientMap_projection A G).lift_comp _ hfac) x

/-- The local descent of an invariant morphism: over a basic open `D(r)` which the induced
continuous map sends into an affine open `V`, the base change of `f` descends. -/
private theorem exists_desc_away {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) (b : C(quotient A G, X))
    (hb : ∀ x, b (projection A G x) = f x) (r : FixedPoints.subring A G) (V : X.affineOpens)
    (hrV : ∀ y ∈ PrimeSpectrum.basicOpen r, b y ∈ (V : Set X)) :
    ∃ u : quotient (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G ⟶ X,
      pullback.fst (projection A G) (Spec.algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G)) ≫ f =
        pullback.snd _ _ ≫ u := by
  have hpb := isPullback_away G r
  have hV : Set.range
      (Spec.algebraMap A (Localization (Algebra.algebraMapSubmonoid A (.powers r))) ≫ f) ⊆
      Set.range V.1.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, hpb.w,
      Scheme.Hom.comp_apply]
    exact hrV _ ((range_specAlgebraMap_away G r).le ⟨_, rfl⟩)
  let f' := IsOpenImmersion.lift V.1.ι _ hV
  have hf' (g : G) :
      specComap (Localization (Algebra.algebraMapSubmonoid A (.powers r))) G g ≫ f' = f' := by
    rw [← cancel_mono V.1.ι]
    simp [f', specComap_comp_specAlgebraMap_away_assoc, hf]
  refine ⟨desc f' hf' ≫ V.1.ι, ?_⟩
  rw [← cancel_epi hpb.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc, projection_desc_assoc, IsOpenImmersion.lift_fac]

/-- The universal property for arbitrary target schemes, as an existence statement. -/
private theorem exists_projection_comp_eq {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃ h : quotient A G ⟶ X, projection A G ≫ h = f := by
  obtain ⟨b, hb⟩ := exists_continuousMap_comp_projection f hf
  -- Basic opens `D(r)` sent by `b` into affine opens of `X` cover the quotient.
  let I := {p : FixedPoints.subring A G × X.affineOpens //
    ∀ y ∈ PrimeSpectrum.basicOpen p.1, b y ∈ (p.2 : Set X)}
  have hcov (y : quotient A G) : ∃ i : I, y ∈ PrimeSpectrum.basicOpen i.1.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (b y)) isOpen_univ
    obtain ⟨_, ⟨r, rfl⟩, hyr, hrV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_preimage.mpr hbV) ((V : X.Opens).isOpen.preimage b.continuous)
    exact ⟨⟨(r, ⟨V, hV⟩), fun z hz ↦ hrV hz⟩, hyr⟩
  let 𝒰 : (quotient A G).OpenCover :=
    { I₀ := I
      X i := quotient (Localization (Algebra.algebraMapSubmonoid A (.powers i.1.1))) G
      f i := Spec.algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A (.powers i.1.1))) G)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun y ↦ ?_, inferInstance⟩
        obtain ⟨i, hi⟩ := hcov y
        obtain ⟨z, hz⟩ := (range_specAlgebraMap_away G i.1.1).ge hi
        exact ⟨i, z, hz⟩ }
  choose u hu using fun i : I ↦ exists_desc_away f hf b hb i.1.1 i.1.2 i.2
  -- The local descents glue, since the projection stays an epimorphism over open subschemes.
  exact Scheme.Hom.exists_comp_eq_of_openCover (projection A G)
    (fun _ g _ ↦ Scheme.Hom.epi_pullback_snd_of_isOpenImmersion _ g
      (stalkMap_projection_injective A G)) 𝒰 f u hu

/-- The morphism `Spec Aᴳ ⟶ X` induced by a `G`-invariant morphism `Spec A ⟶ X` to an arbitrary
scheme, for a finite group `G`. -/
noncomputable def descOfFinite {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) : quotient A G ⟶ X :=
  (exists_projection_comp_eq f hf).choose

/-- Morphisms from the invariant quotient by a finite group to an arbitrary scheme are determined by
their composition with the projection. -/
@[ext]
theorem hom_ext_of_finite {X : Scheme.{u}} {f h : quotient A G ⟶ X}
    (e : projection A G ≫ f = projection A G ≫ h) : f = h :=
  (cancel_epi (projection A G)).mp e

/-- The induced morphism factors the given invariant morphism. -/
@[reassoc (attr := simp)]
theorem projection_descOfFinite {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    projection A G ≫ descOfFinite f hf = f :=
  (exists_projection_comp_eq f hf).choose_spec

/-- **The universal property of the affine invariant quotient by a finite group.** Every
`G`-invariant morphism from `Spec A` to an arbitrary scheme factors uniquely through the
projection `Spec A ⟶ Spec Aᴳ`. -/
theorem existsUnique_desc_of_finite {X : Scheme.{u}} (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    ∃! h : quotient A G ⟶ X, projection A G ≫ h = f :=
  ⟨descOfFinite f hf, projection_descOfFinite f hf, fun _ hh ↦
    hom_ext_of_finite (hh.trans (projection_descOfFinite f hf).symm)⟩

/-- Descending the composite of the projection with a morphism to an arbitrary scheme recovers
that morphism. -/
@[simp]
theorem descOfFinite_projection {X : Scheme.{u}} (f : quotient A G ⟶ X) :
    descOfFinite (projection A G ≫ f) (fun g ↦ by simp) = f :=
  hom_ext_of_finite (projection_descOfFinite _ _)

/-- For an affine target, `descOfFinite` is the affine descent `desc`. -/
theorem descOfFinite_eq_desc {X : Scheme.{u}} [IsAffine X] (f : Spec (CommRingCat.of A) ⟶ X)
    (hf : ∀ g : G, specComap A G g ≫ f = f) :
    descOfFinite f hf = desc f hf :=
  hom_ext_of_finite (by simp)

end TauCeti.AffineInvariantQuotient
