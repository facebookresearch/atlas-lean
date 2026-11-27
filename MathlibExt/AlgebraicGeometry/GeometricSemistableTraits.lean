/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SemistableModels
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Actual geometric traits for semistable nearby cycles

The normalization ring is the actual integral closure of R in the chosen
algebraic closure L of its fraction field K. The geometric closed point is
an actual maximal ideal P, and its residue field is the actual quotient.
The henselian/localization/residue facts are explicit characterized
normalization data, supplied by the existing local-field toolbox.

All generic/special/normalized models and arrows are native scheme
pullbacks and prescribed ring maps. Decomposition and inertia are the
actual stabilizer and ideal inertia groups. No alternative cohomology,
normalization scheme or field action is selected.

Reference: SGA 7 I, section 2; Illusie, Astérisque 223, Exposé I, section
3.1. Axiom's strict-local fibre/maps and TauCeti's local-field normalization
and inertia producers are source-covered dependencies, not new requests.
https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.GeometricSemistableTraits

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open scoped Pointwise

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- The actual normalization ring, rather than an arbitrary trait model. -/
abbrev normalRing := integralClosure R L

/-- The actual Galois group of the chosen closure. -/
abbrev Galois := L ≃ₐ[K] L

instance galoisScalarComm : SMulCommClass (Galois K L) R L where
  smul_comm σ r x := by
    simp only [AlgEquiv.smul_def, Algebra.smul_def, map_mul]
    have h : σ (algebraMap R L r) = algebraMap R L r := by
      rw [IsScalarTower.algebraMap_apply R K L, σ.commutes]
    rw [h]

/-- Characterized facts about the actual geometric normalization. -/
structure GeometricTrait (π : R) [IsAlgClosure K L] where
  point : Ideal (normalRing R L)
  [maximal : point.IsMaximal]
  [normalHenselian : HenselianLocalRing (normalRing R L)]
  point_eq_maximal : point = IsLocalRing.maximalIdeal (normalRing R L)
  liesOver : point.comap (algebraMap R (normalRing R L)) =
    IsLocalRing.maximalIdeal R
  residueAlgClosed :
    letI := Ideal.Quotient.field point
    IsAlgClosed (normalRing R L ⧸ point)
  [genericLocalization : IsLocalization.Away
    (algebraMap R (normalRing R L) π) L]

attribute [instance] GeometricTrait.maximal

variable {R K L} (π : R) [IsAlgClosure K L]
  (T : GeometricTrait R K L π)

/-- The actual algebraically closed residue field at the chosen point. -/
abbrev Residue := normalRing R L ⧸ T.point

instance residueField : Field (Residue π T) := Ideal.Quotient.field T.point

instance residueAlgClosed : IsAlgClosed (Residue π T) := T.residueAlgClosed

/-- The actual residue-field inclusion R/m -> A/P, forced by the point's
lying-over equation. -/
def residueScalars : IsLocalRing.ResidueField R →+* Residue π T :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal R)
    ((Ideal.Quotient.mk T.point).comp (algebraMap R (normalRing R L)))
    (fun r hr ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (by
      change r ∈ T.point.comap (algebraMap R (normalRing R L))
      rw [T.liesOver]
      exact hr))

instance residueAlgebra : Algebra (IsLocalRing.ResidueField R) (Residue π T) :=
  (residueScalars π T).toAlgebra

/-- The actual geometric residue-field map. -/
def residueBaseMap : Spec (.of (Residue π T)) ⟶
    Spec (.of (IsLocalRing.ResidueField R)) :=
  Spec.map (CommRingCat.ofHom (residueScalars π T))

/-- The actual decomposition subgroup at the chosen geometric point. -/
abbrev Decomposition := MulAction.stabilizer (Galois K L) T.point

/-- Actual inertia inside the decomposition subgroup. -/
abbrev Inertia := T.point.inertia (Decomposition π T)

/-- The action on the normalization is the native integral-closure action. -/
def normalAction (σ : Galois K L) : normalRing R L ≃ₐ[R] normalRing R L :=
  MulSemiringAction.toAlgEquiv R (normalRing R L) σ

/-- The prescribed action on the actual quotient residue field. -/
def residueAction : Decomposition π T →* (Residue π T ≃+* Residue π T) where
  toFun σ := (Ideal.Quotient.stabilizerHom T.point
    (T.point.under R) (Galois K L) σ).toRingEquiv
  map_one' := congrArg AlgEquiv.toRingEquiv
    (map_one (Ideal.Quotient.stabilizerHom T.point
      (T.point.under R) (Galois K L)))
  map_mul' σ τ := congrArg AlgEquiv.toRingEquiv
    (map_mul (Ideal.Quotient.stabilizerHom T.point
      (T.point.under R) (Galois K L)) σ τ)

/-- The actual generic geometric point of the normalization. -/
def genericIntoNormal : Spec (.of L) ⟶ Spec (.of (normalRing R L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (normalRing R L) L))

/-- The actual closed geometric point, from the quotient map. -/
def specialIntoNormal : Spec (.of (Residue π T)) ⟶
    Spec (.of (normalRing R L)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk T.point))

instance specialIntoNormal_closed : IsClosedImmersion (specialIntoNormal π T) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk T.point)) Ideal.Quotient.mk_surjective

/-- The actual normalization map to Spec R. -/
def normalizationMap : Spec (.of (normalRing R L)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (normalRing R L)))

/-- The actual field inclusion R -> L. -/
def genericBaseMap : Spec (.of L) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R L))

/-- The prescribed special field map R -> A/P. -/
def specialBaseMap : Spec (.of (Residue π T)) ⟶ Spec (.of R) :=
  specialIntoNormal π T ≫ normalizationMap (R := R) (L := L)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem generic_normalization :
    genericIntoNormal (R := R) (L := L) ≫
      normalizationMap (R := R) (L := L) =
        genericBaseMap (R := R) (L := L) := by
  rw [genericIntoNormal, normalizationMap, genericBaseMap, ← Spec.map_comp]
  congr 1

variable (X : Over (Spec (.of R)))

/-- The actual scalar automorphism on a native scheme fibre product. -/
def scalarOperator (S : Type) [CommRing S] [Algebra R S]
    (σ : S ≃ₐ[R] S) :
    pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (by
      rw [Category.assoc, ← Spec.map_comp]
      have h : CommRingCat.ofHom (algebraMap R S) ≫
          CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom (algebraMap R S)
            := by
        ext r
        exact σ.commutes r
      rw [h]
      exact pullback.condition)

/-- The actual normalized total space. -/
abbrev NormalizedModel := pullback X.hom (normalizationMap (R := R) (L := L))

/-- The actual Galois automorphism of the normalized total space. -/
def normalGalois (σ : Galois K L) : NormalizedModel (L := L) X ⟶
    NormalizedModel (L := L) X :=
  scalarOperator X (normalRing R L) (normalAction (R := R) σ)

/-- The actual geometric generic fibre. -/
abbrev GenericFibre := pullback X.hom (genericBaseMap (R := R) (L := L))

/-- The actual geometric special fibre. -/
abbrev SpecialFibre := pullback X.hom (specialBaseMap π T)

/-- The prescribed geometric generic-fibre arrow into the normalized model. -/
def genericArrow : GenericFibre (L := L) X ⟶ NormalizedModel (L := L) X :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ genericIntoNormal (R := R) (L := L))
    (by rw [Category.assoc, generic_normalization]; exact pullback.condition)

/-- The prescribed geometric special-fibre arrow into the normalized model. -/
def specialArrow : SpecialFibre π T X ⟶ NormalizedModel (L := L) X :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ specialIntoNormal π T) pullback.condition

/-- Galois acts through the actual field automorphism on the fibre product. -/
def genericGalois (σ : Galois K L) : GenericFibre (L := L) X ⟶
    GenericFibre (L := L) X :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (by
      dsimp only [genericBaseMap]
      rw [Category.assoc, ← Spec.map_comp]
      have h : CommRingCat.ofHom (algebraMap R L) ≫
          CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom (algebraMap R L)
            := by
        ext r
        change σ (algebraMap R L r) = algebraMap R L r
        rw [IsScalarTower.algebraMap_apply R K L, σ.commutes]
      rw [h]
      exact pullback.condition)

/-- The Galois actions on the generic fibre and on the normalized model are compatible with the
generic arrow, and inertia acts trivially on the special fibre. These always hold
(`inertiaSchemeCompatibility`). -/
class InertiaSchemeCompatibility : Prop where
  genericSquare : ∀ σ : Inertia π T,
    genericGalois (K := K) X σ.1.1 ≫ genericArrow X =
      genericArrow X ≫ normalGalois (K := K) X σ.1.1
  specialSquare : ∀ σ : Inertia π T,
    specialArrow π T X ≫ normalGalois (K := K) X σ.1.1 = specialArrow π T X

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsAlgClosure K L] in
@[reassoc (attr := simp)]
theorem normalGalois_fst (σ : Galois K L) :
    normalGalois (K := K) X σ ≫ pullback.fst X.hom (normalizationMap (R := R) (L := L)) =
      pullback.fst X.hom (normalizationMap (R := R) (L := L)) :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsAlgClosure K L] in
@[reassoc (attr := simp)]
theorem normalGalois_snd (σ : Galois K L) :
    normalGalois (K := K) X σ ≫ pullback.snd X.hom (normalizationMap (R := R) (L := L)) =
      pullback.snd X.hom (normalizationMap (R := R) (L := L)) ≫
        Spec.map (CommRingCat.ofHom (normalAction (R := R) σ).toRingHom) :=
  pullback.lift_snd _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
theorem genericArrow_fst :
    genericArrow (L := L) X ≫ pullback.fst X.hom (normalizationMap (R := R) (L := L)) =
      pullback.fst _ _ :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
theorem genericArrow_snd :
    genericArrow (L := L) X ≫ pullback.snd X.hom (normalizationMap (R := R) (L := L)) =
      pullback.snd _ _ ≫ genericIntoNormal (R := R) (L := L) :=
  pullback.lift_snd _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsAlgClosure K L] in
@[reassoc (attr := simp)]
theorem genericGalois_fst (σ : Galois K L) :
    genericGalois (K := K) X σ ≫ pullback.fst X.hom (genericBaseMap (R := R) (L := L)) =
      pullback.fst _ _ :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsAlgClosure K L] in
@[reassoc (attr := simp)]
theorem genericGalois_snd (σ : Galois K L) :
    genericGalois (K := K) X σ ≫ pullback.snd X.hom (genericBaseMap (R := R) (L := L)) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  pullback.lift_snd _ _ _

omit [Algebra R K] [IsFractionRing R K] [IsScalarTower R K L] in
@[reassoc (attr := simp)]
theorem specialArrow_fst :
    specialArrow π T X ≫ pullback.fst X.hom (normalizationMap (R := R) (L := L)) =
      pullback.fst _ _ :=
  pullback.lift_fst _ _ _

omit [Algebra R K] [IsFractionRing R K] [IsScalarTower R K L] in
@[reassoc (attr := simp)]
theorem specialArrow_snd :
    specialArrow π T X ≫ pullback.snd X.hom (normalizationMap (R := R) (L := L)) =
      pullback.snd _ _ ≫ specialIntoNormal π T :=
  pullback.lift_snd _ _ _

instance inertiaSchemeCompatibility : InertiaSchemeCompatibility π T X where
  genericSquare σ := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, genericArrow_snd, genericGalois_snd_assoc, normalGalois_snd,
        genericArrow_snd_assoc, genericIntoNormal, ← Spec.map_comp]
      rfl
  specialSquare σ := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, normalGalois_snd, specialArrow_snd_assoc, specialArrow_snd,
        specialIntoNormal, ← Spec.map_comp]
      congr 2
      ext a
      exact Ideal.Quotient.eq.mpr (σ.2 a)

end MathlibExt.AlgebraicGeometry.GeometricSemistableTraits
