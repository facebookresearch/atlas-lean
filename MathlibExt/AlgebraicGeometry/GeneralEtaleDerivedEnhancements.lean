/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The integer-linearity compatibility proofs are adapted from
Mathlib/CategoryTheory/Linear/Basic.lean:
Copyright (c) 2021 Kim Morrison. All rights reserved.
Licensed under the Apache License, Version 2.0.
Authors: Kim Morrison.
Modification: restrict the same native integer action through the
ULift ring equivalence so the scalar and Hom universes match.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralEtaleCoefficientModels
public import MathlibExt.CategoryTheory.DGSource.DGCochainCategory
public import MathlibExt.CategoryTheory.NativeDGNerveModels
public import Mathlib.Algebra.Module.RingHom

/-!
# Full DG and K-injective étale derived category models

The scalar lift only changes the universe of the central integer action.
All objects are actual complexes of left-Λ étale module sheaves. Their
full native linear Hom complex has every shifted cochain, the native
differential and the actual Koszul composition from the completed source
port. In particular it is not a nerve of degree-zero cohomology.

The derived model is the native coherent nerve of the full K-injective
subcategory. Bounded constructible and fixed amplitude categories are
full enhanced subcategories of that same model. No field, commutativity,
finite-type or Noetherian assumption on Λ or the scheme is imposed here.
Localization, coherent pullbacks and arc hyperdescent are separate requests.

Source: Bhatt--Mathew arXiv:1807.04725v4, Notation 5.8 and Theorem 5.13;
Keller, Deriving DG categories; Lurie, Higher Algebra, Section 1.3.1.
The imported full Hom, Dold--Kan and coherent nerve ports retain their
original Tau Ceti Apache 2.0 attribution and pinned revision.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open CochainComplex.HomComplex
open scoped Simplicial

/-- The central integer scalar in the universe of the actual sheaf Homs. -/
abbrev LargeInt := ULift.{1} ℤ

variable (Λ : Type) [Ring Λ]

/-- The actual integer action on every sheaf Hom, lifted through the
native ring equivalence. It does not require commutativity of Λ. -/
@[instance_reducible]
def coefficientLinear (X : Scheme.{0}) : Linear LargeInt (CoefficientSheaves Λ X) where
  homModule F H := Module.compHom (F ⟶ H) ULift.ringEquiv.toRingHom
  smul_comp F _H _J r a b := by
    change (r.down • a) ≫ b = r.down • (a ≫ b)
    exact (Preadditive.rightComp F b).map_zsmul r.down a
  comp_smul _F _H J a r b := by
    change a ≫ (r.down • b) = r.down • (a ≫ b)
    exact (Preadditive.leftComp J a).map_zsmul r.down b

/-- Completed native full cochain DG enrichment for these actual sheaves. -/
@[instance_reducible]
def coefficientDG (X : Scheme.{0}) : DGCategory LargeInt (CoefficientComplexes Λ X) := by
  letI := coefficientLinear Λ X
  infer_instance

/-- Every degree of Hom is the actual native shifted sheaf cochain group. -/
theorem full_hom_degree (X : Scheme.{0}) (F H : CoefficientComplexes Λ X) (n : ℤ) :
    letI := coefficientLinear Λ X
    letI := coefficientDG Λ X
    (dgHomComplex LargeInt F H).X n = ModuleCat.of LargeInt (Cochain F H n) := rfl

/-- The native coherent nerve on all actual coefficient complexes. -/
def rawNerve (X : Scheme.{0}) : SSet.{2} := by
  letI := coefficientDG Λ X
  exact dgNerve (k := LargeInt) (CoefficientComplexes Λ X)

/-- The full native coherent nerve is a genuine quasicategory. -/
theorem rawNerve_quasicategory (X : Scheme.{0}) : SSet.Quasicategory (rawNerve Λ X) := by
  exact @dgNerve_quasicategory LargeInt _ (CoefficientComplexes Λ X) (coefficientDG Λ X)

variable [∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)]

/-- The actual full K-injective category retains the same full Hom complexes. -/
abbrev KInjectives (X : Scheme.{0}) :=
  letI := coefficientDG Λ X
  DGFullSubcategory (IsKInjective (Λ := Λ) (X := X))

/-- The native coherent nerve of actual K-injective sheaf complexes. -/
def derivedNerve (X : Scheme.{0}) : SSet.{2} := by
  letI := coefficientDG Λ X
  exact dgNerve (k := LargeInt) (KInjectives Λ X)

variable (S : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), EtalePullbackSource Λ f)

/-- Full bounded constructible derived category, with every actual homogeneous Hom. -/
def constructibleNerve (X : QcqsScheme) : SSet.{2} := by
  letI := coefficientDG Λ X.scheme
  exact dgNerve (k := LargeInt) (DGFullSubcategory
    (fun K : CoefficientComplexes Λ X.scheme =>
      IsKInjective (Λ := Λ) K ∧ IsBoundedConstructible Λ S X K))

/-- The full fixed cohomological-amplitude subcategory from Notation 5.8. -/
def amplitudeNerve (X : QcqsScheme) (a b : ℤ) : SSet.{2} := by
  letI := coefficientDG Λ X.scheme
  exact dgNerve (k := LargeInt) (DGFullSubcategory
    (fun K : CoefficientComplexes Λ X.scheme =>
      IsKInjective (Λ := Λ) K ∧ IsBoundedConstructible Λ S X K ∧
        InAmplitude Λ K a b))

/-- A fixed-amplitude value is still the full coherent nerve, not its core. -/
theorem amplitudeNerve_quasicategory (X : QcqsScheme) (a b : ℤ) :
    SSet.Quasicategory (amplitudeNerve Λ S X a b) := by
  let _ := coefficientDG Λ X.scheme
  exact dgNerve_quasicategory LargeInt (DGFullSubcategory
    (fun K : CoefficientComplexes Λ X.scheme =>
      IsKInjective (Λ := Λ) K ∧ IsBoundedConstructible Λ S X K ∧
        InAmplitude Λ K a b))

end MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements
