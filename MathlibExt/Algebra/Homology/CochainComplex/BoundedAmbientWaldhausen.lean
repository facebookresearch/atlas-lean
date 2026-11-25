/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAdmissiblePushout
public import MathlibExt.Algebra.Homology.CochainComplex.PushoutQuasiIso
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.Waldhausen.Gluing

/-!
# Waldhausen structure from ambient cohomology

On bounded cochain complexes in an exact category, cofibrations are
degreewise admissible monomorphisms. An additive exact functor to an abelian
category defines weak equivalences by quasi-isomorphisms of the mapped
complexes. Degreewise admissible pushouts give the pushout and gluing
axioms for these classes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.IsExact]

omit [F.IsExact] [ExactCategory E] [HasBinaryBiproducts E] [HasZeroObject E] in
/-- Weak equivalences are the inverse image of ambient quasi-isomorphisms. -/
def ambientWeakEquivalences : MorphismProperty (Bounded E) :=
  (HomologicalComplex.quasiIso A (.up ℤ)).inverseImage
    (ι E ⋙ F.mapHomologicalComplex (.up ℤ))

omit [F.IsExact] [ExactCategory E] [HasBinaryBiproducts E] [HasZeroObject E] in
/-- Ambient weak equivalences satisfy the two-out-of-three property. -/
theorem ambientWeakEquivalences_hasTwoOutOfThree :
    (ambientWeakEquivalences F).HasTwoOutOfThreeProperty := by
  dsimp only [ambientWeakEquivalences]
  infer_instance

/-- Maps from the zero bounded complex are degreewise admissible. -/
theorem degreewiseAdmissibleMonomorphisms_zero (X : Bounded E) (f : (0 : Bounded E) ⟶ X) :
    degreewiseAdmissibleMonomorphisms E f := by
  intro j
  have hZ : IsZero ((0 : Bounded E).obj.X j) :=
    (HomologicalComplex.eval E (.up ℤ) j).map_isZero
      ((ι E).map_isZero (isZero_zero (Bounded E)))
  let e := hZ.isoZero
  have h : IsAdmissibleMono (e.inv ≫ f.hom.f j) := IsAdmissibleMono.fromZero _
  have hcomp : IsAdmissibleMono (e.hom ≫ (e.inv ≫ f.hom.f j)) :=
    admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso e.hom) h
  simpa only [Iso.hom_inv_id_assoc] using hcomp

omit [F.IsExact] in
/-- Waldhausen structure with degreewise admissible cofibrations and ambient quasi-isomorphisms. -/
@[instance_reducible, no_expose]
def ambientWaldhausenCategory : WaldhausenCategory (Bounded E) where
  cofibrations := degreewiseAdmissibleMonomorphisms E
  weakEquivalences := ambientWeakEquivalences F
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := by
    dsimp only [ambientWeakEquivalences]
    infer_instance
  weakEquivalences_respectsIso := by
    dsimp only [ambientWeakEquivalences]
    infer_instance
  zero_isCofibration X f := degreewiseAdmissibleMonomorphisms_zero X f
  cofibration_pushout i hi C f := by
    let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
    obtain ⟨P, inB, inC, hP, _, _, hadm, _⟩ := exists_boundedAdmissiblePushout E i f hi
    exact ⟨P, inC, inB, hP.flip, hadm⟩

omit [F.IsExact] in
/-- Cofibrations are exactly the degreewise admissible monomorphisms. -/
theorem ambient_isCofibration_iff {X Y : Bounded E} (f : X ⟶ Y) :
    letI := ambientWaldhausenCategory F
    IsCofibration f ↔ ∀ j : ℤ, IsAdmissibleMono (f.hom.f j) := Iff.rfl

omit [F.IsExact] in
/-- Weak equivalences are exactly ambient quasi-isomorphisms. -/
theorem ambient_isWeakEquivalence_iff {X Y : Bounded E} (f : X ⟶ Y) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence f ↔ QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := Iff.rfl

omit [F.IsExact] in
/-- The Waldhausen weak equivalences satisfy the two-out-of-three property. -/
theorem ambientWaldhausen_hasTwoOutOfThree :
    letI := ambientWaldhausenCategory F
    (WaldhausenCategory.weakEquivalences (C := Bounded E)).HasTwoOutOfThreeProperty := by
  let _ := ambientWaldhausenCategory F
  exact ambientWeakEquivalences_hasTwoOutOfThree F

/-- A map of admissible pushout squares whose vertex maps are weak equivalences
induces a weak equivalence of the apices. -/
theorem ambientWaldhausen_gluing :
    letI := ambientWaldhausenCategory F
    WaldhausenGluingAxiom (C := Bounded E) := by
  let _ := ambientWaldhausenCategory F
  let J := F.mapHomologicalComplex (.up ℤ)
  constructor
  intro X B C P X' B' C' P' i f inB inC i' f' inB' inC'
    hP hP' x y z p hi hi' wi wf wB wC hx hy hz
  have hi₀ := (ambient_isCofibration_iff F i).1 hi
  have hi₀' := (ambient_isCofibration_iff F i').1 hi'
  have hiF := F.mapCochainComplexBounded_degreewiseAdmissibleMonomorphisms i hi₀
  have hiF' := F.mapCochainComplexBounded_degreewiseAdmissibleMonomorphisms i' hi₀'
  have hPF := F.mapCochainComplexBounded_isPushout_of_degreewiseAdmissibleMono hi₀ hP
  have hPF' := F.mapCochainComplexBounded_isPushout_of_degreewiseAdmissibleMono hi₀' hP'
  have hRaw := admissiblePushout_raw A hiF hPF
  have hRaw' := admissiblePushout_raw A hiF' hPF'
  let _ : Mono (F.mapCochainComplexBounded.map i).hom := HomologicalComplex.mono_of_mono_f _
    (fun j => IsAdmissibleMono.mono (hiF j))
  let _ : Mono (F.mapCochainComplexBounded.map i').hom := HomologicalComplex.mono_of_mono_f _
    (fun j => IsAdmissibleMono.mono (hiF' j))
  have wiF : J.map i.hom ≫ J.map y.hom = J.map x.hom ≫ J.map i'.hom := by
    have h := congrArg (fun t : X ⟶ B' => t.hom) wi
    change i.hom ≫ y.hom = x.hom ≫ i'.hom at h
    simpa only [J.map_comp] using congrArg J.map h
  have wfF : J.map f.hom ≫ J.map z.hom = J.map x.hom ≫ J.map f'.hom := by
    have h := congrArg (fun t : X ⟶ C' => t.hom) wf
    change f.hom ≫ z.hom = x.hom ≫ f'.hom at h
    simpa only [J.map_comp] using congrArg J.map h
  have wBF : J.map inB.hom ≫ J.map p.hom = J.map y.hom ≫ J.map inB'.hom := by
    have h := congrArg (fun t : B ⟶ P' => t.hom) wB
    change inB.hom ≫ p.hom = y.hom ≫ inB'.hom at h
    simpa only [J.map_comp] using congrArg J.map h
  have wCF : J.map inC.hom ≫ J.map p.hom = J.map z.hom ≫ J.map inC'.hom := by
    have h := congrArg (fun t : C ⟶ P' => t.hom) wC
    change inC.hom ≫ p.hom = z.hom ≫ inC'.hom at h
    simpa only [J.map_comp] using congrArg J.map h
  apply (ambient_isWeakEquivalence_iff F p).2
  exact CochainComplex.quasiIso_of_pushout hRaw hRaw'
    (J.map x.hom) (J.map y.hom) (J.map z.hom) (J.map p.hom)
    wiF wfF wBF wCF
    ((ambient_isWeakEquivalence_iff F x).1 hx)
    ((ambient_isWeakEquivalence_iff F y).1 hy)
    ((ambient_isWeakEquivalence_iff F z).1 hz)

end CochainComplex.Bounded

end
