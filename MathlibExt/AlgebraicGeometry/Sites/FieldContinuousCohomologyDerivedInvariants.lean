/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeComparison
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Precomposition
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.ZeroIsoNaturality
public import MathlibExt.FieldTheory.Galois.RestrictedCoefficientMaps
public import MathlibExt.AlgebraicGeometry.Sites.FieldDerivedSectionsInvariants
public import MathlibExt.AlgebraicGeometry.Sites.FieldInjectiveContinuousCochainAcyclicity
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-!
# Continuous field cohomology as derived invariants

Fix a field `k` with separable closure `Ω` and discrete Galois coefficients in universe `max u
w`. Continuous homogeneous cohomology and right-derived invariants are universal cohomological
delta functors. Their degree-zero invariant coordinates determine a normalized isomorphism in
every natural degree.

The comparison commutes with coefficient maps and connecting morphisms. Injective-resolution
coordinates respect every coaugmentation-compatible resolution map and every change of
resolution. A zero cocycle is evaluated at the group identity, and every degree-one class has
a preimage under an injective-presentation cokernel boundary.

Continuous homomorphisms of Galois groups, including groups in an independent field universe,
give restriction maps. The comparison respects simultaneous group and coefficient change. For
coefficients initially in different ranks, each is lifted once to the shared height `max u v
w`, retaining the intertwiner's element values. Lifted field sheaves give the corresponding
sheaf-natural comparison of derived sections and continuous cohomology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
universe u v w

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Continuous cohomology functor of field coefficients.

For a field with separable closure, take degree-`n` continuous homogeneous cohomology of a
discrete Galois coefficient, valued in additive groups of universe `max u w`. -/
abbrev fieldContinuousCohomologyFunctor (n : ℕ) :
    FieldCohomologyModule.{u, w} k Ω ⥤ AddCommGrpCat.{max u w} :=
  ContinuousCohomology.discreteCoefficientCohomologyFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) n

/-- Continuous field cohomology is additive in coefficients.

Each degree functor preserves sums of discrete Galois coefficient maps. -/
instance fieldContinuousCohomologyFunctor_additive (n : ℕ) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω n).Additive where
  map_add {M N} f g := by
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)
    let C := ContinuousCohomology.homogeneousCochainsFunctor.{0, u, w}
      (k := ℤ) (G := Gal(Ω/k))
    let H := HomologicalComplex.homologyFunctor (TopModuleCat.{max u w} ℤ)
      (ComplexShape.up ℕ) n
    let U := ContinuousCohomology.discreteCoefficientForget.{max u w}
    let : C.Additive := ContinuousCohomology.homogeneousCochainsFunctor_additive
    have hp : P.map (f + g) = P.map f + P.map g := by
      apply TopRep.hom_ext
      rfl
    change U.map (H.map (C.map (P.map (f + g)))) =
      U.map (H.map (C.map (P.map f))) + U.map (H.map (C.map (P.map g)))
    have hc : C.map (P.map (f + g)) = C.map (P.map f) + C.map (P.map g) :=
      (congrArg C.map hp).trans (C.map_add (f := P.map f) (g := P.map g))
    have hh : H.map (C.map (P.map (f + g))) =
        H.map (C.map (P.map f)) + H.map (C.map (P.map g)) :=
      (congrArg H.map hc).trans (H.map_add (f := C.map (P.map f)) (g := C.map (P.map g)))
    exact (congrArg U.map hh).trans
      (U.map_add (f := H.map (C.map (P.map f))) (g := H.map (C.map (P.map g))))

/-- Short exact field coefficients satisfy the concrete exactness predicate.

A categorical short exact sequence of field coefficient modules has the underlying map
exactness required by continuous-coefficient cohomology. -/
theorem fieldShortExact_discreteCoefficientExact
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact) :
    ContinuousCohomology.DiscreteCoefficientExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S :=
  (fieldModule_shortExact_iff_original_maps.{u, w} k Ω S).mp hS

-- The unchanged field-alias LES tuple exceeded 200000 in retained v5-v7 attempts.
/-- Continuous field cohomology forms a cohomological delta functor.

The degree functors and continuous-coefficient connecting morphisms form a cohomological delta
functor. -/
def fieldContinuousCohomologyDeltaFunctor :
    CohomologicalDeltaFunctor (FieldCohomologyModule.{u, w} k Ω)
      AddCommGrpCat.{max u w} where
  T n := fieldContinuousCohomologyFunctor.{u, w} k Ω n
  additive n := by infer_instance
  connecting n := by
    let G := InfiniteGalois.profiniteGalGrp k Ω
    let h (S : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω)) :
        ContinuousCohomology.DiscreteCoefficientExact.{u, w} (G := G) S.obj :=
      fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property
    exact
      { app S := ContinuousCohomology.discreteCoefficientConnecting.{u, w} (G := G) S.obj (h S) n
        naturality S S' f :=
          (ContinuousCohomology.discreteCoefficientConnecting_naturality.{u, w}
            (G := G) f.hom (h S) (h S') n).symm }
  exactLeft n S := by
    let h : ContinuousCohomology.DiscreteCoefficientExact.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj :=
      fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property
    have hw := ContinuousCohomology.discreteCoefficient_connecting_comp.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj h n
    have he := ContinuousCohomology.discreteCoefficient_cohomology_exact₁.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj h n
    exact ⟨hw, he⟩
  exactMiddle n S := by
    let F := fieldContinuousCohomologyFunctor.{u, w} k Ω n
    let h : ContinuousCohomology.DiscreteCoefficientExact.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj :=
      fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property
    have he := ContinuousCohomology.discreteCoefficient_cohomology_exact₂.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj h n
    exact ⟨(S.obj.map F).zero, he⟩
  exactRight n S := by
    let h : ContinuousCohomology.DiscreteCoefficientExact.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj :=
      fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property
    have hw := ContinuousCohomology.discreteCoefficient_comp_connecting.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj h n
    have he := ContinuousCohomology.discreteCoefficient_cohomology_exact₃.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj h n
    exact ⟨hw, he⟩
  monoZero S := by
    let h : ContinuousCohomology.DiscreteCoefficientExact.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj :=
      fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property
    exact ContinuousCohomology.discreteCoefficient_cohomology_mono_zero.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj h

/-- Injective field coefficients have zero positive continuous cohomology.

For an injective coefficient object `I`, continuous cohomology in every degree `n + 1` is
zero. -/
theorem fieldContinuousCohomologyFunctor_isZero_injective
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ) :
    IsZero ((fieldContinuousCohomologyFunctor.{u, w} k Ω (n + 1)).obj I) := by
  let U := ContinuousCohomology.discreteCoefficientForget.{max u w}
  exact U.map_isZero (fieldInjectiveContinuousCohomology_succ_isZero.{u, w} k Ω I n)

/-- Continuous field cohomology delta functor is universal.

The continuous-cohomology delta functor on field coefficient modules is universal. -/
theorem fieldContinuousCohomologyDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal
      (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
      (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) :=
  by
    apply CohomologicalDeltaFunctor.isUniversal_of_effaceable
    intro n
    exact Functor.isEffaceable_of_isZero_obj_injective
      (fieldContinuousCohomologyFunctor.{u, w} k Ω (n + 1))
      (fun I _ => fieldContinuousCohomologyFunctor_isZero_injective.{u, w} k Ω I n)

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

open CategoryTheory CategoryTheory.Limits



attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Degree zero continuous field cohomology is invariants.

The degree-zero continuous-cohomology functor is naturally isomorphic to the field invariant
functor. -/
def fieldContinuousCohomologyZeroIso :
    fieldContinuousCohomologyFunctor.{u, w} k Ω 0 ≅ fieldInvariantFunctor.{u, w} k Ω :=
  NatIso.ofComponents (fun M => ContinuousCohomology.discreteCoefficientZeroIso.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) M) (fun f => by
      let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)
      let U := ContinuousCohomology.discreteCoefficientForget.{max u w}
      let C := ContinuousCohomology.homogeneousCochainsFunctor.{0, u, w}
        (k := ℤ) (G := Gal(Ω/k))
      have h := congrArg U.map
        (ContinuousCohomology.homogeneousZeroIso_coefficient_naturality
          (G := InfiniteGalois.profiniteGalGrp k Ω) (P.map f))
      exact (U.map_comp (HomologicalComplex.homologyMap (C.map (P.map f)) 0)
        (ContinuousCohomology.zeroIso (P.obj _)).hom).symm.trans
        (h.trans (U.map_comp (ContinuousCohomology.zeroIso (P.obj _)).hom
          ((TopRep.invariantsFunctor ℤ Gal(Ω/k)).map (P.map f)))))

/-- Right derived field invariants delta functor.

Take the right-derived delta functor of field invariants. -/
abbrev fieldDerivedInvariantsDeltaFunctor :=
  Functor.rightDerivedDeltaFunctor (fieldInvariantFunctor.{u, w} k Ω)

/-- Right derived field invariants are universal.

The delta functor of right-derived field invariants is universal. -/
theorem fieldDerivedInvariantsDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal
      (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
      (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω) :=
  Functor.isUniversal_rightDerivedDeltaFunctor
    (fieldInvariantFunctor.{u, w} k Ω)

/-- Normalized comparison of continuous cohomology and derived invariants.

The degree-zero invariant coordinate extends to an isomorphism of the two universal delta
functors. -/
def fieldContinuousDerivedInvariantsDeltaIso :
    fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω ≅
      fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω :=
  CohomologicalDeltaFunctor.isoOfZeroIso
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
    (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω)
    (fieldContinuousCohomologyDeltaFunctor_isUniversal.{u, w} k Ω)
    (fieldDerivedInvariantsDeltaFunctor_isUniversal.{u, w} k Ω)
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω ≪≫
      (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.symm)

/-- Continuous cohomology as derived invariants in each degree.

Evaluate the delta-functor isomorphism in natural degree `q` to obtain a natural isomorphism
with `R^q` of invariants. -/
def fieldContinuousDerivedInvariantsIso (q : ℕ) :
    fieldContinuousCohomologyFunctor.{u, w} k Ω q ≅
      (fieldInvariantFunctor.{u, w} k Ω).rightDerived q :=
  (CohomologicalDeltaFunctor.evaluation
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w} q).mapIso
    (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω)

/-- Derived invariant comparison has the degree zero normalization.

The forward comparison in degree zero followed by the derived-zero coordinate equals the
continuous-cohomology invariant coordinate. -/
theorem fieldContinuousDerivedInvariantsIso_zero :
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom ≫
        (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom := by
  have h := CohomologicalDeltaFunctor.isoOfZeroIso_hom_app_zero
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
    (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω)
    (fieldContinuousCohomologyDeltaFunctor_isUniversal.{u, w} k Ω)
    (fieldDerivedInvariantsDeltaFunctor_isUniversal.{u, w} k Ω)
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω ≪≫
      (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.symm)
  have h' : (fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω ≪≫
        (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.symm).hom := h
  exact (congrArg (· ≫ (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom)
    h').trans (by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id])

/-- Continuous derived comparison is coefficient natural.

Each coefficient map commutes with the degreewise comparison and its right-derived invariant
map. -/
theorem fieldContinuousDerivedInvariantsIso_naturality (q : ℕ)
    {M N : FieldCohomologyModule.{u, w} k Ω} (f : M ⟶ N) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
        (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app N =
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app M ≫
        ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map f :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.naturality f

/-- Continuous derived comparison respects coefficient connecting maps.

For a short exact coefficient sequence, the continuous connecting map followed by comparison
in degree `n+1` equals comparison in degree `n` followed by the derived-invariant connecting
map. -/
theorem fieldContinuousDerivedInvariantsIso_connecting (n : ℕ)
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact) :
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).hom.app S.X₁ =
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫
      (Functor.rightDerivedConnecting (fieldInvariantFunctor.{u, w} k Ω) n).app
        ⟨S, hS⟩ :=
  DeltaFunctor.System.comm (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω).hom.hom
    n ⟨S, hS⟩

/-- Continuous cohomology in injective resolution invariant coordinates.

For any injective resolution, compare continuous cohomology with cohomology of its termwise
invariant complex. -/
def fieldContinuousDerivedInvariantsResolutionIso (q : ℕ)
    {M : FieldCohomologyModule.{u, w} k Ω} (I : InjectiveResolution M) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj M ≅
      (((fieldInvariantFunctor.{u, w} k Ω).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology q :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app M ≪≫
    I.isoRightDerivedObj (fieldInvariantFunctor.{u, w} k Ω) q

-- The final field-resolution association reached 200000 in retained v4.
/-- Resolution comparison is natural for augmented resolution maps.

A map of injective-resolution cochain complexes agreeing with the coefficient map in degree
zero commutes with the continuous-to-resolution cohomology coordinates. -/
theorem fieldContinuousDerivedInvariantsResolutionIso_naturality (q : ℕ)
    {M N : FieldCohomologyModule.{u, w} k Ω} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
        (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J).hom =
      (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
        HomologicalComplex.homologyMap
          (((fieldInvariantFunctor.{u, w} k Ω).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ) q := by
  let C := FieldCohomologyModule.{u, w} k Ω
  let A := AddCommGrpCat.{max u w}
  let F : C ⥤ A := fieldContinuousCohomologyFunctor.{u, w} k Ω q
  let G : C ⥤ A := fieldInvariantFunctor.{u, w} k Ω
  let c : F ≅ G.rightDerived q := fieldContinuousDerivedInvariantsIso.{u, w} k Ω q
  let KI : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let KJ : CochainComplex A ℕ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let eI : (G.rightDerived q).obj M ≅ KI.homology q := I.isoRightDerivedObj G q
  let eJ : (G.rightDerived q).obj N ≅ KJ.homology q := J.isoRightDerivedObj G q
  let ψ : KI ⟶ KJ := (G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  let m : KI.homology q ⟶ KJ.homology q := HomologicalComplex.homologyMap ψ q
  have hR : (G.rightDerived q).map f ≫ eJ.hom = eI.hom ≫ m := by
    simpa only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] using
      (InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ G q)
  have hC : F.map f ≫ c.hom.app N = c.hom.app M ≫ (G.rightDerived q).map f :=
    c.hom.naturality f
  change F.map f ≫ (c.hom.app N ≫ eJ.hom) = (c.hom.app M ≫ eI.hom) ≫ m
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ eJ.hom) hC).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun x => c.hom.app M ≫ x) hR).trans (Category.assoc _ _ _).symm)))

/-- Resolution comparison is independent of resolution choice.

The comparison for one injective resolution followed by its canonical cohomology comparison
equals the comparison for the other resolution. -/
theorem fieldContinuousDerivedInvariantsResolutionIso_choice (q : ℕ)
    {M : FieldCohomologyModule.{u, w} k Ω} (I J : InjectiveResolution M) :
    fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I ≪≫
        InjectiveResolution.cohomologyComparisonIso I J
          (fieldInvariantFunctor.{u, w} k Ω) q =
      fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J := by
  apply Iso.ext
  change (((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app M).hom ≫
      (I.isoRightDerivedObj (fieldInvariantFunctor.{u, w} k Ω) q).hom) ≫
    ((I.isoRightDerivedObj (fieldInvariantFunctor.{u, w} k Ω) q).inv ≫
      (J.isoRightDerivedObj (fieldInvariantFunctor.{u, w} k Ω) q).hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- Degree zero comparison evaluates a cocycle at the group identity.

For a continuous degree-zero cocycle, its compared invariant element has value equal to the
included homogeneous cochain evaluated at `1`. -/
theorem fieldContinuousDerivedInvariantsIso_zero_cycle_value
    (M : FieldCohomologyModule.{u, w} k Ω)
    (c : ContinuousCohomology.cocycles
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) 0) :
    ((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app M
      ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom.app M
        (ContinuousCohomology.π _ 0 c))).val =
      ((TopRep.homogeneousCochains _).iCycles 0 c).val 1 := by
  have h := congrArg (fun α => α.app M)
    (fieldContinuousDerivedInvariantsIso_zero.{u, w} k Ω)
  have hv := congrArg (fun α => (α (ContinuousCohomology.π _ 0 c)).val) h
  exact hv.trans (ContinuousCohomology.homogeneousZeroIso_cycles_value.{0, u, w}
    _ c)

/-- Connecting map of an injective cokernel sequence is epi.

For a monomorphism into an injective coefficient, the continuous connecting map from cokernel
cohomology to the next degree of the source is an epimorphism. -/
theorem fieldContinuousCokerConnecting_epi (n : ℕ)
    {M I : FieldCohomologyModule.{u, w} k Ω} (i : M ⟶ I) [Mono i] [Injective I] :
    Epi (((fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω).connecting n).app
      ⟨ShortComplex.cokernelSequence i,
        ShortComplex.shortExact_cokernelSequence i⟩) := by
  let T := fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω
  have hk : (T.T (n + 1)).map i = 0 :=
    (fieldContinuousCohomologyFunctor_isZero_injective.{u, w} k Ω I n).eq_of_tgt _ _
  obtain ⟨w, hex⟩ := T.exactLeft n
    ⟨ShortComplex.cokernelSequence i, ShortComplex.shortExact_cokernelSequence i⟩
  exact (ShortComplex.exact_iff_epi _ hk).mp hex

-- Instantiating the full original field-family uniqueness reached 200000 in retained v4.
/-- Connecting and zero normalization determine the comparison maps.

Any family of natural transformations commuting with coefficient connecting maps and having
the same degree-zero normalization equals the canonical comparison in every degree. -/
theorem fieldContinuousDerivedInvariantsIso_unique
    (f : ∀ n, fieldContinuousCohomologyFunctor.{u, w} k Ω n ⟶
      (fieldInvariantFunctor.{u, w} k Ω).rightDerived n)
    (hδ : ∀ n (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω))
      (hS : S.ShortExact),
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
          (G := InfiniteGalois.profiniteGalGrp k Ω) S
          (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
        (f (n + 1)).app S.X₁ = (f n).app S.X₃ ≫
          (Functor.rightDerivedConnecting (fieldInvariantFunctor.{u, w} k Ω) n).app
            ⟨S, hS⟩)
    (h₀ : f 0 ≫ (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom) :
    ∀ n, f n = (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom := by
  let C := FieldCohomologyModule.{u, w} k Ω
  let A := AddCommGrpCat.{max u w}
  let T : CohomologicalDeltaFunctor C A := fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω
  let S : CohomologicalDeltaFunctor C A := fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω
  let e : T ≅ S := fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω
  let G : C ⥤ A := fieldInvariantFunctor.{u, w} k Ω
  let z : G.rightDerived 0 ≅ G := G.rightDerivedZeroIsoSelf
  let g : T ⟶ S := CohomologicalDeltaFunctor.homMk C A f
    (fun n Z => hδ n Z.obj Z.property)
  have hg₀ : CohomologicalDeltaFunctor.Hom.app g 0 =
      CohomologicalDeltaFunctor.Hom.app e.hom 0 := by
    apply (cancel_mono z.hom).1
    exact h₀.trans (fieldContinuousDerivedInvariantsIso_zero.{u, w} k Ω).symm
  have hUniversal : CohomologicalDeltaFunctor.IsUniversal C A T :=
    fieldContinuousCohomologyDeltaFunctor_isUniversal.{u, w} k Ω
  obtain ⟨a, ha, hu⟩ := hUniversal S (CohomologicalDeltaFunctor.Hom.app e.hom 0)
  have hg : g = e.hom := (hu g hg₀).trans (hu e.hom rfl).symm
  intro n
  exact congrArg (fun h => CohomologicalDeltaFunctor.Hom.app h n) hg

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

open CategoryTheory CategoryTheory.Limits

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
variable (k' Ω' : Type v) [Field k'] [Field Ω'] [Algebra k' Ω'] [IsSepClosure k' Ω']

-- Preserve the original public compatibility name and its signature, as recorded by the
-- field-cohomology-cut6 validation; the `[IsSepClosure K L]` binder is unused.
/-- Let `K` and `L` be fields in universe `u`, with a `K`-algebra structure on `L`
and a specified separable-closure structure for `L/K`. The category of discrete continuous
`Gal(L/K)`-actions on abelian coefficient groups in the independent universe `w` is
preadditive: addition and zero on equivariant morphisms are computed componentwise. -/
@[nolint defsWithUnderscore unusedArguments]
abbrev fieldDiscreteModule_preadditive_raw
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    Preadditive (DiscreteAbelianAction.{u, w} Gal(L/K)) :=
  DiscreteAbelianAction.instPreadditive.{u, w} (G := Gal(L/K))

/-- Coefficient restriction along a continuous Galois group homomorphism.

For fields in universes `u` and `v`, restrict the action along a continuous group map, using
common coefficient height `max u v w`. -/
def fieldModuleRestriction
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    FieldCohomologyModule.{u, max v w} k Ω ⥤ FieldCohomologyModule.{v, max u w} k' Ω' :=
  GaloisUnits.restrictModules.{u, v, max u (max v w)} φ

/-- Field coefficient restriction is additive.

Restriction of the Galois action preserves sums of coefficient morphisms. -/
instance fieldModuleRestriction_additive
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).Additive where
  map_add {_ _} f g := by rfl

/-- Field coefficient restriction preserves zero maps.

The restriction functor sends zero coefficient morphisms to zero morphisms. -/
instance fieldModuleRestriction_preservesZeroMorphisms
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).PreservesZeroMorphisms where
  map_zero _ _ := by rfl

/-- Field coefficient restriction preserves short exact sequences.

A short exact coefficient sequence remains short exact after restriction along a continuous
Galois-group homomorphism. -/
theorem fieldModuleRestriction_shortExact
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (S : ShortComplex (FieldCohomologyModule.{u, max v w} k Ω)) (hS : S.ShortExact) :
    (S.map (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)).ShortExact :=
  (fieldModule_shortExact_iff_original_maps.{v, max u w} k' Ω'
    (S.map (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ))).mpr
    ((fieldModule_shortExact_iff_original_maps.{u, max v w} k Ω S).mp hS)

/-- Restricted coefficient representation has its identity coordinate map.

The restricted topological representation and the representation of the restricted coefficient
are connected by the identity underlying map. -/
def fieldModuleRestrictionTopRepHom
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, max v w} k Ω) :
    TopRep.res φ ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj
          ((fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).obj M) :=
  𝟙 _

/-- Galois invariant elements restrict naturally.

An element invariant under the source group is invariant under the target group acting through
the continuous group homomorphism. -/
def fieldInvariantRestriction
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldInvariantFunctor.{u, max v w} k Ω ⟶
      fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ ⋙
        fieldInvariantFunctor.{v, max u w} k' Ω' where
  app M := AddCommGrpCat.ofHom
    { toFun m := ⟨m.val, fun h => m.property (φ h)⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality {M N} f := by
    ext m
    apply Subtype.ext
    rfl

/-- Restriction map on continuous field cohomology.

Group restriction and the canonical coefficient intertwiner induce a natural map on continuous
cohomology in every degree. -/
def fieldContinuousCohomologyRestriction (n : ℕ)
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldContinuousCohomologyFunctor.{u, max v w} k Ω n ⟶
      fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ ⋙
        fieldContinuousCohomologyFunctor.{v, max u w} k' Ω' n where
  app M := ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
    (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ
      (fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ M) n)
  naturality {M N} f :=
    ContinuousCohomology.discreteCoefficientGroupCohomologySquare.{u, v, w} φ f
      ((fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).map f)
      (fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ M)
      (fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ N)
      (by apply TopRep.hom_ext; rfl) n

/-- Group restriction map of coefficient short complexes.

The restriction functor gives the corresponding group-and-coefficient morphism from a short
complex to its restricted short complex. -/
def fieldModuleRestrictionGroupSequence
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (S : ShortComplex (FieldCohomologyModule.{u, max v w} k Ω)) :
    letI : (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).PreservesZeroMorphisms :=
      ⟨fun _ _ => by rfl⟩
    ContinuousCohomology.DiscreteCoefficientGroupHom.{u, v, w} S
      (S.map (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)) φ := by
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let T : ShortComplex B := S.map R
  let P : C ⥤ TopRep.{max u (max v w), 0, u} ℤ Gal(Ω/k) :=
    ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
      (InfiniteGalois.profiniteGalGrp k Ω)
  let Q : B ⥤ TopRep.{max v (max u w), 0, v} ℤ Gal(Ω'/k') :=
    ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
      (InfiniteGalois.profiniteGalGrp k' Ω')
  let a₁ : TopRep.res φ (P.obj S.X₁) ⟶ Q.obj T.X₁ :=
    fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ S.X₁
  let a₂ : TopRep.res φ (P.obj S.X₂) ⟶ Q.obj T.X₂ :=
    fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ S.X₂
  let a₃ : TopRep.res φ (P.obj S.X₃) ⟶ Q.obj T.X₃ :=
    fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ S.X₃
  exact
    { τ₁ := a₁
      τ₂ := a₂
      τ₃ := a₃
      comm₁₂ := by apply TopRep.hom_ext; rfl
      comm₂₃ := by apply TopRep.hom_ext; rfl }

-- The direct two-field connector instantiation reached 200000/800000 in retained v6-v8.
/-- Continuous restriction commutes with connecting maps.

The coefficient connecting morphisms commute with restriction in adjacent cohomological
degrees. -/
theorem fieldContinuousRestriction_comm
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (n : ℕ) (S : ShortComplex.ShortExactSequences
      (FieldCohomologyModule.{u, max v w} k Ω)) :
    ((fieldContinuousCohomologyDeltaFunctor.{u, max v w} k Ω).connecting n).app S ≫
        (fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' (n + 1) φ).app S.obj.X₁ =
      (fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ).app S.obj.X₃ ≫
        ((CohomologicalDeltaFunctor.precompose
          (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
          (fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ)
          (fieldContinuousCohomologyDeltaFunctor.{v, max u w} k' Ω')).connecting n).app S := by
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let Z : ShortComplex B := S.obj.map R
  let hS : ContinuousCohomology.DiscreteCoefficientExact.{u, max v w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj :=
    fieldShortExact_discreteCoefficientExact.{u, max v w} k Ω S.obj S.property
  let hZ : ContinuousCohomology.DiscreteCoefficientExact.{v, max u w}
      (G := InfiniteGalois.profiniteGalGrp k' Ω') Z :=
    fieldShortExact_discreteCoefficientExact.{v, max u w} k' Ω' Z (hR S.obj S.property)
  let f : ContinuousCohomology.DiscreteCoefficientGroupHom.{u, v, w} S.obj Z φ :=
    fieldModuleRestrictionGroupSequence.{u, v, w} k Ω k' Ω' φ S.obj
  have h := ContinuousCohomology.discreteCoefficientConnecting_group_naturality.{u, v, w}
    hS hZ f n
  exact h

-- Bind the checked pointwise connector proof before constructing the delta morphism.
/-- Continuous field restriction as a delta functor morphism.

The restriction maps in all degrees form a morphism to the target continuous delta functor
precomposed with coefficient restriction. -/
def fieldContinuousRestrictionDeltaHom
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldContinuousCohomologyDeltaFunctor.{u, max v w} k Ω ⟶
      CohomologicalDeltaFunctor.precompose
        (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
        (fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ)
        (fieldContinuousCohomologyDeltaFunctor.{v, max u w} k' Ω') :=
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let T : CohomologicalDeltaFunctor C A :=
    fieldContinuousCohomologyDeltaFunctor.{u, max v w} k Ω
  let T' : CohomologicalDeltaFunctor C A :=
    CohomologicalDeltaFunctor.precompose R hR
      (fieldContinuousCohomologyDeltaFunctor.{v, max u w} k' Ω')
  let a : ∀ n, T.T n ⟶ T'.T n :=
    fun n => fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ
  let h : ∀ n (Z : ShortComplex.ShortExactSequences C),
      (T.connecting n).app Z ≫ (a (n + 1)).app Z.obj.X₁ =
        (a n).app Z.obj.X₃ ≫ (T'.connecting n).app Z :=
    fun n Z => fieldContinuousRestriction_comm.{u, v, w} k Ω k' Ω' φ n Z
  CohomologicalDeltaFunctor.homMk C A a h

/-- Continuous restriction agrees with invariant restriction in degree zero.

The degree-zero restriction map commutes with the invariant coordinates and the natural
inclusion of invariants under group restriction. -/
theorem fieldContinuousCohomologyRestriction_zero
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' 0 φ ≫
        Functor.whiskerLeft (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
          (fieldContinuousCohomologyZeroIso.{v, max u w} k' Ω').hom =
      (fieldContinuousCohomologyZeroIso.{u, max v w} k Ω).hom ≫
        fieldInvariantRestriction.{u, v, w} k Ω k' Ω' φ := by
  apply NatTrans.ext
  funext M
  exact ContinuousCohomology.discreteCoefficientGroupZeroIso_naturality.{u, v, w} φ
    (fieldModuleRestrictionTopRepHom.{u, v, w} k Ω k' Ω' φ M)

/-- Degree zero restriction on derived invariants.

Use the derived-zero invariant isomorphisms to transport invariant restriction to a map on
degree-zero right-derived invariants. -/
def fieldDerivedInvariantsRestrictionZero
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    (fieldInvariantFunctor.{u, max v w} k Ω).rightDerived 0 ⟶
      fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ ⋙
        (fieldInvariantFunctor.{v, max u w} k' Ω').rightDerived 0 :=
  (fieldInvariantFunctor.{u, max v w} k Ω).rightDerivedZeroIsoSelf.hom ≫
    fieldInvariantRestriction.{u, v, w} k Ω k' Ω' φ ≫
      Functor.whiskerLeft (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
        (fieldInvariantFunctor.{v, max u w} k' Ω').rightDerivedZeroIsoSelf.inv

-- The dependent all-field universal extension reached 200000 in retained v6.
/-- Universal extension of derived invariant restriction.

The normalized universal extension of invariant restriction defines a morphism of right-
derived invariant delta functors. -/
def fieldDerivedInvariantsRestrictionDeltaHom
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldDerivedInvariantsDeltaFunctor.{u, max v w} k Ω ⟶
      CohomologicalDeltaFunctor.precompose
        (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
        (fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ)
        (fieldDerivedInvariantsDeltaFunctor.{v, max u w} k' Ω') :=
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let I : C ⥤ A := fieldInvariantFunctor.{u, max v w} k Ω
  let I' : B ⥤ A := fieldInvariantFunctor.{v, max u w} k' Ω'
  let S : CohomologicalDeltaFunctor C A := fieldDerivedInvariantsDeltaFunctor.{u, max v w} k Ω
  let S' : CohomologicalDeltaFunctor C A :=
    CohomologicalDeltaFunctor.precompose R hR (fieldDerivedInvariantsDeltaFunctor.{v, max u w} k' Ω')
  let hS : CohomologicalDeltaFunctor.IsUniversal C A S :=
    fieldDerivedInvariantsDeltaFunctor_isUniversal.{u, max v w} k Ω
  let eS : S.T 0 ≅ I := I.rightDerivedZeroIsoSelf
  let eS' : S'.T 0 ≅ R ⋙ I' := Functor.isoWhiskerLeft R I'.rightDerivedZeroIsoSelf
  let f : I ⟶ R ⋙ I' := fieldInvariantRestriction.{u, v, w} k Ω k' Ω' φ
  CohomologicalDeltaFunctor.normalizedExtension S S' hS eS eS' f

/-- Derived invariant restriction in a fixed degree.

Evaluate the derived-invariant restriction delta morphism in natural degree `n`. -/
def fieldDerivedInvariantsRestriction (n : ℕ)
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :=
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let S : CohomologicalDeltaFunctor C A := fieldDerivedInvariantsDeltaFunctor.{u, max v w} k Ω
  let S' : CohomologicalDeltaFunctor C A :=
    CohomologicalDeltaFunctor.precompose R hR (fieldDerivedInvariantsDeltaFunctor.{v, max u w} k' Ω')
  let f : S ⟶ S' := fieldDerivedInvariantsRestrictionDeltaHom.{u, v, w} k Ω k' Ω' φ
  let a : S.T n ⟶ S'.T n := CohomologicalDeltaFunctor.Hom.app f n
  a


-- Retained direct degree-zero field headers reached 800000; assemble the abstract
-- universal comparison first, with every actual functor and normalization fixed.
/-- Continuous and derived restriction comparison square.

Restriction on continuous delta functors followed by the target comparison equals the source
comparison followed by derived-invariant restriction. -/
theorem fieldContinuousDerivedRestriction_delta_square
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldContinuousRestrictionDeltaHom.{u, v, w} k Ω k' Ω' φ ≫
        (CohomologicalDeltaFunctor.precomposeFunctor
          (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
          (fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ)).map
            (fieldContinuousDerivedInvariantsDeltaIso.{v, max u w} k' Ω').hom =
      (fieldContinuousDerivedInvariantsDeltaIso.{u, max v w} k Ω).hom ≫
        fieldDerivedInvariantsRestrictionDeltaHom.{u, v, w} k Ω k' Ω' φ := by
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let T : CohomologicalDeltaFunctor C A := fieldContinuousCohomologyDeltaFunctor.{u, max v w} k Ω
  let S : CohomologicalDeltaFunctor C A := fieldDerivedInvariantsDeltaFunctor.{u, max v w} k Ω
  let P : CohomologicalDeltaFunctor B A ⥤ CohomologicalDeltaFunctor C A :=
    CohomologicalDeltaFunctor.precomposeFunctor R hR
  let T' : CohomologicalDeltaFunctor C A :=
    P.obj (fieldContinuousCohomologyDeltaFunctor.{v, max u w} k' Ω')
  let S' : CohomologicalDeltaFunctor C A :=
    P.obj (fieldDerivedInvariantsDeltaFunctor.{v, max u w} k' Ω')
  let F : C ⥤ A := fieldInvariantFunctor.{u, max v w} k Ω
  let G : C ⥤ A := R ⋙ fieldInvariantFunctor.{v, max u w} k' Ω'
  let eT : T.T 0 ≅ F := fieldContinuousCohomologyZeroIso.{u, max v w} k Ω
  let eS : S.T 0 ≅ F := F.rightDerivedZeroIsoSelf
  let eT' : T'.T 0 ≅ G := Functor.isoWhiskerLeft R
    (fieldContinuousCohomologyZeroIso.{v, max u w} k' Ω')
  let eS' : S'.T 0 ≅ G := Functor.isoWhiskerLeft R
    (fieldInvariantFunctor.{v, max u w} k' Ω').rightDerivedZeroIsoSelf
  let c : T ≅ S := fieldContinuousDerivedInvariantsDeltaIso.{u, max v w} k Ω
  let d : T' ≅ S' := P.mapIso (fieldContinuousDerivedInvariantsDeltaIso.{v, max u w} k' Ω')
  let m : T ⟶ T' := fieldContinuousRestrictionDeltaHom.{u, v, w} k Ω k' Ω' φ
  let f : F ⟶ G := fieldInvariantRestriction.{u, v, w} k Ω k' Ω' φ
  have hc : CohomologicalDeltaFunctor.Hom.app c.hom 0 ≫ eS.hom = eT.hom :=
    fieldContinuousDerivedInvariantsIso_zero.{u, max v w} k Ω
  have hd : CohomologicalDeltaFunctor.Hom.app d.hom 0 ≫ eS'.hom = eT'.hom :=
    (Functor.whiskerLeft_comp R
      (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' 0).hom
      (fieldInvariantFunctor.{v, max u w} k' Ω').rightDerivedZeroIsoSelf.hom).symm.trans
      (congrArg (Functor.whiskerLeft R)
        (fieldContinuousDerivedInvariantsIso_zero.{v, max u w} k' Ω'))
  have hm : CohomologicalDeltaFunctor.Hom.app m 0 ≫ eT'.hom = eT.hom ≫ f :=
    fieldContinuousCohomologyRestriction_zero.{u, v, w} k Ω k' Ω' φ
  let hT : CohomologicalDeltaFunctor.IsUniversal C A T :=
    fieldContinuousCohomologyDeltaFunctor_isUniversal.{u, max v w} k Ω
  let hS : CohomologicalDeltaFunctor.IsUniversal C A S :=
    fieldDerivedInvariantsDeltaFunctor_isUniversal.{u, max v w} k Ω
  have h : m ≫ d.hom = c.hom ≫
      CohomologicalDeltaFunctor.normalizedExtension S S' hS eS eS' f :=
    CohomologicalDeltaFunctor.normalizedExtension_comparison T S T' S' hT hS
      eT eS eT' eS' f c.hom d.hom m hc hd hm
  change m ≫ d.hom = c.hom ≫ CohomologicalDeltaFunctor.normalizedExtension S S' hS eS eS' f
  exact h

-- The original all-degree field header reached 200000 in retained V1.
/-- Degreewise comparison is natural in Galois group restriction.

The continuous restriction map commutes with the degreewise comparisons to derived invariants,
for independently ranked source and target fields. -/
theorem fieldContinuousDerivedInvariantsIso_group_naturality (n : ℕ)
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ ≫
        Functor.whiskerLeft (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
          (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom =
      (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom ≫
        fieldDerivedInvariantsRestriction.{u, v, w} k Ω k' Ω' n φ := by
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let T : CohomologicalDeltaFunctor C A := fieldContinuousCohomologyDeltaFunctor.{u, max v w} k Ω
  let S : CohomologicalDeltaFunctor C A := fieldDerivedInvariantsDeltaFunctor.{u, max v w} k Ω
  let P : CohomologicalDeltaFunctor B A ⥤ CohomologicalDeltaFunctor C A :=
    CohomologicalDeltaFunctor.precomposeFunctor R hR
  let T' : CohomologicalDeltaFunctor C A :=
    P.obj (fieldContinuousCohomologyDeltaFunctor.{v, max u w} k' Ω')
  let S' : CohomologicalDeltaFunctor C A :=
    P.obj (fieldDerivedInvariantsDeltaFunctor.{v, max u w} k' Ω')
  let m : T ⟶ T' := fieldContinuousRestrictionDeltaHom.{u, v, w} k Ω k' Ω' φ
  let c : T ≅ S := fieldContinuousDerivedInvariantsDeltaIso.{u, max v w} k Ω
  let d : T' ⟶ S' := P.map (fieldContinuousDerivedInvariantsDeltaIso.{v, max u w} k' Ω').hom
  let g : S ⟶ S' := fieldDerivedInvariantsRestrictionDeltaHom.{u, v, w} k Ω k' Ω' φ
  have h : CohomologicalDeltaFunctor.Hom.app (m ≫ d) n =
      CohomologicalDeltaFunctor.Hom.app (c.hom ≫ g) n :=
    congrArg (fun f : T ⟶ S' => CohomologicalDeltaFunctor.Hom.app f n)
      (fieldContinuousDerivedRestriction_delta_square.{u, v, w} k Ω k' Ω' φ)
  change CohomologicalDeltaFunctor.Hom.app (m ≫ d) n =
    CohomologicalDeltaFunctor.Hom.app (c.hom ≫ g) n
  exact h

/-- Equivariant coefficient map factors through action restriction.

A map of restricted topological coefficient representations gives a morphism from the
restricted discrete source module to the target module. -/
def fieldRestrictedCoefficientHom
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    {M : FieldCohomologyModule.{u, max v w} k Ω}
    {N : FieldCohomologyModule.{v, max u w} k' Ω'}
    (f : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) :
    (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).obj M ⟶ N :=
  (ContinuousCohomology.originalCoefficient_factorization_all.{u, v, w}
    (G := InfiniteGalois.profiniteGalGrp k Ω)
    (H := InfiniteGalois.profiniteGalGrp k' Ω') φ M N f).choose

/-- Group coefficient cohomology map factors through restriction.

The map induced by a group homomorphism and coefficient intertwiner equals group restriction
followed by the cohomology map of the factored coefficient morphism. -/
theorem fieldGroupCoefficientCohomology_factorization (n : ℕ)
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    {M : FieldCohomologyModule.{u, max v w} k Ω}
    {N : FieldCohomologyModule.{v, max u w} k' Ω'}
    (f : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) :
    ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
        (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f n) =
      (fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ).app M ≫
        (fieldContinuousCohomologyFunctor.{v, max u w} k' Ω' n).map
          (fieldRestrictedCoefficientHom.{u, v, w} k Ω k' Ω' φ f) := by
  have h := ContinuousCohomology.originalCoefficient_factorization_all.{u, v, w}
    (G := InfiniteGalois.profiniteGalGrp k Ω)
    (H := InfiniteGalois.profiniteGalGrp k' Ω') φ M N f
  exact h.choose_spec.2 n

/-- Derived invariant map for group and coefficient change.

Compose derived group restriction with the derived-invariant map of the factored coefficient
intertwiner. -/
def fieldDerivedInvariantsGroupCoefficientMap (n : ℕ)
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    {M : FieldCohomologyModule.{u, max v w} k Ω}
    {N : FieldCohomologyModule.{v, max u w} k' Ω'}
    (f : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) :=
  (fieldDerivedInvariantsRestriction.{u, v, w} k Ω k' Ω' n φ).app M ≫
    ((fieldInvariantFunctor.{v, max u w} k' Ω').rightDerived n).map
      (fieldRestrictedCoefficientHom.{u, v, w} k Ω k' Ω' φ f)

-- This full original coefficient-naturality header reached 200000 in retained V3.
/-- Comparison respects simultaneous group and coefficient maps.

The continuous group-and-coefficient cohomology map followed by comparison equals comparison
followed by its derived-invariant counterpart. -/
theorem fieldContinuousDerivedInvariantsIso_group_coefficient_naturality (n : ℕ)
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    {M : FieldCohomologyModule.{u, max v w} k Ω}
    {N : FieldCohomologyModule.{v, max u w} k' Ω'}
    (f : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) :
    ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
        (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f n) ≫
      (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom.app N =
    (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom.app M ≫
      fieldDerivedInvariantsGroupCoefficientMap.{u, v, w} k Ω k' Ω' n φ f := by
  let C := FieldCohomologyModule.{u, max v w} k Ω
  let B := FieldCohomologyModule.{v, max u w} k' Ω'
  let A := AddCommGrpCat.{max u (max v w)}
  let R : C ⥤ B := fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ
  let _ : R.Additive := fieldModuleRestriction_additive.{u, v, w} k Ω k' Ω' φ
  let _ : R.PreservesZeroMorphisms :=
    fieldModuleRestriction_preservesZeroMorphisms.{u, v, w} k Ω k' Ω' φ
  let hR : ∀ Z : ShortComplex C, Z.ShortExact → (Z.map R).ShortExact :=
    fieldModuleRestriction_shortExact.{u, v, w} k Ω k' Ω' φ
  let I : C ⥤ A := fieldInvariantFunctor.{u, max v w} k Ω
  let I' : B ⥤ A := fieldInvariantFunctor.{v, max u w} k' Ω'
  let F : C ⥤ A := fieldContinuousCohomologyFunctor.{u, max v w} k Ω n
  let F' : B ⥤ A := fieldContinuousCohomologyFunctor.{v, max u w} k' Ω' n
  let b : R.obj M ⟶ N := fieldRestrictedCoefficientHom.{u, v, w} k Ω k' Ω' φ f
  let eM : F.obj M ≅ (I.rightDerived n).obj M :=
    (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).app M
  let eR : F'.obj (R.obj M) ≅ (I'.rightDerived n).obj (R.obj M) :=
    (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).app (R.obj M)
  let eN : F'.obj N ≅ (I'.rightDerived n).obj N :=
    (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).app N
  let mC : F.obj M ⟶ F'.obj (R.obj M) :=
    (fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ).app M
  let mD : (I.rightDerived n).obj M ⟶ (I'.rightDerived n).obj (R.obj M) :=
    (fieldDerivedInvariantsRestriction.{u, v, w} k Ω k' Ω' n φ).app M
  let c : F'.obj (R.obj M) ⟶ F'.obj N := F'.map b
  let d : (I'.rightDerived n).obj (R.obj M) ⟶ (I'.rightDerived n).obj N :=
    (I'.rightDerived n).map b
  let a : F.obj M ⟶ F'.obj N :=
    ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
      (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f n)
  have hG : mC ≫ eR.hom = eM.hom ≫ mD :=
    congrArg (fun t => t.app M)
      (fieldContinuousDerivedInvariantsIso_group_naturality.{u, v, w} k Ω k' Ω' n φ)
  have hC : c ≫ eN.hom = eR.hom ≫ d :=
    fieldContinuousDerivedInvariantsIso_naturality.{v, max u w} k' Ω' n b
  have hFactor : a = mC ≫ c :=
    fieldGroupCoefficientCohomology_factorization.{u, v, w} k Ω k' Ω' n φ f
  change a ≫ eN.hom = eM.hom ≫ (mD ≫ d)
  calc
    _ = (mC ≫ c) ≫ eN.hom := congrArg (fun t => t ≫ eN.hom) hFactor
    _ = mC ≫ (eR.hom ≫ d) :=
      (Category.assoc _ _ _).trans (congrArg (fun t => mC ≫ t) hC)
    _ = (eM.hom ≫ mD) ≫ d :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ d) hG)
    _ = _ := Category.assoc _ _ _

-- The exact native field one-lift header reached 200000 in retained V5.
/-- Comparison for group maps with individually lifted coefficients.

Lift each source and target coefficient once to the common height. The lifted intertwiner
sends a lifted element to the lift of its given value, and the group-and-coefficient
comparison square holds in every degree. -/
theorem fieldContinuousDerivedInvariantsIso_native_group_naturality
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, w} k Ω)
    (N : FieldCohomologyModule.{v, w} k' Ω')
    (f : ContinuousCohomology.nativeCoefficientIntertwiner.{0, u, v, w}
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M)
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) φ) :
    let M' : FieldCohomologyModule.{u, max v w} k Ω :=
      (ContinuousCohomology.discreteCoefficientULiftFunctor.{u, v, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M
    let N' : FieldCohomologyModule.{v, max u w} k' Ω' :=
      (ContinuousCohomology.discreteCoefficientULiftFunctor.{v, u, w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N
    let f' : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M') ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N' :=
      ContinuousCohomology.nativeULiftGroupIntertwiner.{0, u, v, w} φ.toMonoidHom f
    (∀ x : (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M,
      f'.hom (ULift.up.{v, max u w} x) = ULift.up.{u, max v w} (f x)) ∧
    ∀ n, ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
        (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f' n) ≫
      (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom.app N' =
    (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom.app M' ≫
      fieldDerivedInvariantsGroupCoefficientMap.{u, v, w} k Ω k' Ω' n φ f' := by
  intro M' N' f'
  have hValue : ∀ x : (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M,
      f'.hom (ULift.up.{v, max u w} x) = ULift.up.{u, max v w} (f x) :=
    fun x => ContinuousCohomology.nativeULiftGroupIntertwiner_apply.{0, u, v, w}
      φ.toMonoidHom f x
  have hNatural : ∀ n,
      ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
        (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f' n) ≫
        (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom.app N' =
      (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom.app M' ≫
        fieldDerivedInvariantsGroupCoefficientMap.{u, v, w} k Ω k' Ω' n φ f' :=
    fun n => fieldContinuousDerivedInvariantsIso_group_coefficient_naturality.{u, v, w}
      k Ω k' Ω' n φ f'
  exact ⟨hValue, hNatural⟩

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

open CategoryTheory CategoryTheory.Limits

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Continuous derived comparison on lifted sheaf fibers.

Evaluate the field comparison at the geometric fiber of a coefficient sheaf lifted to the
common universe. -/
def originalFieldContinuousDerivedInvariantsIso (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) ≅
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
      ((liftCoefficients.{u, w} (Spec (.of k))).obj F))

/-- Lifted sheaf fiber comparison is natural.

The comparison commutes with the geometric-fiber map induced by a lifted sheaf morphism. -/
theorem originalFieldContinuousDerivedInvariantsIso_naturality (q : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)) ≫
      (originalFieldContinuousDerivedInvariantsIso.{u, w} k Ω q F').hom =
    (originalFieldContinuousDerivedInvariantsIso.{u, w} k Ω q F).hom ≫
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)) :=
  fieldContinuousDerivedInvariantsIso_naturality.{u, w} k Ω q
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      ((liftCoefficients.{u, w} (Spec (.of k))).map f))

/-- Derived field sections as continuous geometric fiber cohomology.

The derived section-invariant coordinate followed by the inverse continuous-to-derived-
invariant comparison gives a natural isomorphism for every degree. -/
def fieldDerivedSectionsContinuousCohomologyIso (q : ℕ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q :=
  fieldDerivedSectionsInvariantsIso.{u, w} k Ω q ≪≫
    Functor.isoWhiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).symm

/-- Derived section continuous comparison is sheaf natural.

Every sheaf map commutes with the degreewise comparison to continuous cohomology of its
geometric fiber. -/
theorem fieldDerivedSectionsContinuousCohomologyIso_naturality (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f ≫
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app Q' =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app Q ≫
        (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f) :=
  (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.naturality f

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

open CategoryTheory CategoryTheory.Limits

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Invariant coordinate of a continuous zero cocycle.

The compared degree-zero class has underlying invariant value equal to the homogeneous cocycle
evaluated at the group identity. -/
theorem original_zero_cycle_consumer
    (M : FieldCohomologyModule.{u, w} k Ω)
    (z : ContinuousCohomology.cocycles
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) 0) :
    ((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app M
      ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom.app M
        (ContinuousCohomology.π _ 0 z))).val =
      ((TopRep.homogeneousCochains _).iCycles 0 z).val 1 :=
  fieldContinuousDerivedInvariantsIso_zero_cycle_value.{u, w} k Ω M z

/-- Comparison commutes with the canonical resolution map.

For any coefficient map and injective resolutions of its source and target, the comparison
square uses the canonical descended resolution map on invariant-complex cohomology. -/
theorem actual_resolution_map_consumer (q : ℕ)
    {M N : FieldCohomologyModule.{u, w} k Ω} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
        (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J).hom =
      (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
        HomologicalComplex.homologyMap
          (((fieldInvariantFunctor.{u, w} k Ω).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (InjectiveResolution.descHom f I J).hom) q :=
  by
    let φ : InjectiveResolution.Hom I J f := InjectiveResolution.descHom f I J
    have hφ : I.ι.f 0 ≫ φ.hom.f 0 = f ≫ J.ι.f 0 := by
      simpa only [CochainComplex.single₀_map_f_zero] using φ.ι_f_zero_comp_hom_f_zero
    exact fieldContinuousDerivedInvariantsResolutionIso_naturality.{u, w} k Ω q f I J φ.hom hφ

/-- Connecting comparison with arbitrary endpoint resolutions.

The continuous connecting map agrees through comparison with the right-derived invariant
boundary defined using any injective resolutions of the sequence's endpoint objects. -/
theorem actual_connector_resolution_consumer (n : ℕ)
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃) :
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).hom.app S.X₁ =
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫
      RightDerivedDelta.RDdelta (fieldInvariantFunctor.{u, w} k Ω) n S hS I₁ I₃ :=
  (fieldContinuousDerivedInvariantsIso_connecting.{u, w} k Ω n S hS).trans
    (congrArg ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫ ·)
      (Functor.RightDerived.rightDerivedConnecting_eq_endpoints
        (fieldInvariantFunctor.{u, w} k Ω) n S hS I₁ I₃))

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections
open CategoryTheory CategoryTheory.Limits
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Degree zero cohomology of the injective presentation cokernel.

For a coefficient `M`, take continuous cohomology in degree zero of the cokernel of its
canonical injective presentation. -/
def fieldInitialCokernelDomain (M : FieldCohomologyModule.{u, w} k Ω) : AddCommGrpCat.{max u w} :=
  (fieldContinuousCohomologyFunctor.{u, w} k Ω 0).obj (cokernel (Injective.ι M))

/-- Degree one cohomology of the coefficient.

The initial cokernel boundary target is the degree-one continuous cohomology object of `M`. -/
def fieldInitialCokernelCodomain (M : FieldCohomologyModule.{u, w} k Ω) : AddCommGrpCat.{max u w} :=
  (fieldContinuousCohomologyFunctor.{u, w} k Ω 1).obj M

/-- Initial boundary domain has the specified cokernel cohomology.

The named domain is degree-zero continuous cohomology of the canonical injective-presentation
cokernel. -/
theorem fieldInitialCokernelDomain_eq_original (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelDomain.{u, w} k Ω M =
      (fieldContinuousCohomologyFunctor.{u, w} k Ω 0).obj (cokernel (Injective.ι M)) := rfl

/-- Initial boundary target has the specified coefficient cohomology.

The named codomain is degree-one continuous cohomology of `M`. -/
theorem fieldInitialCokernelCodomain_eq_original (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelCodomain.{u, w} k Ω M =
      (fieldContinuousCohomologyFunctor.{u, w} k Ω 1).obj M := rfl

/-- Initial connecting map of an injective presentation.

The canonical injective cokernel sequence gives a boundary from its cokernel's degree-zero
cohomology to degree-one cohomology of `M`. -/
def fieldInitialCokernelBoundary (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelDomain.{u, w} k Ω M ⟶ fieldInitialCokernelCodomain.{u, w} k Ω M :=
  ContinuousCohomology.discreteCoefficientConnecting.{u, w}
    (G := InfiniteGalois.profiniteGalGrp k Ω)
    (ShortComplex.cokernelSequence (Injective.ι M))
    (fieldShortExact_discreteCoefficientExact.{u, w} k Ω
      (ShortComplex.cokernelSequence (Injective.ι M))
      (ShortComplex.shortExact_cokernelSequence (Injective.ι M))) 0

/-- Initial injective cokernel boundary is epi.

The initial boundary is an epimorphism because the middle coefficient of the presentation is
injective. -/
theorem fieldInitialCokernelBoundary_epi (M : FieldCohomologyModule.{u, w} k Ω) :
    Epi (fieldInitialCokernelBoundary.{u, w} k Ω M) :=
  by
    let C := FieldCohomologyModule.{u, w} k Ω
    let A := AddCommGrpCat.{max u w}
    let S : ShortComplex C := ShortComplex.cokernelSequence (Injective.ι M)
    let hS : S.ShortExact := ShortComplex.shortExact_cokernelSequence (Injective.ι M)
    let T : CohomologicalDeltaFunctor C A := fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω
    have h : Epi ((T.connecting 0).app ⟨S, hS⟩) :=
      fieldContinuousCokerConnecting_epi.{u, w} k Ω 0
        (M := M) (I := Injective.under M) (Injective.ι M)
    change Epi ((T.connecting 0).app ⟨S, hS⟩)
    exact h

/-- Every degree one class has an initial boundary preimage.

Every element of the initial boundary target is the image of an element in its cokernel
cohomology domain. -/
theorem original_initial_cokernel_preimage_consumer
    (M : FieldCohomologyModule.{u, w} k Ω)
    (a : fieldInitialCokernelCodomain.{u, w} k Ω M) :
    ∃ c : fieldInitialCokernelDomain.{u, w} k Ω M,
      (fieldInitialCokernelBoundary.{u, w} k Ω M).hom c = a := by
  let : Epi (fieldInitialCokernelBoundary.{u, w} k Ω M) :=
    fieldInitialCokernelBoundary_epi.{u, w} k Ω M
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance a

end AlgebraicGeometry.Scheme.DerivedSections

namespace AlgebraicGeometry.Scheme.DerivedSections

open CategoryTheory CategoryTheory.Limits
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Initial boundary is the specified continuous connecting map.

The named boundary equals the degree-zero continuous-coefficient connecting map of the
canonical injective cokernel sequence. -/
theorem fieldInitialCokernelBoundary_eq_original (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelBoundary.{u, w} k Ω M =
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω)
        (ShortComplex.cokernelSequence (Injective.ι M))
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω
          (ShortComplex.cokernelSequence (Injective.ι M))
          (ShortComplex.shortExact_cokernelSequence (Injective.ι M))) 0 := rfl

-- The full original law structure reached200000 in retained final gateV3.
/-- Full laws of the continuous derived invariant comparison.

These laws record the fixed cohomology functors, universality, normalized comparison, all
coefficient and resolution maps, endpoint boundaries, initial cokernel preimages, group maps
with coefficient intertwiners and single lifts, uniqueness, and lifted-sheaf naturality. -/
structure OriginalContinuousDerivedInvariantsLaws : Prop where
/-- Comparison record identifies the continuous cohomology functors.

Every degree functor is the continuous discrete-coefficient cohomology functor of the
specified profinite Galois group. -/
  original_functor : ∀ q, fieldContinuousCohomologyFunctor.{u, w} k Ω q =
    ContinuousCohomology.discreteCoefficientCohomologyFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω) q
/-- Comparison record gives continuous delta universality.

The continuous cohomology delta functor on the field coefficient category is universal. -/
  actual_hg_universal : CohomologicalDeltaFunctor.IsUniversal
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
/-- Comparison record gives derived invariant delta universality.

The right-derived invariant delta functor is universal. -/
  actual_rd_universal : CohomologicalDeltaFunctor.IsUniversal
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
    (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω)
/-- Comparison record has an all degree delta isomorphism.

The continuous and right-derived invariant delta functors admit the normalized isomorphism. -/
  one_delta_comparison : Nonempty (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω ≅
    fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω)
/-- Comparison record fixes the zero degree invariant coordinate.

The degree-zero comparison followed by the derived-zero coordinate equals the continuous
invariant coordinate. -/
  zero_normalization : (fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom ≫
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom
/-- Comparison record evaluates zero cocycles at the identity.

For every coefficient and continuous zero cocycle, the compared invariant value is the
homogeneous cochain value at `1`. -/
  original_zero_value : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (c : ContinuousCohomology.cocycles
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) 0),
    ((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app M
      ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom.app M
        (ContinuousCohomology.π _ 0 c))).val =
      ((TopRep.homogeneousCochains _).iCycles 0 c).val 1
/-- Comparison record is natural for all coefficient arrows.

The degreewise comparisons commute with every coefficient map and its derived-invariant map. -/
  coefficient_naturality : ∀ q (M N : FieldCohomologyModule.{u, w} k Ω) (f : M ⟶ N),
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
        (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app N =
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app M ≫
        ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map f
/-- Comparison record respects all coefficient boundaries.

Every short exact coefficient connecting map commutes with the comparisons in adjacent
degrees. -/
  coefficient_connectors : ∀ n (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω))
    (hS : S.ShortExact),
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).hom.app S.X₁ =
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫
      (Functor.rightDerivedConnecting (fieldInvariantFunctor.{u, w} k Ω) n).app
        ⟨S, hS⟩
/-- Comparison record respects all augmented resolution morphisms.

For any resolution cochain map agreeing with the coefficient map on coaugmentation, the
continuous-to-invariant-resolution comparison square commutes. -/
  every_augmented_resolution_map : ∀ q (M N : FieldCohomologyModule.{u, w} k Ω)
    (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex), I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 →
      (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
          (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J).hom =
        (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
          HomologicalComplex.homologyMap
            (((fieldInvariantFunctor.{u, w} k Ω).mapHomologicalComplex
              (ComplexShape.up ℕ)).map φ) q
/-- Comparison record is compatible with every resolution choice.

The comparison coordinates for two injective resolutions agree through their canonical
cohomology comparison. -/
  every_resolution_choice : ∀ q (M : FieldCohomologyModule.{u, w} k Ω)
    (I J : InjectiveResolution M),
    fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I ≪≫
        InjectiveResolution.cohomologyComparisonIso I J (fieldInvariantFunctor.{u, w} k Ω) q =
      fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J
/-- Comparison record retains arbitrary endpoint boundary coordinates.

For every short exact sequence and every pair of endpoint injective resolutions, continuous
and right-derived invariant boundaries commute through the comparison. -/
  every_endpoint_connector : ∀ n
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃),
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).hom.app S.X₁ =
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫
      RightDerivedDelta.RDdelta (fieldInvariantFunctor.{u, w} k Ω) n S hS I₁ I₃
/-- Comparison record supplies initial boundary preimages.

Every degree-one coefficient cohomology element has a preimage under the initial injective-
cokernel boundary. -/
  initial_cokernel_preimage : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (a : fieldInitialCokernelCodomain.{u, w} k Ω M),
    ∃ c : fieldInitialCokernelDomain.{u, w} k Ω M,
      (fieldInitialCokernelBoundary.{u, w} k Ω M).hom c = a
/-- Comparison record fixes initial boundary objects.

The initial domain is degree-zero cohomology of the injective-presentation cokernel, and its
codomain is degree-one cohomology of the coefficient. -/
  initial_original_objects : ∀ (M : FieldCohomologyModule.{u, w} k Ω),
    fieldInitialCokernelDomain.{u, w} k Ω M =
        (fieldContinuousCohomologyFunctor.{u, w} k Ω 0).obj (cokernel (Injective.ι M)) ∧
      fieldInitialCokernelCodomain.{u, w} k Ω M =
        (fieldContinuousCohomologyFunctor.{u, w} k Ω 1).obj M
/-- Comparison record respects all continuous Galois group maps.

For independently ranked source and target fields, every continuous Galois-group restriction
commutes with the degreewise derived-invariant comparisons. -/
  every_group_map : ∀ (k' Ω' : Type v) [Field k'] [Field Ω'] [Algebra k' Ω']
    [IsSepClosure k' Ω'] (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ*
      InfiniteGalois.profiniteGalGrp k Ω) n,
    fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ ≫
        Functor.whiskerLeft (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
          (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom =
      (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom ≫
        fieldDerivedInvariantsRestriction.{u, v, w} k Ω k' Ω' n φ
/-- Comparison record respects all group coefficient intertwiners.

The comparison square holds for every continuous group homomorphism together with an
equivariant coefficient representation map. -/
  every_group_coefficient_map : ∀ (k' Ω' : Type v) [Field k'] [Field Ω'] [Algebra k' Ω']
    [IsSepClosure k' Ω'] (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ*
      InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, max v w} k Ω)
    (N : FieldCohomologyModule.{v, max u w} k' Ω')
    (f : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) n,
    ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
        (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f n) ≫
      (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom.app N =
    (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom.app M ≫
      fieldDerivedInvariantsGroupCoefficientMap.{u, v, w} k Ω k' Ω' n φ f
/-- Comparison record preserves all single lift coefficient values.

For independently ranked coefficients, a single lift of each coefficient sends the intertwiner
value to its lift and gives the comparison square in every degree. -/
  every_native_one_lift_map : ∀ (k' Ω' : Type v) [Field k'] [Field Ω'] [Algebra k' Ω']
    [IsSepClosure k' Ω'] (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ*
      InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, w} k Ω) (N : FieldCohomologyModule.{v, w} k' Ω')
    (f : ContinuousCohomology.nativeCoefficientIntertwiner.{0, u, v, w}
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M)
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N) φ),
    let M' : FieldCohomologyModule.{u, max v w} k Ω :=
      (ContinuousCohomology.discreteCoefficientULiftFunctor.{u, v, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M
    let N' : FieldCohomologyModule.{v, max u w} k' Ω' :=
      (ContinuousCohomology.discreteCoefficientULiftFunctor.{v, u, w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N
    let f' : TopRep.res φ
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M') ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj N' :=
      ContinuousCohomology.nativeULiftGroupIntertwiner.{0, u, v, w} φ.toMonoidHom f
    (∀ x : (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M,
      f'.hom (ULift.up.{v, max u w} x) = ULift.up.{u, max v w} (f x)) ∧
    ∀ n, ContinuousCohomology.discreteCoefficientForget.{max u (max v w)}.map
        (ContinuousCohomology.nativeGroupCoefficientCohomologyMap.{0, u, v, w} φ f' n) ≫
      (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom.app N' =
    (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom.app M' ≫
      fieldDerivedInvariantsGroupCoefficientMap.{u, v, w} k Ω k' Ω' n φ f'
/-- Comparison record gives uniqueness of normalized families.

A family of natural transformations compatible with connecting maps and normalized in degree
zero equals the canonical comparison in every degree. -/
  unique_normalized_family : ∀
    (f : ∀ n, fieldContinuousCohomologyFunctor.{u, w} k Ω n ⟶
      (fieldInvariantFunctor.{u, w} k Ω).rightDerived n),
    (∀ n (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact),
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
          (G := InfiniteGalois.profiniteGalGrp k Ω) S
          (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
        (f (n + 1)).app S.X₁ = (f n).app S.X₃ ≫
          (Functor.rightDerivedConnecting (fieldInvariantFunctor.{u, w} k Ω) n).app
            ⟨S, hS⟩) →
    f 0 ≫ (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom →
    ∀ n, f n = (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom
/-- Comparison record respects all lifted sheaf morphisms.

The field comparison on lifted geometric fibers commutes with each coefficient sheaf morphism
and its derived-invariant map. -/
  original_sheaf_map : ∀ q
    (F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) (f : F ⟶ F'),
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)) ≫
      (originalFieldContinuousDerivedInvariantsIso.{u, w} k Ω q F').hom =
    (originalFieldContinuousDerivedInvariantsIso.{u, w} k Ω q F).hom ≫
      ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f))

/-- Continuous field cochains satisfy the full derived invariant laws.

The continuous-cohomology comparison satisfies the complete coefficient, resolution,
connecting, initial cokernel, group-map, single-lift, uniqueness, and lifted-sheaf laws. -/
theorem original_continuous_cochains_compute_derived_invariants :
    OriginalContinuousDerivedInvariantsLaws.{u, v, w} k Ω where
  original_functor _ := rfl
  actual_hg_universal := fieldContinuousCohomologyDeltaFunctor_isUniversal.{u, w} k Ω
  actual_rd_universal := fieldDerivedInvariantsDeltaFunctor_isUniversal.{u, w} k Ω
  one_delta_comparison := ⟨fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω⟩
  zero_normalization := fieldContinuousDerivedInvariantsIso_zero.{u, w} k Ω
  original_zero_value := fieldContinuousDerivedInvariantsIso_zero_cycle_value.{u, w} k Ω
  coefficient_naturality := fun q _ _ =>
    fieldContinuousDerivedInvariantsIso_naturality.{u, w} k Ω q
  coefficient_connectors := fieldContinuousDerivedInvariantsIso_connecting.{u, w} k Ω
  every_augmented_resolution_map := fun q _ _ =>
    fieldContinuousDerivedInvariantsResolutionIso_naturality.{u, w} k Ω q
  every_resolution_choice := fun q _ =>
    fieldContinuousDerivedInvariantsResolutionIso_choice.{u, w} k Ω q
  every_endpoint_connector := actual_connector_resolution_consumer.{u, w} k Ω
  initial_cokernel_preimage := original_initial_cokernel_preimage_consumer.{u, w} k Ω
  initial_original_objects := fun M =>
    ⟨fieldInitialCokernelDomain_eq_original.{u, w} k Ω M,
      fieldInitialCokernelCodomain_eq_original.{u, w} k Ω M⟩
  every_group_map := fun _ _ _ _ _ _ φ n =>
    fieldContinuousDerivedInvariantsIso_group_naturality.{u, v, w} k Ω _ _ n φ
  every_group_coefficient_map := fun k' Ω' _ _ _ _ φ M N f n =>
    fieldContinuousDerivedInvariantsIso_group_coefficient_naturality.{u, v, w}
      k Ω k' Ω' n φ (M := M) (N := N) f
  every_native_one_lift_map := fun k' Ω' _ _ _ _ φ M N f =>
    fieldContinuousDerivedInvariantsIso_native_group_naturality.{u, v, w}
      k Ω k' Ω' φ M N f
  unique_normalized_family := fieldContinuousDerivedInvariantsIso_unique.{u, w} k Ω
  original_sheaf_map := fun q _ _ =>
    originalFieldContinuousDerivedInvariantsIso_naturality.{u, w} k Ω q

end AlgebraicGeometry.Scheme.DerivedSections
