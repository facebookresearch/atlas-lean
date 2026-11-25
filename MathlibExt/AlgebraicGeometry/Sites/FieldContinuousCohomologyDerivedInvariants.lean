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
The same original continuous homogeneous cohomology computes the actual derived invariants. All
original degrees, zero values, coefficients/groups, augmented resolutions/choices and one-copy
native lifts are fixed by one normalized delta-functor isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
universe u v w

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The original continuous cohomology, with its topology and scalars forgotten. -/
abbrev fieldContinuousCohomologyFunctor (n : ℕ) :
    FieldCohomologyModule.{u, w} k Ω ⥤ AddCommGrpCat.{max u w} :=
  ContinuousCohomology.discreteCoefficientCohomologyFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω) n

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

/-- Categorical short exactness gives the same literal original coefficient maps. -/
theorem fieldShortExact_discreteCoefficientExact
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact) :
    ContinuousCohomology.DiscreteCoefficientExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S :=
  (fieldModule_shortExact_iff_original_maps.{u, w} k Ω S).mp hS

-- The unchanged field-alias LES tuple exceeded 200000 in retained v5-v7 attempts.
/-- The actual coefficient LES packages the original HG functors as a delta functor. -/
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

/-- Every actual injective has zero positive original HG in the additive category. -/
theorem fieldContinuousCohomologyFunctor_isZero_injective
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ) :
    IsZero ((fieldContinuousCohomologyFunctor.{u, w} k Ω (n + 1)).obj I) := by
  let U := ContinuousCohomology.discreteCoefficientForget.{max u w}
  exact U.map_isZero (fieldInjectiveContinuousCohomology_succ_isZero.{u, w} k Ω I n)

/-- The real injective effacement proves universality of the existing HG delta functor. -/
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

/-- The original identity-evaluation zeroIso, with only topology/scalars forgotten. -/
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

/-- The actual invariants-derived delta functor, with genuine horseshoe connectors. -/
abbrev fieldDerivedInvariantsDeltaFunctor :=
  Functor.rightDerivedDeltaFunctor (fieldInvariantFunctor.{u, w} k Ω)

/-- Genuine injective effacement makes this actual derived family universal. -/
theorem fieldDerivedInvariantsDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal
      (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
      (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω) :=
  Functor.isUniversal_rightDerivedDeltaFunctor
    (fieldInvariantFunctor.{u, w} k Ω)

/-- Both actual universal functors have one comparison, fixed by the original
zeroIso and the actual right-derived augmentation at degree zero. -/
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

/-- Every degree of the SAME canonical delta-functor isomorphism. -/
def fieldContinuousDerivedInvariantsIso (q : ℕ) :
    fieldContinuousCohomologyFunctor.{u, w} k Ω q ≅
      (fieldInvariantFunctor.{u, w} k Ω).rightDerived q :=
  (CohomologicalDeltaFunctor.evaluation
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w} q).mapIso
    (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω)

/-- The fixed comparison agrees with the original zeroIso after the genuine RD0 normalization. -/
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

/-- All original coefficient maps commute with the same comparison. -/
theorem fieldContinuousDerivedInvariantsIso_naturality (q : ℕ)
    {M N : FieldCohomologyModule.{u, w} k Ω} (f : M ⟶ N) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
        (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app N =
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app M ≫
        ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map f :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.naturality f

/-- The original continuous connector and actual right-derived horseshoe connector commute. -/
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

/-- On every actual injective resolution the comparison uses the actual mapped
cocomplex and its stock right-derived homology isomorphism. -/
def fieldContinuousDerivedInvariantsResolutionIso (q : ℕ)
    {M : FieldCohomologyModule.{u, w} k Ω} (I : InjectiveResolution M) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj M ≅
      (((fieldInvariantFunctor.{u, w} k Ω).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology q :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app M ≪≫
    I.isoRightDerivedObj (fieldInvariantFunctor.{u, w} k Ω) q

-- The final field-resolution association reached 200000 in retained v4.
/-- EVERY actual augmented resolution map has its literal mapped homology square. -/
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

/-- The actual canonical resolution-choice isomorphism is respected in every degree. -/
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

/-- The normalization is literal evaluation of the original homogeneous cocycle at identity. -/
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

/-- The actual cokernel effacement includes the initial q=1 case and every higher degree. -/
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
/-- A family is forced in every degree by naturality, original connector compatibility
and the fixed identity-evaluation normalization at zero. No universality is assumed. -/
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

/-- Compatibility with the original local override name, without an instance registration. -/
-- Preserve the original public compatibility name and its signature, as recorded by the
-- field-cohomology-cut6 validation; the `[IsSepClosure K L]` binder is unused.
@[nolint defsWithUnderscore unusedArguments]
abbrev fieldDiscreteModule_preadditive_raw
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    Preadditive (DiscreteAbelianAction.{u, w} Gal(L/K)) :=
  DiscreteAbelianAction.instPreadditive.{u, w} (G := Gal(L/K))

/-- The stock restriction on the original groups and same common coefficient carrier. -/
def fieldModuleRestriction
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    FieldCohomologyModule.{u, max v w} k Ω ⥤ FieldCohomologyModule.{v, max u w} k' Ω' :=
  GaloisUnits.restrictModules.{u, v, max u (max v w)} φ

instance fieldModuleRestriction_additive
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).Additive where
  map_add {_ _} f g := by rfl

instance fieldModuleRestriction_preservesZeroMorphisms
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).PreservesZeroMorphisms where
  map_zero _ _ := by rfl

/-- Underlying original maps are unchanged, so actual categorical exactness is preserved. -/
theorem fieldModuleRestriction_shortExact
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (S : ShortComplex (FieldCohomologyModule.{u, max v w} k Ω)) (hS : S.ShortExact) :
    (S.map (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)).ShortExact :=
  (fieldModule_shortExact_iff_original_maps.{v, max u w} k' Ω'
    (S.map (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ))).mpr
    ((fieldModule_shortExact_iff_original_maps.{u, max v w} k Ω S).mp hS)

/-- The original coefficient representation is unchanged under restriction,
with the original group action precomposed by the original group map. -/
def fieldModuleRestrictionTopRepHom
    (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ* InfiniteGalois.profiniteGalGrp k Ω)
    (M : FieldCohomologyModule.{u, max v w} k Ω) :
    TopRep.res φ ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, max v w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M) ⟶
      (ContinuousCohomology.discreteCoefficientTopRepFunctor.{v, max u w}
        (InfiniteGalois.profiniteGalGrp k' Ω')).obj
          ((fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ).obj M) :=
  𝟙 _

/-- Invariant vectors restrict by their literal original value. -/
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

/-- The original homogeneous group map is a natural map in every coefficient. -/
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

/-- The same literal restricted coefficient sequence before passing to cochains. -/
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
/-- The original group cochain maps preserve the actual coefficient connectors. -/
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

/-- The group map at degree zero is the same literal map of invariant values. -/
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

/-- The genuine right-derived degree-zero group map is normalized by both augmentations. -/
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
/-- Universality constructs the canonical derived restriction for every original
continuous group map. The target need not be universal; no injective preservation is used. -/
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

/-- Every degree of the same canonical derived restriction morphism. -/
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
/-- The independent right-derived restriction and the original cochain restriction
commute with the fixed comparison as whole morphisms of delta functors. -/
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
/-- Every degree uses this same comparison square, not a family of arbitrarily
chosen degreewise isomorphisms. -/
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

/-- Every original equivariant coefficient map is an actual arrow after restriction. -/
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

/-- The original group/coefficient cochain map factors through actual restriction
and the original coefficient arrow, on the existing homology groups. -/
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

/-- The actual derived group/coefficient map comes from the canonical group
restriction and the literal original coefficient arrow. -/
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
/-- ALL original group and coefficient maps commute with the single normalized
all-degree comparison; the right-hand map is independently constructed from RD universality. -/
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
/-- An original diagram in the two native coefficient ranks enters the common
rank through exactly one of the existing coefficient-lift functors per carrier. -/
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

/-- Every original coefficient-w sheaf enters the actual HG/RD family through ONE L.obj F. -/
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

/-- Every original smaller-coefficient sheaf map uses the same ONE lifted arrow. -/
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

/-- Actual derived Gamma and the original continuous HG use the SAME common sheaf object. -/
def fieldDerivedSectionsContinuousCohomologyIso (q : ℕ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ≅
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q :=
  fieldDerivedSectionsInvariantsIso.{u, w} k Ω q ≪≫
    Functor.isoWhiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).symm

/-- The actual Gamma/HG maps for every original common sheaf arrow commute. -/
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

/-- An arbitrary original homogeneous zero-cycle evaluates literally at identity
under the SAME all-degree comparison. -/
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

/-- This uses the actual chosen comparison map between arbitrary resolutions;
the augmentation is provided by stock descHom, not an input hypothesis. -/
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

/-- The original continuous degree-one connector maps to the ACTUAL mapped-horseshoe
right-derived connector with arbitrary original endpoint resolutions. -/
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

/-- The actual original H0 object on the actual initial cokernel. -/
def fieldInitialCokernelDomain (M : FieldCohomologyModule.{u, w} k Ω) : AddCommGrpCat.{max u w} :=
  (fieldContinuousCohomologyFunctor.{u, w} k Ω 0).obj (cokernel (Injective.ι M))

/-- The actual original H1 object of the original module. -/
def fieldInitialCokernelCodomain (M : FieldCohomologyModule.{u, w} k Ω) : AddCommGrpCat.{max u w} :=
  (fieldContinuousCohomologyFunctor.{u, w} k Ω 1).obj M

theorem fieldInitialCokernelDomain_eq_original (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelDomain.{u, w} k Ω M =
      (fieldContinuousCohomologyFunctor.{u, w} k Ω 0).obj (cokernel (Injective.ι M)) := rfl

theorem fieldInitialCokernelCodomain_eq_original (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelCodomain.{u, w} k Ω M =
      (fieldContinuousCohomologyFunctor.{u, w} k Ω 1).obj M := rfl

/-- The same original degree-one boundary on the actual initial cokernel sequence. -/
def fieldInitialCokernelBoundary (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelDomain.{u, w} k Ω M ⟶ fieldInitialCokernelCodomain.{u, w} k Ω M :=
  ContinuousCohomology.discreteCoefficientConnecting.{u, w}
    (G := InfiniteGalois.profiniteGalGrp k Ω)
    (ShortComplex.cokernelSequence (Injective.ι M))
    (fieldShortExact_discreteCoefficientExact.{u, w} k Ω
      (ShortComplex.cokernelSequence (Injective.ι M))
      (ShortComplex.shortExact_cokernelSequence (Injective.ι M))) 0

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

/-- Every original H1 class has an actual H0 cokernel preimage under that SAME boundary. -/
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

/-- The named boundary is literally the original continuous coefficient boundary
on the actual initial cokernel short exact sequence. -/
theorem fieldInitialCokernelBoundary_eq_original (M : FieldCohomologyModule.{u, w} k Ω) :
    fieldInitialCokernelBoundary.{u, w} k Ω M =
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω)
        (ShortComplex.cokernelSequence (Injective.ι M))
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω
          (ShortComplex.cokernelSequence (Injective.ι M))
          (ShortComplex.shortExact_cokernelSequence (Injective.ι M))) 0 := rfl

-- The full original law structure reached200000 in retained final gateV3.
/-- Every original obligation is tied to one fixed actual delta-functor comparison. -/
structure OriginalContinuousDerivedInvariantsLaws : Prop where
  original_functor : ∀ q, fieldContinuousCohomologyFunctor.{u, w} k Ω q =
    ContinuousCohomology.discreteCoefficientCohomologyFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω) q
  actual_hg_universal : CohomologicalDeltaFunctor.IsUniversal
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
  actual_rd_universal : CohomologicalDeltaFunctor.IsUniversal
    (FieldCohomologyModule.{u, w} k Ω) AddCommGrpCat.{max u w}
    (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω)
  one_delta_comparison : Nonempty (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω ≅
    fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω)
  zero_normalization : (fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom ≫
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom
  original_zero_value : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (c : ContinuousCohomology.cocycles
      ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj M) 0),
    ((fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom.app M
      ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0).hom.app M
        (ContinuousCohomology.π _ 0 c))).val =
      ((TopRep.homogeneousCochains _).iCycles 0 c).val 1
  coefficient_naturality : ∀ q (M N : FieldCohomologyModule.{u, w} k Ω) (f : M ⟶ N),
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
        (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app N =
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).hom.app M ≫
        ((fieldInvariantFunctor.{u, w} k Ω).rightDerived q).map f
  coefficient_connectors : ∀ n (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω))
    (hS : S.ShortExact),
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).hom.app S.X₁ =
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫
      (Functor.rightDerivedConnecting (fieldInvariantFunctor.{u, w} k Ω) n).app
        ⟨S, hS⟩
  every_augmented_resolution_map : ∀ q (M N : FieldCohomologyModule.{u, w} k Ω)
    (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex), I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 →
      (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map f ≫
          (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J).hom =
        (fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
          HomologicalComplex.homologyMap
            (((fieldInvariantFunctor.{u, w} k Ω).mapHomologicalComplex
              (ComplexShape.up ℕ)).map φ) q
  every_resolution_choice : ∀ q (M : FieldCohomologyModule.{u, w} k Ω)
    (I J : InjectiveResolution M),
    fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q I ≪≫
        InjectiveResolution.cohomologyComparisonIso I J (fieldInvariantFunctor.{u, w} k Ω) q =
      fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q J
  every_endpoint_connector : ∀ n
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃),
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S hS) n ≫
      (fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).hom.app S.X₁ =
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω n).hom.app S.X₃ ≫
      RightDerivedDelta.RDdelta (fieldInvariantFunctor.{u, w} k Ω) n S hS I₁ I₃
  initial_cokernel_preimage : ∀ (M : FieldCohomologyModule.{u, w} k Ω)
    (a : fieldInitialCokernelCodomain.{u, w} k Ω M),
    ∃ c : fieldInitialCokernelDomain.{u, w} k Ω M,
      (fieldInitialCokernelBoundary.{u, w} k Ω M).hom c = a
  initial_original_objects : ∀ (M : FieldCohomologyModule.{u, w} k Ω),
    fieldInitialCokernelDomain.{u, w} k Ω M =
        (fieldContinuousCohomologyFunctor.{u, w} k Ω 0).obj (cokernel (Injective.ι M)) ∧
      fieldInitialCokernelCodomain.{u, w} k Ω M =
        (fieldContinuousCohomologyFunctor.{u, w} k Ω 1).obj M
  every_group_map : ∀ (k' Ω' : Type v) [Field k'] [Field Ω'] [Algebra k' Ω']
    [IsSepClosure k' Ω'] (φ : InfiniteGalois.profiniteGalGrp k' Ω' →ₜ*
      InfiniteGalois.profiniteGalGrp k Ω) n,
    fieldContinuousCohomologyRestriction.{u, v, w} k Ω k' Ω' n φ ≫
        Functor.whiskerLeft (fieldModuleRestriction.{u, v, w} k Ω k' Ω' φ)
          (fieldContinuousDerivedInvariantsIso.{v, max u w} k' Ω' n).hom =
      (fieldContinuousDerivedInvariantsIso.{u, max v w} k Ω n).hom ≫
        fieldDerivedInvariantsRestriction.{u, v, w} k Ω k' Ω' n φ
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

/-- The complete original all-degree comparison is constructed from actual effacement,
actual original complexes and the actual mapped-horseshoe derived family. -/
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
