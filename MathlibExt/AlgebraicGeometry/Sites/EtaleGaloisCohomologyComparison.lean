/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldSiteModuleCohomologyNaturality

/-!
# Étale and Galois cohomology over a field

For every sheaf of abelian groups in the common universe, the original small
étale cohomology is identified with the original continuous homogeneous
cohomology of its geometric fiber. The comparison is the canonical Ext-to-Γ
map followed by the existing Γ-to-continuous-cohomology isomorphism.

The same maps respect every coefficient arrow, the original Yoneda connecting
maps, and the independently constructed field pullback. No coefficient lift,
cochain family, connecting map, or comparison square is supplied as an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

private theorem comparisonSquareValue.{v}
    {A B C D : AddCommGrpCat.{v}}
    {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ C} {i : C ⟶ D}
    (comm : f ≫ g = h ≫ i) (x : A) : g (f x) = i (h x) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (C := AddCommGrpCat.{v}) comm x

private theorem comparisonCompositionValue.{v}
    {A B C : AddCommGrpCat.{v}} {f : A ⟶ C} {g : A ⟶ B} {h : B ⟶ C}
    (comm : f = g ≫ h) (x : A) : f x = h (g x) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (C := AddCommGrpCat.{v}) comm x

private theorem comparisonDeltaConnector.{cU, cV, dU, dV}
    {C : Type cU} {D : Type dU} [Category.{cV} C] [Preadditive C]
    [Category.{dV} D] [Preadditive D]
    {T T' : CohomologicalDeltaFunctor C D} (e : T ≅ T') (q : ℕ)
    (S : ShortComplex.ShortExactSequences C) :
    (T.connecting q).app S ≫
        (CohomologicalDeltaFunctor.Hom.app e.hom (q + 1)).app S.obj.X₁ =
      (CohomologicalDeltaFunctor.Hom.app e.hom q).app S.obj.X₃ ≫
        (T'.connecting q).app S :=
  DeltaFunctor.System.comm e.hom.hom q S

private theorem comparisonCanonicalDeltaHom_app.{cU, cV, bU, bV, dU, dV}
    {C : Type cU} [Category.{cV} C] [Abelian C] [HasInjectiveResolutions C]
    {B : Type bU} [Category.{bV} B] [Abelian B] [HasInjectiveResolutions B]
    {D : Type dU} [Category.{dV} D] [Abelian D]
    (R : C ⥤ B) [R.Additive] [R.PreservesInjectiveObjects] [R.PreservesHomology]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (I : B ⥤ D) [I.Additive]
    {P : C ⥤ D} [P.Additive] (α : P ≅ R ⋙ I)
    {T : CohomologicalDeltaFunctor B D} (ε : T ≅ Functor.rightDerivedDeltaFunctor I)
    (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app
      ((Functor.RightDerived.precompDeltaIsoOfIso R I α ≪≫
        (CohomologicalDeltaFunctor.precomposeFunctor R
          (Functor.RightDerived.precompShortExact R)).mapIso ε.symm).hom) q =
      (Functor.rightDerivedPrecompIsoOfIso R I α q ≪≫
        Functor.isoWhiskerLeft R
          ((CohomologicalDeltaFunctor.evaluation B D q).mapIso ε).symm).hom := by
  dsimp only [CohomologicalDeltaFunctor.precomposeFunctor]
  rw [Iso.trans_hom, Functor.mapIso_hom, CohomologicalDeltaFunctor.Hom.comp_app,
    Functor.RightDerived.precompDeltaIsoOfIso_hom_app]
  rfl

private theorem comparisonRightDerivedConnector.{cU, cV, dU, dV}
    {C : Type cU} [Category.{cV} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type dU} [Category.{dV} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    (q : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (F.rightDerivedDeltaFunctor.connecting q).app S =
      (F.rightDerivedConnecting q).app S := rfl

private theorem comparisonSquareSelectors.{v}
    {A B C D : AddCommGrpCat.{v}}
    {f f' : A ⟶ B} {g g' : B ⟶ D} {h h' : A ⟶ C} {i i' : C ⟶ D}
    (hf : f = f') (hg : g = g') (hh : h = h') (hi : i = i')
    (comm : f ≫ g = h ≫ i) :
    f' ≫ g' = h' ≫ i' :=
  (congrArg₂ (fun (f : A ⟶ B) (g : B ⟶ D) => f ≫ g) hf hg).symm.trans
    (comm.trans (congrArg₂ (fun (h : A ⟶ C) (i : C ⟶ D) => h ≫ i) hh hi))

private theorem comparisonTargetObjectTransport.{v}
    {A B B' : AddCommGrpCat.{v}} (hB : B = B')
    {f : A ⟶ B} {g : A ⟶ B'} (hf : HEq f g) :
    f ≫ eqToHom hB = g := by
  cases hB
  simpa only [eqToHom_refl, Category.comp_id] using eq_of_heq hf

private theorem comparisonHomObjectTransport.{v}
    {A A' B B' : AddCommGrpCat.{v}} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (hf : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  cases hA
  cases hB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using eq_of_heq hf

private theorem comparisonSquareObjectTransport.{v}
    {A B C₀ D₀ C D : AddCommGrpCat.{v}}
    (hC : C₀ = C) (hD : D₀ = D)
    {f : A ⟶ B} {g : B ⟶ D₀} {h : A ⟶ C₀} {i : C₀ ⟶ D₀}
    (comm : f ≫ g = h ≫ i) :
    f ≫ (g ≫ eqToHom hD) =
      (h ≫ eqToHom hC) ≫ (eqToHom hC.symm ≫ i ≫ eqToHom hD) := by
  cases hC
  cases hD
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using comm

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
attribute [local instance] IsSepClosure.sep_closed

local instance fieldEtaleGeometricStalkAdditive :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).Additive :=
  fieldGeometricStalkGaloisFunctor_additive.{u, w} k Ω

local instance fieldEtaleGeometricStalkPreservesZero :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).PreservesZeroMorphisms := by
  infer_instance

/-- The original small étale cohomology, through its canonical derived-Γ map,
is identified with continuous cohomology of the same geometric fiber. -/
def fieldEtaleContinuousEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+
      (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
  (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q).trans
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w}
      k Ω q).app Q).addCommGroupIsoToAddEquiv

/-- The comparison uses the literal canonical Γ map and the accepted native component. -/
theorem fieldEtaleContinuousEquiv_apply
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleContinuousEquiv.{u, w} k Ω Q q x =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app Q
        (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q x) := rfl

/-- The right-hand object is the original homogeneous-cochain homology of the
same fiber module, with the original scalar, group, and coefficient universe indices. -/
theorem fieldEtaleContinuousEquiv_native_model
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
      ContinuousCohomology.discreteCoefficientForget.{max u w}.obj
        ((TopRep.homogeneousCochains.{0, u, w}
          ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
            (InfiniteGalois.profiniteGalGrp k Ω)).obj
              ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))).homology q) := rfl

/-- Every actual sheaf arrow is compared with its actual geometric-fiber coefficient arrow. -/
theorem fieldEtaleContinuousEquiv_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleContinuousEquiv.{u, w} k Ω Q' q (Sheaf.H.map f q x) =
      (fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f)
        (fieldEtaleContinuousEquiv.{u, w} k Ω Q q x) := by
  have hv := comparisonSquareValue
    (fieldDerivedSectionsContinuousCohomologyIso_naturality.{u, w} k Ω q f)
    (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q x)
  change (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app Q'
      (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q' q
        (Sheaf.H.map f q x)) = _
  exact (congrArg
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app Q')
    (CanonicalLongExactSequence.canonicalEquiv_naturality.{u, w}
      (Spec (.of k)) f q x)).trans hv

/-- The coefficient map on the right is literally homology of the original
homogeneous-cochain map of the actual geometric-fiber arrow. -/
theorem fieldEtaleContinuousEquiv_naturality_original_map
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleContinuousEquiv.{u, w} k Ω Q' q (Sheaf.H.map f q x) =
      ContinuousCohomology.discreteCoefficientForget.{max u w}.map
        (HomologicalComplex.homologyMap
          ((ContinuousCohomology.homogeneousCochainsFunctor.{0, u, w}
            (k := ℤ) (G := InfiniteGalois.profiniteGalGrp k Ω)).map
              ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
                (InfiniteGalois.profiniteGalGrp k Ω)).map
                  ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map f))) q)
        (fieldEtaleContinuousEquiv.{u, w} k Ω Q q x) :=
  fieldEtaleContinuousEquiv_naturality.{u, w} k Ω f q x

/-- The actual continuous-cohomology delta functor on sheaves is the target of
the accepted Γ/native delta isomorphism. -/
def fieldGeometricFiberContinuousDeltaFunctor :
    CohomologicalDeltaFunctor
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      AddCommGrpCat.{max u w} :=
  CohomologicalDeltaFunctor.precompose
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)

/-- Every degree uses the same geometric fiber followed by original continuous cohomology. -/
theorem fieldGeometricFiberContinuousDeltaFunctor_T (q : ℕ) :
    (fieldGeometricFiberContinuousDeltaFunctor.{u, w} k Ω).T q =
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q := rfl

private def fieldEtaleCanonicalDeltaIso :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedDeltaFunctor ≅
      CohomologicalDeltaFunctor.precompose
        (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact
          (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) :=
  Functor.RightDerived.precompDeltaIsoOfIso
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (fieldInvariantFunctor.{u, w} k Ω)
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) ≪≫
    (CohomologicalDeltaFunctor.precomposeFunctor
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (Functor.RightDerived.precompShortExact
        (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))).mapIso
      (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω).symm

private theorem fieldEtaleCanonicalDeltaIso_hom_app (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldEtaleCanonicalDeltaIso.{u, w} k Ω).hom q =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom := by
  have h := comparisonCanonicalDeltaHom_app
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldInvariantFunctor.{u, w} k Ω) (fieldGlobalSectionsInvariantsIso.{u, w} k Ω)
    (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω) q
  dsimp only [fieldEtaleCanonicalDeltaIso, fieldDerivedSectionsContinuousCohomologyIso,
    fieldDerivedSectionsInvariantsIso, fieldContinuousDerivedInvariantsIso,
    CohomologicalDeltaFunctor.precomposeFunctor, FieldCohomologyModule] at h ⊢
  exact h


set_option backward.isDefEq.respectTransparency false in
private theorem fieldEtaleGammaNativeConnecting
    (S : ShortComplex
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ) :
    let T : ShortComplex (FieldCohomologyModule.{u, w} k Ω) :=
      S.map (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    let hT : T.ShortExact := Functor.RightDerived.precompShortExact
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) S hS
    (Functor.rightDerivedConnecting
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).app ⟨S, hS⟩ ≫
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω (q + 1)).hom.app S.X₁ =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app S.X₃ ≫
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) T
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω T hT) q := by
  intro T hT
  let SE : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) := ⟨S, hS⟩
  let e := fieldEtaleCanonicalDeltaIso.{u, w} k Ω
  let P := CohomologicalDeltaFunctor.precompose
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)
  let A : AddCommGrpCat.{max u w} :=
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).obj S.X₃
  let B : AddCommGrpCat.{max u w} :=
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{max u w}).rightDerived (q + 1)).obj S.X₁
  let C₀ : AddCommGrpCat.{max u w} := (P.T q).obj S.X₃
  let D₀ : AddCommGrpCat.{max u w} := (P.T (q + 1)).obj S.X₁
  let C : AddCommGrpCat.{max u w} :=
    (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj S.X₃)
  let D : AddCommGrpCat.{max u w} :=
    (fieldContinuousCohomologyFunctor.{u, w} k Ω (q + 1)).obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj S.X₁)
  have hC : C₀ = C := rfl
  have hD : D₀ = D := rfl
  let f : A ⟶ B :=
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology
      AddCommGrpCat.{max u w}).rightDerivedDeltaFunctor.connecting q).app SE
  let f' : A ⟶ B :=
    (Functor.rightDerivedConnecting
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).app SE
  let g₀ : B ⟶ D₀ :=
    (CohomologicalDeltaFunctor.Hom.app e.hom (q + 1)).app S.X₁
  let g' : B ⟶ D :=
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω (q + 1)).hom.app S.X₁
  let h₀ : A ⟶ C₀ :=
    (CohomologicalDeltaFunctor.Hom.app e.hom q).app S.X₃
  let h' : A ⟶ C :=
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app S.X₃
  let i₀ : C₀ ⟶ D₀ := (P.connecting q).app SE
  let i' : C ⟶ D :=
    ContinuousCohomology.discreteCoefficientConnecting.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) T
      (fieldShortExact_discreteCoefficientExact.{u, w} k Ω T hT) q
  have hf : f = f' := comparisonRightDerivedConnector
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q SE
  have h1 := congrArg (fun t => t.app S.X₁)
    (fieldEtaleCanonicalDeltaIso_hom_app.{u, w} k Ω (q + 1))
  have hgHEq : HEq g₀ g' := heq_of_eq h1
  have h0 := congrArg (fun t => t.app S.X₃)
    (fieldEtaleCanonicalDeltaIso_hom_app.{u, w} k Ω q)
  have hhHEq : HEq h₀ h' := heq_of_eq h0
  have hc := CohomologicalDeltaFunctor.original_precompose_connector
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
    (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) q SE
  have ho := fieldOldNativeDelta_connector.{u, w} k Ω q
    (⟨T, hT⟩ : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω))
  have hi := hc.trans ho
  have hiHEq : HEq i₀ i' := heq_of_eq hi
  have hδ : f ≫ g₀ = h₀ ≫ i₀ := comparisonDeltaConnector e q SE
  have hgModel : g₀ ≫ eqToHom hD = g' := comparisonTargetObjectTransport
    (A := B) (B := D₀) (B' := D) (f := g₀) (g := g') hD hgHEq
  have hhModel : h₀ ≫ eqToHom hC = h' := comparisonTargetObjectTransport
    (A := A) (B := C₀) (B' := C) (f := h₀) (g := h') hC hhHEq
  have hiModel : eqToHom hC.symm ≫ i₀ ≫ eqToHom hD = i' :=
    comparisonHomObjectTransport (A := C₀) (A' := C) (B := D₀) (B' := D)
      (f := i₀) (g := i') hC hD hiHEq
  have transported : f ≫ (g₀ ≫ eqToHom hD) =
      (h₀ ≫ eqToHom hC) ≫ (eqToHom hC.symm ≫ i₀ ≫ eqToHom hD) :=
    comparisonSquareObjectTransport (A := A) (B := B) (C₀ := C₀) (D₀ := D₀)
      (C := C) (D := D) (f := f) (g := g₀) (h := h₀) (i := i₀) hC hD hδ
  have square : f' ≫ g' = h' ≫ i' := comparisonSquareSelectors
    (A := A) (B := B) (C := C) (D := D)
    (f := f) (f' := f') (g := g₀ ≫ eqToHom hD) (g' := g')
    (h := h₀ ≫ eqToHom hC) (h' := h')
    (i := eqToHom hC.symm ≫ i₀ ≫ eqToHom hD) (i' := i')
    hf hgModel hhModel hiModel transported
  simpa only [SE, T, hT, f', g', h', i'] using square

/-- The original Yoneda connector is sent to the original native coefficient
connector of the same geometric-fiber short exact sequence in every degree. -/
theorem fieldEtaleContinuousEquiv_connecting
    (S : ShortComplex
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} S.X₃ q) :
    let T : ShortComplex (FieldCohomologyModule.{u, w} k Ω) :=
      S.map (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    let hT : T.ShortExact := Functor.RightDerived.precompShortExact
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) S hS
    fieldEtaleContinuousEquiv.{u, w} k Ω S.X₁ (q + 1)
        (smallEtaleConnectingMap.{u, w} hS q x) =
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) T
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω T hT) q
        (fieldEtaleContinuousEquiv.{u, w} k Ω S.X₃ q x) := by
  have hv := comparisonSquareValue
    (fieldEtaleGammaNativeConnecting.{u, w} k Ω S hS q)
    (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) S.X₃ q x)
  have hΓ := OriginalGammaBridge.canonicalEquiv_connecting.{u, w}
    (Spec (.of k)) S hS q x
  have h := (congrArg
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω (q + 1)).hom.app S.X₁)
    hΓ.symm).trans hv
  rw [fieldEtaleContinuousEquiv_apply, fieldEtaleContinuousEquiv_apply]
  dsimp only [Functor.comp, ShortComplex.map] at h ⊢
  exact h

/-- The original-map name refers to this same literal native connector equation. -/
alias fieldEtaleContinuousEquiv_connecting_original_map := fieldEtaleContinuousEquiv_connecting

variable (K Ψ : Type u) [Field K] [Field Ψ] [Algebra K Ψ] [IsSepClosure K Ψ]

/-- The original étale field pullback is induced by the canonical derived-Γ
pullback, independently of the continuous-cohomology comparison square. -/
def fieldEtaleCohomologyPullback (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ) :
    Sheaf.H.{max u w, max u w, u, u + 1} Q q →+
      Sheaf.H.{max u w, max u w, u, u + 1}
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q :=
  (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)
      q).symm.toAddMonoidHom.comp
    (((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q).hom.comp
      (CanonicalLongExactSequence.canonicalEquiv.{u, w}
        (Spec (.of k)) Q q).toAddMonoidHom)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- The field pullback is the literal canonical transport of the actual Γ pullback. -/
theorem fieldEtaleCohomologyPullback_apply
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x =
      (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q).symm
        ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q
          (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q x)) := rfl

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Applying the actual target canonical Γ map to étale pullback recovers
exactly the independently constructed original derived-Γ pullback. -/
theorem fieldEtaleCohomologyPullback_canonicalEquiv
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q
        (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x) =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q
        (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q x) := by
  let d := CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
    ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q
  change d (d.symm _) = _
  exact d.apply_symm_apply _

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Every coefficient arrow commutes with the original étale field pullback. -/
theorem fieldEtaleCohomologyPullback_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : Q ⟶ Q') (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q' q (Sheaf.H.map f q x) =
      Sheaf.H.map ((smallEtaleInverseImage.{u, w}
        (fieldOriginalPullback k Ω K Ψ e)).map f) q
        (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x) := by
  let L := smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)
  apply (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
    (L.obj Q') q).injective
  have hv := comparisonSquareValue
    (fieldDerivedPullback_naturality.{u, w} k Ω K Ψ e q f)
    (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q x)
  exact (fieldEtaleCohomologyPullback_canonicalEquiv.{u, w} k Ω K Ψ e Q' q
    (Sheaf.H.map f q x)).trans
      ((congrArg ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q')
        (CanonicalLongExactSequence.canonicalEquiv_naturality.{u, w}
          (Spec (.of k)) f q x)).trans
        (hv.trans
          ((congrArg (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology
              AddCommGrpCat.{max u w}).rightDerived q).map (L.map f))
            (fieldEtaleCohomologyPullback_canonicalEquiv.{u, w}
              k Ω K Ψ e Q q x).symm).trans
            (CanonicalLongExactSequence.canonicalEquiv_naturality.{u, w}
              (Spec (.of K)) (L.map f) q
              (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x)).symm)))

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- The actual field pullback preserves the original Yoneda connectors,
using the actual inverse-image short exact sequence. -/
theorem fieldEtaleCohomologyPullback_connecting
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (S : ShortComplex
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} S.X₃ q) :
    fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e S.X₁ (q + 1)
        (smallEtaleConnectingMap.{u, w} hS q x) =
      smallEtaleConnectingMap.{u, w}
        (smallEtaleInverseImage_shortExact.{u, w}
          (fieldOriginalPullback k Ω K Ψ e) S hS) q
        (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e S.X₃ q x) := by
  let L := smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)
  let hL := smallEtaleInverseImage_shortExact.{u, w}
    (fieldOriginalPullback k Ω K Ψ e) S hS
  apply (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
    (L.obj S.X₁) (q + 1)).injective
  have hv := comparisonSquareValue
    (fieldDerivedPullback_etale_connecting.{u, w} k Ω K Ψ e q S hS)
    (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) S.X₃ q x)
  have hs := CanonicalLongExactSequence.derivedBoundary_comparison.{u, w} hS q x
  have ht := CanonicalLongExactSequence.derivedBoundary_comparison.{u, w} hL q
    (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e S.X₃ q x)
  exact (fieldEtaleCohomologyPullback_canonicalEquiv.{u, w} k Ω K Ψ e S.X₁ (q + 1)
    (smallEtaleConnectingMap.{u, w} hS q x)).trans
      ((congrArg ((fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁)
        hs.symm).trans
        (hv.trans
          ((congrArg (CanonicalLongExactSequence.derivedBoundary.{u, w} hL q)
            (fieldEtaleCohomologyPullback_canonicalEquiv.{u, w}
              k Ω K Ψ e S.X₃ q x).symm).trans ht)))

/-- The direct étale/native comparison respects the original field square. -/
theorem fieldEtaleContinuousEquiv_field
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleContinuousEquiv.{u, w} K Ψ
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q
        (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x) =
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q
        (fieldEtaleContinuousEquiv.{u, w} k Ω Q q x) := by
  have hs := congrArg (fun a => a.app Q)
    (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e q)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hs
  have hv := comparisonSquareValue hs
    (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of k)) Q q x)
  change (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom.app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)
      (CanonicalLongExactSequence.canonicalEquiv.{u, w} (Spec (.of K))
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q
        (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x)) = _
  exact (congrArg
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom.app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    (fieldEtaleCohomologyPullback_canonicalEquiv.{u, w} k Ω K Ψ e Q q x)).trans hv

/-- The field map is the original cochain restriction followed by the actual
field-change stalk coefficient map, on the same source and target native models. -/
theorem fieldEtaleContinuousEquiv_field_original_map
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (x : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    fieldEtaleContinuousEquiv.{u, w} K Ψ
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) q
        (fieldEtaleCohomologyPullback.{u, w} k Ω K Ψ e Q q x) =
      (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)
        (ContinuousCohomology.discreteCoefficientForget.{max u w}.map
          (HomologicalComplex.homologyMap
            (fieldOriginalRankRestrictionCochainMap.{u, w} k Ω K Ψ
              (GaloisUnits.FieldMap.restrictContinuous e)
              ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) q)
          (fieldEtaleContinuousEquiv.{u, w} k Ω Q q x)) := by
  exact (fieldEtaleContinuousEquiv_field.{u, w} k Ω K Ψ e Q q x).trans
    (comparisonCompositionValue
      (fieldNativePullback_original_map.{u, w} k Ω K Ψ e q Q)
      (fieldEtaleContinuousEquiv.{u, w} k Ω Q q x))

/-- The original comparison exists for every actual common sheaf and every degree. -/
theorem original_field_etale_continuous_cohomology_comparison :
    ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ),
      Nonempty (Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+
        (fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) :=
  fun Q q => ⟨fieldEtaleContinuousEquiv.{u, w} k Ω Q q⟩

end AlgebraicGeometry.Scheme.DerivedSections
