/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGlobalSectionsPullback
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageExactness
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaComparison
public import MathlibExt.AlgebraicGeometry.Sites.FieldDerivedSectionsInvariants

/-!
# Derived global sections, field pullback, and continuous cohomology

For a field k, the right-derived global-section functors form a universal cohomological
δ-functor. Compatible embeddings of field pairs induce a degree-zero global-section pullback
through the inverse-image adjunction unit. Exactness of inverse image gives the target
δ-functor, and source universality extends that map uniquely to every derived degree,
commuting with the connecting morphisms.

For a prescribed separable closure Ω of k, the fixed Γ/invariant comparison extends to a
δ-functor isomorphism with derived Galois invariants of the geometric stalk. Composing with
the continuous-cohomology comparison gives the all-degree continuous Galois cohomology
δ-isomorphism. Coefficients have height max(u,w).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Let k be a field of universe u. The functors R^nΓ_k on small-étale additive-group sheaves of
height max(u,w), with the canonical short-exact-sequence connecting maps, define a
cohomological δ-functor to AddCommGrpCat of that height. -/
abbrev fieldOriginalGammaDeltaFunctor (k : Type u) [Field k] :
    CohomologicalDeltaFunctor
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      AddCommGrpCat.{max u w} :=
  Functor.rightDerivedDeltaFunctor
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})

theorem fieldOriginalGammaDeltaFunctor_isUniversal (k : Type u) [Field k] :
    CohomologicalDeltaFunctor.IsUniversal
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      AddCommGrpCat.{max u w} (fieldOriginalGammaDeltaFunctor.{u, w} k) :=
  Functor.isUniversal_rightDerivedDeltaFunctor
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]
attribute [local instance] IsSepClosure.sep_closed

/-- For compatible field embeddings e : (k,Ω) → (K,Ψ), the small-étale inverse-image functor for
Spec(e.base) : Spec(K) → Spec(k) is additive on additive-group sheaves of height max(u,w).
This is the inverse-image functor used in the derived pullback construction. -/
local instance fieldChangeInverseImage_additive (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)


/-- Let e be compatible embeddings of field pairs and f : Spec(K) → Spec(k) their base spectrum
map. Precompose the right-derived global-section δ-functor of K by the exact inverse image
f^*. Its degree-n functor is f^*⋙R^nΓ_K, and its connectors are those of the short exact
sequence obtained by inverse image. -/
def fieldInverseImageGammaDeltaFunctor (e : GaloisUnits.FieldMap k Ω K Ψ) :=
  CohomologicalDeltaFunctor.precompose
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
    (fun S hS => smallEtaleInverseImage_shortExact.{u, w}
      (fieldOriginalPullback k Ω K Ψ e) S hS)
    (fieldOriginalGammaDeltaFunctor.{u, w} K)

/-- For compatible field embeddings e with f : Spec(K) → Spec(k), the universal source δ-functor
R^•Γ_k extends the unit-defined Γ pullback to a morphism R^•Γ_k → f^*⋙R^•Γ_K. Its degree-zero
component is normalized by the canonical R^0Γ≅Γ isomorphisms and fieldPullbackGlobalSections.
No target-injective-preservation hypothesis is used. -/
def fieldDerivedPullbackDeltaHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldOriginalGammaDeltaFunctor.{u, w} k ⟶
      fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e :=
  CohomologicalDeltaFunctor.normalizedExtension
    (fieldOriginalGammaDeltaFunctor.{u, w} k)
    (fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e)
    (fieldOriginalGammaDeltaFunctor_isUniversal.{u, w} k)
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
    (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf)
    (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e)

/-- For compatible field embeddings e and n∈ℕ, take the nth component of
fieldDerivedPullbackDeltaHom to obtain R^nΓ_k → f^*⋙R^nΓ_K. The objects are the canonical
right-derived global-section objects on small-étale additive-group sheaves of height max(u,w). -/
def fieldDerivedPullback (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n ⟶
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n :=
  CohomologicalDeltaFunctor.Hom.app (fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e) n

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldDerivedPullback_zero (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e 0 ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom =
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom ≫
        fieldPullbackGlobalSections.{u, w} k Ω K Ψ e :=
  CohomologicalDeltaFunctor.normalizedExtension_normalization
    (fieldOriginalGammaDeltaFunctor.{u, w} k)
    (fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e)
    (fieldOriginalGammaDeltaFunctor_isUniversal.{u, w} k)
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
    (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf)
    (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldDerivedPullback_naturality (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map τ ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q' =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q ≫
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map τ) :=
  (fieldDerivedPullback.{u, w} k Ω K Ψ e n).naturality τ


omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Let e be compatible field embeddings, S₁ → S₂ → S₃ a short exact small-étale sheaf sequence
over k, and n∈ℕ. The derived pullback maps γ satisfy δ_k,n(S)≫γ_{n+1}(S₁)=γ_n(S₃)≫δ_K,n(f^*S).
The equality is between maps R^nΓ_k(S₃) → R^{n+1}Γ_K(f^*S₁) and requires no separable-closure
assumption on the field-pair data. -/
theorem fieldDerivedPullback_connecting (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    ((fieldOriginalGammaDeltaFunctor.{u, w} k).connecting n).app S ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e (n + 1)).app S.obj.X₁ =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app S.obj.X₃ ≫
        ((fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e).connecting n).app S :=
  DeltaFunctor.System.comm (fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e).hom n S

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- For compatible field embeddings e, any δ-functor morphism g : R^•Γ_k → f^*⋙R^•Γ_K whose
zero-degree component equals fieldDerivedPullback(e,0) is equal to
fieldDerivedPullbackDeltaHom(e). Universality is required only of the source right-derived Γ
δ-functor. -/
theorem fieldDerivedPullback_unique (e : GaloisUnits.FieldMap k Ω K Ψ)
    (g : fieldOriginalGammaDeltaFunctor.{u, w} k ⟶
      fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e)
    (hg : CohomologicalDeltaFunctor.Hom.app g 0 =
      fieldDerivedPullback.{u, w} k Ω K Ψ e 0) :
    g = fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e :=
  CohomologicalDeltaFunctor.hom_eq_of_app_zero
    (fieldOriginalGammaDeltaFunctor.{u, w} k)
    (fieldOriginalGammaDeltaFunctor_isUniversal.{u, w} k)
    (fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e) g
    (fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e) hg

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- For compatible field embeddings e, n∈ℕ, and τ : F → F′ a small-étale sheaf map of coefficient
universe w, let L be ULift^u. The degree-n map γ satisfies
R^nΓ_k(Lτ)≫γ_n(LF′)=γ_n(LF)≫(f^*⋙R^nΓ_K)(Lτ). Thus each naturality square uses the same single
coefficient lift. -/
theorem fieldDerivedPullback_original_coefficient_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map τ) ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map τ)) :=
  (fieldDerivedPullback.{u, w} k Ω K Ψ e n).naturality
    ((liftCoefficients.{u, w} (Spec (.of k))).map τ)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let k have prescribed separable closure Ω and Φ its geometric Galois stalk functor. The
canonical Γ≅Φ⋙Inv comparison gives an isomorphism of cohomological δ-functors R^•Γ_k ≅
Φ⋙R^•Inv. Its components and connecting maps are those of the right-derived comparison, at
additive-group coefficient height max(u,w). -/
def fieldGammaInvariantsDeltaIso :
    fieldOriginalGammaDeltaFunctor.{u, w} k ≅
      CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldDerivedInvariantsDeltaFunctor.{u, w} k Ω) :=
  Functor.RightDerived.precompDeltaIsoOfIso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω)

theorem fieldGammaInvariantsDeltaIso_hom_app (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldGammaInvariantsDeltaIso.{u, w} k Ω).hom n =
      (fieldDerivedSectionsInvariantsIso.{u, w} k Ω n).hom :=
  Functor.RightDerived.precompDeltaIsoOfIso_hom_app
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) n

/-- For a field k and prescribed separable closure Ω, R^•Γ_k on small-étale additive-group sheaves
is isomorphic as a cohomological δ-functor to continuous cohomology of Gal(Ω/k) applied to the
geometric stalk. The comparison composes the Γ/derived-invariants δ-isomorphism with the
continuous-cohomology/derived-invariants comparison and preserves all connectors. -/
def fieldGammaContinuousDeltaIso :
    fieldOriginalGammaDeltaFunctor.{u, w} k ≅
      CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) :=
  fieldGammaInvariantsDeltaIso.{u, w} k Ω ≪≫
    (CohomologicalDeltaFunctor.precomposeFunctor (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))).mapIso
        (fieldContinuousDerivedInvariantsDeltaIso.{u, w} k Ω).symm

theorem fieldGammaContinuousDeltaIso_hom_app (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).hom n =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω n).hom := rfl

end AlgebraicGeometry.Scheme.DerivedSections

end
