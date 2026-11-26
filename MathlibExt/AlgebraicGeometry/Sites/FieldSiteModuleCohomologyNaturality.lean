/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGammaCohomologyComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedConnectingComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientLiftExactness
public import MathlibExt.AlgebraicGeometry.Sites.FieldCohomologyUniverseComparison
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedGammaPullback
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.PrecompositionCoherence
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionRealization
public import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence

/-!
# Naturality of field étale and continuous cohomology comparisons

Let Ω/k and Ψ/K be separable closures of fields in universe u, with
compatible embeddings β : k → K and σ : Ω → Ψ. Put c = max(u, w),
G = Gal(Ω/k), H = Gal(Ψ/K), f = Spec β and φ = res_e : H → G.
The Galois stalk change identifies Res_φ(E(Q)) with E′(f*Q).

The continuous pullback b_e first restricts the homogeneous cochains along
φ and then changes coefficients by this stalk isomorphism.
The derived-section comparison χ identifies it with étale pullback a_e:
χ_K ∘ a_e = b_e ∘ χ_k in every degree.
The degree-zero normalization is the global-section/invariant comparison.

The same square holds on any chosen source and target injective resolutions,
naturally under augmented coefficient maps and changes of resolution.
Both pullbacks commute with connecting maps and satisfy identity and
composition laws using the inverse-image comparisons.
The invariant-cohomology factorization is described on the mapped stalk
resolution. Coefficients originally in universe w are lifted once to c.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

local instance fieldNativeInverseImage_additive (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
theorem fieldNativeInverseImageShortExact (e : GaloisUnits.FieldMap k Ω K Ψ)
    (S : ShortComplex (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) :
    (S.map (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))).ShortExact :=
  smallEtaleInverseImage_shortExact.{u, w} (fieldOriginalPullback k Ω K Ψ e) S hS

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
Group-cochain restriction along φ followed by the stalk-change map
χ : Res_φ E ≅ E′L gives a morphism of cohomological delta functors
H_cts^*(G, E(-)) → H_cts^*(H, E′L(-)).
It commutes with the connecting maps of short exact coefficient sheaves. -/
def fieldNativePullbackDeltaHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) ⟶
      CohomologicalDeltaFunctor.precompose
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
        (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ)) := by
  let φ := GaloisUnits.FieldMap.restrictContinuous e
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let T' := fieldGeometricStalkGaloisFunctor.{u, w} K Ψ
  let R := fieldModuleRestriction.{u, u, w} k Ω K Ψ φ
  letI : R.Additive := fieldModuleRestriction_additive.{u, u, w} k Ω K Ψ φ
  let L := smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)
  let hT := Functor.RightDerived.precompShortExact T
  let hT' := Functor.RightDerived.precompShortExact T'
  let hR := fieldModuleRestriction_shortExact.{u, u, w} k Ω K Ψ φ
  let hL := fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e
  let H := fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ
  let χ := fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e
  let g : CohomologicalDeltaFunctor.precompose T hT
      (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) ⟶
      CohomologicalDeltaFunctor.precompose T hT (CohomologicalDeltaFunctor.precompose R hR H) :=
    (CohomologicalDeltaFunctor.precomposeFunctor T hT).map
      (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ)
  let a := CohomologicalDeltaFunctor.precomposeCompIso T R hT hR H
  let b := CohomologicalDeltaFunctor.precomposeCompIso L T' hL hT' H
  let c := CohomologicalDeltaFunctor.precomposeChangeHom (T ⋙ R) (L ⋙ T')
    (CohomologicalDeltaFunctor.precomposeCompShortExact T R hT hR)
    (CohomologicalDeltaFunctor.precomposeCompShortExact L T' hL hT') χ.hom H
  exact g ≫ a.hom ≫ c ≫ b.inv

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For n ∈ ℕ, the continuous pullback is the natural additive map
b_e^n(Q) : Hⁿ_cts(G, E(Q)) → Hⁿ_cts(H, E′(LQ)),
obtained from group restriction followed by the equivariant stalk change. -/
def fieldNativePullback (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ) :
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙ fieldContinuousCohomologyFunctor.{u, w} k Ω n ⟶
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙ fieldContinuousCohomologyFunctor.{u, w} K Ψ n
          :=
  CohomologicalDeltaFunctor.Hom.app (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem fieldNativePullback_app (e : GaloisUnits.FieldMap k Ω K Ψ) (n : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldNativePullback.{u, w} k Ω K Ψ e n).app Q =
      (CohomologicalDeltaFunctor.Hom.app
        (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ
          (GaloisUnits.FieldMap.restrictContinuous e)) n).app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
        (fieldContinuousCohomologyFunctor.{u, w} K Ψ n).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) := by
  simp only [fieldNativePullback, fieldNativePullbackDeltaHom,
    CohomologicalDeltaFunctor.Hom.comp_app,
    CohomologicalDeltaFunctor.precomposeCompIso_hom_app,
    CohomologicalDeltaFunctor.precomposeChangeHom_app]
  rfl

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
Let χ_k and χ_K be the delta-functor comparisons from derived
global sections to continuous Galois cohomology.
Conjugating continuous pullback gives the derived-section delta morphism
χ_K⁻¹ ∘ b_e ∘ χ_k : R*Γ_k → R*Γ_K ∘ L. -/
def fieldNativeTransportedGammaDeltaHom (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldOriginalGammaDeltaFunctor.{u, w} k ⟶
      fieldInverseImageGammaDeltaFunctor.{u, w} k Ω K Ψ e :=
  (fieldGammaContinuousDeltaIso.{u, w} k Ω).hom ≫
    fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e ≫
    (CohomologicalDeltaFunctor.precomposeFunctor
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)).map
      (fieldGammaContinuousDeltaIso.{u, w} K Ψ).inv

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Typed actual original/wide model comparison, with no change to Γ or the native family.
theorem fieldOriginalRankRestrictionDeltaHom_zero
    (φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω) :
    CohomologicalDeltaFunctor.Hom.app
        (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ) 0 ≫
      Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ)
        (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom =
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom ≫
      fieldInvariantRestriction.{u, u, w} k Ω K Ψ φ := by
  rw [fieldOriginalRankRestrictionDeltaHom_app]
  have htarget := rankIso_inv_zero (fieldSameRankContinuousIso.{u, w} K Ψ 0)
    (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom
    (fieldContinuousCohomologyZeroIso.{u, max u w} K Ψ).hom
    (fieldSameRankContinuousIso_zero.{u, w} K Ψ)
  calc
    _ = (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
      fieldContinuousCohomologyRestriction.{u, u, w} k Ω K Ψ 0 φ ≫
      Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ)
        (fieldContinuousCohomologyZeroIso.{u, max u w} K Ψ).hom := by
      simpa only [Category.assoc, Functor.whiskerLeft_comp] using
        congrArg (fun a => (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
          fieldContinuousCohomologyRestriction.{u, u, w} k Ω K Ψ 0 φ ≫
          Functor.whiskerLeft (fieldModuleRestriction.{u, u, w} k Ω K Ψ φ) a) htarget
    _ = (fieldSameRankContinuousIso.{u, w} k Ω 0).hom ≫
      (fieldContinuousCohomologyZeroIso.{u, max u w} k Ω).hom ≫
      fieldInvariantRestriction.{u, u, w} k Ω K Ψ φ := by
      rw [fieldContinuousCohomologyRestriction_zero]
    _ = _ := by rw [← Category.assoc, fieldSameRankContinuousIso_zero]

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For every coefficient sheaf Q, the degree-zero comparison obeys
z_G ∘ χ_k^0 = λ_Q ∘ z_Γ, where z_G : H⁰_cts(G,E(Q)) ≅ E(Q)^G,
z_Γ : R⁰Γ_k(Q) ≅ Γ_k(Q), and λ_Q : Γ_k(Q) ≅ E(Q)^G. -/
theorem fieldGammaContinuousIso_zero
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω 0).hom.app Q ≫
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) =
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u
      w}).rightDerivedZeroIsoSelf.hom.app Q ≫
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q := by
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  have h := rankIso_inv_zero (fieldContinuousDerivedInvariantsIso.{u, w} k Ω 0)
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom
    (fieldInvariantFunctor.{u, w} k Ω).rightDerivedZeroIsoSelf.hom
    (fieldContinuousDerivedInvariantsIso_zero.{u, w} k Ω)
  have hQ := congrArg (fun a => a.app (T.obj Q)) h
  simp only [NatTrans.comp_app] at hQ
  rw [fieldDerivedSectionsContinuousCohomologyIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, hQ]
  exact fieldDerivedSectionsInvariantsIso_zero.{u, w} k Ω Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

-- This finite declaration scope keeps every original field, coefficient object and map.
-- The proved native map uses the fixed old-rank cochains and actual ξ coefficient arrow.
theorem fieldNativePullback_zero_invariants
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldNativePullback.{u, w} k Ω K Ψ e 0).app Q ≫
      (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) =
    (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
      (fieldInvariantRestriction.{u, u, w} k Ω K Ψ (GaloisUnits.FieldMap.restrictContinuous e)).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
      (fieldInvariantFunctor.{u, w} K Ψ).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) := by
  let φ : InfiniteGalois.profiniteGalGrp K Ψ →ₜ* InfiniteGalois.profiniteGalGrp k Ω :=
    GaloisUnits.FieldMap.restrictContinuous e
  let M := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q
  let ξ := (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q
  have h := congrArg (fun a => a.app M)
    (fieldOriginalRankRestrictionDeltaHom_zero.{u, w} k Ω K Ψ φ)
  have h' := postcompose_natural_zero
    (fieldContinuousCohomologyFunctor.{u, w} K Ψ 0)
    (fieldInvariantFunctor.{u, w} K Ψ)
    (fieldContinuousCohomologyZeroIso.{u, w} K Ψ) ξ
    ((CohomologicalDeltaFunctor.Hom.app
      (fieldOriginalRankRestrictionDeltaHom.{u, w} k Ω K Ψ φ) 0).app M)
    ((fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app M ≫
      (fieldInvariantRestriction.{u, u, w} k Ω K Ψ φ).app M) h
  exact (congrArg (fun a => a ≫ (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom.app
      ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)))
    (fieldNativePullback_app.{u, w} k Ω K Ψ e 0 Q)).trans h'

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
The degree q component of the inverse delta-functor comparison
is the inverse natural map of the degree q derived-sections/continuous
cohomology isomorphism χ_k^q. -/
theorem fieldGammaContinuousDeltaIso_inv_app (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).inv q =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).inv := by
  apply (cancel_mono (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom).mp
  have h := congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (fieldGammaContinuousDeltaIso.{u, w} k Ω).inv_hom_id
  change CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).inv q ≫
    CohomologicalDeltaFunctor.Hom.app (fieldGammaContinuousDeltaIso.{u, w} k Ω).hom q = 𝟙 _ at h
  rw [fieldGammaContinuousDeltaIso_hom_app] at h
  exact h.trans (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).inv_hom_id.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Evaluate only the existing delta-functor operations before instantiating the field components.
theorem fieldNativeTransportedGammaDeltaHom_app
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app
      (fieldNativeTransportedGammaDeltaHom.{u, w} k Ω K Ψ e) q =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom ≫
      fieldNativePullback.{u, w} k Ω K Ψ e q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).inv := by
  simp only [fieldNativeTransportedGammaDeltaHom, CohomologicalDeltaFunctor.Hom.comp_app,
    CohomologicalDeltaFunctor.delta_precompose_map_app,
    fieldGammaContinuousDeltaIso_hom_app, fieldGammaContinuousDeltaIso_inv_app]
  rfl

set_option linter.defProp false in



/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a coefficient sheaf Q, continuous pullback conjugated by
χ_k^0 and χ_K^0 has degree-zero normalization
z_Γ,K ∘ χ_K⁻¹ ∘ b_e^0 ∘ χ_k =
pullback_Γ ∘ z_Γ,k.
Here pullback_Γ sends Γ_k(Q) to Γ_K(LQ). -/
def fieldNativeGammaZeroProof (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  normalized_conjugate_map
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω 0).app Q)
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ 0).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u
      w}).rightDerivedZeroIsoSelf.app Q)
    ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).app Q)
    ((fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((fieldContinuousCohomologyZeroIso.{u, w} k Ω).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
    ((fieldContinuousCohomologyZeroIso.{u, w} K Ψ).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)))
    ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q)
    ((fieldNativePullback.{u, w} k Ω K Ψ e 0).app Q)
    ((fieldInvariantRestriction.{u, u, w} k Ω K Ψ (GaloisUnits.FieldMap.restrictContinuous e)).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
      (fieldInvariantFunctor.{u, w} K Ψ).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q))
    (fieldGammaContinuousIso_zero.{u, w} k Ω Q)
    (fieldGammaContinuousIso_zero.{u, w} K Ψ
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    (fieldNativePullback_zero_invariants.{u, w} k Ω K Ψ e Q)
    (congrArg (fun a => a.app Q)
      (fieldPullbackGlobalSections_invariants_naturality.{u, w} k Ω K Ψ e))

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem fieldNativeTransportedGammaDeltaHom_zero
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    CohomologicalDeltaFunctor.Hom.app
        (fieldNativeTransportedGammaDeltaHom.{u, w} k Ω K Ψ e) 0 ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
          w}).rightDerivedZeroIsoSelf.hom =
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom
      ≫
      fieldPullbackGlobalSections.{u, w} k Ω K Ψ e := by
  rw [fieldNativeTransportedGammaDeltaHom_app]
  apply NatTrans.ext
  funext Q
  exact fieldNativeGammaZeroProof.{u, w} k Ω K Ψ e Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Actual zero normalization and genuine source universality identify every degree.
theorem fieldNativeTransportedGammaDeltaHom_eq
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldNativeTransportedGammaDeltaHom.{u, w} k Ω K Ψ e =
      fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e := by
  apply fieldDerivedPullback_unique.{u, w} k Ω K Ψ e
  apply (cancel_mono (Functor.isoWhiskerLeft
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
      w}).rightDerivedZeroIsoSelf).hom).mp
  exact (fieldNativeTransportedGammaDeltaHom_zero.{u, w} k Ω K Ψ e).trans
    (fieldDerivedPullback_zero.{u, w} k Ω K Ψ e).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem fieldDerivedPullback_native_square
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom ≫
      fieldNativePullback.{u, w} k Ω K Ψ e q := by
  have h := congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (fieldNativeTransportedGammaDeltaHom_eq.{u, w} k Ω K Ψ e)
  rw [fieldNativeTransportedGammaDeltaHom_app] at h
  exact conjugate_map_square
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q)
    (Functor.isoWhiskerLeft
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q))
    (fieldNativePullback.{u, w} k Ω K Ψ e q)
    (fieldDerivedPullback.{u, w} k Ω K Ψ e q) h

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- For fields k, Ω in universe u with k-algebra Ω, the compatible
identity field map induces the identity scheme map on Spec k:
Spec(id_k) = id_(Spec k). -/
theorem fieldOriginalPullback_id (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω) = 𝟙 (Spec (.of k)) := by
  change Spec.map (𝟙 (CommRingCat.of k)) = 𝟙 (Spec (.of k))
  exact Spec.map_id _

/-- For compatible field maps e₁ : (k,Ω) → (K,Ψ) and
e₂ : (K,Ψ) → (l,Λ), with all fields in universe u, the induced
spectrum maps satisfy f_(e₂∘e₁) = f_e₁ ∘ f_e₂.
This is contravariance of the spectrum construction on the base embeddings. -/
theorem fieldOriginalPullback_comp
    (k Ω K Ψ L Φ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ] [Field L] [Field Φ]
    [Algebra k Ω] [Algebra K Ψ] [Algebra L Φ]
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) :
    fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) =
      fieldOriginalPullback K Ψ L Φ e₂ ≫ fieldOriginalPullback k Ω K Ψ e₁ := by
  change Spec.map ((CommRingCat.ofHom e₁.base) ≫ (CommRingCat.ofHom e₂.base)) = _
  exact Spec.map_comp _ _

/-- For a scheme X in universe u, c = max(u, w), an endomorphism
f : X → X with f = id_X, and q ∈ ℕ, derived global-section pullback
along f followed by the inverse-image comparison f* ≅ id is
id_(RᑫΓ_X). The comparison includes the given equality f = id_X. -/
theorem smallEtaleDerivedGammaPullback_id_to (X : Scheme.{u}) (f : X ⟶ X)
    (hf : f = 𝟙 X) (q : ℕ) :
    smallEtaleDerivedGammaPullback.{u, w} f q ≫
      Functor.whiskerRight
        (smallEtaleInverseImageCongr.{u, w} hf ≪≫ smallEtaleInverseImageIdIso.{u, w} X).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    𝟙 ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) := by
  subst f
  simpa only [smallEtaleInverseImageCongr, eqToIso_refl, Iso.refl_trans] using
    smallEtaleDerivedGammaPullback_id.{u, w} X q

/-- For f : X → Y, g : Y → Z and h : X → Z with h = g ∘ f,
all schemes in universe u, derived-section pullback in degree q
composes as pullback along g then along f, followed by
f*g* ≅ h*. The result is pullback along h on AddCommGrpCat max(u,w)-valued
étale sheaves. -/
theorem smallEtaleDerivedGammaPullback_comp_to
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (q : ℕ) :
    smallEtaleDerivedGammaPullback.{u, w} g q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} g)
        (smallEtaleDerivedGammaPullback.{u, w} f q) ≫
      (Functor.associator (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv ≫
      Functor.whiskerRight (smallEtaleInverseImageCompTo.{u, w} f g fg hfg).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    smallEtaleDerivedGammaPullback.{u, w} fg q := by
  subst fg
  simpa only [smallEtaleInverseImageCompTo_eq, smallEtaleInverseImageCongr, eqToIso_refl,
    Iso.trans_refl] using smallEtaleDerivedGammaPullback_comp.{u, w} f g q

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
The field global-section map Γ_k(Q) → Γ_K(LQ) is the canonical
small étale scheme pullback map for f. Both come from the same
inverse-image adjunction unit and terminal-section comparison. -/
theorem fieldPullbackGlobalSections_eq_scheme (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldPullbackGlobalSections.{u, w} k Ω K Ψ e =
      smallEtalePullbackGlobalSections.{u, w} (fieldOriginalPullback k Ω K Ψ e) := rfl

set_option backward.isDefEq.respectTransparency false in
-- Only actual common Γ objects and the proved same unit map are compared.
theorem fieldDerivedPullbackDeltaHom_eq_scheme (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldDerivedPullbackDeltaHom.{u, w} k Ω K Ψ e =
      smallEtaleDerivedGammaPullbackDeltaHom.{u, w} (fieldOriginalPullback k Ω K Ψ e) := by
  unfold fieldDerivedPullbackDeltaHom smallEtaleDerivedGammaPullbackDeltaHom
  rw [fieldPullbackGlobalSections_eq_scheme]
  rfl

theorem fieldDerivedPullback_eq_scheme (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e q =
      smallEtaleDerivedGammaPullback.{u, w} (fieldOriginalPullback k Ω K Ψ e) q :=
  congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (fieldDerivedPullbackDeltaHom_eq_scheme.{u, w} k Ω K Ψ e)

/-- For fields k, Ω in universe u with k-algebra Ω and c = max(u,w),
inverse image along the compatible identity field map is naturally
isomorphic to the identity on abelian étale sheaves over k.
The comparison uses Spec(id_k) = id_(Spec k). -/
def fieldInverseImageIdentityIso :
    smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω)) ≅
      𝟭 (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  smallEtaleInverseImageCongr.{u, w} (fieldOriginalPullback_id k Ω) ≪≫
    smallEtaleInverseImageIdIso.{u, w} (Spec (.of k))

/-- For fields k, Ω in universe u with k-algebra Ω, c = max(u,w)
and q ∈ ℕ, the derived-section pullback along the identity field map,
followed by the inverse-image identity comparison, is
id_(RᑫΓ_k). -/
theorem fieldDerivedPullback_id (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
      Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
        ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    𝟙 ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) := by
  rw [fieldDerivedPullback_eq_scheme]
  exact smallEtaleDerivedGammaPullback_id_to.{u, w} (Spec (.of k))
    (fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω)) (fieldOriginalPullback_id k Ω) q

variable (L Φ : Type u) [Field L] [Field Φ] [Algebra L Φ]

/-- For compatible field maps e₁ : (k,Ω) → (K,Ψ) and
e₂ : (K,Ψ) → (l,Λ) in universe u and c = max(u,w),
the iterated inverse image L_e₂ L_e₁ is naturally isomorphic to
L_(e₂∘e₁) on the small étale coefficient categories. -/
def fieldInverseImageCompositionIso
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) :
    smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁) ⋙
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂) ≅
    smallEtaleInverseImage.{u, w}
      (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁)) :=
  smallEtaleInverseImageCompTo.{u, w}
    (fieldOriginalPullback K Ψ L Φ e₂) (fieldOriginalPullback k Ω K Ψ e₁)
    (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁))
    (fieldOriginalPullback_comp k Ω K Ψ L Φ e₁ e₂)

/-- For compatible field maps e₁ : (k,Ω) → (K,Ψ),
e₂ : (K,Ψ) → (l,Λ) in universe u, c = max(u,w), and q ∈ ℕ,
field derived-section pullbacks satisfy
a_(e₂∘e₁) = RᑫΓ_l(c₁₂) ∘ a_e₂(L_e₁(-)) ∘ a_e₁,
where c₁₂ : L_e₂ L_e₁ ≅ L_(e₂∘e₁) is the inverse-image comparison. -/
theorem fieldDerivedPullback_comp
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ) :
    fieldDerivedPullback.{u, w} k Ω K Ψ e₁ q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (fieldDerivedPullback.{u, w} K Ψ L Φ e₂ q) ≫
      (Functor.associator
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂))
        ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv ≫
      Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e₁ e₂).hom
        ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    fieldDerivedPullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q := by
  simp only [fieldDerivedPullback_eq_scheme]
  exact smallEtaleDerivedGammaPullback_comp_to.{u, w}
    (fieldOriginalPullback K Ψ L Φ e₂) (fieldOriginalPullback k Ω K Ψ e₁)
    (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁))
    (fieldOriginalPullback_comp k Ω K Ψ L Φ e₁ e₂) q

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
In degree q, continuous field pullback along the identity map,
followed by the inverse-image identity comparison, is the identity
on Hᑫ_cts(G,E(-)). -/
theorem fieldNativePullback_id (q : ℕ) :
    fieldNativePullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
      Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
        (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
          fieldContinuousCohomologyFunctor.{u, w} k Ω q) =
    𝟙 (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      fieldContinuousCohomologyFunctor.{u, w} k Ω q) :=
  comparison_identity (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q)
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω k Ω (GaloisUnits.FieldMap.id k Ω)))
    (fieldInverseImageIdentityIso.{u, w} k Ω)
    (fieldDerivedPullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q)
    (fieldNativePullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q)
    (fieldDerivedPullback_native_square.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q)
    (fieldDerivedPullback_id.{u, w} k Ω q)

variable (K Ψ L Φ : Type u) [Field K] [Field Ψ] [Field L] [Field Φ]
variable [Algebra K Ψ] [Algebra L Φ] [IsSepClosure K Ψ] [IsSepClosure L Φ]

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a further compatible map (K,Ψ) → (l,Λ) of separable closures
in universe u, the continuous pullbacks compose in field-map order:
first e, then the further map. After identifying the iterated inverse
image with the composite inverse image, this is b_(eNext∘e) in every degree q. -/
theorem fieldNativePullback_comp
    (e₁ : GaloisUnits.FieldMap k Ω K Ψ) (e₂ : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ) :
    fieldNativePullback.{u, w} k Ω K Ψ e₁ q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (fieldNativePullback.{u, w} K Ψ L Φ e₂ q) ≫
      (Functor.associator
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂))
        (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
          fieldContinuousCohomologyFunctor.{u, w} L Φ q)).inv ≫
      Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e₁ e₂).hom
        (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
          fieldContinuousCohomologyFunctor.{u, w} L Φ q) =
    fieldNativePullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q :=
  comparison_composition
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q)
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q)
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} L Φ q)
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e₁))
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ e₂))
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω L Φ (GaloisUnits.FieldMap.comp e₂
      e₁)))
    (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e₁ e₂)
    (fieldDerivedPullback.{u, w} k Ω K Ψ e₁ q)
    (fieldNativePullback.{u, w} k Ω K Ψ e₁ q)
    (fieldDerivedPullback.{u, w} K Ψ L Φ e₂ q)
    (fieldNativePullback.{u, w} K Ψ L Φ e₂ q)
    (fieldDerivedPullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q)
    (fieldNativePullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q)
    (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e₁ q)
    (fieldDerivedPullback_native_square.{u, w} K Ψ L Φ e₂ q)
    (fieldDerivedPullback_native_square.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp e₂ e₁) q)
    (fieldDerivedPullback_comp.{u, w} k Ω K Ψ L Φ e₁ e₂ q)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For any injective resolution I of Q and q ∈ ℕ, the resolution
comparison and χ_k give
Hᑫ(Γ_k(I)) ≅ Hᑫ_cts(G,E(Q)).
Its forward map first returns to RᑫΓ_k(Q), then applies χ_k^q. -/
def fieldGammaNativeResolutionIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology q ≅
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      fieldContinuousCohomologyFunctor.{u, w} k Ω q).obj Q :=
  (I.isoRightDerivedObj
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).symm ≪≫
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).app Q

/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
For injective resolutions I of Q and J of LQ, the realized
derived pullback is Hᑫ(Γ_k(I)) → Hᑫ(Γ_K(J)).
It returns from the source resolution to RᑫΓ_k(Q), applies a_e^q,
then maps into the target resolution cohomology. -/
def fieldDerivedPullbackResolutionMap (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q)
    (J : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :
    (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology q ⟶
    (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex).homology q :=
  (I.isoRightDerivedObj
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).inv ≫
    (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q ≫
    (J.isoRightDerivedObj
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom

set_option linter.defProp false in

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For injective resolutions I of Q and J of LQ, let a_IJ be the
realized derived pullback and χ_I, χ_J their continuous comparisons.
Then χ_J ∘ a_IJ = b_e^q(Q) ∘ χ_I.
The equality holds for the independently chosen two resolutions. -/
def fieldResolutionNativeSquareProof
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q)
    (J : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :=
  resolution_realization_square
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q)
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).app Q)
    ((fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))
    ((fieldNativePullback.{u, w} k Ω K Ψ e q).app Q) (congrArg (fun a => a.app Q)
      (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e q))


/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For any injective resolutions I of Q and J of LQ, the section
resolution pullback square commutes:
χ_J ∘ a_IJ = b_e^q(Q) ∘ χ_I in degree q. -/
theorem fieldDerivedPullbackResolutionMap_native_square
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q)
    (J : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :
    fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
      (fieldGammaNativeResolutionIso.{u, w} K Ψ q J).hom =
    (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q := by
  exact fieldResolutionNativeSquareProof.{u, w} k Ω K Ψ e q I J

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
For choices I, I′ resolving Q and J, J′ resolving LQ, the
realized pullbacks satisfy a_I′J′ ∘ comp_(I,I′) =
comp_(J,J′) ∘ a_IJ, where the comparisons are the canonical
cohomology isomorphisms of the two injective resolutions. -/
theorem fieldDerivedPullbackResolutionMap_choice
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I I' : InjectiveResolution Q)
    (J J' : InjectiveResolution
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) :
    (InjectiveResolution.cohomologyComparisonIso I I'
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom ≫
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
    fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
      (InjectiveResolution.cohomologyComparisonIso J J'
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom := by
  exact resolution_realization_choice
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (I'.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J'.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q)

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a sheaf F with coefficient universe w, set Q = Lift(F) in c.
The comparison square χ_K ∘ a_e^q(Q) = b_e^q(Q) ∘ χ_k holds
on this lifted sheaf in every q ∈ ℕ. -/
theorem original_field_derived_pullback_native_square
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}) :
    (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) =
    (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) :=
  congrArg (fun a => a.app ((liftCoefficients.{u, w} (Spec (.of k))).obj F))
    (fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e q)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

set_option linter.defProp false in
-- Bind the SAME actual source/target augmentation equations and existing Γ naturality first.
/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
Let t : Q → Q′, injective resolutions I, I′ of Q, Q′ and
J, J′ of LQ, LQ′, and cochain maps α : I → I′, β : J → J′
extending t and L(t) on augmentations be given.
The realized maps obey
a_I′J′ ∘ Hᑫ(Γ_k(α)) = Hᑫ(Γ_K(β)) ∘ a_IJ. -/
def fieldResolutionCoefficientNaturalityProof
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
    (I : InjectiveResolution Q) (I' : InjectiveResolution Q')
    (J : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
      Q))
    (J' : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
      e)).obj Q'))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0)
    (ψ : J.cocomplex ⟶ J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 =
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f ≫ J'.ι.f 0) :=
  resolution_realization_naturality
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (I'.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (J'.isoRightDerivedObj (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map f)
    (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f))
    (HomologicalComplex.homologyMap
      (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ) q)
    (HomologicalComplex.homologyMap
      (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ψ) q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app Q')
    (InjectiveResolution.isoRightDerivedObj_hom_naturality f I I' φ hφ
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (InjectiveResolution.isoRightDerivedObj_hom_naturality
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f) J J' ψ hψ
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q)
    (fieldDerivedPullback_naturality.{u, w} k Ω K Ψ e q f)

/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
For t : Q → Q′ and augmented cochain comparisons
α : I_Q → I_Q′ over t and β : J_LQ → J_LQ′ over L(t),
the chosen-resolution pullbacks satisfy
a_I′J′ ∘ Hᑫ(Γ_k(α)) = Hᑫ(Γ_K(β)) ∘ a_IJ.
Both augmentation compatibility equations are hypotheses. -/
theorem fieldDerivedPullbackResolutionMap_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
    (I : InjectiveResolution Q) (I' : InjectiveResolution Q')
    (J : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
      Q))
    (J' : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
      e)).obj Q'))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0)
    (ψ : J.cocomplex ⟶ J'.cocomplex)
    (hψ : J.ι.f 0 ≫ ψ.f 0 =
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f ≫ J'.ι.f 0) :
    HomologicalComplex.homologyMap
      (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ) q ≫
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
    fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
      HomologicalComplex.homologyMap
        (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ψ) q :=
  fieldResolutionCoefficientNaturalityProof.{u, w} k Ω K Ψ e q f I I' J J' φ hφ ψ hψ

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

open CategoryTheory.CohomologicalDeltaFunctor
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a coefficient sheaf Q, b_e^q is the cohomology map of
homogeneous cochain restriction along φ, followed by the cohomology
map of Res_φ(E(Q)) ≅ E′(LQ).
Restriction precomposes each group coordinate with φ. -/
theorem fieldNativePullback_original_map (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q =
      ContinuousCohomology.discreteCoefficientForget.{max u w}.map
        (HomologicalComplex.homologyMap
          (fieldOriginalRankRestrictionCochainMap.{u, w} k Ω K Ψ
            (GaloisUnits.FieldMap.restrictContinuous e)
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) q) ≫
      (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) :=
  (fieldNativePullback_app.{u, w} k Ω K Ψ e q Q).trans
    (congrArg (fun a => a ≫ (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
      ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q))
      (fieldOriginalRankRestrictionDeltaHom_original_map.{u, w} k Ω K Ψ
        (GaloisUnits.FieldMap.restrictContinuous e) q
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)))

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
The source delta system has degree q functor
Q ↦ Hᑫ_cts(G,E(Q)), with the continuous connecting maps on stalk
images of short exact coefficient sheaves. -/
def fieldNativeSourceDeltaSystem (e : GaloisUnits.FieldMap k Ω K Ψ) :=
  (Arrow.mk (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e)).left

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
The target delta system has degree q functor
Q ↦ Hᑫ_cts(H,E′(LQ)), with connecting maps after exact inverse
image and the target Galois stalk functor. -/
def fieldNativeTargetDeltaSystem (e : GaloisUnits.FieldMap k Ω K Ψ) :=
  (Arrow.mk (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e)).right


/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a short exact coefficient sequence S, continuous pullback
commutes with the two connecting families:
b_e^(q+1)(S₁) ∘ δ_source = δ_target ∘ b_e^q(S₃). -/
theorem fieldNativePullback_connecting (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    ((fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e (q + 1)).app S.obj.X₁ =
    (fieldNativePullback.{u, w} k Ω K Ψ e q).app S.obj.X₃ ≫
      ((fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S :=
  DeltaFunctor.System.comm (fieldNativePullbackDeltaHom.{u, w} k Ω K Ψ e).hom q S

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a map t : F → F′ of sheaves with coefficients in w, lift
both to c. The maps b_e^q are natural with respect to the source
cohomology of E(Lift(t)) and target cohomology of E′(L(Lift(t))). -/
theorem original_field_native_pullback_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F') :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
      fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
    (fieldNativePullback.{u, w} k Ω K Ψ e q).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
      (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
          fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
        ((liftCoefficients.{u, w} (Spec (.of k))).map f) :=
  (fieldNativePullback.{u, w} k Ω K Ψ e q).naturality
    ((liftCoefficients.{u, w} (Spec (.of k))).map f)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
The source delta system is exactly the continuous G-cohomology
delta functor precomposed with E, including its connecting maps
on stalk images of short exact sheaf sequences. -/
theorem fieldNativeSourceDeltaSystem_eq (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e =
      CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω) := rfl

local instance nativeSystemIdentification_inverseImage_additive
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
The target delta system is exactly continuous H-cohomology
precomposed with E′ and then L, including the connecting maps
on the inverse images of short exact sheaf sequences. -/
theorem fieldNativeTargetDeltaSystem_eq (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e =
      CohomologicalDeltaFunctor.precompose
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
        (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ)) := rfl

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a short exact sheaf sequence S, the source connecting map
equals the canonical continuous G-cohomology connector on E(S),
under the source delta-functor identification. -/
theorem fieldNativeSourceConnecting_identification (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    HEq ((fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).connecting q |>.app S)
      ((CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
        (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
        (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)).connecting q |>.app S) :=
  CohomologicalDeltaFunctor.equal_system_connecting
    (fieldNativeSourceDeltaSystem_eq.{u, w} k Ω K Ψ e) q S

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
For a short exact sheaf sequence S, the target connecting map
equals the canonical continuous H-cohomology connector on E′(L(S)),
under the target delta-functor identification. -/
theorem fieldNativeTargetConnecting_identification (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex.ShortExactSequences
      (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})) :
    HEq ((fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).connecting q |>.app S)
      ((CohomologicalDeltaFunctor.precompose
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
        (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
        (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ))).connecting q |>.app S) :=
  CohomologicalDeltaFunctor.equal_system_connecting
    (fieldNativeTargetDeltaSystem_eq.{u, w} k Ω K Ψ e) q S

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
In degree q, the source system's functor is
E followed by Hᑫ_cts(G,-) on the common coefficient sheaf category. -/
theorem fieldNativeSourceDeltaSystem_T (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    (fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).T q =
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q := rfl

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
In degree q, the target system's functor is
L followed by E′ and Hᑫ_cts(H,-) on the common coefficient sheaf category. -/
theorem fieldNativeTargetDeltaSystem_T (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ) :
    (fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).T q =
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
          fieldContinuousCohomologyFunctor.{u, w} K Ψ q := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For a short exact sequence S of discrete continuous G-modules,
the delta-functor connecting map Hᑫ_cts(G,S₃) → Hᑫ⁺¹_cts(G,S₁)
equals the continuous coefficient-sequence connecting map obtained
from the exact underlying abelian-group sequence. -/
theorem fieldOldNativeDelta_connector (q : ℕ)
    (S : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω)) :
    ((fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω).connecting q).app S =
      ContinuousCohomology.discreteCoefficientConnecting.{u, w}
        (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj
        (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property) q := rfl

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For M a discrete continuous G-module, the comparison family
Hᑫ_cts(G,M) ≅ Hᑫ(Inv_G(I)) over injective resolutions I of M
equals the family obtained from Hᑫ_cts(G,M) ≅ RᑫInv_G(M)
and the injective-resolution realization. -/
theorem fieldNativeActualResolutionFamily (q : ℕ) (M : FieldCohomologyModule.{u, w} k Ω) :
    (fun R : InjectiveResolution M => fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q R)
      =
      (fun R : InjectiveResolution M => InjectiveResolution.actualHomologyResolutionIso
        (fieldInvariantFunctor.{u, w} k Ω) q R
        ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app M)) := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The canonical presentation isomorphism identifies invariant
cohomology of the specified mapped stalk resolution with B_I,
the cohomology of the functorially mapped resolution E(I).
It uses the equality of their resolution complexes. -/
def fieldMappedNativePresentationIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  InjectiveResolution.homologyResolutionPresentationIso (fieldInvariantFunctor.{u, w} k Ω) q
    (fieldMappedInjectiveResolution.{u, w} k Ω I)
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I) rfl

set_option linter.defProp false in
/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
Following the continuous-cohomology comparison for the specified
mapped resolution by its presentation isomorphism gives the comparison
for E(I). This is the compatibility equality of the two invariant
resolution presentations. -/
def fieldMappedNativePresentationProof (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  InjectiveResolution.actualHomologyResolutionIso_presentation
    (fieldInvariantFunctor.{u, w} k Ω) q
    (fieldMappedInjectiveResolution.{u, w} k Ω I)
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I) rfl
    ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The right comparison C_Q ≅ B_I is the continuous-to-invariant
resolution isomorphism followed by the canonical presentation
comparison to E(I). -/
def fieldMappedNativeRightIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  fieldContinuousDerivedInvariantsResolutionIso.{u, w} k Ω q
    (fieldMappedInjectiveResolution.{u, w} k Ω I) ≪≫ fieldMappedNativePresentationIso.{u, w} k Ω q I

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The right comparison C_Q ≅ B_I can also be written as
C_Q ≅ RᑫInv_G(E(Q)) followed by the realization
RᑫInv_G(E(Q)) ≅ Hᑫ(Inv_G(E(I))). -/
def fieldMappedNativeRawRightIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≪≫
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).mapInjectiveResolution I).isoRightDerivedObj
      (fieldInvariantFunctor.{u, w} k Ω) q

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The comparison through the mapped-resolution presentation equals
the comparison through RᑫInv_G(E(Q)), as isomorphisms C_Q ≅ B_I. -/
theorem fieldMappedNativeRightIso_presentation (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldMappedNativeRightIso.{u, w} k Ω q I =
      fieldMappedNativeRawRightIso.{u, w} k Ω q I := by
  have h := congrFun (fieldNativeActualResolutionFamily.{u, w} k Ω q
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))
      (fieldMappedInjectiveResolution.{u, w} k Ω I)
  exact (congrArg (fun b => b ≪≫ fieldMappedNativePresentationIso.{u, w} k Ω q I) h).trans
    (fieldMappedNativePresentationProof.{u, w} k Ω q I)

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The section-resolution comparison A_I ≅ C_Q is the composite
A_I ≅ RᑫΓ_k(Q) ≅ RᑫInv_G(E(Q)) ≅ C_Q,
using global sections as Galois invariants and the continuous/derived
invariant comparison. -/
def fieldMappedNativeRawGammaIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).symm
    ≪≫
    ((Functor.rightDerivedPrecompIsoOfIso (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (fieldInvariantFunctor.{u, w} k Ω) (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q).app Q ≪≫
      ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).symm)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The canonical left comparison A_I ≅ B_I is induced by the
global-section/invariant natural isomorphism Γ_k ≅ Inv_G ∘ E,
applied to I and then to degree q homology. -/
def fieldMappedNativeRawLeftIso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  Functor.rightDerivedPrecompHomologyIsoOfIso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The field section-resolution/continuous comparison equals its
factorization through derived global sections and derived invariants,
as an isomorphism A_I ≅ C_Q. -/
theorem fieldMappedNativeGammaIso_eq (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldGammaNativeResolutionIso.{u, w} k Ω q I = fieldMappedNativeRawGammaIso.{u, w} k Ω q I :=
  resolution_natIso_app (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
    (fieldDerivedSectionsInvariantsIso.{u, w} k Ω q)
    (fieldContinuousDerivedInvariantsIso.{u, w} k Ω q) Q
    (I.isoRightDerivedObj (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The canonical section-to-invariant resolution comparison equals
the homology isomorphism of Γ_k(I) ≅ Inv_G(E(I)). -/
theorem fieldMappedNativeLeftIso_eq (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I =
      fieldMappedNativeRawLeftIso.{u, w} k Ω q I := rfl

set_option linter.defProp false in
-- The complete actual generic formula is an iso equality, avoiding repeated hom-codomain inference.
/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
If ℓ_I : A_I ≅ B_I is the section/invariant comparison and
r_I : C_Q ≅ B_I the continuous/invariant comparison, then the
section/continuous comparison is r_I⁻¹ ∘ ℓ_I. -/
def fieldMappedNativeRawIsoProof (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :=
  Functor.precomp_native_resolution_iso
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω) (fieldInvariantFunctor.{u, w} k Ω)
    (fieldGlobalSectionsInvariantsIso.{u, w} k Ω) q I
    ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω q).app
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q))

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The canonical field section/continuous resolution isomorphism equals
ℓ_I followed by r_I⁻¹, where ℓ_I : A_I ≅ B_I and
r_I : C_Q ≅ B_I are the mapped invariant comparisons. -/
theorem fieldGammaNativeResolutionIso_mapped_T_iso (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    fieldGammaNativeResolutionIso.{u, w} k Ω q I =
      fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I ≪≫
        (fieldMappedNativeRightIso.{u, w} k Ω q I).symm := by
  have h := fieldMappedNativeRawIsoProof.{u, w} k Ω q I
  change fieldMappedNativeRawGammaIso.{u, w} k Ω q I =
    fieldMappedNativeRawLeftIso.{u, w} k Ω q I ≪≫
      (fieldMappedNativeRawRightIso.{u, w} k Ω q I).symm at h
  exact (fieldMappedNativeGammaIso_eq.{u, w} k Ω q I).trans
    (h.trans (inverse_comp_iso_eq
      (fieldMappedNativeRawLeftIso.{u, w} k Ω q I)
      (fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I)
      (fieldMappedNativeRawRightIso.{u, w} k Ω q I)
      (fieldMappedNativeRightIso.{u, w} k Ω q I)
      (fieldMappedNativeLeftIso_eq.{u, w} k Ω q I).symm
      (fieldMappedNativeRightIso_presentation.{u, w} k Ω q I).symm))

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), c = max(u, w), E the Galois stalk functor on abelian
étale sheaves over k with coefficients in c, and Γ_k global sections.
For q ∈ ℕ and an injective resolution I of Q, put
A_I = Hᑫ(Γ_k(I)), B_I = Hᑫ(Inv_G(E(I))), and C_Q = Hᑫ_cts(G, E(Q)),
where Inv_G(M) = M^G.
The forward section/continuous comparison is
A_I → B_I → C_Q, namely the forward section/invariant map
followed by the inverse continuous/invariant map. -/
theorem fieldGammaNativeResolutionIso_mapped_T (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q) :
    (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom =
      (fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
        (fieldMappedNativeRightIso.{u, w} k Ω q I).inv :=
  congrArg Iso.hom (fieldGammaNativeResolutionIso_mapped_T_iso.{u, w} k Ω q I)

end AlgebraicGeometry.Scheme.DerivedSections

end

section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ]

local instance fieldOriginalConnecting_inverseImage_additive
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
For a short exact sequence S of common-universe étale sheaves,
derived-section pullback commutes with the étale connecting maps:
a_e^(q+1)(S₁) ∘ δ_S = δ_(L(S)) ∘ a_e^q(S₃).
The target sequence is short exact by exactness of L. -/
theorem fieldDerivedPullback_etale_connecting
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    (S : ShortComplex (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) :
    AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁ =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃ ≫
        AddCommGrpCat.ofHom
          (CanonicalLongExactSequence.derivedBoundary.{u, w}
            (smallEtaleInverseImage_shortExact.{u, w}
              (fieldOriginalPullback k Ω K Ψ e) S hS) q) := by
  let L := smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)
  let hL := smallEtaleInverseImage_shortExact.{u, w}
    (fieldOriginalPullback k Ω K Ψ e) S hS
  exact connector_equality_transport
    (AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q))
    ((Functor.rightDerivedConnecting (OriginalGammaBridge.Γ.{u, w} (Spec (.of k)))
      q).app ⟨S, hS⟩)
    (AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hL q))
    ((Functor.rightDerivedConnecting (OriginalGammaBridge.Γ.{u, w} (Spec (.of K)))
      q).app ⟨S.map L, hL⟩)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁)
    ((fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃)
    (OriginalGammaBridge.derivedBoundary_eq_canonicalConnecting.{u, w}
      (Spec (.of k)) S hS q)
    (OriginalGammaBridge.derivedBoundary_eq_canonicalConnecting.{u, w}
      (Spec (.of K)) (S.map L) hL q)
    (fieldDerivedPullback_connecting.{u, w} k Ω K Ψ e q ⟨S, hS⟩)

/-- Let k, Ω, K, Ψ be fields in universe u with k-algebra Ω,
K-algebra Ψ and compatible embeddings e = (β, σ).
Put c = max(u, w), f = Spec β : Spec K → Spec k and L = f*.
Let F′ → F → F″ have coefficients in universe w, with the first
map injective and image equal to the second map's kernel on each
étale section group, and the second map locally surjective.
After lifting to c, derived pullback commutes with the connecting
map of this short exact sequence and its inverse image. -/
theorem original_field_derived_pullback_etale_connecting
    (e : GaloisUnits.FieldMap k Ω K Ψ) (q : ℕ)
    {F' F F'' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}}
    {a : F' ⟶ F} {b : F ⟶ F''} (h : originalSmallEtaleLocalShortExact a b) :
    let S := coefficientLiftLocalShortComplex h
    let hS := coefficientLift_shortExact h
    let hL := smallEtaleInverseImage_shortExact.{u, w}
      (fieldOriginalPullback k Ω K Ψ e) S hS
    AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) ≫
        (fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁ =
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃ ≫
        AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hL q) :=
  fieldDerivedPullback_etale_connecting.{u, w} k Ω K Ψ e q
    (coefficientLiftLocalShortComplex h) (coefficientLift_shortExact h)

end AlgebraicGeometry.Scheme.DerivedSections

end

section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]

local instance fullFieldNaturality_inverseImage_additive (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).Additive :=
  smallEtaleInverseImage_additive.{u, w} (fieldOriginalPullback k Ω K Ψ e)

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
This proposition records the base-changed geometric-point projections,
germ formula through the adjunction unit, equivariant stalk change and
terminal-section/invariant degree-zero maps. It includes naturality,
all-degree derived/continuous comparison, the homogeneous restriction map,
the identified delta systems and connectors, and their compatibility
with étale connecting maps after coefficient lifting.
It also records arbitrary resolution squares, choice and augmented-map
naturality, the mapped invariant-cohomology factorization, identity and
composition laws, and the bijection of finite étale algebra embeddings
under σ. All these properties use the specified maps for e. -/
structure FieldSiteModuleCohomologyNaturalityLaws (e : GaloisUnits.FieldMap k Ω K Ψ) : Prop where
  point_fst : ∀ (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U),
      (fieldChangeOriginalPoint k Ω K Ψ e U z).left ≫
          pullback.fst U.hom (fieldOriginalPullback k Ω K Ψ e) =
        fieldChangeSpec k Ω K Ψ e ≫ z.left

  point_snd : ∀ (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U),
      (fieldChangeOriginalPoint k Ω K Ψ e U z).left ≫
          pullback.snd U.hom (fieldOriginalPullback k Ω K Ψ e) = Spec.algebraMap K Ψ

  original_germ : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U),
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) Q.obj ≫ (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q =
        ((smallEtaleInverseImageAdjunction.{u, w} (fieldOriginalPullback k Ω K Ψ e)).unit.app
          Q).hom.app
            (op U) ≫
          (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
            ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
            (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj

  left_action : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (h : Gal(Ψ/K)) (m : fieldGeometricStalkCarrier.{u, w} k Ω Q),
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
          ((GaloisUnits.FieldMap.restrictHom e h) • m) =
        h • (show fieldGeometricStalkCarrier.{u, w} K Ψ
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) from
          (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q m)

  same_underlying_stalk : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (DiscreteAbelianAction.forget Gal(Ψ/K)).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q) =
        (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q

  terminal_sections : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q ≫
          (fieldGammaSectionsIso.{u, w} K).hom.app
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) =
        (fieldGammaSectionsIso.{u, w} k).hom.app Q ≫
          ((smallEtaleInverseImageAdjunction.{u, w}
            (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)) ≫
          (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
            (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op)

  zero_invariants : fieldPullbackGlobalSections.{u, w} k Ω K Ψ e ≫
          Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
            (fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom =
        (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom ≫
          Functor.whiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
            (fieldInvariantRestriction.{u, u, w} k Ω K Ψ
              (GaloisUnits.FieldMap.restrictContinuous e)) ≫
          Functor.whiskerRight (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom
            (fieldInvariantFunctor.{u, w} K Ψ)

  single_lift_germ : (∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (c : F.obj.obj (op U)),
      let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
          ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
            U (ULift.up z) Q.obj (ULift.up c)) =
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
          ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
          (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj
          (((smallEtaleInverseImageAdjunction.{u, w}
            (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op U) (ULift.up c)))

  single_lift_stalk_map : ∀ {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ :
    F ⟶ F'),
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
          GaloisUnits.restrictModules (GaloisUnits.FieldMap.restrictContinuous e)).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map τ) ≫
          (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
        (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
            fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).map
              ((liftCoefficients.{u, w} (Spec (.of k))).map τ)

  gamma_naturality : ∀ (n : ℕ)
      {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q'),
      ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map τ ≫
          (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q' =
        (fieldDerivedPullback.{u, w} k Ω K Ψ e n).app Q ≫
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
            (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived n).map
              τ)

  gamma_zero : fieldDerivedPullback.{u, w} k Ω K Ψ e 0 ≫
          Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
            (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
              w}).rightDerivedZeroIsoSelf.hom =
        (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u
          w}).rightDerivedZeroIsoSelf.hom ≫
          fieldPullbackGlobalSections.{u, w} k Ω K Ψ e

  all_degree_comparison : ∀ (q : ℕ),
      fieldDerivedPullback.{u, w} k Ω K Ψ e q ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom ≫
        fieldNativePullback.{u, w} k Ω K Ψ e q

  literal_original_cochains : ∀ (q : ℕ)
      (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q =
        ContinuousCohomology.discreteCoefficientForget.{max u w}.map
          (HomologicalComplex.homologyMap
            (fieldOriginalRankRestrictionCochainMap.{u, w} k Ω K Ψ
              (GaloisUnits.FieldMap.restrictContinuous e)
              ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) q) ≫
        (fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)

  native_zero_invariants : ∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}),
      (fieldNativePullback.{u, w} k Ω K Ψ e 0).app Q ≫
        (fieldContinuousCohomologyZeroIso.{u, w} K Ψ).hom.app
          ((fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).obj
            ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) =
      (fieldContinuousCohomologyZeroIso.{u, w} k Ω).hom.app
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
        (fieldInvariantRestriction.{u, u, w} k Ω K Ψ (GaloisUnits.FieldMap.restrictContinuous
          e)).app
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) ≫
        (fieldInvariantFunctor.{u, w} K Ψ).map
          ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)

  native_source_system : fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e =
        CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
          (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} k Ω))
          (fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω)

  native_target_system : fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e =
        CohomologicalDeltaFunctor.precompose
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldNativeInverseImageShortExact.{u, w} k Ω K Ψ e)
          (CohomologicalDeltaFunctor.precompose (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ)
            (Functor.RightDerived.precompShortExact (fieldGeometricStalkGaloisFunctor.{u, w} K Ψ))
            (fieldContinuousCohomologyDeltaFunctor.{u, w} K Ψ))

  source_degree_objects : ∀ (q : ℕ),
      (fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).T q =
        fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
          fieldContinuousCohomologyFunctor.{u, w} k Ω q

  target_degree_objects : ∀ (q : ℕ),
      (fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).T q =
        smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
            fieldContinuousCohomologyFunctor.{u, w} K Ψ q

  old_native_connector : ∀ (q : ℕ)
      (S : ShortComplex.ShortExactSequences (FieldCohomologyModule.{u, w} k Ω)),
      ((fieldContinuousCohomologyDeltaFunctor.{u, w} k Ω).connecting q).app S =
        ContinuousCohomology.discreteCoefficientConnecting.{u, w}
          (G := InfiniteGalois.profiniteGalGrp k Ω) S.obj
          (fieldShortExact_discreteCoefficientExact.{u, w} k Ω S.obj S.property) q

  native_connecting : ∀ (q : ℕ)
      (S : ShortComplex.ShortExactSequences
        (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})),
      ((fieldNativeSourceDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e (q + 1)).app S.obj.X₁ =
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app S.obj.X₃ ≫
        ((fieldNativeTargetDeltaSystem.{u, w} k Ω K Ψ e).connecting q).app S

  original_etale_connecting : ∀ (q : ℕ)
      (S : ShortComplex (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}))
      (hS : S.ShortExact),
      AddCommGrpCat.ofHom (CanonicalLongExactSequence.derivedBoundary.{u, w} hS q) ≫
          (fieldDerivedPullback.{u, w} k Ω K Ψ e (q + 1)).app S.X₁ =
        (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app S.X₃ ≫
          AddCommGrpCat.ofHom
            (CanonicalLongExactSequence.derivedBoundary.{u, w}
              (smallEtaleInverseImage_shortExact.{u, w}
                (fieldOriginalPullback k Ω K Ψ e) S hS) q)

  single_lift_all_degree : ∀ (q : ℕ)
      (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}),
      (fieldDerivedPullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (fieldDerivedSectionsContinuousCohomologyIso.{u, w} K Ψ q).hom.app
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj
            ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) =
      (fieldDerivedSectionsContinuousCohomologyIso.{u, w} k Ω q).hom.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F)

  single_lift_coefficient_maps : ∀ (q : ℕ)
      {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (f : F ⟶ F'),
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f) ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
      (fieldNativePullback.{u, w} k Ω K Ψ e q).app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          fieldGeometricStalkGaloisFunctor.{u, w} K Ψ ⋙
            fieldContinuousCohomologyFunctor.{u, w} K Ψ q).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map f)

  resolution_square : ∀ (q : ℕ)
      {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      (I : InjectiveResolution Q)
      (J : InjectiveResolution
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)),
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
        (fieldGammaNativeResolutionIso.{u, w} K Ψ q J).hom =
      (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom ≫
        (fieldNativePullback.{u, w} k Ω K Ψ e q).app Q

  resolution_choices : ∀ (q : ℕ)
      {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      (I I' : InjectiveResolution Q)
      (J J' : InjectiveResolution
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)),
      (InjectiveResolution.cohomologyComparisonIso I I'
        (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom ≫
        fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
        (InjectiveResolution.cohomologyComparisonIso J J'
          (Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}) q).hom

  augmented_resolution_maps : ∀ (q : ℕ)
      {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q')
      (I : InjectiveResolution Q) (I' : InjectiveResolution Q')
      (J : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
        e)).obj Q))
      (J' : InjectiveResolution ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ
        e)).obj Q'))
      (φ : I.cocomplex ⟶ I'.cocomplex)
      (_hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ I'.ι.f 0)
      (ψ : J.cocomplex ⟶ J'.cocomplex)
      (_hψ : J.ι.f 0 ≫ ψ.f 0 =
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).map f ≫ J'.ι.f 0),
      HomologicalComplex.homologyMap
        (((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ) q ≫
        fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I' J' =
      fieldDerivedPullbackResolutionMap.{u, w} k Ω K Ψ e q I J ≫
        HomologicalComplex.homologyMap
          (((Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u
            w}).mapHomologicalComplex
            (ComplexShape.up ℕ)).map ψ) q

  canonical_mapped_p : ∀ (q : ℕ)
      {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      (I : InjectiveResolution Q),
      fieldMappedNativeRightIso.{u, w} k Ω q I =
        fieldMappedNativeRawRightIso.{u, w} k Ω q I

  mapped_T_homology_formula : ∀ (q : ℕ)
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (I : InjectiveResolution Q),
    (fieldGammaNativeResolutionIso.{u, w} k Ω q I).hom =
      (fieldDerivedSectionsInvariantsResolutionIso.{u, w} k Ω q I).hom ≫
        (fieldMappedNativeRightIso.{u, w} k Ω q I).inv

  gamma_identity : ∀ (q : ℕ),
      fieldDerivedPullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
        Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
          ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
      𝟙 ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)

  native_identity : ∀ (q : ℕ),
      fieldNativePullback.{u, w} k Ω k Ω (GaloisUnits.FieldMap.id k Ω) q ≫
        Functor.whiskerRight (fieldInverseImageIdentityIso.{u, w} k Ω).hom
          (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
            fieldContinuousCohomologyFunctor.{u, w} k Ω q) =
      𝟙 (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldContinuousCohomologyFunctor.{u, w} k Ω q)

  finite_algebra_embedding :
    letI : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
    ∀ A : CommAlgCat.FiniteEtale.{u} k,
      Function.Bijective (fun f : A →ₐ[k] Ω =>
        (GaloisUnits.FieldMap.extensionAlgHom e).comp f)
  gamma_composition :
    ∀ (L Φ : Type u) [Field L] [Field Φ] [Algebra L Φ] [IsSepClosure L Φ]
      (eNext : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ),
      fieldDerivedPullback.{u, w} k Ω K Ψ e q ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldDerivedPullback.{u, w} K Ψ L Φ eNext q) ≫
        (Functor.associator
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ eNext))
          ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv
            ≫
        Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e eNext).hom
          ((Sheaf.Γ (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
      fieldDerivedPullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp eNext e) q
  native_composition :
    ∀ (L Φ : Type u) [Field L] [Field Φ] [Algebra L Φ] [IsSepClosure L Φ]
      (eNext : GaloisUnits.FieldMap K Ψ L Φ) (q : ℕ),
      fieldNativePullback.{u, w} k Ω K Ψ e q ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldNativePullback.{u, w} K Ψ L Φ eNext q) ≫
        (Functor.associator
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (smallEtaleInverseImage.{u, w} (fieldOriginalPullback K Ψ L Φ eNext))
          (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
            fieldContinuousCohomologyFunctor.{u, w} L Φ q)).inv ≫
        Functor.whiskerRight (fieldInverseImageCompositionIso.{u, w} k Ω K Ψ L Φ e eNext).hom
          (fieldGeometricStalkGaloisFunctor.{u, w} L Φ ⋙
            fieldContinuousCohomologyFunctor.{u, w} L Φ q) =
      fieldNativePullback.{u, w} k Ω L Φ (GaloisUnits.FieldMap.comp eNext e) q

/-- Let Ω/k and Ψ/K be separable closures of fields in universe u,
e = (β, σ) compatible base and closure embeddings, G = Gal(Ω/k),
H = Gal(Ψ/K), c = max(u, w), and f = Spec β.
Let L = f*, E and E′ the Galois stalk functors, and φ = res_e : H → G.
The stated point, germ, coefficient, invariant, derived-section and
continuous-cohomology properties hold for e in every degree.
They include arbitrary injective-resolution choices and comparisons,
connecting maps for lifted local short exact sequences, and the
identity/composition laws of both pullback constructions. -/
theorem original_field_site_module_cohomology_naturality (e : GaloisUnits.FieldMap k Ω K Ψ) :
    FieldSiteModuleCohomologyNaturalityLaws.{u, w} k Ω K Ψ e where
  point_fst := fieldChangeOriginalPoint_fst.{u} k Ω K Ψ e
  point_snd := fieldChangeOriginalPoint_snd.{u} k Ω K Ψ e
  original_germ := fieldChangeUnderlyingStalkIso_original_germ.{u, w} k Ω K Ψ e
  left_action := fieldChangeUnderlyingStalkIso_equivariant.{u, w} k Ω K Ψ e
  same_underlying_stalk := fieldChangeStalkModuleIso_hom_underlying.{u, w} k Ω K Ψ e
  terminal_sections := fieldPullbackGlobalSections_terminal_section.{u, w} k Ω K Ψ e
  zero_invariants := fieldPullbackGlobalSections_invariants_naturality.{u, w} k Ω K Ψ e
  single_lift_germ := fieldChange_original_coefficient_germ.{u, w} k Ω K Ψ e
  single_lift_stalk_map := fieldChange_original_coefficient_naturality.{u, w} k Ω K Ψ e
  gamma_naturality := fieldDerivedPullback_naturality.{u, w} k Ω K Ψ e
  gamma_zero := fieldDerivedPullback_zero.{u, w} k Ω K Ψ e
  all_degree_comparison := fieldDerivedPullback_native_square.{u, w} k Ω K Ψ e
  literal_original_cochains := fieldNativePullback_original_map.{u, w} k Ω K Ψ e
  native_zero_invariants := fieldNativePullback_zero_invariants.{u, w} k Ω K Ψ e
  native_source_system := fieldNativeSourceDeltaSystem_eq.{u, w} k Ω K Ψ e
  native_target_system := fieldNativeTargetDeltaSystem_eq.{u, w} k Ω K Ψ e
  source_degree_objects := fieldNativeSourceDeltaSystem_T.{u, w} k Ω K Ψ e
  target_degree_objects := fieldNativeTargetDeltaSystem_T.{u, w} k Ω K Ψ e
  old_native_connector := fieldOldNativeDelta_connector.{u, w} k Ω
  native_connecting := fieldNativePullback_connecting.{u, w} k Ω K Ψ e
  original_etale_connecting := fieldDerivedPullback_etale_connecting.{u, w} k Ω K Ψ e
  single_lift_all_degree := original_field_derived_pullback_native_square.{u, w} k Ω K Ψ e
  single_lift_coefficient_maps := original_field_native_pullback_naturality.{u, w} k Ω K Ψ e
  resolution_square := fieldDerivedPullbackResolutionMap_native_square.{u, w} k Ω K Ψ e
  resolution_choices := fieldDerivedPullbackResolutionMap_choice.{u, w} k Ω K Ψ e
  augmented_resolution_maps := fieldDerivedPullbackResolutionMap_naturality.{u, w} k Ω K Ψ e
  canonical_mapped_p := fieldMappedNativeRightIso_presentation.{u, w} k Ω
  mapped_T_homology_formula := fieldGammaNativeResolutionIso_mapped_T.{u, w} k Ω
  gamma_identity := fieldDerivedPullback_id.{u, w} k Ω
  native_identity := fieldNativePullback_id.{u, w} k Ω

  finite_algebra_embedding := by
    let : Algebra k Ψ := GaloisUnits.FieldMap.sourceBaseAlgebra e
    intro A
    exact (CommAlgCat.FiniteEtale.embeddingHomEquiv k Ω Ψ
      (GaloisUnits.FieldMap.extensionAlgHom e) A).bijective
  gamma_composition := fun L Φ _ _ _ _ eNext q =>
    fieldDerivedPullback_comp.{u, w} k Ω K Ψ L Φ e eNext q
  native_composition := fun L Φ _ _ _ _ eNext q =>
    fieldNativePullback_comp.{u, w} k Ω K Ψ L Φ e eNext q

end AlgebraicGeometry.Scheme.DerivedSections

#print axioms
AlgebraicGeometry.Scheme.DerivedSections.original_field_site_module_cohomology_naturality

end
