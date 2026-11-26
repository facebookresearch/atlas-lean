/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.InvariantHomogeneousComplex
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-!
# Continuous cochains in two universe-parameter presentations

Let G be a profinite group in universe u and c = max(u,w).
A coefficient representation with carrier c has homogeneous cochain
presentations labelled by w and by c. Their tuple-form and nested complexes
are canonically isomorphic, preserving the same coefficients and group
coordinate values.

The comparisons are natural in coefficients, commute with the cohomology
realizations and connecting maps of exact discrete coefficient sequences,
and preserve identity evaluation in degree zero.
For G,H,K in universe u, the fixed-carrier group/coefficient maps satisfy
identity, composition and cycle-class laws, and commute with the parameter
comparisons.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable (G : ProfiniteGrp.{u})

/-- Let G be a profinite group in universe u and c = max(u,w).
Let X be a topological ℤ-representation with carrier in c.
The coefficient-universe parameters w and c describe this same carrier.
The tuple-form homogeneous degree q terms at parameters w and c
are isomorphic in topological ℤ-modules, by the same continuous
equivariant function on G^(q+1). -/
def sameRankFlatTermIso (X : TopRep.{max u w, 0, u} ℤ G) (q : ℕ) :
    flatHomogeneousTerm.{0, u, w} X q ≅
      flatHomogeneousTerm.{0, u, max u w} X q := Iso.refl _

set_option backward.isDefEq.respectTransparency false in

theorem sameRank_flat_d (X : TopRep.{max u w, 0, u} ℤ G) (q : ℕ) :
    flatHomogeneousD.{0, u, w} X q ≫ (sameRankFlatTermIso.{u, w} G X (q + 1)).hom =
      (sameRankFlatTermIso.{u, w} G X q).hom ≫
        flatHomogeneousD.{0, u, max u w} X q := by
  change flatHomogeneousD.{0, u, w} X q = flatHomogeneousD.{0, u, max u w} X q
  apply ConcreteCategory.ext (C := TopModuleCat.{max u w} ℤ)
  change (flatHomogeneousD.{0, u, w} X q).hom =
    (flatHomogeneousD.{0, u, max u w} X q).hom
  exact DFunLike.ext _ _ (fun c => Subtype.ext (ContinuousMap.ext (fun t =>
    (flatHomogeneousD_apply.{0, u, w} X q c t).trans
      (flatHomogeneousD_apply.{0, u, max u w} X q c t).symm)))

/-- Let G be a profinite group in universe u and c = max(u,w).
Let X be a topological ℤ-representation with carrier in c.
The coefficient-universe parameters w and c describe this same carrier.
The tuple-form homogeneous complexes at parameters w and c
are isomorphic, degreewise retaining the function values and
alternating deletion differential. -/
def sameRankFlatComplexIso (X : TopRep.{max u w, 0, u} ℤ G) :
    flatHomogeneousComplex.{0, u, w} X ≅
      flatHomogeneousComplex.{0, u, max u w} X :=
  HomologicalComplex.Hom.isoOfComponents (sameRankFlatTermIso.{u, w} G X) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    dsimp only [flatHomogeneousComplex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact (sameRank_flat_d.{u, w} G X i).symm)

/-- Let G be a profinite group in universe u and c = max(u,w).
Let X be a topological ℤ-representation with carrier in c.
The coefficient-universe parameters w and c describe this same carrier.
The nested invariant homogeneous complexes at parameters w and c
are isomorphic by passing through their tuple-form comparisons. -/
def sameRankOriginalComplexIso (X : TopRep.{max u w, 0, u} ℤ G) :
    (homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X ≅
      (homogeneousCochainsFunctor.{0, u, max u w} (k := ℤ) (G := G)).obj X :=
  homogeneousFlatComplexIso.{0, u, w} X ≪≫
    sameRankFlatComplexIso.{u, w} G X ≪≫
      (homogeneousFlatComplexIso.{0, u, max u w} X).symm

end ContinuousCohomology

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable (G : ProfiniteGrp.{u})

set_option backward.isDefEq.respectTransparency false in
-- The V5 differential probe required typed function extensionality for these stored modules.
theorem sameRank_original_complex_iso_hom_apply
    (X : TopRep.{max u w, 0, u} ℤ G) (q : ℕ)
    (c : (homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X |>.X q)
    (t : Fin (q + 1) → G) :
    (homogeneousFinContinuousLinearEquiv.{0, u, max u w} X q
      ((sameRankOriginalComplexIso.{u, w} G X).hom.f q c)).val t =
        (homogeneousFinContinuousLinearEquiv.{0, u, w} X q c).val t := by
  let : Module ℤ (flatHomogeneousCochains.{0, u, max u w} X q) :=
    (flatHomogeneousCochains.{0, u, max u w} X q).module
  change (homogeneousFinContinuousLinearEquiv.{0, u, max u w} X q
    ((homogeneousFinContinuousLinearEquiv.{0, u, max u w} X q).symm
      (homogeneousFinContinuousLinearEquiv.{0, u, w} X q c))).val t = _
  exact congrArg (fun x : flatHomogeneousCochains.{0, u, max u w} X q => x.val t)
    ((homogeneousFinContinuousLinearEquiv.{0, u, max u w} X q).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
-- Same typed old/new coefficient comparison; no coefficient object is lifted.
theorem sameRank_original_complex_iso_naturality
    {X Y : TopRep.{max u w, 0, u} ℤ G} (f : X ⟶ Y) :
    (homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).map f ≫
        (sameRankOriginalComplexIso.{u, w} G Y).hom =
      (sameRankOriginalComplexIso.{u, w} G X).hom ≫
        (homogeneousCochainsFunctor.{0, u, max u w} (k := ℤ) (G := G)).map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply (cancel_mono (homogeneousFinIso.{0, u, max u w} Y q).hom).mp
  apply ConcreteCategory.ext (C := TopModuleCat.{max u w} ℤ)
  exact DFunLike.ext _ _ (fun c => Subtype.ext (ContinuousMap.ext (fun t => by
    change (homogeneousFinContinuousLinearEquiv.{0, u, max u w} Y q
        ((sameRankOriginalComplexIso.{u, w} G Y).hom.f q
          (((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).map f).f q c))).val t =
      (homogeneousFinContinuousLinearEquiv.{0, u, max u w} Y q
        (((homogeneousCochainsFunctor.{0, u, max u w} (k := ℤ) (G := G)).map f).f q
          ((sameRankOriginalComplexIso.{u, w} G X).hom.f q c))).val t
    rw [sameRank_original_complex_iso_hom_apply,
      homogeneousNestedCoefficientMap_apply.{0, u, w},
      homogeneousNestedCoefficientMap_apply.{0, u, max u w},
      sameRank_original_complex_iso_hom_apply])))

/-- Let G be a profinite group in universe u and c = max(u,w).
Let X be a topological ℤ-representation with carrier in c.
The coefficient-universe parameters w and c describe this same carrier.
The nested complex comparisons are natural in continuous equivariant
ℤ-linear coefficient maps, giving a natural isomorphism of the two
homogeneous cochain functors. -/
def sameRankOriginalComplexNatIso :
    homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G) ≅
      homogeneousCochainsFunctor.{0, u, max u w} (k := ℤ) (G := G) :=
  NatIso.ofComponents (sameRankOriginalComplexIso.{u, w} G)
    (fun f => sameRank_original_complex_iso_naturality.{u, w} G f)

/-- Let G be a profinite group in universe u and c = max(u,w).
Let A be a discrete topological ℤ-module with jointly continuous G-action.
Its continuous cochains and cohomology have presentations at parameters
w and c, on the same actual coefficient carrier.
The discrete abelian-group cochain functors at parameters w and c
are naturally isomorphic, after the same coefficient realization
and topology-forgetting functor. -/
def sameRankDiscreteCochainNatIso :
    discreteCoefficientCochainFunctor.{u, w} G ≅
      discreteCoefficientCochainFunctor.{u, max u w} G :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (discreteCoefficientTopRepFunctor.{u, w} G)
      (sameRankOriginalComplexNatIso.{u, w} G))
    (discreteCoefficientForget.{max u w}.mapHomologicalComplex (ComplexShape.up ℕ))

/-- Let G be a profinite group in universe u and c = max(u,w).
Let A be a discrete topological ℤ-module with jointly continuous G-action.
Its continuous cochains and cohomology have presentations at parameters
w and c, on the same actual coefficient carrier.
For every q ∈ ℕ, the continuous cohomology functors at parameters
w and c are naturally isomorphic on the fixed coefficient category. -/
def sameRankDiscreteCohomologyNatIso (q : ℕ) :
    discreteCoefficientCohomologyFunctor.{u, w} G q ≅
      discreteCoefficientCohomologyFunctor.{u, max u w} G q :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (discreteCoefficientTopRepFunctor.{u, w} G)
        (sameRankOriginalComplexNatIso.{u, w} G))
      (HomologicalComplex.homologyFunctor (TopModuleCat.{max u w} ℤ)
        (ComplexShape.up ℕ) q))
    discreteCoefficientForget.{max u w}

/-- Let G be a profinite group in universe u and c = max(u,w).
Let A be a discrete topological ℤ-module with jointly continuous G-action.
Its continuous cochains and cohomology have presentations at parameters
w and c, on the same actual coefficient carrier.
For the cohomology comparisons γ_w,γ_c and parameter maps α_H,α_C,
the realization square is
γ_c ∘ α_H = Hᑫ(α_C) ∘ γ_w. -/
theorem sameRank_discrete_homology_square
    (A : DiscreteContAction (TopModuleCat.{max u w} ℤ) G) (q : ℕ) :
    (sameRankDiscreteCohomologyNatIso.{u, w} G q).hom.app A ≫
        (discreteCoefficientHomologyIso.{u, max u w} G A q).hom =
      (discreteCoefficientHomologyIso.{u, w} G A q).hom ≫
        HomologicalComplex.homologyMap
          ((sameRankDiscreteCochainNatIso.{u, w} G).hom.app A) q :=
  (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ)
    q discreteCoefficientForget.{max u w}).inv.naturality
      ((sameRankOriginalComplexNatIso.{u, w} G).hom.app
        ((discreteCoefficientTopRepFunctor.{u, w} G).obj A))

end ContinuousCohomology

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable (G : ProfiniteGrp.{u})

/-- For a profinite G in universe u, c=max(u,w), and a short complex
S of discrete continuous coefficients with carrier c, the parameter
comparison gives a map from its cochain short complex at w to that at c.
The three components are the cochain parameter isomorphisms of S's terms. -/
def sameRankDiscreteSequenceMap
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max u w} ℤ) G)) :
    S.map (discreteCoefficientCochainFunctor.{u, w} G) ⟶
      S.map (discreteCoefficientCochainFunctor.{u, max u w} G) :=
  S.mapNatTrans (sameRankDiscreteCochainNatIso.{u, w} G).hom

/-- Let G be a profinite group in universe u and c = max(u,w).
Let A be a discrete topological ℤ-module with jointly continuous G-action.
Its continuous cochains and cohomology have presentations at parameters
w and c, on the same actual coefficient carrier.
The inverse realization square is
α_H ∘ γ_w⁻¹ = γ_c⁻¹ ∘ Hᑫ(α_C),
where γ_w,γ_c identify the two continuous cohomology presentations with
homology of their algebraic cochain complexes. -/
theorem sameRank_discrete_homology_inv_square
    (A : DiscreteContAction (TopModuleCat.{max u w} ℤ) G) (q : ℕ) :
    (discreteCoefficientHomologyIso.{u, w} G A q).inv ≫
        (sameRankDiscreteCohomologyNatIso.{u, w} G q).hom.app A =
      HomologicalComplex.homologyMap
        ((sameRankDiscreteCochainNatIso.{u, w} G).hom.app A) q ≫
          (discreteCoefficientHomologyIso.{u, max u w} G A q).inv :=
  ((HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ)
    q discreteCoefficientForget.{max u w}).hom.naturality
      ((sameRankOriginalComplexNatIso.{u, w} G).hom.app
        ((discreteCoefficientTopRepFunctor.{u, w} G).obj A))).symm

/-- For a profinite G in universe u, c=max(u,w), let S be a short
complex of discrete continuous coefficients with carrier c.
Assume its underlying maps are injective, image equals kernel and
surjective in both parameter presentations, with their given witnesses.
The connecting maps satisfy
α_H^(q+1) ∘ δ_w = δ_c ∘ α_H^q. -/
theorem sameRank_discrete_connecting
    (S : ShortComplex (DiscreteContAction (TopModuleCat.{max u w} ℤ) G))
    (hS : DiscreteCoefficientExact.{u, w} S)
    (hS' : DiscreteCoefficientExact.{u, max u w} S) (q : ℕ) :
    discreteCoefficientConnecting.{u, w} S hS q ≫
        (sameRankDiscreteCohomologyNatIso.{u, w} G (q + 1)).hom.app S.X₁ =
      (sameRankDiscreteCohomologyNatIso.{u, w} G q).hom.app S.X₃ ≫
        discreteCoefficientConnecting.{u, max u w} S hS' q := by
  have hδ := HomologicalComplex.HomologySequence.δ_naturality
    (sameRankDiscreteSequenceMap.{u, w} G S)
    (discreteCoefficientCochain_shortExact.{u, w} S hS)
    (discreteCoefficientCochain_shortExact.{u, max u w} S hS')
    q (q + 1) (discreteCoefficientUpRel q)
  change (discreteCoefficientCochain_shortExact.{u, w} S hS).δ q (q + 1)
      (discreteCoefficientUpRel q) ≫
      HomologicalComplex.homologyMap
        ((sameRankDiscreteCochainNatIso.{u, w} G).hom.app S.X₁) (q + 1) =
    HomologicalComplex.homologyMap
      ((sameRankDiscreteCochainNatIso.{u, w} G).hom.app S.X₃) q ≫
      (discreteCoefficientCochain_shortExact.{u, max u w} S hS').δ q (q + 1)
        (discreteCoefficientUpRel q) at hδ
  change (discreteCoefficientHomologyIso.{u, w} G S.X₃ q).hom ≫
      (discreteCoefficientCochain_shortExact.{u, w} S hS).δ q (q + 1)
        (discreteCoefficientUpRel q) ≫
      (discreteCoefficientHomologyIso.{u, w} G S.X₁ (q + 1)).inv ≫
      (sameRankDiscreteCohomologyNatIso.{u, w} G (q + 1)).hom.app S.X₁ =
    (sameRankDiscreteCohomologyNatIso.{u, w} G q).hom.app S.X₃ ≫
      (discreteCoefficientHomologyIso.{u, max u w} G S.X₃ q).hom ≫
      (discreteCoefficientCochain_shortExact.{u, max u w} S hS').δ q (q + 1)
        (discreteCoefficientUpRel q) ≫
      (discreteCoefficientHomologyIso.{u, max u w} G S.X₁ (q + 1)).inv
  calc
    _ = (discreteCoefficientHomologyIso.{u, w} G S.X₃ q).hom ≫
        (discreteCoefficientCochain_shortExact.{u, w} S hS).δ q (q + 1)
          (discreteCoefficientUpRel q) ≫
        HomologicalComplex.homologyMap
          ((sameRankDiscreteCochainNatIso.{u, w} G).hom.app S.X₁) (q + 1) ≫
        (discreteCoefficientHomologyIso.{u, max u w} G S.X₁ (q + 1)).inv := by
      exact congrArg (fun a => (discreteCoefficientHomologyIso.{u, w} G S.X₃ q).hom ≫
        (discreteCoefficientCochain_shortExact.{u, w} S hS).δ q (q + 1)
          (discreteCoefficientUpRel q) ≫ a)
        (sameRank_discrete_homology_inv_square.{u, w} G S.X₁ (q + 1))
    _ = (discreteCoefficientHomologyIso.{u, w} G S.X₃ q).hom ≫
        HomologicalComplex.homologyMap
          ((sameRankDiscreteCochainNatIso.{u, w} G).hom.app S.X₃) q ≫
        (discreteCoefficientCochain_shortExact.{u, max u w} S hS').δ q (q + 1)
          (discreteCoefficientUpRel q) ≫
        (discreteCoefficientHomologyIso.{u, max u w} G S.X₁ (q + 1)).inv := by
      simpa only [Category.assoc] using
        congrArg (fun a => (discreteCoefficientHomologyIso.{u, w} G S.X₃ q).hom ≫ a ≫
          (discreteCoefficientHomologyIso.{u, max u w} G S.X₁ (q + 1)).inv) hδ
    _ = _ := by rw [← Category.assoc, ← sameRank_discrete_homology_square]; simp only [Category.assoc]

end ContinuousCohomology

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable (G : ProfiniteGrp.{u})

set_option backward.isDefEq.respectTransparency false in
-- Typed original and common model coordinates use their stored integer modules.
theorem sameRank_original_complex_iso_zero_value
    (X : TopRep.{max u w, 0, u} ℤ G)
    (c : (homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X |>.X 0)
    (g : G) :
    (((sameRankOriginalComplexIso.{u, w} G X).hom.f 0 c).val g) = c.val g := by
  have h := sameRank_original_complex_iso_hom_apply.{u, w} G X 0 c (fun _ => g)
  rw [homogeneousFinContinuousLinearEquiv_apply,
    homogeneousFinContinuousLinearEquiv_apply] at h
  exact h

/-- Let G be a profinite group in universe u and c = max(u,w).
Let X be a topological ℤ-representation with carrier in c.
The coefficient-universe parameters w and c describe this same carrier.
The nested-complex parameter comparison preserves the canonical
degree-zero invariant identification:
zeroIso_c ∘ H⁰(α_C)=zeroIso_w. -/
theorem sameRank_original_zero
    (X : TopRep.{max u w, 0, u} ℤ G) :
    HomologicalComplex.homologyMap (sameRankOriginalComplexIso.{u, w} G X).hom 0 ≫
        (ContinuousCohomology.zeroIso.{0, u, max u w} X).hom =
      (ContinuousCohomology.zeroIso.{0, u, w} X).hom := by
  apply (cancel_epi (ContinuousCohomology.π.{0, u, w} X 0)).mp
  apply ConcreteCategory.ext (C := TopModuleCat.{max u w} ℤ)
  exact DFunLike.ext _ _ (fun c => Subtype.ext (by
    let m := (sameRankOriginalComplexIso.{u, w} G X).hom
    let cY := HomologicalComplex.cyclesMap m 0 c
    have hπ := congrArg (fun q => q c) (HomologicalComplex.homologyπ_naturality m 0)
    have hI := congrArg (fun q => (q c).val 1) (HomologicalComplex.cyclesMap_i m 0)
    have hval : (m.f 0
        (((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X).iCycles 0 c)).val 1 =
      (((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X).iCycles 0 c).val 1 :=
      sameRank_original_complex_iso_zero_value.{u, w} G X _ 1
    exact (congrArg (fun q => ((ContinuousCohomology.zeroIso.{0, u, max u w} X).hom q).val) hπ).trans
      ((homogeneousZeroIso_cycles_value.{0, u, max u w} X cY).trans
        (hI.trans (hval.trans
          (homogeneousZeroIso_cycles_value.{0, u, w} X c).symm)))))

/-- Let G be a profinite group in universe u and c = max(u,w).
Let A be a discrete topological ℤ-module with jointly continuous G-action.
Its continuous cochains and cohomology have presentations at parameters
w and c, on the same actual coefficient carrier.
The discrete cohomology parameter comparison in degree zero
commutes with identity evaluation to the coefficient invariants. -/
theorem sameRank_discrete_zero
    (A : DiscreteContAction (TopModuleCat.{max u w} ℤ) G) :
    (sameRankDiscreteCohomologyNatIso.{u, w} G 0).hom.app A ≫
        (discreteCoefficientZeroIso.{u, max u w} G A).hom =
      (discreteCoefficientZeroIso.{u, w} G A).hom := by
  let X := (discreteCoefficientTopRepFunctor.{u, w} G).obj A
  let F := discreteCoefficientForget.{max u w}
  exact (F.map_comp _ _).symm.trans
    (congrArg F.map (sameRank_original_zero.{u, w} G X))

end ContinuousCohomology

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable (G H : ProfiniteGrp.{u})

/-- For profinite groups G,H in universe u and c=max(u,w), let X,Y
be topological ℤ-representations with carrier c. A continuous φ:H→G
and equivariant continuous ℤ-linear f:Res_φ(X)→Y give a map of the
w-parameter homogeneous complexes. In tuple values it precomposes
each coordinate by φ and then applies f. -/
def sameRankOriginalGroupCochainMap
    {X : TopRep.{max u w, 0, u} ℤ G} {Y : TopRep.{max u w, 0, u} ℤ H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    (homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X ⟶
      (homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := H)).obj Y :=
  cochainsMap φ f

set_option backward.isDefEq.respectTransparency false in
-- The actual finite-tuple evaluation theorem fixes every original group/coefficient value.
theorem sameRank_original_group_cochain_map_apply
    {X : TopRep.{max u w, 0, u} ℤ G} {Y : TopRep.{max u w, 0, u} ℤ H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (q : ℕ)
    (c : ((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X).X q)
    (t : Fin (q + 1) → H) :
    (homogeneousFinContinuousLinearEquiv.{0, u, w} Y q
      ((sameRankOriginalGroupCochainMap.{u, w} G H φ f).f q c)).val t =
    f.hom ((homogeneousFinContinuousLinearEquiv.{0, u, w} X q c).val
      (fun i => φ (t i))) := by
  rw [homogeneousFinContinuousLinearEquiv_apply,
    homogeneousFinContinuousLinearEquiv_apply]
  exact resolutionFinUncurry_resolutionMap.{0, u, w} φ f (q + 1) c.val t

set_option backward.isDefEq.respectTransparency false in
-- Both sides use the fixed original group map on the same stored coefficient modules.
theorem sameRank_original_complex_iso_group_naturality
    {X : TopRep.{max u w, 0, u} ℤ G} {Y : TopRep.{max u w, 0, u} ℤ H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    sameRankOriginalGroupCochainMap.{u, w} G H φ f ≫
        (sameRankOriginalComplexIso.{u, w} H Y).hom =
      (sameRankOriginalComplexIso.{u, w} G X).hom ≫
        sameRankOriginalGroupCochainMap.{u, max u w} G H φ f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply (cancel_mono (homogeneousFinIso.{0, u, max u w} Y q).hom).mp
  apply ConcreteCategory.ext (C := TopModuleCat.{max u w} ℤ)
  exact DFunLike.ext _ _ (fun c => Subtype.ext (ContinuousMap.ext (fun t => by
    change (homogeneousFinContinuousLinearEquiv.{0, u, max u w} Y q
        ((sameRankOriginalComplexIso.{u, w} H Y).hom.f q
          ((sameRankOriginalGroupCochainMap.{u, w} G H φ f).f q c))).val t =
      (homogeneousFinContinuousLinearEquiv.{0, u, max u w} Y q
        ((sameRankOriginalGroupCochainMap.{u, max u w} G H φ f).f q
          ((sameRankOriginalComplexIso.{u, w} G X).hom.f q c))).val t
    rw [sameRank_original_complex_iso_hom_apply,
      sameRank_original_group_cochain_map_apply.{u, w},
      sameRank_original_group_cochain_map_apply.{u, max u w},
      sameRank_original_complex_iso_hom_apply])))

end ContinuousCohomology

end


section

universe u w
open CategoryTheory

namespace ContinuousCohomology
variable (G H K : ProfiniteGrp.{u})

/-- For profinite G in universe u, c=max(u,w), and a topological
ℤ-representation X with carrier c, the fixed-carrier cochain map
for id_G and id_X is id_(C_hom^•(G,X)). -/
theorem sameRank_original_group_cochain_map_id (X : TopRep.{max u w, 0, u} ℤ G) :
    sameRankOriginalGroupCochainMap.{u, w} G G (ContinuousMonoidHom.id G) (𝟙 X) =
      𝟙 ((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X) :=
  cochainsMap_id X

/-- For profinite G,H,K in universe u, c=max(u,w), continuous
φ:H→G, ψ:K→H and coefficient maps f:Res_φ(X)→Y, g:Res_ψ(Y)→Z,
the fixed-carrier cochain maps obey
map_(φ∘ψ, g∘Res_ψ(f)) = map_(ψ,g) ∘ map_(φ,f). -/
theorem sameRank_original_group_cochain_map_comp
    {X : TopRep.{max u w, 0, u} ℤ G} {Y : TopRep.{max u w, 0, u} ℤ H}
    {Z : TopRep.{max u w, 0, u} ℤ K}
    (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ Y ⟶ Z) :
    sameRankOriginalGroupCochainMap.{u, w} G K (φ.comp ψ)
        ((TopRep.resFunctor ψ.toMonoidHom).map f ≫ g) =
      sameRankOriginalGroupCochainMap.{u, w} G H φ f ≫
        sameRankOriginalGroupCochainMap.{u, w} H K ψ g :=
  cochainsMap_comp φ ψ f g

/-- For profinite G,H in universe u, fixed coefficient carrier
c=max(u,w), and a group/coefficient cochain map a from (φ,f),
the cycle-to-cohomology projections satisfy
Hᑫ(a) ∘ π_X = π_Y ∘ Zᑫ(a). -/
theorem sameRank_original_group_cochain_map_cycle_class
    {X : TopRep.{max u w, 0, u} ℤ G} {Y : TopRep.{max u w, 0, u} ℤ H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (q : ℕ) :
    ((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := G)).obj X).homologyπ q ≫
        HomologicalComplex.homologyMap (sameRankOriginalGroupCochainMap.{u, w} G H φ f) q =
      HomologicalComplex.cyclesMap (sameRankOriginalGroupCochainMap.{u, w} G H φ f) q ≫
        ((homogeneousCochainsFunctor.{0, u, w} (k := ℤ) (G := H)).obj Y).homologyπ q :=
  HomologicalComplex.homologyπ_naturality _ q

end ContinuousCohomology

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable (G H : ProfiniteGrp.{u})

/-- For profinite G,H in universe u, fixed coefficient carrier
c=max(u,w), and group/coefficient data (φ,f), the cohomology maps
at the two parameters commute with the parameter isomorphisms:
α_Y ∘ Hᑫ(map_w)=Hᑫ(map_c) ∘ α_X. -/
theorem sameRank_original_group_cohomology_square
    {X : TopRep.{max u w, 0, u} ℤ G} {Y : TopRep.{max u w, 0, u} ℤ H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (q : ℕ) :
    HomologicalComplex.homologyMap (sameRankOriginalGroupCochainMap.{u, w} G H φ f) q ≫
        HomologicalComplex.homologyMap (sameRankOriginalComplexIso.{u, w} H Y).hom q =
      HomologicalComplex.homologyMap (sameRankOriginalComplexIso.{u, w} G X).hom q ≫
        HomologicalComplex.homologyMap
          (sameRankOriginalGroupCochainMap.{u, max u w} G H φ f) q := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    sameRank_original_complex_iso_group_naturality]

end ContinuousCohomology

end
