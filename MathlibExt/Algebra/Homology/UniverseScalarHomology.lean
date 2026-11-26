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

public import MathlibExt.Algebra.Category.ModuleCat.UniverseScalarRestriction
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport

/-!
# Scalar equivalence, cycles and homology in an independent coefficient universe

Let R be a commutative ring in universe u, W=max(u,v), and R̂ its canonical copy in W. Scalar
restriction along R→R̂ is an equivalence between the R̂-module and R-module categories with
carriers in W. It acts termwise on chain complexes of shape down ℕ and gives inverse chain
scalar functors S_C and T_C with their canonical unit and counit.

Exactness of scalar restriction provides natural isomorphisms z_{K,n}:Z_n(S_CK)≅S(Z_nK) and
σ_{K,n}:H_n(S_CK)≅S(H_nK). They commute with cycle inclusions and homology quotient projections:
z.hom≫S(i)=i and π≫σ.hom=z.hom≫S(π). They are natural in all chain maps and commute with
equal-degree identifications. The counit S_C(T_CK)≅K also gives its homology isomorphism in
every n∈ℕ. The lift height v is independent of u.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. This functor S_C sends a chain complex K over R̂ of shape
down ℕ to the R-linear complex with terms S(K_n) and differentials S(d_{n,m}). A chain map f is
sent to the componentwise scalar-restricted map S(f_n). The chain grading is unchanged. -/
abbrev complexFunctor : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) ⥤
  (ChainComplex (Modules.{u,v} R) ℕ) := (toOriginal.{u,v} R).mapHomologicalComplex (ComplexShape.down ℕ)

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. The scalar equivalence extends termwise to an equivalence
between chain complexes over R̂ and over R, both of shape down ℕ. Its forward functor is S_C and
its inverse is restriction along the inverse scalar-ring isomorphism. The unit and counit are
chain isomorphisms induced by the module scalar equivalence. -/
def complexEquivalence : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) ≌
  (ChainComplex (Modules.{u,v} R) ℕ) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (scalarEquiv.{u,v} R)).mapHomologicalComplex
    (ComplexShape.down ℕ)

@[simp]
theorem complexEquivalence_functor :
    (complexEquivalence.{u,v} R).functor = complexFunctor.{u,v} R := rfl

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For a chain complex K over R̂ of shape down ℕ and n∈ℕ, this
is the canonical isomorphism z_{K,n}:Z_n(S_CK)≅S(Z_nK). If i_K:Z_nK→K_n is the cycles inclusion,
its forward map satisfies z_{K,n}.hom≫S(i_K)=i_{S_CK}. This specifies the comparison through the
kernel defining cycles. -/
def cyclesComparison (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj K).cycles n ≅ (toOriginal.{u,v} R).obj (K.cycles n) :=
  ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map (toOriginal.{u,v} R)).cyclesIso

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For a chain complex K over R̂ of shape down ℕ and n∈ℕ, this
is the canonical isomorphism σ_{K,n}:H_n(S_CK)≅S(H_nK). With z_{K,n} the cycles comparison and
π_K:Z_nK→H_nK the homology projection, π_{S_CK}≫σ_{K,n}.hom=z_{K,n}.hom≫S(π_K). -/
def homologyComparison (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj K).homology n ≅ (toOriginal.{u,v} R).obj (K.homology n) :=
  ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map (toOriginal.{u,v} R)).homologyIso

@[reassoc (attr := simp)]
theorem cyclesComparison_i (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    (cyclesComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (K.iCycles n) =
      ((complexFunctor.{u,v} R).obj K).iCycles n := by
  exact ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i
    ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map (toOriginal.{u,v} R))

@[reassoc (attr := simp)]
theorem quotient_homologyComparison (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj K).homologyπ n ≫ (homologyComparison.{u,v} R K n).hom =
      (cyclesComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (K.homologyπ n) := by
  exact ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map
    (toOriginal.{u,v} R)).homologyπ_comp_homologyIso_hom

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For a chain map f:K→L over R̂ of shape down ℕ and n∈ℕ, let
z_K,z_L be the degree-n cycles comparisons. Then Z_n(S_C(f))≫z_L.hom=z_K.hom≫S(Z_n(f)). Both
sides map cycles of the restricted K to the restriction of cycles of L. -/
@[reassoc]
theorem cyclesComparison_naturality {K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)} (f : K ⟶ L)
  (n : ℕ) :
    HomologicalComplex.cyclesMap ((complexFunctor.{u,v} R).map f) n ≫
      (cyclesComparison.{u,v} R L n).hom =
    (cyclesComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (HomologicalComplex.cyclesMap f n) := by
  let F := toOriginal.{u,v} R
  let FK := (complexFunctor.{u,v} R).obj K
  let FL := (complexFunctor.{u,v} R).obj L
  let ff := (complexFunctor.{u,v} R).map f
  let eK := cyclesComparison.{u,v} R K n
  let eL := cyclesComparison.{u,v} R L n
  letI : Mono (F.map (L.iCycles n)) := inferInstance
  apply (cancel_mono (F.map (L.iCycles n))).1
  have hl := (Category.assoc _ _ _).trans
    ((congrArg (fun z => HomologicalComplex.cyclesMap ff n ≫ z)
      (cyclesComparison_i.{u,v} R L n)).trans (HomologicalComplex.cyclesMap_i ff n))
  have hr : (eK.hom ≫ F.map (HomologicalComplex.cyclesMap f n)) ≫ F.map (L.iCycles n) =
      FK.iCycles n ≫ F.map (f.f n) := by
    calc
      _ = eK.hom ≫ F.map (HomologicalComplex.cyclesMap f n ≫ L.iCycles n) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => eK.hom ≫ z) (F.map_comp _ _).symm)
      _ = eK.hom ≫ F.map (K.iCycles n ≫ f.f n) :=
        congrArg (fun z => eK.hom ≫ F.map z) (HomologicalComplex.cyclesMap_i f n)
      _ = (eK.hom ≫ F.map (K.iCycles n)) ≫ F.map (f.f n) :=
        (congrArg (fun z => eK.hom ≫ z) (F.map_comp _ _)).trans
          (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z => z ≫ F.map (f.f n)) (cyclesComparison_i.{u,v} R K n)
  exact hl.trans hr.symm


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For a chain map f:K→L over R̂ of shape down ℕ and n∈ℕ, let
σ_K,σ_L be the degree-n homology comparisons. Then H_n(S_C(f))≫σ_L.hom=σ_K.hom≫S(H_n(f)). The
comparison therefore intertwines the homology maps with scalar restriction. -/
@[reassoc]
theorem homologyComparison_naturality {K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)}
  (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap ((complexFunctor.{u,v} R).map f) n ≫
      (homologyComparison.{u,v} R L n).hom =
    (homologyComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (HomologicalComplex.homologyMap f n) := by
  let F := toOriginal.{u,v} R
  let FK := (complexFunctor.{u,v} R).obj K
  let FL := (complexFunctor.{u,v} R).obj L
  let ff := (complexFunctor.{u,v} R).map f
  let cK := cyclesComparison.{u,v} R K n
  let cL := cyclesComparison.{u,v} R L n
  let eK := homologyComparison.{u,v} R K n
  let eL := homologyComparison.{u,v} R L n
  apply (cancel_epi (FK.homologyπ n)).1
  calc
    _ = (HomologicalComplex.cyclesMap ff n ≫ FL.homologyπ n) ≫ eL.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ eL.hom) (HomologicalComplex.homologyπ_naturality ff n))
    _ = HomologicalComplex.cyclesMap ff n ≫ (cL.hom ≫ F.map (L.homologyπ n)) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => HomologicalComplex.cyclesMap ff n ≫ z)
          (quotient_homologyComparison.{u,v} R L n))
    _ = (cK.hom ≫ F.map (HomologicalComplex.cyclesMap f n)) ≫ F.map (L.homologyπ n) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ F.map (L.homologyπ n))
          (cyclesComparison_naturality.{u,v} R f n))
    _ = cK.hom ≫ F.map (HomologicalComplex.cyclesMap f n ≫ L.homologyπ n) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => cK.hom ≫ z) (F.map_comp _ _).symm)
    _ = cK.hom ≫ F.map (K.homologyπ n ≫ HomologicalComplex.homologyMap f n) :=
      congrArg (fun z => cK.hom ≫ F.map z) (HomologicalComplex.homologyπ_naturality f n).symm
    _ = (FK.homologyπ n ≫ eK.hom) ≫ F.map (HomologicalComplex.homologyMap f n) :=
      (congrArg (fun z => cK.hom ≫ z) (F.map_comp _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ F.map (HomologicalComplex.homologyMap f n))
            (quotient_homologyComparison.{u,v} R K n).symm))
    _ = _ := Category.assoc _ _ _


/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For a chain complex K over R̂ of shape down ℕ and i,j∈ℕ with
i=j, let e_S:H_i(S_CK)≅H_j(S_CK) and e_K:H_iK≅H_jK be the canonical degree-identification
isomorphisms. Then e_S.hom≫σ_{K,j}.hom=σ_{K,i}.hom≫S(e_K.hom). -/
@[reassoc]
theorem homologyComparison_degree_transport (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ))
  {i j : ℕ} (h : i = j) :
    (HomologicalComplex.homologyIsoOfEq ((complexFunctor.{u,v} R).obj K) h).hom ≫
      (homologyComparison.{u,v} R K j).hom =
    (homologyComparison.{u,v} R K i).hom ≫
      (toOriginal.{u,v} R).map (HomologicalComplex.homologyIsoOfEq K h).hom := by
  cases h
  simp

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. This functor T_C sends R-linear chain complexes of shape down
ℕ in W to their R̂-linear representations in W. It is the inverse of the scalar-restriction
complex equivalence; it changes the scalar action through the inverse ring isomorphism while
retaining the chain grading. -/
def toLiftedComplex : (ChainComplex (Modules.{u,v} R) ℕ) ⥤
  (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) := (complexEquivalence.{u,v} R).inverse

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For an R-linear chain complex K of shape down ℕ, this is the
canonical counit isomorphism ε_K:S_C(T_CK)≅K. It identifies scalar restriction of the inverse
scalar representation with K as a chain complex, and is natural in K. -/
def originalComplexIso (K : (ChainComplex (Modules.{u,v} R) ℕ)) :
    (complexFunctor.{u,v} R).obj ((toLiftedComplex.{u,v} R).obj K) ≅ K :=
  (complexEquivalence.{u,v} R).counitIso.app K

/-- Let R be a commutative ring in universe u, v an independent lift height and W=max(u,v). Let R̂
be the canonical copy of R in W and S the scalar-restriction equivalence from R̂-modules to
R-modules, all with carriers in W. For an R-linear chain complex K of shape down ℕ and n∈ℕ,
homology of the scalar-equivalence counit ε_K:S_C(T_CK)≅K gives this isomorphism
H_n(S_C(T_CK))≅H_nK. Its forward and inverse maps are the homology maps of ε_K.hom and ε_K.inv. -/
def originalHomologyIso (K : (ChainComplex (Modules.{u,v} R) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj ((toLiftedComplex.{u,v} R).obj K)).homology n ≅ K.homology n :=
  HomologicalComplex.homologyMapIso (originalComplexIso.{u,v} R K) n

end ModuleCat.UniverseScalarRestriction
