/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantStablePageCanonicalNaturality
public import MathlibExt.Algebra.Homology.SpectralObjectCokernelENaturality
public import
  MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotientNaturality

/-!
# Naturality of the canonical abutment cokernel presentation

Let f:K→L be a morphism of bicomplexes of shape (down ℕ,down ℕ) in an abelian category. For p,q
: ℕ put m=p+q, ℓ=p−1 as an integer cut and u=m+1. The two incoming relative homology maps are
a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and δ:H^{-m-1}(p,u)→H^{-m}(⊥,p).

The spectral morphism of f gives vertical maps α,χ,β on these two sources and their common
target, satisfying a_K≫β=α≫a_L and δ_K≫β=χ≫δ_L. They induce the canonical map
coker[a_K,δ_K]→coker[a_L,δ_L]. Through the canonical cokernel isomorphisms, this map agrees with
the spectral E-map on the bottom-indexed abutment terms. The map's projection formula and the
isomorphism's quotient-map formula are explicit.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be an abelian category in arbitrary universes, K,L bicomplexes of shape (down ℕ,down ℕ),
f:K→L and p,q : ℕ. Put m=p+q, ℓ=(p:ℤ)−1 and u=m+1; Hᵃ(s,t) denotes relative cochain homology of
the complete horizontal filtration. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and
δ:H^{-m-1}(p,u)→H^{-m}(⊥,p) be the two incoming abutment maps. The induced relative homology
maps α,χ,β satisfy a_K≫β=α≫a_L and δ_K≫β=χ≫δ_L. They therefore define
horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex:coker[a_K,δ_K]→coker[a_L,δ_L]. -/
noncomputable def horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    cokernel (biprod.desc
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundaryMap K p q)) ⟶
      cokernel (biprod.desc
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentBoundaryMap L p q)) := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let α := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentLowerMap p))
  let χ := (φ.hom n₀).app
    (mk₁ (horizontalCanonicalAbutmentUpperMap p q))
  let β := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p))
  have ha : horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫ β =
      α ≫ horizontalCanonicalAbutmentPreviousHomologyMap L p q := by
    simp [φ, n₁, α, β,
      horizontalCanonicalAbutmentPreviousHomologyMap]
  have hx : horizontalCanonicalAbutmentBoundaryMap K p q ≫ β =
      χ ≫ horizontalCanonicalAbutmentBoundaryMap L p q := by
    simp [φ, n₀, n₁, χ, β,
      horizontalCanonicalAbutmentBoundaryMap]
  exact CategoryTheory.biprodQuotientMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentBoundaryMap K p q)
    (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
    (horizontalCanonicalAbutmentBoundaryMap L p q)
    α χ β ha hx

/-- Let C be an abelian category in arbitrary universes, K,L bicomplexes of shape (down ℕ,down ℕ),
f:K→L and p,q : ℕ. Put m=p+q, ℓ=(p:ℤ)−1 and u=m+1; Hᵃ(s,t) denotes relative cochain homology of
the complete horizontal filtration. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and
δ:H^{-m-1}(p,u)→H^{-m}(⊥,p) be the two incoming abutment maps. If Q_f is the induced cokernel
map and β:H^{-m}_K(⊥,p)→H^{-m}_L(⊥,p), then π_K≫Q_f=β≫π_L for the cokernel projections π_K,π_L
of the maps [a,δ]. -/
@[reassoc]
theorem horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π
    (f : K ⟶ L) (p q : ℕ) :
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q =
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentBoundaryMap L p q)) := by
  simp [horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex,
    CategoryTheory.cokernel_π_biprodQuotientMap]

/-- Let C be abelian and K a bicomplex of shape (down ℕ,down ℕ). For p,q : ℕ, the cokernel
projection of [a,δ] followed by horizontalCanonicalAbutmentCokernelIso.hom equals the
epimorphism g of horizontalCanonicalAbutmentCokernelSequence, whose target is the canonical
abutment E-object. The maps use m=p+q, ℓ=p−1, u=m+1 and degrees -m,-m-1. -/
@[reassoc]
theorem horizontalCanonicalAbutmentCokernelIso_hom_fac
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentCokernelIso K p q).hom =
      (horizontalCanonicalAbutmentCokernelSequence K p q).g := by
  let S := horizontalCanonicalAbutmentCokernelSequence K p q
  have hS : S.Exact :=
    horizontalCanonicalAbutmentCokernelSequence_exact K p q
  have hg : Epi S.g := by
    dsimp [S, horizontalCanonicalAbutmentCokernelSequence]
    infer_instance
  let _ := hg
  have hleg := IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel S.f) hS.gIsCokernel WalkingParallelPair.one
  change cokernel.π (biprod.desc
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
      (horizontalCanonicalAbutmentCokernelIso K p q).hom = S.g at hleg
  exact hleg

/-- Let C be an abelian category in arbitrary universes, K,L bicomplexes of shape (down ℕ,down ℕ),
f:K→L and p,q : ℕ. Put m=p+q, ℓ=(p:ℤ)−1 and u=m+1; Hᵃ(s,t) denotes relative cochain homology of
the complete horizontal filtration. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p) and
δ:H^{-m-1}(p,u)→H^{-m}(⊥,p) be the two incoming abutment maps. Let Q_f be the map between
coker[a,δ] objects, e_K,e_L their canonical E-object isomorphisms, and E_f the induced canonical
abutment map. Then Q_f≫e_L.hom=e_K.hom≫E_f. -/
theorem horizontalCanonicalAbutmentCokernelIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentCokernelIso L p q).hom =
      (horizontalCanonicalAbutmentCokernelIso K p q).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  have hE :
      (horizontalCanonicalAbutmentCokernelSequence K p q).g ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q =
        (φ.hom n₁).app
            (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
          (horizontalCanonicalAbutmentCokernelSequence L p q).g := by
    simpa [φ, n₀, n₁, n₂,
      horizontalCanonicalAbutmentCokernelSequence,
      horizontalCanonicalAbutmentMapOfBicomplex] using
      CategoryTheory.Abelian.SpectralObject.Hom.cokernelSequenceE_g_EMap φ
        (horizontalCanonicalAbutmentLowerMap p)
        (horizontalCanonicalAbutmentMiddleMap p)
        (horizontalCanonicalAbutmentUpperMap p q)
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentLower_comp_middle p)
        n₀ n₁ n₂
  apply (cancel_epi (cokernel.π (biprod.desc
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentBoundaryMap K p q)))).1
  calc
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentCokernelIso L p q).hom) =
      (((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentBoundaryMap L p q))) ≫
        (horizontalCanonicalAbutmentCokernelIso L p q).hom := by
      rw [← Category.assoc,
        horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π]
    _ = (φ.hom n₁).app
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        (horizontalCanonicalAbutmentCokernelSequence L p q).g := by
      dsimp only [φ, n₁]
      rw [Category.assoc,
        horizontalCanonicalAbutmentCokernelIso_hom_fac]
    _ = (horizontalCanonicalAbutmentCokernelSequence K p q).g ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q := hE.symm
    _ = (cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentCokernelIso K p q).hom) ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q := by
      rw [horizontalCanonicalAbutmentCokernelIso_hom_fac]
    _ = cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        ((horizontalCanonicalAbutmentCokernelIso K p q).hom ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q) :=
      Category.assoc _ _ _

end HomologicalComplex₂

end
