/-
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse
Provenance: original construction for Hartshorne III.6 foundations on ringed
spaces: the local-to-global Ext edge morphism.
Author: @toskua
Promotion contribution: generic complex-homology comparison API.
-/
module

public import MathlibExt.Algebra.Homology.ShortComplex.MapHomologyLeftExact
public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology comparison for a left-exact functor

Let C,D be categories with zero morphisms and homology, F:C→D preserve zero morphisms and finite
limits, and c be any complex shape. There is a canonical forward edge H_q(FK)→F(H_qK),
constructed from the cycle comparison and descent through the homology projection of the
degree-q short complex.

The edge is natural in a complex morphism and in a natural transformation between such functors.
Replacing the predecessor and successor by equal indices gives the same edge through the
corresponding short-complex homology isomorphisms. If F also preserves homology, the edge is the
forward map of the canonical homology comparison isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ u₁ u₂ uι

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [CategoryWithHomology C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [CategoryWithHomology D]
variable {ι : Type uι} (c : ComplexShape ι)
variable (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
variable (K : HomologicalComplex C c) (q : ι)

/-- Let C,D be categories with zero morphisms and homology, in independent object/morphism universes
(u₁,v₁),(u₂,v₂). Let c be a complex shape on I in uI, F:C→D preserve zero morphisms and finite
limits, and K a c-shaped complex. For q∈I, the edge α_{F,K,q}:H_q(FK)→F(H_qK) is the homology
descent of the map Z_q(FK)→F(H_qK) obtained from the finite-limit cycle comparison
Z_q(FK)≅F(Z_qK) and F applied to the class projection. -/
def leftExactHomologyEdge :
    ((F.mapHomologicalComplex c).obj K).homology q ⟶ F.obj (K.homology q) := by
  with_unfolding_all exact CategoryTheory.ShortComplex.leftExactHomologyEdge F (K.sc q)

/-- Let C,D be categories with zero morphisms and homology, in independent object/morphism universes
(u₁,v₁),(u₂,v₂). Let c be a complex shape on I in uI, F:C→D preserve zero morphisms and finite
limits, and K a c-shaped complex. For q∈I, i=c.prev(q), k=c.next(q), let
e_K:H_qK≅H(K.sc'(i,q,k)) and e_T:H_q(FK)≅H((FK).sc'(i,q,k)). Then
α_{F,K,q}=e_T.hom≫α_{F,K.sc'}≫F(e_K.inv). The middle edge is the corresponding short-complex
descent. -/
theorem leftExactHomologyEdge_sc' (i k : ι) (hi : c.prev q = i) (hk : c.next q = k) :
    leftExactHomologyEdge c F K q =
      (((F.mapHomologicalComplex c).obj K).homologyIsoSc' i q k hi hk).hom ≫
        CategoryTheory.ShortComplex.leftExactHomologyEdge F (K.sc' i q k) ≫
          F.map (K.homologyIsoSc' i q k hi hk).inv := by
  subst i
  subst k
  let T := (F.mapHomologicalComplex c).obj K
  let a : T.homology q ⟶ F.obj (K.homology q) := leftExactHomologyEdge c F K q
  let eK := K.homologyIsoSc' (c.prev q) q (c.next q) rfl rfl
  let eT := T.homologyIsoSc' (c.prev q) q (c.next q) rfl rfl
  have hT : eT.hom = 𝟙 (T.homology q) := by
    have h := congrArg (fun z => z.hom) (T.homologyIsoSc'_eq_refl q)
    with_unfolding_all exact h
  have hK : eK.inv = 𝟙 (K.homology q) := by
    have h := congrArg (fun z => z.inv) (K.homologyIsoSc'_eq_refl q)
    with_unfolding_all exact h
  have hMap : F.map eK.inv = 𝟙 (F.obj (K.homology q)) :=
    (congrArg (fun z => F.map z) hK).trans (F.map_id (K.homology q))
  have hMapped : eT.hom ≫ a ≫ F.map eK.inv =
      (𝟙 (T.homology q)) ≫ a ≫ (𝟙 (F.obj (K.homology q))) :=
    (congrArg₂ (fun z t => z ≫ a ≫ t) hT hMap)
  have hCancel : (𝟙 (T.homology q)) ≫ a ≫ (𝟙 (F.obj (K.homology q))) = a :=
    (Category.id_comp (a ≫ (𝟙 (F.obj (K.homology q))))).trans (Category.comp_id a)
  have h := (hMapped.trans hCancel).symm
  with_unfolding_all exact h

/-- Let C,D be categories with zero morphisms and homology, in independent object/morphism universes
(u₁,v₁),(u₂,v₂). Let c be a complex shape on I in uI, F:C→D preserve zero morphisms and finite
limits, and K a c-shaped complex. Let G:C→D also preserve zero morphisms and finite limits, and
τ:F⇒G. For q∈I, H_q(τ_K)≫α_{G,K,q}=α_{F,K,q}≫τ_{H_qK} as maps H_q(FK)→G(H_qK). -/
theorem leftExactHomologyEdge_naturality
    (G : C ⥤ D) [G.PreservesZeroMorphisms] [PreservesFiniteLimits G] (τ : F ⟶ G) :
    homologyMap ((τ.mapHomologicalComplex c).app K) q ≫ leftExactHomologyEdge c G K q =
      leftExactHomologyEdge c F K q ≫ τ.app (K.homology q) := by
  with_unfolding_all exact
    (CategoryTheory.ShortComplex.leftExactHomologyEdge_naturality F (K.sc q) G τ)

/-- Let C,D be categories with zero morphisms and homology, in independent object/morphism universes
(u₁,v₁),(u₂,v₂). Let c be a complex shape on I in uI, F:C→D preserve zero morphisms and finite
limits, and K a c-shaped complex. For a c-shaped complex L and φ:K→L, one has
H_q(Fφ)≫α_{F,L,q}=α_{F,K,q}≫F(H_qφ). Both sides map H_q(FK) to F(H_qL). -/
theorem leftExactHomologyEdge_map_naturality
    (L : HomologicalComplex C c) (φ : K ⟶ L) :
    homologyMap ((F.mapHomologicalComplex c).map φ) q ≫ leftExactHomologyEdge c F L q =
      leftExactHomologyEdge c F K q ≫ F.map (homologyMap φ q) := by
  with_unfolding_all exact
    (CategoryTheory.ShortComplex.leftExactHomologyEdge_map_naturality F (K.sc q) (L.sc q)
      ((shortComplexFunctor C c q).map φ))

section ExactFunctor

variable [F.PreservesHomology]

/-- Let C,D be categories with zero morphisms and homology, in independent object/morphism universes
(u₁,v₁),(u₂,v₂). Let c be a complex shape on I in uI, F:C→D preserve zero morphisms and finite
limits, and K a c-shaped complex. Assume additionally that F preserves homology. For q∈I,
α_{F,K,q} equals the forward component at K of the natural isomorphism H_q(F(-))≅F(H_q(-)). The
edge itself therefore uses the canonical homology-comparison morphism. -/
theorem leftExactHomologyEdge_eq_exactFunctorHomologyIso_hom :
    leftExactHomologyEdge c F K q = ((mapHomologyFunctorIso (c := c) q F).app K).hom := by
  with_unfolding_all exact
    (CategoryTheory.ShortComplex.leftExactHomologyEdge_eq_mapHomologyIso_hom F (K.sc q))

end ExactFunctor

end HomologicalComplex
