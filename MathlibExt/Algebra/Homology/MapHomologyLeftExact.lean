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
# Actual complex-homology edges and their native short-complex normalization
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

/-- The native kernel/cokernel descent on the actual degree-q short complex. -/
def leftExactHomologyEdge :
    ((F.mapHomologicalComplex c).obj K).homology q ⟶ F.obj (K.homology q) := by
  with_unfolding_all exact CategoryTheory.ShortComplex.leftExactHomologyEdge F (K.sc q)

/-- The original chosen predecessor/successor construction gives the same actual edge. -/
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

/-- The genuine complex edge is natural in a map between actual left-exact functors. -/
theorem leftExactHomologyEdge_naturality
    (G : C ⥤ D) [G.PreservesZeroMorphisms] [PreservesFiniteLimits G] (τ : F ⟶ G) :
    homologyMap ((τ.mapHomologicalComplex c).app K) q ≫ leftExactHomologyEdge c G K q =
      leftExactHomologyEdge c F K q ≫ τ.app (K.homology q) := by
  with_unfolding_all exact
    (CategoryTheory.ShortComplex.leftExactHomologyEdge_naturality F (K.sc q) G τ)

/-- The generic forward homology edge is natural in morphisms of complexes
of any shape, without any exact-functor assumption. -/
theorem leftExactHomologyEdge_map_naturality
    (L : HomologicalComplex C c) (φ : K ⟶ L) :
    homologyMap ((F.mapHomologicalComplex c).map φ) q ≫ leftExactHomologyEdge c F L q =
      leftExactHomologyEdge c F K q ≫ F.map (homologyMap φ q) := by
  with_unfolding_all exact
    (CategoryTheory.ShortComplex.leftExactHomologyEdge_map_naturality F (K.sc q) (L.sc q)
      ((shortComplexFunctor C c q).map φ))

section ExactFunctor

variable [F.PreservesHomology]

/-- At an actually exact functor, the edge retains its native comparison homomorphism. -/
theorem leftExactHomologyEdge_eq_exactFunctorHomologyIso_hom :
    leftExactHomologyEdge c F K q = ((mapHomologyFunctorIso (c := c) q F).app K).hom := by
  with_unfolding_all exact
    (CategoryTheory.ShortComplex.leftExactHomologyEdge_eq_mapHomologyIso_hom F (K.sc q))

end ExactFunctor

end HomologicalComplex
