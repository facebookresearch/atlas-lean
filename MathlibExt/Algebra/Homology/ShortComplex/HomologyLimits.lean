/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Canonical limits of short complexes and their homology

The limit short complex is built by applying the limit functor to the
short complex in the functor category supplied by functorEquivalence. Its
projections induce a canonical homology comparison. Exact limits make that
comparison an isomorphism, using the homology preservation and
evaluation comparisons. No exactness or desired comparison is supplied as data.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

universe u v uJ vJ

variable {J : Type uJ} [Category.{vJ} J] {C : Type u} [Category.{v} C] [Abelian C]

/-- Evaluation comparisons identify functor-category homology with pointwise homology. -/
def homologyDiagramIso (S : J ⥤ ShortComplex C) :
    ((functorEquivalence J C).inverse.obj S).homology ≅ S ⋙ homologyFunctor C := by
  let E := functorEquivalence J C
  let K := E.inverse.obj S
  let e : K.homology ≅ E.functor.obj K ⋙ homologyFunctor C :=
    NatIso.ofComponents (fun j => (K.mapHomologyIso ((evaluation J C).obj j)).symm)
      (fun {j j'} f => by
        have hEval : ((evaluation J C).map f).app K.homology = K.homology.map f := rfl
        change K.homology.map f ≫ (K.mapHomologyIso ((evaluation J C).obj j')).inv =
          (K.mapHomologyIso ((evaluation J C).obj j)).inv ≫
            homologyMap (K.mapNatTrans ((evaluation J C).map f))
        rw [K.homologyMap_mapNatTrans ((evaluation J C).map f)]
        simp only [Iso.inv_hom_id_assoc]
        exact congrArg (fun a => a ≫ (K.mapHomologyIso ((evaluation J C).obj j')).inv)
          hEval.symm)
  exact e ≪≫ Functor.isoWhiskerRight (E.counitIso.app S) (homologyFunctor C)

/-- The pointwise comparison retains the evaluation and counit arrows. -/
lemma homologyDiagramIso_hom_app (S : J ⥤ ShortComplex C) (j : J) :
    (homologyDiagramIso S).hom.app j =
      (((functorEquivalence J C).inverse.obj S).mapHomologyIso
        ((evaluation J C).obj j)).inv ≫
      homologyMap (((functorEquivalence J C).counitIso.app S).app j).hom := rfl

section Limits

variable [HasLimitsOfShape J C]

/-- The functor taking a diagram of short complexes to its componentwise limit. -/
def limitShortComplexFunctor : (J ⥤ ShortComplex C) ⥤ ShortComplex C :=
  (functorEquivalence J C).inverse ⋙ (lim (J := J) (C := C)).mapShortComplex

/-- The canonical limit short complex of the given diagram. -/
def limitShortComplex (S : J ⥤ ShortComplex C) : ShortComplex C :=
  (limitShortComplexFunctor (J := J) (C := C)).obj S

/-- A map of the diagrams induces the limit short-complex map. -/
def limitShortComplexMap {S T : J ⥤ ShortComplex C} (η : S ⟶ T) :
    limitShortComplex S ⟶ limitShortComplex T :=
  (limitShortComplexFunctor (J := J) (C := C)).map η

/-- The projection uses the limit natural transformation and diagram counit. -/
def limitShortComplexProjection (S : J ⥤ ShortComplex C) (j : J) :
    limitShortComplex S ⟶ S.obj j :=
  ((functorEquivalence J C).inverse.obj S).mapNatTrans
      (lim.π (J := J) (C := C) j) ≫
    (((functorEquivalence J C).counitIso.app S).app j).hom

/-- The first component is the limit projection. -/
lemma limitShortComplexProjection_τ₁ (S : J ⥤ ShortComplex C) (j : J) :
    (limitShortComplexProjection S j).τ₁ = limit.π (S ⋙ π₁) j := by
  change limit.π (S ⋙ π₁) j ≫ 𝟙 _ = limit.π (S ⋙ π₁) j
  exact Category.comp_id _

/-- The middle component is the limit projection. -/
lemma limitShortComplexProjection_τ₂ (S : J ⥤ ShortComplex C) (j : J) :
    (limitShortComplexProjection S j).τ₂ = limit.π (S ⋙ π₂) j := by
  change limit.π (S ⋙ π₂) j ≫ 𝟙 _ = limit.π (S ⋙ π₂) j
  exact Category.comp_id _

/-- The third component is the limit projection. -/
lemma limitShortComplexProjection_τ₃ (S : J ⥤ ShortComplex C) (j : J) :
    (limitShortComplexProjection S j).τ₃ = limit.π (S ⋙ π₃) j := by
  change limit.π (S ⋙ π₃) j ≫ 𝟙 _ = limit.π (S ⋙ π₃) j
  exact Category.comp_id _

/-- The projections form a cone on the entire short-complex diagram. -/
lemma limitShortComplexProjection_naturality (S : J ⥤ ShortComplex C)
    {j j' : J} (f : j ⟶ j') :
    limitShortComplexProjection S j ≫ S.map f = limitShortComplexProjection S j' := by
  apply ShortComplex.hom_ext
  · change (limitShortComplexProjection S j).τ₁ ≫ (S.map f).τ₁ =
      (limitShortComplexProjection S j').τ₁
    rw [limitShortComplexProjection_τ₁, limitShortComplexProjection_τ₁]
    exact limit.w (S ⋙ π₁) f
  · change (limitShortComplexProjection S j).τ₂ ≫ (S.map f).τ₂ =
      (limitShortComplexProjection S j').τ₂
    rw [limitShortComplexProjection_τ₂, limitShortComplexProjection_τ₂]
    exact limit.w (S ⋙ π₂) f
  · change (limitShortComplexProjection S j).τ₃ ≫ (S.map f).τ₃ =
      (limitShortComplexProjection S j').τ₃
    rw [limitShortComplexProjection_τ₃, limitShortComplexProjection_τ₃]
    exact limit.w (S ⋙ π₃) f

/-- Projections commute with the map induced by a map of diagrams. -/
lemma limitShortComplexMap_projection {S T : J ⥤ ShortComplex C}
    (η : S ⟶ T) (j : J) :
    limitShortComplexMap η ≫ limitShortComplexProjection T j =
      limitShortComplexProjection S j ≫ η.app j := by
  apply ShortComplex.hom_ext
  · change (lim (J := J) (C := C)).map (Functor.whiskerRight η π₁) ≫
        (limitShortComplexProjection T j).τ₁ =
      (limitShortComplexProjection S j).τ₁ ≫ (η.app j).τ₁
    rw [limitShortComplexProjection_τ₁, limitShortComplexProjection_τ₁]
    exact limit.map_π (Functor.whiskerRight η π₁) j
  · change (lim (J := J) (C := C)).map (Functor.whiskerRight η π₂) ≫
        (limitShortComplexProjection T j).τ₂ =
      (limitShortComplexProjection S j).τ₂ ≫ (η.app j).τ₂
    rw [limitShortComplexProjection_τ₂, limitShortComplexProjection_τ₂]
    exact limit.map_π (Functor.whiskerRight η π₂) j
  · change (lim (J := J) (C := C)).map (Functor.whiskerRight η π₃) ≫
        (limitShortComplexProjection T j).τ₃ =
      (limitShortComplexProjection S j).τ₃ ≫ (η.app j).τ₃
    rw [limitShortComplexProjection_τ₃, limitShortComplexProjection_τ₃]
    exact limit.map_π (Functor.whiskerRight η π₃) j

/-- The canonical homology comparison is induced by the limit projections. -/
def homologyLimitComparison (S : J ⥤ ShortComplex C) :
    (limitShortComplex S).homology ⟶ limit (S ⋙ homologyFunctor C) :=
  limit.lift (S ⋙ homologyFunctor C)
    { pt := (limitShortComplex S).homology
      π :=
        { app j := (homologyMap (limitShortComplexProjection S j) :
            (limitShortComplex S).homology ⟶ (S.obj j).homology)
          naturality {j j'} f := by
            change 𝟙 _ ≫ homologyMap (limitShortComplexProjection S j') =
              homologyMap (limitShortComplexProjection S j) ≫ homologyMap (S.map f)
            rw [Category.id_comp, ← homologyMap_comp, limitShortComplexProjection_naturality] } }

/-- Each component is precisely the homology map of the limit projection. -/
@[reassoc]
lemma homologyLimitComparison_π (S : J ⥤ ShortComplex C) (j : J) :
    homologyLimitComparison S ≫ limit.π (S ⋙ homologyFunctor C) j =
      homologyMap (limitShortComplexProjection S j) :=
  limit.lift_π _ j

/-- The constructed comparison is natural under maps of the diagrams. -/
lemma homologyLimitComparison_naturality {S T : J ⥤ ShortComplex C} (η : S ⟶ T) :
    homologyMap (limitShortComplexMap η) ≫ homologyLimitComparison T =
      homologyLimitComparison S ≫ (lim (J := J) (C := C)).map
        (Functor.whiskerRight η (homologyFunctor C)) := by
  apply limit.hom_ext
  intro j
  have hWhisker : (Functor.whiskerRight η (homologyFunctor C)).app j =
      homologyMap (η.app j) := rfl
  simp only [Category.assoc, homologyLimitComparison_π, limit.map_π,
    homologyLimitComparison_π_assoc]
  have hComp :
      homologyMap (limitShortComplexMap η) ≫ homologyMap (limitShortComplexProjection T j) =
        homologyMap (limitShortComplexProjection S j) ≫ homologyMap (η.app j) :=
    (homologyMap_comp (limitShortComplexMap η) (limitShortComplexProjection T j)).symm.trans
      ((congrArg
          (fun f : limitShortComplex S ⟶ T.obj j =>
            (homologyMap f : (limitShortComplex S).homology ⟶ (T.obj j).homology))
          (limitShortComplexMap_projection η j)).trans
        (homologyMap_comp (limitShortComplexProjection S j) (η.app j)))
  exact hComp.trans
    (congrArg (fun a : (S.obj j).homology ⟶ (T.obj j).homology =>
      homologyMap (limitShortComplexProjection S j) ≫ a) hWhisker.symm)

section ExactLimits

variable [HasExactLimitsOfShape J C]

/-- Exact-limit and evaluation comparisons make the canonical comparison an isomorphism. -/
def homologyLimitIso (S : J ⥤ ShortComplex C) :
    (limitShortComplex S).homology ≅ limit (S ⋙ homologyFunctor C) :=
  (((functorEquivalence J C).inverse.obj S).mapHomologyIso
    (lim (J := J) (C := C))) ≪≫
      (lim (J := J) (C := C)).mapIso (homologyDiagramIso S)

/-- The isomorphism has the same projection characteristic as the canonical map. -/
@[reassoc]
lemma homologyLimitIso_hom_π (S : J ⥤ ShortComplex C) (j : J) :
    (homologyLimitIso S).hom ≫ limit.π (S ⋙ homologyFunctor C) j =
      homologyMap (limitShortComplexProjection S j) := by
  let K := (functorEquivalence J C).inverse.obj S
  let μ : (lim (J := J) (C := C)) ⟶ (evaluation J C).obj j := lim.π j
  let c : K.map ((evaluation J C).obj j) ≅ S.obj j :=
    ((functorEquivalence J C).counitIso.app S).app j
  let a : (limitShortComplex S).homology ⟶ limit K.homology :=
    (K.mapHomologyIso (lim (J := J) (C := C))).hom
  let b : limit K.homology ⟶ limit (S ⋙ homologyFunctor C) :=
    (lim (J := J) (C := C)).map (homologyDiagramIso S).hom
  let π : limit (S ⋙ homologyFunctor C) ⟶ (S.obj j).homology :=
    limit.π (S ⋙ homologyFunctor C) j
  let p : limit K.homology ⟶ K.homology.obj j := limit.π K.homology j
  let q : K.homology.obj j ⟶ (K.map ((evaluation J C).obj j)).homology :=
    (K.mapHomologyIso ((evaluation J C).obj j)).inv
  let r : (K.map ((evaluation J C).obj j)).homology ⟶ (S.obj j).homology :=
    homologyMap c.hom
  let d : K.homology.obj j ⟶ (S.obj j).homology := (homologyDiagramIso S).hom.app j
  let m : (limitShortComplex S).homology ⟶ (K.map ((evaluation J C).obj j)).homology :=
    homologyMap (K.mapNatTrans μ)
  have hIso : (homologyLimitIso S).hom = a ≫ b := rfl
  have hProjection : limitShortComplexProjection S j = K.mapNatTrans μ ≫ c.hom := rfl
  have hMap : m = a ≫ p ≫ q := by
    dsimp only [m, a, p, q, μ, K, limitShortComplex, limitShortComplexFunctor,
      Functor.comp_obj, Functor.mapShortComplex]
    have hNative := K.homologyMap_mapNatTrans μ
    have hProjectionComponent : μ.app K.homology = limit.π K.homology j := rfl
    rw [hProjectionComponent] at hNative
    exact hNative
  have hDiagram : d = q ≫ r := by
    exact homologyDiagramIso_hom_app S j
  have hLimit : b ≫ π = p ≫ d :=
    limit.map_π (homologyDiagramIso S).hom j
  have h₀ : (homologyLimitIso S).hom ≫ π = (a ≫ b) ≫ π :=
    congrArg (fun t : (limitShortComplex S).homology ⟶ limit (S ⋙ homologyFunctor C) =>
      t ≫ π) hIso
  have h₁ : (a ≫ b) ≫ π = a ≫ b ≫ π := Category.assoc a b π
  have h₂ : a ≫ b ≫ π = a ≫ p ≫ d :=
    congrArg (fun t : limit K.homology ⟶ (S.obj j).homology => a ≫ t) hLimit
  have h₃ : a ≫ p ≫ d = a ≫ p ≫ (q ≫ r) :=
    congrArg (fun t : K.homology.obj j ⟶ (S.obj j).homology => a ≫ p ≫ t) hDiagram
  have h₄ : a ≫ p ≫ (q ≫ r) = (a ≫ p ≫ q) ≫ r := by
    simp only [Category.assoc]
  have h₅ : (a ≫ p ≫ q) ≫ r = m ≫ r :=
    congrArg (fun t : (limitShortComplex S).homology ⟶
      (K.map ((evaluation J C).obj j)).homology => t ≫ r) hMap.symm
  have h₆ : m ≫ r = homologyMap (K.mapNatTrans μ ≫ c.hom) :=
    (homologyMap_comp (K.mapNatTrans μ) c.hom).symm
  have h₇ : homologyMap (K.mapNatTrans μ ≫ c.hom) =
      homologyMap (limitShortComplexProjection S j) :=
    congrArg
      (fun f : limitShortComplex S ⟶ S.obj j =>
        (homologyMap f : (limitShortComplex S).homology ⟶ (S.obj j).homology))
      hProjection.symm
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇))))))

/-- The forward isomorphism is the canonical homology comparison. -/
lemma homologyLimitIso_hom (S : J ⥤ ShortComplex C) :
    (homologyLimitIso S).hom = homologyLimitComparison S := by
  apply limit.hom_ext
  intro j
  rw [homologyLimitIso_hom_π, homologyLimitComparison_π]

/-- Exactness proves the canonical comparison is invertible. -/
lemma isIso_homologyLimitComparison (S : J ⥤ ShortComplex C) :
    IsIso (homologyLimitComparison S) := by
  rw [← homologyLimitIso_hom]
  infer_instance

/-- The exact-limit isomorphism is natural in the short-complex diagram. -/
lemma homologyLimitIso_naturality {S T : J ⥤ ShortComplex C} (η : S ⟶ T) :
    homologyMap (limitShortComplexMap η) ≫ (homologyLimitIso T).hom =
      (homologyLimitIso S).hom ≫ (lim (J := J) (C := C)).map
        (Functor.whiskerRight η (homologyFunctor C)) := by
  simpa only [homologyLimitIso_hom] using homologyLimitComparison_naturality η

end ExactLimits

end Limits

end CategoryTheory.ShortComplex
