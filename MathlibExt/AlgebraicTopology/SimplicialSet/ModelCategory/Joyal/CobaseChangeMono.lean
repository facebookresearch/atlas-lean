/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeCorrection

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeComplete
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryTwo
public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import
  Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting

/-! # Cobase-change stability along monomorphisms (packet T31)

This module continues `CobaseChangeComplete.lean` (packet T30) on two inputs
recorded in the header of `CobaseChange.lean`: TODO(T26-A), the isofibration
property of precomposition with a general monomorphism into a quasicategory
(proved here for Kan complex targets; since proved in full generality as
`SSet.hoFunctor_pre_isIsofibration_of_mono` in `DwyerKanFinal.lean`), and
TODO(T26-B), fullness/faithfulness of precomposition with the cobase change
in the resulting pullback square (still open).

## What this module proves

* TODO(T26-A) for Kan complex targets, for every monomorphism:
  `SSet.exists_strict_edge_lift_src_of_kanComplex` and its target-vertex
  variant (strict lifting of edges along the Kan fibration
  `(pre i).app C` against the anodyne vertex inclusions of `Δ[1]`),
  `SSet.hoPrePrismStrictExtension_of_kanComplex`,
  `SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex`, the boundary
  case `SSet.hoFunctor_pre_isIsofibration_boundary_kanComplex`
  (for every `n`), the raw inner/isofibration form
  `SSet.innerIsoFibrations_pre_app_of_mono_kanComplex`, and the
  resulting essential surjectivity of a cobase change into a Kan
  complex (`SSet.hoFunctor_pre_essSurj_of_isPushout_kanComplex`).
* Closure of the (A) inputs under composition:
  `SSet.HoPrePrismStrictExtension.comp` and
  `SSet.hoFunctor_pre_isIsofibration_comp`.
* The edge-correction step of TODO(T26-B), unconditionally, for an
  arbitrary inner fibration: `SSet.exists_edge_correction_of_innerFibration`
  corrects an edge within its homotopy class so that its strict image
  is a prescribed edge representing the same downstairs morphism, by a
  lift against the inner horn `Λ[2, 1]`. Applied to the inner fibration
  `(pre i).app C`, this is exactly the `2`-simplex correction from which
  fullness of precomposition with the cobase change is assembled by
  pullback gluing (`SSet.exists_pre_lift_of_isPushout`).

## Remaining TODOs

* TODO(T31-A) — CLOSED: TODO(T26-A) for a general quasicategory target `C`
  is now `SSet.hoFunctor_pre_isIsofibration_of_mono` in `DwyerKanFinal.lean`,
  proved unconditionally by shuffle-derived prism extension. The analysis
  below records the prism-dictionary reduction (formerly open already for
  a boundary inclusion `∂Δ[n].ι` with `n ≥ 1`): through the prism
  dictionary it is extension of maps out of
  `Δ[n] ⊗ Δ[0] ∪ ∂Δ[n] ⊗ Δ[1]` to the prism `Δ[n] ⊗ Δ[1]` with
  pointwise equivalence data, i.e. TODO(T15) (extension of an
  equivalence edge along `Δ[1] ⟶ SSet.coherentIso`) together with its
  relative form (A2) of the `CobaseChangeComplete.lean` header, by
  skeletal induction with special outer horn filling
  (`SSet.hasSpecialOuterHornFilling_of_quasicategory`, landed) at the
  attaching steps. No statement in this module claims (A) beyond the
  Kan complex, inner anodyne, and isomorphism cases; the general case
  is proved in `DwyerKanFinal.lean` (packet T66).
* TODO(T31-B): the two formal assemblies on top of
  `SSet.exists_edge_correction_of_innerFibration` are not carried out
  here: (1) fullness of `(hoFunctor.map ((pre f').app C)).toFunctor`
  in a pushout square along a monomorphism, obtained by representing
  a downstairs morphism by an edge of `Fun(B, C)`, choosing a preimage
  edge in `Fun(X, C)` through the equivalence induced by the
  categorical equivalence `f`, correcting the first edge by
  `SSet.exists_edge_correction_of_innerFibration` so the two edges
  agree strictly in `Fun(A, C)`, and gluing along
  `SSet.isPullback_pre_app_of_isPushout`; (2) faithfulness, which
  needs the analogous correction of `CompStruct` `2`-simplices
  through the inner horns `Λ[3, 1]`/`Λ[3, 2]` (or a mapping-space
  argument). Consequently the unconditional instance
  `(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet)` is *not* proved in this
  module: by `SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`
  (packet T30) it still requires TODO(T31-A) for every quasicategory
  target together with the full-and-faithful assembly TODO(T31-B).

## References

* J. Lurie, *Higher Topos Theory*, §2.3.
* D. Stevenson, *Notes on the Joyal model structure*, arXiv:1810.05233, §2.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {A B D X Y : SSet.{u}}

/-! ## Endpoint inclusions of `Δ[1]` are anodyne

The two vertex inclusions `Δ[0] ⟶ Δ[1]` are the one-dimensional horn
inclusions `Λ[1, 0]` and `Λ[1, 1]`, hence anodyne extensions. The
proofs follow the face identification used for the endpoint `δ 1` in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetSquareTransport`. -/

private theorem cobaseMono_faceZero_anodyne :
    anodyneExtensions (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq : (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
      horn (n := 1) (0 : Fin 2) := by
    have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
    calc (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)
        = stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = horn (n := 1) (0 : Fin 2) := by
          ext m x
          simp [horn_eq_iSup]
  rw [h_eq]
  exact anodyneExtensions.horn_ι (0 : Fin 2)

private theorem cobaseMono_faceOne_anodyne :
    anodyneExtensions (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq : (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) =
      horn (n := 1) (1 : Fin 2) := by
    have h_fin : ({1} : Finset (Fin 2)) = {0}ᶜ := by decide
    calc (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex)
        = stdSimplex.face ({0}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = horn (n := 1) (1 : Fin 2) := by
          ext m x
          simp [horn_eq_iSup]
  rw [h_eq]
  exact anodyneExtensions.horn_ι (1 : Fin 2)

/-- The vertex-`0` inclusion `δ 1 : Δ[0] ⟶ Δ[1]` is anodyne. -/
private theorem cobaseMono_anodyne_δ_one :
    anodyneExtensions (stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have h_eq : stdSimplex.δ (1 : Fin 2) =
      (stdSimplex.faceSingletonIso (0 : Fin 2)).hom ≫
        (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι :=
    stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ.symm
  rw [h_eq]
  exact anodyneExtensions.comp_mem _ _
    (anodyneExtensions.of_isIso _) cobaseMono_faceZero_anodyne

/-- The vertex-`1` inclusion `δ 0 : Δ[0] ⟶ Δ[1]` is anodyne. -/
private theorem cobaseMono_anodyne_δ_zero :
    anodyneExtensions (stdSimplex.δ (0 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have h_eq : stdSimplex.δ (0 : Fin 2) =
      (stdSimplex.faceSingletonIso (1 : Fin 2)).hom ≫
        (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι :=
    stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ.symm
  rw [h_eq]
  exact anodyneExtensions.comp_mem _ _
    (anodyneExtensions.of_isIso _) cobaseMono_faceOne_anodyne

private lemma cobaseMono_edge_map_map {E F G : SSet.{u}} {x₀ x₁ : E _⦋0⦌}
    (e : Edge x₀ x₁) (f : E ⟶ F) (g : F ⟶ G) :
    (e.map f).map g = e.map (f ≫ g) :=
  Edge.ext (by simp [Edge.map_edge])

/-! ## TODO(T26-A) for Kan complex targets

If `C` is a Kan complex and `i : A ⟶ B` is a monomorphism, the
precomposition map `(pre i).app C` is a Kan fibration (upstream
pushout-product instance), so every edge of `Fun(A, C)` lifts strictly
along it with prescribed source (resp. target) vertex: the lifting
square has the anodyne endpoint inclusion `δ 1` (resp. `δ 0`) on the
left. Every edge of `Fun(B, C)` is an equivalence because `Fun(B, C)`
is a Kan complex. Hence TODO(T26-A) holds for every monomorphism when
the target is a Kan complex. -/

/-- **Strict edge lifting along precomposition into a Kan complex,
with prescribed source.** Let `i : A ⟶ B` be a monomorphism and `C`
a Kan complex. Every edge `e` of `Fun(A, C)` out of the restriction
of a vertex `b` of `Fun(B, C)` is the strict image of an equivalence
edge of `Fun(B, C)` out of `b`, with strict target restriction. The
lift is the diagonal filler of the square with left side the anodyne
vertex inclusion `δ 1 : Δ[0] ⟶ Δ[1]` and right side the Kan
fibration `(pre i).app C`. -/
theorem exists_strict_edge_lift_src_of_kanComplex (i : A ⟶ B) [Mono i]
    (C : SSet.{u}) [KanComplex C]
    {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
    (e : Edge (((pre i).app C).app _ b) a') :
    ∃ (b' : ((ihom B).obj C) _⦋0⦌)
      (_hb' : ((pre i).app C).app _ b' = a') (e' : Edge b b'),
      e'.IsEquivalence ∧ (e'.map ((pre i).app C)).edge = e.edge := by
  have hp : HomotopicalAlgebra.Fibration ((pre i).app C) := inferInstance
  have hw : yonedaEquiv.symm b ≫ (pre i).app C =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]
    simp only [Equiv.apply_symm_apply]
    exact e.src_eq.symm
  let sq : CommSq (yonedaEquiv.symm b) (stdSimplex.δ (1 : Fin 2))
      ((pre i).app C) (yonedaEquiv.symm e.edge) := CommSq.mk hw
  have hlp : HasLiftingProperty (stdSimplex.δ (1 : Fin 2)) ((pre i).app C) :=
    anodyneExtensions.hasLeftLiftingProperty cobaseMono_anodyne_δ_one _
  obtain ⟨⟨l, hl_src, hl_pre⟩⟩ := (hlp.sq_hasLift sq).exists_lift
  have hsrc : ((ihom B).obj C).δ 1 (yonedaEquiv l) = b := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hl_src, Equiv.apply_symm_apply]
  have happ : ((pre i).app C).app _ (yonedaEquiv l) = e.edge := by
    rw [← yonedaEquiv_comp, hl_pre, Equiv.apply_symm_apply]
  refine ⟨((ihom B).obj C).δ 0 (yonedaEquiv l), ?_,
    Edge.mk (yonedaEquiv l) hsrc rfl,
    Edge.isEquivalence_of_kanComplex _, ?_⟩
  · calc ((pre i).app C).app _ (((ihom B).obj C).δ 0 (yonedaEquiv l))
        = ((ihom A).obj C).δ 0 (((pre i).app C).app _ (yonedaEquiv l)) :=
          (δ_naturality_apply ((pre i).app C) 0 _).symm
      _ = a' := by rw [happ]; exact e.tgt_eq
  · rw [Edge.map_edge]
    exact happ

/-- **Strict edge lifting along precomposition into a Kan complex,
with prescribed target.** The target-vertex variant of
`SSet.exists_strict_edge_lift_src_of_kanComplex`, using the anodyne
vertex inclusion `δ 0 : Δ[0] ⟶ Δ[1]`. -/
theorem exists_strict_edge_lift_tgt_of_kanComplex (i : A ⟶ B) [Mono i]
    (C : SSet.{u}) [KanComplex C]
    {b' : ((ihom B).obj C) _⦋0⦌} {a : ((ihom A).obj C) _⦋0⦌}
    (e : Edge a (((pre i).app C).app _ b')) :
    ∃ (b : ((ihom B).obj C) _⦋0⦌)
      (_hb : ((pre i).app C).app _ b = a) (e' : Edge b b'),
      e'.IsEquivalence ∧ (e'.map ((pre i).app C)).edge = e.edge := by
  have hp : HomotopicalAlgebra.Fibration ((pre i).app C) := inferInstance
  have hw : yonedaEquiv.symm b' ≫ (pre i).app C =
      stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]
    simp only [Equiv.apply_symm_apply]
    exact e.tgt_eq.symm
  let sq : CommSq (yonedaEquiv.symm b') (stdSimplex.δ (0 : Fin 2))
      ((pre i).app C) (yonedaEquiv.symm e.edge) := CommSq.mk hw
  have hlp : HasLiftingProperty (stdSimplex.δ (0 : Fin 2)) ((pre i).app C) :=
    anodyneExtensions.hasLeftLiftingProperty cobaseMono_anodyne_δ_zero _
  obtain ⟨⟨l, hl_tgt, hl_pre⟩⟩ := (hlp.sq_hasLift sq).exists_lift
  have htgt : ((ihom B).obj C).δ 0 (yonedaEquiv l) = b' := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hl_tgt, Equiv.apply_symm_apply]
  have happ : ((pre i).app C).app _ (yonedaEquiv l) = e.edge := by
    rw [← yonedaEquiv_comp, hl_pre, Equiv.apply_symm_apply]
  refine ⟨((ihom B).obj C).δ 1 (yonedaEquiv l), ?_,
    Edge.mk (yonedaEquiv l) rfl htgt,
    Edge.isEquivalence_of_kanComplex _, ?_⟩
  · calc ((pre i).app C).app _ (((ihom B).obj C).δ 1 (yonedaEquiv l))
        = ((ihom A).obj C).δ 1 (((pre i).app C).app _ (yonedaEquiv l)) :=
          (δ_naturality_apply ((pre i).app C) 1 _).symm
      _ = a := by rw [happ]; exact e.src_eq
  · rw [Edge.map_edge]
    exact happ

/-- **The prism strict extension property holds into a Kan complex,
for every monomorphism.** This is
`SSet.exists_strict_edge_lift_src_of_kanComplex` read through
`SSet.hoPrePrismStrictExtension_iff_strict_lift`. -/
theorem hoPrePrismStrictExtension_of_kanComplex (i : A ⟶ B) [Mono i]
    (C : SSet.{u}) [KanComplex C] :
    HoPrePrismStrictExtension i C :=
  (hoPrePrismStrictExtension_iff_strict_lift C).2
    (fun e _ => exists_strict_edge_lift_src_of_kanComplex i C e)

/-- **TODO(T26-A) for Kan complex targets.** For a monomorphism
`i : A ⟶ B` and a Kan complex `C`, precomposition with `i` induces
an isofibration on homotopy categories of functor objects into `C`.
This is the general monomorphism case of
`SSet.hoFunctor_pre_isIsofibration_of_mono` restricted to Kan complex
targets; for a general quasicategory target the statement remains
TODO(T31-A) in this module's header. -/
theorem hoFunctor_pre_isIsofibration_of_mono_kanComplex (i : A ⟶ B)
    [Mono i] (C : SSet.{u}) [KanComplex C] :
    (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration :=
  hoFunctor_pre_isIsofibration_of_prismStrictExtension C
    (hoPrePrismStrictExtension_of_kanComplex i C)

/-- Precomposition with a monomorphism into a Kan complex is an
inner fibration by the upstream pushout-product theorem and induces an
isofibration on homotopy categories by
`SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex`. -/
theorem innerIsoFibrations_pre_app_of_mono_kanComplex (i : A ⟶ B)
    [Mono i] (C : SSet.{u}) [KanComplex C] :
    innerIsoFibrations ((pre i).app C) := by
  rw [innerIsoFibrations.mem_iff]
  exact ⟨(innerFibration_iff _).1 (innerFibration_pre_app_of_mono i C),
    hoFunctor_pre_isIsofibration_of_mono_kanComplex i C⟩

/-- **TODO(T26-A) for boundary inclusions into Kan complexes.** For
every `n` and every Kan complex `C`, precomposition with the boundary
inclusion `∂Δ[n].ι` induces an isofibration on homotopy categories
of functor objects into `C`. This is the boundary case of
`SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex`; for a general
quasicategory target and `n ≥ 1` the boundary case remains part of
TODO(T31-A) in this module's header. -/
theorem hoFunctor_pre_isIsofibration_boundary_kanComplex (n : ℕ)
    (C : SSet.{u}) [KanComplex C] :
    (hoFunctor.map ((pre ∂Δ[n].ι).app C)).toFunctor.IsIsofibration :=
  hoFunctor_pre_isIsofibration_of_mono_kanComplex ∂Δ[n].ι C

variable {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

/-- Essential surjectivity of precomposition with a cobase change of
a categorical equivalence along a monomorphism, into a Kan complex:
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration` with the
isofibration input supplied by
`SSet.hoFunctor_pre_isIsofibration_of_mono_kanComplex`. -/
theorem hoFunctor_pre_essSurj_of_isPushout_kanComplex
    (sq : IsPushout i f f' j) [Mono i] (hf : categoricalEquivalences f)
    (C : SSet.{u}) [KanComplex C] :
    (hoFunctor.map ((pre f').app C)).toFunctor.EssSurj :=
  hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C
    (hoFunctor_pre_isIsofibration_of_mono_kanComplex i C)

/-! ## Closure of the strict extension property under composition -/

/-- The prism strict extension property is closed under composition:
strictly extending an equivalence-edge prism along `i` and then along
`j` extends it along `i ≫ j`, since precomposition with `i ≫ j` is
precomposition with `j` followed by precomposition with `i`. -/
theorem HoPrePrismStrictExtension.comp (C : SSet.{u})
    {i : A ⟶ B} {j : B ⟶ D}
    (hi : HoPrePrismStrictExtension i C)
    (hj : HoPrePrismStrictExtension j C) :
    HoPrePrismStrictExtension (i ≫ j) C := by
  rw [hoPrePrismStrictExtension_iff_strict_lift] at hi hj ⊢
  intro d a' e he
  have hp : ((pre (i ≫ j)).app C) = ((pre j).app C) ≫ ((pre i).app C) := by
    rw [pre_map]; rfl
  have hpt : ((pre (i ≫ j)).app C).app _ d =
      ((pre i).app C).app _ (((pre j).app C).app _ d) := by
    rw [hp]; rfl
  let e' : Edge (((pre i).app C).app _ (((pre j).app C).app _ d)) a' :=
    e.ofEq hpt rfl
  have he' : e'.IsEquivalence := he.of_edge_eq rfl
  obtain ⟨b', hb', eB, heB, hedgeB⟩ := hi e' he'
  obtain ⟨d', hd', eD, heD, hedgeD⟩ := hj eB heB
  refine ⟨d', ?_, eD, heD, ?_⟩
  · rw [hp]
    change ((pre i).app C).app _ (((pre j).app C).app _ d') = a'
    rw [hd']
    exact hb'
  · have h1 : (eD.map ((pre (i ≫ j)).app C)).edge =
        ((pre i).app C).app _ ((eD.map ((pre j).app C)).edge) := by
      rw [Edge.map_edge, Edge.map_edge, hp]; rfl
    rw [h1, hedgeD]
    have h2 : (eB.map ((pre i).app C)).edge = e.edge := hedgeB
    rwa [Edge.map_edge] at h2

/-- The isofibration conclusion of TODO(T26-A) is closed under
composition: if precomposition with `i` and with `j` each induce
isofibrations on homotopy categories of functor objects into
`C`, so does precomposition with `i ≫ j`. No hypothesis on `C`
is needed: this is functoriality of precomposition
(`SSet.hoFunctor_pre_comp`) and closure of isofibrations under
composition. -/
theorem hoFunctor_pre_isIsofibration_comp (C : SSet.{u})
    {i : A ⟶ B} {j : B ⟶ D}
    (hi : (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration)
    (hj : (hoFunctor.map ((pre j).app C)).toFunctor.IsIsofibration) :
    (hoFunctor.map ((pre (i ≫ j)).app C)).toFunctor.IsIsofibration := by
  rw [hoFunctor_pre_comp]
  exact @Functor.isIsofibration_comp _ _ _ _ _ _
    (hoFunctor.map ((pre j).app C)).toFunctor
    (hoFunctor.map ((pre i).app C)).toFunctor hj hi

/-! ## Edge correction through an inner fibration

The generic `SSet.exists_edge_correction_of_innerFibration` and its strict
endpoint/image contract are reexported from `Quasicategory.EdgeCorrection`.
-/

end SSet

end
