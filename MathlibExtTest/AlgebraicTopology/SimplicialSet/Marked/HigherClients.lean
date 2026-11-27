/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianMonoidal
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Constants
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFreeIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InitialMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PullbackMarkingCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges

/-!
# Focused clients of the higher-level marked simplicial-set API

* Limits and colimits through the instances: a pullback whose marking is exactly the intersection of
  the projected markings, a pushout in which the image of an unmarked edge becomes marked, and the
  empty colimit, which has no edges at all, with the initial maps being monomorphisms.
* Generated markings: selecting the identity edge of `Δ[1]` also marks the degenerate edges, so the
  marking strictly enlarges the selected set.
* The Cartesian closed structure: in the internal hom from the minimally marked interval to itself,
  the edge given by the second projection is marked and the edge given by the first projection is
  not; currying and evaluation recover the second projection.
* The simplicial enrichment: the hom object from the point to the maximally marked interval has an
  edge between two distinct vertices.
* Enriched left Kan extension, along the identity of the one-object enriched category: the left Kan
  extension of a free diagram carries the marking of its coefficient.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedHigherClients

open SSet SSet.stdSimplex SSet.Marked

/-! ### The interval -/

/-- The identity edge of the interval. -/
abbrev idEdge : (Δ[1] : SSet.{u}) _⦋1⦌ :=
  objMk₁ (1 : Fin 3)

/-- The first vertex of the interval. -/
abbrev v₀ : (Δ[1] : SSet.{u}) _⦋0⦌ :=
  objMk₁ (0 : Fin 2)

/-- The interval with its minimal marking. -/
abbrev minInterval : Marked.{u} :=
  Marked.min (Δ[1] : SSet.{u})

/-- The interval with its maximal marking. -/
abbrev maxInterval : Marked.{u} :=
  Marked.max (Δ[1] : SSet.{u})

/-- Every degenerate edge of the interval is one of the two constant edges. -/
theorem degenerate_edge (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (Δ[1] : SSet.{u}).σ (0 : Fin 1) x = objMk₁ (0 : Fin 3) ∨
      (Δ[1] : SSet.{u}).σ (0 : Fin 1) x = objMk₁ (2 : Fin 3) := by
  obtain ⟨i, rfl⟩ := objMk₁_surjective x
  fin_cases i
  · exact Or.inl (σ_objMk₁_of_le (0 : Fin 2) (0 : Fin 1) (by decide))
  · exact Or.inr (σ_objMk₁_of_lt (1 : Fin 2) (0 : Fin 1) (by decide))

/-- The identity edge is not marked in the minimal marking. -/
theorem idEdge_not_mem_min : idEdge.{u} ∉ minInterval.{u}.marking := by
  rintro ⟨x, hx⟩
  rcases degenerate_edge x with h | h
  · exact absurd (objMk₁_injective (h.symm.trans hx)) (by decide)
  · exact absurd (objMk₁_injective (h.symm.trans hx)) (by decide)

/-- The maximally marked point is terminal. -/
def point : IsTerminal (Marked.max (Δ[0] : SSet.{u})) :=
  parameterZeroIsTerminal .maximal

/-! ### Limits through the instances -/

example : HasLimitsOfSize.{u, u} Marked.{u} :=
  inferInstance

example : HasColimitsOfSize.{u, u} Marked.{u} :=
  inferInstance

/-- The maps of the two intervals to the point. -/
noncomputable abbrev fP : maxInterval.{u} ⟶ Marked.max (Δ[0] : SSet.{u}) :=
  point.from maxInterval

noncomputable abbrev gP : minInterval.{u} ⟶ Marked.max (Δ[0] : SSet.{u}) :=
  point.from minInterval

/-- The pullback of the maximally and the minimally marked interval over the point. -/
noncomputable abbrev P : Marked.{u} :=
  pullback fP.{u} gP.{u}

/-- The map `t ↦ (t, v₀)` from the maximally marked interval into the pullback. -/
noncomputable def ℓ₁ : maxInterval.{u} ⟶ P.{u} :=
  pullback.lift (𝟙 maxInterval) (Marked.const (X := maxInterval) (Y := minInterval) v₀)
    (point.hom_ext _ _)

theorem ℓ₁_snd :
    ℓ₁.{u} ≫ pullback.snd fP.{u} gP.{u} = Marked.const (X := maxInterval) (Y := minInterval) v₀ :=
  pullback.lift_snd _ _ _

/-- The map `t ↦ (t, t)` from the minimally marked interval into the pullback. -/
noncomputable def ℓ₂ : minInterval.{u} ⟶ P.{u} :=
  pullback.lift (toMax (𝟙 _) : minInterval ⟶ maxInterval) (𝟙 minInterval) (point.hom_ext _ _)

theorem ℓ₂_snd : ℓ₂.{u} ≫ pullback.snd fP.{u} gP.{u} = 𝟙 minInterval :=
  pullback.lift_snd _ _ _

/-- Both projections of `(id, σ v₀)` are marked, so it is marked in the pullback: the pullback marks
exactly the edges whose projections are marked. -/
theorem markedEdge_mem : ℓ₁.{u}.hom.app (op ⦋1⦌) idEdge ∈ P.{u}.marking := by
  refine (pullback_marking_iff _ _ _).mpr ⟨Set.mem_univ _, ?_⟩
  have h := congrArg (fun m : maxInterval.{u} ⟶ minInterval => m.hom.app (op ⦋1⦌) idEdge) ℓ₁_snd
  exact h.symm ▸ (Marked.const (X := maxInterval) (Y := minInterval) v₀).preserve (Set.mem_univ _)

/-- The first projection of `(id, id)` is marked but the second is not, so it is not marked. -/
theorem unmarkedEdge_not_mem : ℓ₂.{u}.hom.app (op ⦋1⦌) idEdge ∉ P.{u}.marking := by
  intro h
  have hs := (pullback.snd fP.{u} gP.{u}).preserve h
  have e : (pullback.snd fP.{u} gP.{u}).hom.app (op ⦋1⦌) (ℓ₂.{u}.hom.app (op ⦋1⦌) idEdge) =
      idEdge :=
    congrArg (fun m : minInterval.{u} ⟶ minInterval => m.hom.app (op ⦋1⦌) idEdge) ℓ₂_snd
  exact idEdge_not_mem_min (e ▸ hs)

/-! ### Colimits through the instances -/

/-- The identity of the interval, from the minimal to the maximal marking. -/
abbrev up : minInterval.{u} ⟶ maxInterval :=
  toMax (𝟙 _)

/-- Glue the maximally and the minimally marked interval along the identity. -/
noncomputable abbrev Q : Marked.{u} :=
  pushout up.{u} (𝟙 minInterval)

/-- In the pushout the image of the identity edge of the minimally marked side is marked, although
that edge is not marked there: it is also the image of the marked identity edge of the other
side. -/
theorem pushout_inr_marked :
    (pushout.inr up.{u} (𝟙 minInterval)).hom.app (op ⦋1⦌) idEdge ∈ Q.{u}.marking := by
  have h := congrArg (fun m : minInterval.{u} ⟶ Q => m.hom.app (op ⦋1⦌) idEdge)
    (pushout.condition (f := up.{u}) (g := 𝟙 minInterval))
  exact h ▸ (pushout.inl up.{u} (𝟙 minInterval)).preserve (Set.mem_univ idEdge.{u})

example : idEdge.{u} ∉ minInterval.{u}.marking :=
  idEdge_not_mem_min

/-! ### The empty colimit -/

/-- The empty subcomplex of the point, an initial simplicial set with no simplices. -/
abbrev E : SSet.{u} :=
  ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})

/-- The initial marked simplicial set, computed by the instance, has no edges at all ... -/
theorem initial_no_edges (e : (⊥_ Marked.{u}).toSSet _⦋1⦌) : False :=
  ((initial.to (Marked.min E.{u})).hom.app (op ⦋1⦌) e).property

/-- ... so its marking is empty. -/
theorem initial_marking : (⊥_ Marked.{u}).marking = ∅ :=
  Set.eq_empty_of_forall_notMem fun e _ => initial_no_edges e

/-- The minimal marking of the initial simplicial set is initial too. -/
noncomputable example : min (⊥_ SSet.{u}) ≅ ⊥_ Marked.{u} :=
  minimalInitialIsInitial.uniqueUpToIso initialIsInitial

/-- Initial maps are monomorphisms. -/
example : Mono (initial.to minInterval.{u}) := by
  have := initialMonoClass.{u}
  infer_instance

/-! ### Generated markings -/

/-- Selecting the identity edge of the interval. -/
abbrev selected : Marked.{u} :=
  withEdges (Δ[1] : SSet.{u}) {idEdge}

/-- The degenerate edge at `v₀` is marked, although it was not selected: the marking strictly
enlarges the selected set. -/
theorem selected_strict :
    (Δ[1] : SSet.{u}).σ (0 : Fin 1) v₀ ∈ selected.{u}.marking ∧
      (Δ[1] : SSet.{u}).σ (0 : Fin 1) v₀ ∉ ({idEdge.{u}} : Set ((Δ[1] : SSet.{u}) _⦋1⦌)) := by
  refine ⟨Or.inl ⟨v₀, rfl⟩, fun h => ?_⟩
  have h' : (Δ[1] : SSet.{u}).σ (0 : Fin 1) v₀ = idEdge := h
  rw [σ_objMk₁_of_le (0 : Fin 2) (0 : Fin 1) (by decide)] at h'
  exact absurd (objMk₁_injective h') (by decide)

/-! ### The Cartesian closed structure -/

/-- The edge of the internal hom given by the first projection, `(t, x) ↦ t`. -/
abbrev fstEdge : (internalHom minInterval.{u} minInterval).toSSet _⦋1⦌ :=
  prodFst (Marked.min (Δ[1] : SSet.{u})) minInterval

/-- The edge of the internal hom given by the second projection, `(t, x) ↦ x`. -/
abbrev sndEdge : (internalHom minInterval.{u} minInterval).toSSet _⦋1⦌ :=
  prodSnd (Marked.min (Δ[1] : SSet.{u})) minInterval

/-- The second projection is marked: it extends to the maximally marked parameter. -/
theorem sndEdge_mem : sndEdge.{u} ∈ (internalHom minInterval.{u} minInterval).marking :=
  ⟨prodSnd maxInterval minInterval, Hom.ext rfl⟩

/-- The first projection is not marked: on the maximally marked parameter it would send the marked
edge `(id, σ v₀)` to the unmarked identity edge. -/
theorem fstEdge_not_mem : fstEdge.{u} ∉ (internalHom minInterval.{u} minInterval).marking := by
  rintro ⟨f, hf⟩
  have hhom := congrArg Hom.hom hf
  rw [mappingComplexMaxToMin_app_hom] at hhom
  have hm := f.preserve (e := ((idEdge, (Δ[1] : SSet.{u}).σ (0 : Fin 1) v₀) :
      (Marked.prod maxInterval minInterval).toSSet _⦋1⦌)) ⟨Set.mem_univ _, ⟨v₀, rfl⟩⟩
  have hv : f.hom.app (op ⦋1⦌) (idEdge, (Δ[1] : SSet.{u}).σ (0 : Fin 1) v₀) = idEdge.{u} :=
    congrArg (fun g : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] =>
      g.app (op ⦋1⦌) (idEdge, (Δ[1] : SSet.{u}).σ (0 : Fin 1) v₀)) hhom
  exact idEdge_not_mem_min (hv ▸ hm)

/-- Currying the second projection out of `max Δ[0] × min Δ[1]` and evaluating gives it back. -/
example : uncurry (curry (prodSnd (Marked.max (Δ[0] : SSet.{u})) minInterval)) =
    prodSnd (Marked.max (Δ[0] : SSet.{u})) minInterval :=
  uncurry_curry _

section Closed

attribute [local instance] cartesianMonoidalCategory monoidalClosed

/-- The closed structure's internal hom is the marked internal hom. -/
example : (ihom minInterval.{u}).obj minInterval = internalHom minInterval minInterval :=
  rfl

/-- Mathlib's currying for this closed structure is inverse to uncurrying. -/
example (f : minInterval.{u} ⊗ maxInterval ⟶ maxInterval) :
    MonoidalClosed.uncurry (MonoidalClosed.curry f) = f :=
  MonoidalClosed.uncurry_curry f

end Closed

/-! ### The simplicial enrichment -/

section Enrichment

attribute [local instance] markedSimplicialCategory

/-- The hom object is the maximal mapping complex. -/
example : (Marked.max (Δ[0] : SSet.{u}) ⟶[SSet.{u}] maxInterval) =
    mappingComplex .maximal (Marked.max (Δ[0] : SSet.{u})) maxInterval :=
  rfl

/-- The enriched identity is the vertex of the identity map. -/
example : eHomEquiv SSet.{u} (𝟙 maxInterval.{u}) = eId SSet.{u} maxInterval :=
  eHomEquiv_id _ _

/-- The edge of the hom object from the point to the interval given by the projection. -/
abbrev homEdge : (Marked.max (Δ[0] : SSet.{u}) ⟶[SSet.{u}] maxInterval) _⦋1⦌ :=
  prodFst maxInterval (Marked.max (Δ[0] : SSet.{u}))

/-- The vertex of `Δ[0]`. -/
abbrev pt : (Δ[0] : SSet.{u}) _⦋0⦌ :=
  obj₀Equiv.symm 0

/-- Its two endpoints are different vertices of the hom object: the constant maps at the two
vertices of the interval. -/
theorem homEdge_faces_ne :
    (Marked.max (Δ[0] : SSet.{u}) ⟶[SSet.{u}] maxInterval).δ 0 homEdge ≠
      (Marked.max (Δ[0] : SSet.{u}) ⟶[SSet.{u}] maxInterval).δ 1 homEdge := by
  intro h
  have := congrArg (fun g : (Marked.max (Δ[0] : SSet.{u}) ⟶[SSet.{u}] maxInterval) _⦋0⦌ =>
    obj₀Equiv (g.hom.app (op ⦋0⦌) (pt, pt))) h
  exact absurd this (by decide)

end Enrichment

/-! ### Enriched left Kan extension -/

/-- The one-object simplicial category whose only hom object is the point. -/
@[instance_reducible]
def pointEnrichment : EnrichedCategory SSet.{u} PUnit.{u + 1} where
  Hom _ _ := 𝟙_ SSet.{u}
  id _ := 𝟙 _
  comp _ _ _ := (λ_ _).hom
  id_comp _ _ := CartesianMonoidalCategory.toUnit_unique _ _
  comp_id _ _ := CartesianMonoidalCategory.toUnit_unique _ _
  assoc _ _ _ _ := CartesianMonoidalCategory.toUnit_unique _ _

section LeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory pointEnrichment

/-- The identity enriched functor of the one-object category. -/
abbrev j : EnrichedFunctor SSet.{u} PUnit.{u + 1} PUnit.{u + 1} :=
  EnrichedFunctor.id SSet.{u} PUnit.{u + 1}

/-- Left Kan extension along it is left adjoint to restriction. -/
noncomputable example : EnrichedLeftKan.leftExtension j.{u} ⊣ enrichedDiagramRestrict j.{u} :=
  EnrichedLeftKan.adjunction j

/-- The value at the object of the left Kan extension of the free diagram with coefficient `A`. -/
noncomputable def lanValueIso (A : Marked.{u}) :
    (EnrichedLeftKan.object j.{u} (enrichedFreeDiagram PUnit.{u + 1} PUnit.unit A)).obj PUnit.unit ≅
      Marked.prod (Marked.max (𝟙_ SSet.{u})) A :=
  (enrichedDiagramEvaluation PUnit.{u + 1} PUnit.unit).mapIso
    (enrichedLeftKanFreeIso j PUnit.unit A)

/-- The edge of the left Kan extension corresponding to the identity edge of the coefficient. -/
noncomputable def lanEdge (A : Marked.{u}) (e : A.toSSet _⦋1⦌) :
    (EnrichedLeftKan.object j.{u} (enrichedFreeDiagram PUnit.{u + 1} PUnit.unit A)).obj
      PUnit.unit |>.toSSet _⦋1⦌ :=
  (lanValueIso A).inv.hom.app (op ⦋1⦌) (PUnit.unit, e)

theorem lanEdge_image (A : Marked.{u}) (e : A.toSSet _⦋1⦌) :
    (lanValueIso A).hom.hom.app (op ⦋1⦌) (lanEdge A e) = (PUnit.unit, e) :=
  congrArg (fun m : Marked.prod (Marked.max (𝟙_ SSet.{u})) A ⟶
      Marked.prod (Marked.max (𝟙_ SSet.{u})) A =>
    m.hom.app (op ⦋1⦌) (PUnit.unit, e)) (lanValueIso A).inv_hom_id

/-- With the maximally marked interval as coefficient, the identity edge stays marked ... -/
theorem lanEdge_max_mem :
    lanEdge maxInterval.{u} idEdge ∈
      ((EnrichedLeftKan.object j.{u} (enrichedFreeDiagram PUnit.{u + 1} PUnit.unit
        maxInterval)).obj PUnit.unit).marking := by
  have h := lanEdge_image maxInterval.{u} idEdge
  exact (mem_marking_iff_of_iso (lanValueIso maxInterval) _).mpr
    (h ▸ ⟨Set.mem_univ _, Set.mem_univ _⟩)

/-- ... and with the minimally marked interval it stays unmarked. -/
theorem lanEdge_min_not_mem :
    lanEdge minInterval.{u} idEdge ∉
      ((EnrichedLeftKan.object j.{u} (enrichedFreeDiagram PUnit.{u + 1} PUnit.unit
        minInterval)).obj PUnit.unit).marking := by
  intro hm
  have h := lanEdge_image minInterval.{u} idEdge
  have hp := (mem_marking_iff_of_iso (lanValueIso minInterval) _).mp hm
  rw [h] at hp
  exact idEdge_not_mem_min hp.2

end LeftKan

end MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedHigherClients
