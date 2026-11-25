/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.ProperQuotientProduct
public import MathlibExt.Topology.Category.TopCat.ProdPushoutFactors
public import MathlibExt.Topology.Category.TopCat.FixedFiberGauge
public import MathlibExt.AlgebraicTopology.SimplicialSet.PreimagePushout
public import MathlibExt.Topology.Category.TopCat.PushoutOpenRestriction

/-!
# Collar-foundation consumers

Persistent clients for arbitrary-factor quotient products, product-pushout
factorization, fixed-fiber gauge base change, total preimage pushouts, and
open restrictions of topological pushouts.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Function Topology
open CategoryTheory.MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.CollarFoundationTests

universe u v w

section ProperProducts

variable {A : Type u} {B : Type v} {K : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace K]
  [CompactSpace A] [T2Space B]

example {q : A → B} (hc : Continuous q) (hs : Surjective q) :
    IsQuotientMap (Prod.map q (id : K → K)) :=
  IsQuotientMap.prodMap_left_of_compact_to_t2 hc hs

example {q : A → B} (hc : Continuous q) (hs : Surjective q) :
    IsQuotientMap (Prod.map (id : K → K) q) :=
  IsQuotientMap.prodMap_right_of_compact_to_t2 hc hs

end ProperProducts

section ProductPushout

variable {K X₁ X₂ X₃ X₄ : TopCat.{u}}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

example (h : IsPushout t l r b)
    (s : PushoutCocone (prod.map (𝟙 K) t) (prod.map (𝟙 K) l)) :
    Function.FactorsThrough (coprod.desc s.inl s.inr)
      (coprod.desc (prod.map (𝟙 K) r) (prod.map (𝟙 K) b)) :=
  TopCat.prodPushoutFactors_of_isPushout h s

example (h : IsPushout t l r b)
    (hq : IsQuotientMap (coprod.desc
      (prod.map (𝟙 K) r) (prod.map (𝟙 K) b)).hom) :
    IsPushout (prod.map (𝟙 K) t) (prod.map (𝟙 K) l)
      (prod.map (𝟙 K) r) (prod.map (𝟙 K) b) := by
  have hcomm : prod.map (𝟙 K) t ≫ prod.map (𝟙 K) r =
      prod.map (𝟙 K) l ≫ prod.map (𝟙 K) b := by
    rw [prod.map_map, prod.map_map, h.w]
  let c : PushoutCocone (prod.map (𝟙 K) t) (prod.map (𝟙 K) l) :=
    PushoutCocone.mk (prod.map (𝟙 K) r) (prod.map (𝟙 K) b) hcomm
  have hc := TopCat.pushoutCoconeIsColimitOfIsQuotientMap c hq
    (fun s => TopCat.prodPushoutFactors_of_isPushout h s)
  have hs := IsPushout.of_isColimit hc
  change IsPushout (prod.map (𝟙 K) t) (prod.map (𝟙 K) l)
    (prod.map (𝟙 K) r) (prod.map (𝟙 K) b) at hs
  exact hs

end ProductPushout

section Gauge

variable {B B' F : TopCat.{u}}

example (g : B' ⟶ B) (a : TopCat.FixedFiberGauge B F) :
    (a.baseChange g).e.hom ≫ CartesianMonoidalCategory.snd B' F =
      CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst B' F ≫ g)
          (CartesianMonoidalCategory.snd B' F) ≫
        a.e.hom ≫ CartesianMonoidalCategory.snd B F :=
  a.baseChange_hom_snd g

example {Z : TopCat.{u}} (g : B' ⟶ B)
    (a : TopCat.FixedFiberGauge B F) (h : F ⟶ Z) :
    (a.baseChange g).e.hom ≫ CartesianMonoidalCategory.snd B' F ≫ h =
      CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst B' F ≫ g)
          (CartesianMonoidalCategory.snd B' F) ≫
        a.e.hom ≫ CartesianMonoidalCategory.snd B F ≫ h :=
  a.baseChange_hom_snd_assoc g h

end Gauge

section PreimagePushout

variable {A B₀ D B₁ E : SSet.{u}}
  {t : A ⟶ B₀} {i : A ⟶ D} {r : B₀ ⟶ B₁} {b : D ⟶ B₁}

example (p : E ⟶ B₁) :
    SSet.PreimagePushout.boundaryToOld p ≫ pullback.fst p r =
      pullback.fst p (t ≫ r) :=
  SSet.PreimagePushout.boundaryToOld_fst p

example (p : E ⟶ B₁) :
    SSet.PreimagePushout.boundaryToOld p ≫ pullback.snd p r =
      pullback.snd p (t ≫ r) ≫ t :=
  SSet.PreimagePushout.boundaryToOld_snd p

example (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    SSet.PreimagePushout.boundaryToCell sq p ≫ pullback.fst p b =
      pullback.fst p (t ≫ r) :=
  SSet.PreimagePushout.boundaryToCell_fst sq p

example (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    SSet.PreimagePushout.boundaryToCell sq p ≫ pullback.snd p b =
      pullback.snd p (t ≫ r) ≫ i :=
  SSet.PreimagePushout.boundaryToCell_snd sq p

example (p : E ⟶ B₁) :
    IsPullback (SSet.PreimagePushout.boundaryToOld p)
      (pullback.snd p (t ≫ r)) (pullback.snd p r) t :=
  SSet.PreimagePushout.boundaryToOld_isPullback p

example (sq : IsPushout t i r b) (p : E ⟶ B₁) :
    IsPullback (SSet.PreimagePushout.boundaryToCell sq p)
      (pullback.snd p (t ≫ r)) (pullback.snd p b) i :=
  SSet.PreimagePushout.boundaryToCell_isPullback sq p

example (sq : IsPushout t i r b) [Mono i] (p : E ⟶ B₁) :
    IsPushout (SSet.PreimagePushout.boundaryToOld p)
      (SSet.PreimagePushout.boundaryToCell sq p)
      (pullback.fst p r) (pullback.fst p b) :=
  SSet.PreimagePushout.isPushout sq p

end PreimagePushout

section OpenRestriction

section PublicEquations

variable (P : TopCat.RestrictedPushout.{u})

example :
    Set.preimage (P.t ≫ P.r) P.U =
      Set.preimage (P.l ≫ P.b) P.U :=
  P.source_preimage_eq

example : P.tU ≫ P.rU = P.lU ≫ P.bU :=
  P.w

example :
    P.tU ≫ AlgebraicTopology.subspaceIncl (Set.preimage P.r P.U) =
      AlgebraicTopology.subspaceIncl
          (Set.preimage (P.t ≫ P.r) P.U) ≫ P.t :=
  P.tU_incl

example :
    P.lU ≫ AlgebraicTopology.subspaceIncl (Set.preimage P.b P.U) =
      AlgebraicTopology.subspaceIncl
          (Set.preimage (P.t ≫ P.r) P.U) ≫ P.l :=
  P.lU_incl

example :
    P.rU ≫ AlgebraicTopology.subspaceIncl P.U =
      AlgebraicTopology.subspaceIncl (Set.preimage P.r P.U) ≫ P.r :=
  P.rU_incl

example :
    P.bU ≫ AlgebraicTopology.subspaceIncl P.U =
      AlgebraicTopology.subspaceIncl (Set.preimage P.b P.U) ≫ P.b :=
  P.bU_incl

end PublicEquations

/-- Open restriction applies even when the original attaching map is the
noninjective map from two points to one point. -/
example :
    ∃ P : TopCat.RestrictedPushout.{0},
      ¬ Function.Injective P.t ∧ IsPushout P.tU P.lU P.rU P.bU := by
  let X₁ : TopCat.{0} := TopCat.of (Fin 2)
  let X₂ : TopCat.{0} := TopCat.of PUnit
  let X₃ : TopCat.{0} := TopCat.of PUnit
  let t : X₁ ⟶ X₂ := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let l : X₁ ⟶ X₃ := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let X₄ : TopCat.{0} := pushout t l
  let r : X₂ ⟶ X₄ := pushout.inl t l
  let b : X₃ ⟶ X₄ := pushout.inr t l
  have hsquare : IsPushout t l r b :=
    IsPushout.of_isColimit (pushout.isColimit t l)
  let U : Set X₄ := Set.univ
  let P := TopCat.RestrictedPushout.of hsquare U
  have ht : ¬ Function.Injective t := by
    intro ht
    have h01 : t (0 : Fin 2) = t (1 : Fin 2) := rfl
    exact Fin.zero_ne_one (ht h01)
  refine ⟨P, ?_, P.isPushout isOpen_univ⟩
  exact ht

end OpenRestriction

end MathlibExtTest.AlgebraicTopology.ModelCategory.CollarFoundationTests
