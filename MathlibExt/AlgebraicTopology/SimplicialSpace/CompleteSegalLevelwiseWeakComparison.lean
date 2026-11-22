/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalDegreeZeroWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingFaithfulness
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWProduct
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback

/-!
# Intrinsic DK recognition between complete Segal spaces

The original mapping-fibre maps and intrinsic Ho essential surjectivity
detect full realization weakness of every original outer-level map.
The finite-prefix argument uses the original consecutive-edge cospans.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner
attribute [local instance] SSet.modelCategoryQuillen.modelCategory
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace

private theorem rawSourceKan (A : SSet.{u}) (W : SimplicialSpace.{u})
    (hW : segalSpaces W) : SSet.KanComplex ((discreteSourceMapping W).obj (op A)) :=
  ReedyModel.innerHom_kanComplex
    (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)) W
    (ReedyModel.isCofibrant _) hW.1

private theorem originalLevelKan (W : SimplicialSpace.{u}) (hW : segalSpaces W) (n : ℕ) :
    SSet.KanComplex (W.diagram _⦋n⦌) := by
  let _ : SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[n] : SSet.{u}))) :=
    rawSourceKan _ W hW
  exact isFibrant_of_fibration (discreteYonedaIso W n).inv

/-- Actual base-change projection weakness from public changing-cospan HP APIs.
This does not call the foreign private strict-cospan or scalar fibre lemmas. -/
private theorem originalPullbackProjectionWeak {E B B' : SSet.{u}}
    [SSet.KanComplex B] [SSet.KanComplex B'] (p : E ⟶ B) [Fibration p]
    (b : B' ⟶ B) (hb : SSet.realizationWeakEquivalences b) :
    SSet.realizationWeakEquivalences (pullback.fst p b) := by
  let F : WalkingCospan ⥤ SSet.{u} := cospan p b
  let G : WalkingCospan ⥤ SSet.{u} := cospan p (𝟙 B)
  let eta : F ⟶ G := cospanHomMk (𝟙 B) (𝟙 E) b
    (by change p ≫ 𝟙 B = 𝟙 E ≫ p; simp only [Category.comp_id, Category.id_comp])
    (by change b ≫ 𝟙 B = b ≫ 𝟙 B; rfl)
  let _ : IsFibrant (F.obj WalkingCospan.one) := by change IsFibrant B; infer_instance
  let _ : IsFibrant (F.obj WalkingCospan.right) := by change IsFibrant B'; infer_instance
  let _ : Fibration (F.map WalkingCospan.Hom.inl) := by change Fibration p; infer_instance
  let _ : IsFibrant (G.obj WalkingCospan.one) := by change IsFibrant B; infer_instance
  let _ : IsFibrant (G.obj WalkingCospan.right) := by change IsFibrant B; infer_instance
  let _ : Fibration (G.map WalkingCospan.Hom.inl) := by change Fibration p; infer_instance
  have hcF : SSet.realizationWeakEquivalences
      ((homotopyPullbackComparison (C := SSet.{u})).app F) :=
    (weakEquivalence_iff _).mp (weakEquivalence_homotopyPullbackComparison_of_inl F)
  have hcG : SSet.realizationWeakEquivalences
      ((homotopyPullbackComparison (C := SSet.{u})).app G) :=
    (weakEquivalence_iff _).mp (weakEquivalence_homotopyPullbackComparison_of_inl G)
  have hEta : ∀ q, WeakEquivalence (eta.app q) := by
    intro q
    cases q with
    | none => change WeakEquivalence (𝟙 B); infer_instance
    | some q =>
      cases q with
      | left => change WeakEquivalence (𝟙 E); infer_instance
      | right => change WeakEquivalence b; exact (weakEquivalence_iff b).mpr hb
  have hm : SSet.realizationWeakEquivalences
      ((homotopyPullback (C := SSet.{u})).map eta) :=
    (weakEquivalence_iff _).mp (homotopyPullback_map_weakEquivalence eta hEta)
  have hlim : SSet.realizationWeakEquivalences (lim.map eta) := by
    apply SSet.realizationWeakEquivalences.of_postcomp _ _ hcG
    rw [(homotopyPullbackComparison (C := SSet.{u})).naturality eta]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hcF hm
  have hproj : lim.map eta ≫ pullback.fst p (𝟙 B) = pullback.fst p b := by
    have h := limMap_π eta WalkingCospan.left
    change lim.map eta ≫ pullback.fst p (𝟙 B) = pullback.fst p b ≫ 𝟙 E at h
    simpa only [Category.comp_id] using h
  have he : SSet.realizationWeakEquivalences (pullback.fst p (𝟙 B)) :=
    (weakEquivalence_iff (pullback.fst p (𝟙 B))).mp inferInstance
  rw [← hproj]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hlim he

private theorem endpointBaseWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌))) :
    SSet.KanComplex.W
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) := by
  let _ : SSet.KanComplex (W.diagram _⦋0⦌) := originalLevelKan W hW 0
  let _ : SSet.KanComplex (V.diagram _⦋0⦌) := originalLevelKan V hV 0
  have hw := (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr h0
  exact hw.prodMap hw

private theorem endpointProjectionWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌))) :
    SSet.realizationWeakEquivalences
      (pullback.fst (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) := by
  have hb := endpointBaseWeak f hW hV h0
  let _ : SSet.KanComplex (W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌) := hb.kanComplex_source
  let _ : SSet.KanComplex (V.diagram _⦋0⦌ ⨯ V.diagram _⦋0⦌) := hb.kanComplex_target
  let _ : Fibration (mappingEndpoint V) := ReedyModel.mappingEndpoint_fibration V hV.1
  exact originalPullbackProjectionWeak _ _
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp hb)

private theorem originalDegreeOneWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (hm : ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map f (x := x) (y := y) rfl rfl)) :
    SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌)) := by
  have hc := (mappingEndpointComparison_realizationWeak_iff f hW.1 hV.1).mpr hm
  have hp := endpointProjectionWeak f hW hV h0
  rw [← mappingEndpointComparison_fst f]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hc hp

private theorem originalMappingFibresWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (h1 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌))) :
    ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map f (x := x) (y := y) rfl rfl) := by
  apply (mappingEndpointComparison_realizationWeak_iff f hW.1 hV.1).mp
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ (endpointProjectionWeak f hW hV h0)
  simpa only [mappingEndpointComparison_fst] using h1

private theorem edgeMappingIso_target {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n : ℕ) (i : Fin n) :
    (discreteSourceMappingMap f).app (op (SSet.Rezk.segalSpineEdgeSubcomplex.{u} n i : SSet.{u})) ≫
      (spineEdgeMappingIso V n i).hom =
    (spineEdgeMappingIso W n i).hom ≫ f.hom.app (op ⦋1⦌) := by
  let e := (asIso (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineEdgeMap.{u} n i))).op
  have hnat := (discreteSourceMappingMap f).naturality e.hom
  simp only [spineEdgeMappingIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← hnat, Category.assoc, discreteYonedaIso_naturality_target]
  exact (Category.assoc _ _ _).symm

private theorem vertexMappingIso_target {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n k : ℕ) (h : k ≤ n) :
    (discreteSourceMappingMap f).app
      (op (SSet.Rezk.segalSpineVertexSubcomplex.{u} n k h : SSet.{u})) ≫
      (spineVertexMappingIso V n k h).hom =
    (spineVertexMappingIso W n k h).hom ≫ f.hom.app (op ⦋0⦌) := by
  let e := (asIso (SSet.Subcomplex.toRange (SSet.Rezk.segalSpineVertexMap.{u} n k h))).op
  have hnat := (discreteSourceMappingMap f).naturality e.hom
  simp only [spineVertexMappingIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← hnat, Category.assoc, discreteYonedaIso_naturality_target]
  exact (Category.assoc _ _ _).symm

private theorem firstPrefixIso_target {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n : ℕ) (h : 1 ≤ n) :
    (discreteSourceMappingMap f).app (op (SSet.Rezk.spinePrefixSubcomplex.{u} n 1 h : SSet.{u})) ≫
      (spinePrefixFirstMappingIso V n h).hom =
    (spinePrefixFirstMappingIso W n h).hom ≫ f.hom.app (op ⦋1⦌) := by
  rw [spinePrefixFirstMappingIso_hom, spinePrefixFirstMappingIso_hom]
  let a := (SSet.Rezk.spinePrefixPreviousEdge.{u} n 1 h (by omega)).op
  have hn := (discreteSourceMappingMap f).naturality a
  unfold spinePrefixLastEdgeProjection
  rw [← Category.assoc, ← hn, Category.assoc, discreteYonedaIso_naturality_target]
  exact (Category.assoc _ _ _).symm

private theorem originalPrefixMapWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (h1 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌)))
    (n k : ℕ) (hkn : k ≤ n) (hk : 1 ≤ k) :
    SSet.realizationWeakEquivalences ((discreteSourceMappingMap f).app
      (op (SSet.Rezk.spinePrefixSubcomplex.{u} n k hkn : SSet.{u}))) := by
  revert hkn hk
  induction k with
  | zero => intro hkn hk; omega
  | succ k ih =>
    intro hkn hk
    cases k with
    | zero =>
      let e := Arrow.isoMk'
        ((discreteSourceMappingMap f).app
          (op (SSet.Rezk.spinePrefixSubcomplex.{u} n 1 hkn : SSet.{u})))
        (f.hom.app (op ⦋1⦌)) (spinePrefixFirstMappingIso W n hkn)
        (spinePrefixFirstMappingIso V n hkn) (firstPrefixIso_target f n hkn).symm
      exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).mpr h1
    | succ k =>
      have hprev : k + 1 ≤ n := by omega
      have hkprev : 1 ≤ k + 1 := by omega
      let eta := spinePrefixMappingCospanMap f n (k + 1) hkn hkprev
      have hparts : ∀ j, WeakEquivalence (eta.app j) := by
        intro j
        cases j with
        | none =>
          let e := Arrow.isoMk' (eta.app WalkingCospan.one) (f.hom.app (op ⦋0⦌))
            (spineVertexMappingIso W n (k + 1) hprev)
            (spineVertexMappingIso V n (k + 1) hprev)
            (vertexMappingIso_target f n (k + 1) hprev).symm
          exact (weakEquivalence_iff _).mpr
            ((SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).mpr h0)
        | some j =>
          cases j with
          | left =>
            change WeakEquivalence ((discreteSourceMappingMap f).app
              (op (SSet.Rezk.spinePrefixSubcomplex.{u} n (k + 1) hprev : SSet.{u})))
            exact (weakEquivalence_iff _).mpr (ih hprev hkprev)
          | right =>
            let e := Arrow.isoMk' (eta.app WalkingCospan.right) (f.hom.app (op ⦋1⦌))
              (spineEdgeMappingIso W n ⟨k + 1, by omega⟩)
              (spineEdgeMappingIso V n ⟨k + 1, by omega⟩)
              (edgeMappingIso_target f n ⟨k + 1, by omega⟩).symm
            exact (weakEquivalence_iff _).mpr
              ((SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).mpr h1)
      have hm : SSet.realizationWeakEquivalences
          ((homotopyPullback (C := SSet.{u})).map eta) :=
        (weakEquivalence_iff _).mp (homotopyPullback_map_weakEquivalence eta hparts)
      have hcw := spinePrefixToHomotopyPullback_weak W n (k + 1) hkn hkprev hW.1
      have hcv := spinePrefixToHomotopyPullback_weak V n (k + 1) hkn hkprev hV.1
      apply SSet.realizationWeakEquivalences.of_postcomp _ _ hcv
      rw [spinePrefixToHomotopyPullback_naturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hcw hm

private theorem originalHigherLevelsWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (h0 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋0⦌)))
    (h1 : SSet.realizationWeakEquivalences (f.hom.app (op ⦋1⦌))) :
    ∀ n : ℕ, SSet.realizationWeakEquivalences (f.hom.app (op ⦋n⦌)) := by
  intro n
  cases n with
  | zero => exact h0
  | succ n =>
    cases n with
    | zero => exact h1
    | succ n =>
      have hn : 2 ≤ n + 2 := by omega
      have hpref := originalPrefixMapWeak f hW hV h0 h1 (n + 2) (n + 2) le_rfl (by omega)
      have hspine : SSet.realizationWeakEquivalences ((discreteSourceMappingMap f).app
          (op (SSet.Rezk.spineSubcomplex.{u} (n + 2) : SSet.{u}))) := by
        let e := (SSet.Subcomplex.eqToIso
          (SSet.Rezk.spinePrefixSubcomplex_full.{u} (n + 2))).op.symm
        let a := Arrow.isoMk'
          ((discreteSourceMappingMap f).app
            (op (SSet.Rezk.spinePrefixSubcomplex.{u} (n + 2) (n + 2) le_rfl : SSet.{u})))
          ((discreteSourceMappingMap f).app
            (op (SSet.Rezk.spineSubcomplex.{u} (n + 2) : SSet.{u})))
          ((discreteSourceMapping W).mapIso e) ((discreteSourceMapping V).mapIso e)
          ((discreteSourceMappingMap f).naturality e.hom)
        exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff a).mp hpref
      have hw := ((mem_trivialFibrations_iff _).mp
        (rawSegalComparison_trivialFibration W (n + 2) hn hW)).2
      have hv := ((mem_trivialFibrations_iff _).mp
        (rawSegalComparison_trivialFibration V (n + 2) hn hV)).2
      have hqw : SSet.realizationWeakEquivalences (rawSegalComparison W (n + 2)) :=
        (weakEquivalence_iff _).mp hw
      have hqv : SSet.realizationWeakEquivalences (rawSegalComparison V (n + 2)) :=
        (weakEquivalence_iff _).mp hv
      apply SSet.realizationWeakEquivalences.of_postcomp _ _ hqv
      rw [← rawSegalComparison_naturality]
      exact SSet.realizationWeakEquivalences.comp_mem _ _ hqw hspine

private theorem originalHoEssSurj {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (hc : Function.Surjective (SSet.mapπ₀ (f.hom.app (op ⦋0⦌)))) :
    (SegalHomotopy.map f hW hV).EssSurj := by
  constructor
  intro v
  obtain ⟨c, hfc⟩ := hc (SSet.π₀.mk v.vertex)
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  have hnat := SegalHomotopy.objectComponentClass_naturality f hW hV (SSet.π₀.mk x)
  have hcomp := congrArg (SegalHomotopy.objectComponentClass V hV) hfc
  rw [SegalHomotopy.objectComponentClass_mk, SegalHomotopy.objectQuotientMap_class] at hnat
  rw [SegalHomotopy.objectComponentClass_mk] at hcomp
  have hi := (SegalHomotopy.objectClass_eq_iff V hV (mappingVertexMap f x) v.vertex).mp
    (hnat.trans hcomp)
  refine ⟨⟨x⟩, ?_⟩
  change Nonempty ((⟨mappingVertexMap f x⟩ : SegalHomotopy.Object V hV) ≅ ⟨v.vertex⟩)
  exact hi

/-- FULL original intrinsic DK/levelwise weak equivalence at complete endpoints.
No lower-degree or global-core weakness is a caller input. -/
theorem completeSegalMap_levelwiseWeak_iff {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    ((∀ x y : (W.diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map f (x := x) (y := y) rfl rfl)) ∧
      (let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1
       let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
       (SegalHomotopy.map f hS hT).EssSurj)) ↔
    ∀ n : ℕ, SSet.realizationWeakEquivalences (f.hom.app (op ⦋n⦌)) := by
  let hS := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1
  let hT := ((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1
  constructor
  · rintro ⟨hm, hE⟩
    have h0 := completeSegalMap_degreeZero_weak f hW hV hm hE
    have h1 := originalDegreeOneWeak f hS hT h0 hm
    exact originalHigherLevelsWeak f hS hT h0 h1
  · intro hall
    refine ⟨originalMappingFibresWeak f hS hT (hall 0) (hall 1), ?_⟩
    exact originalHoEssSurj f hS hT (SSet.realizationWeakEquivalences.bijective_mapπ₀ (hall 0)).2

end SimplicialSpace
