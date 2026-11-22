/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomGraphCoordinates

/-!
# The SAME entire original row Hom transport

The complete original word remains fixed. Its initial Hom coefficient
is composed with the SAME full original edge to the selected vertex.
Both native universal graph pullback isomorphisms identify that exact
transport with the proved weak original universal base-change map.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph

variable (C : Carrier.{u})

/-- The full native first projection retains the SAME original universal graph map. -/
@[reassoc]
lemma baseChangeComparison_fst (z : C) {T : SSet.{u}} (b : T ⟶ base C) :
    baseChangeComparison C z b ≫ pullback.fst (targetProjection C z) b =
      pullback.fst (sourceProjection C z) b ≫ comparison C z := pullback.lift_fst _ _ _

/-- The full native second projection retains the SAME entire original base word. -/
@[reassoc]
lemma baseChangeComparison_snd (z : C) {T : SSet.{u}} (b : T ⟶ base C) :
    baseChangeComparison C z b ≫ pullback.snd (targetProjection C z) b =
      pullback.snd (sourceProjection C z) b := pullback.lift_snd _ _ _

end CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph

namespace SSet.ScalarUnderCategory
open CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The SAME complete original coefficient is transported along the
full original selected word edge, retaining the entire base word. -/
def rowGraphTransport (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphCoefficients C _root_.Prod.fst z n j ⟶ rowGraphCoefficients C _root_.Prod.snd z n j where
  app q := ↾fun a => ⟨a.1, (eComp SSet.{u} z (a.1.obj 0).obj (a.1.obj j).obj).app q
    (a.2, a.1.map (homOfLE (Fin.zero_le j)))⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Sigma.ext
    · rfl
    · let x : ((z ⟶[SSet.{u}] (a.1.obj 0).obj) ⊗ ((a.1.obj 0).obj ⟶[SSet.{u}] (a.1.obj j).obj)).obj q :=
        (a.2, a.1.map (homOfLE (Fin.zero_le j)))
      exact heq_of_eq (congr($((eComp SSet.{u} z (a.1.obj 0).obj (a.1.obj j).obj).naturality f) x))

/-- The SAME entire original base word is retained by the actual transport. -/
lemma rowGraphTransport_projection (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphTransport C z n j ≫ rowGraphProjection C _root_.Prod.snd z n j =
      rowGraphProjection C _root_.Prod.fst z n j := rfl

/-- The complete original coefficient map is the SAME universal indexed graph on every simplex. -/
lemma rowGraphFamilyMap_transport (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphFamilyMap C _root_.Prod.fst z n j ≫ comparison C z =
      rowGraphTransport C z n j ≫ rowGraphFamilyMap C _root_.Prod.snd z n j := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact SSet.sigmaMap_app_ι_app
    (fun i : C × C => CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies.postGraph z i.1 i.2)
    q.unop.len ((a.1.obj 0).obj, (a.1.obj j).obj) (a.2, a.1.map (homOfLE (Fin.zero_le j)))

/-- BOTH complete native pullback isomorphisms retain the SAME full original row transport square. -/
lemma rowGraphTransport_pullback_square (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphToPullback C _root_.Prod.fst z n j ≫ baseChangeComparison C z (rowWordEdge C n j) =
      rowGraphTransport C z n j ≫ rowGraphToPullback C _root_.Prod.snd z n j := by
  apply pullback.hom_ext
  · apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro a
    have h₁ := congrArg (fun h => h.app q) (baseChangeComparison_fst C z (rowWordEdge C n j))
    have h₂ := congrArg (fun h => h.app q) (rowGraphToPullback_fst C _root_.Prod.fst z n j)
    have h₃ := congrArg (fun h => h.app q) (rowGraphToPullback_fst C _root_.Prod.snd z n j)
    have h₄ := congrArg (fun h => h.app q) (rowGraphFamilyMap_transport C z n j)
    exact (congr($(h₁) ((rowGraphToPullback C _root_.Prod.fst z n j).app q a))).trans
      ((congrArg (fun t => (comparison C z).app q t) (congr($(h₂) a))).trans
        ((congr($(h₄) a)).trans (congr($(h₃) ((rowGraphTransport C z n j).app q a))).symm))
  · apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro a
    have h₁ := congrArg (fun h => h.app q) (baseChangeComparison_snd C z (rowWordEdge C n j))
    have h₂ := congrArg (fun h => h.app q) (rowGraphToPullback_snd C _root_.Prod.fst z n j)
    have h₃ := congrArg (fun h => h.app q) (rowGraphToPullback_snd C _root_.Prod.snd z n j)
    exact (congr($(h₁) ((rowGraphToPullback C _root_.Prod.fst z n j).app q a))).trans
      ((congr($(h₂) a)).trans (congr($(h₃) ((rowGraphTransport C z n j).app q a))).symm)

/-- The SAME full original transport is weak for groupoid components,
with every full word, edge, coefficient and ordinal arity retained. -/
theorem rowGraphTransport_weak [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)]
    (z : C) (n : ℕ) (j : Fin (n + 1)) : realizationWeakEquivalences (rowGraphTransport C z n j) := by
  let e : Arrow.mk (rowGraphTransport C z n j) ≅ Arrow.mk (baseChangeComparison C z (rowWordEdge C n j)) :=
    Arrow.isoMk' _ _ (rowGraphPullbackIso C _root_.Prod.fst z n j)
      (rowGraphPullbackIso C _root_.Prod.snd z n j) (rowGraphTransport_pullback_square C z n j)
  exact (realizationWeakEquivalences.arrow_mk_iso_iff e).mpr
    (baseChangeComparison_weak C z (rowWordEdge C n j))

end SSet.ScalarUnderCategory
