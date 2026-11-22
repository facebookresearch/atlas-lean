/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomUniversalGraph
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderRowCoefficients

/-!
# Entire original word-edge graph coordinates

Every complete base word retains its original edge from zero to the
supplied vertex. Its original pair and whole parameter Hom are retained.
The full original coefficient at either endpoint is the actual native
pullback of the universal indexed Hom graph over that same word-edge map.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph

variable (C : Carrier.{u})

/-- The SAME complete original coefficient and full parameter at the supplied object getter. -/
abbrev coefficients (K : C × C → C) (z : C) (i : C × C) : SSet.{u} :=
  (z ⟶[SSet.{u}] K i) ⊗ parameters C i

/-- The actual full original indexed coefficient object. -/
abbrev coefficientObject (K : C × C → C) (z : C) : SSet.{u} := ∐ (coefficients C K z)

/-- Its SAME complete original parameter projection. -/
def coefficientProjection (K : C × C → C) (z : C) : coefficientObject C K z ⟶ base C :=
  Limits.Sigma.map (fun i : C × C => snd (z ⟶[SSet.{u}] K i) (parameters C i))

end CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph

namespace SSet.ScalarUnderCategory
open CategoryTheory.SimplicialEnrichment.EnrichedHomUniversalGraph

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The actual original whole word-edge map at every scalar degree. -/
def rowWordEdge (n : ℕ) (j : Fin (n + 1)) : baseRow C n ⟶ base C where
  app q := ↾fun w => (Sigma.ι (parameters C) ((w.obj 0).obj, (w.obj j).obj)).app q
    (w.map (homOfLE (Fin.zero_le j)))
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro w
    exact NatTrans.naturality_apply
      (Sigma.ι (parameters C) ((w.obj 0).obj, (w.obj j).obj)) f
      (w.map (homOfLE (Fin.zero_le j)))

/-- The complete original word and full Hom at its supplied original pair endpoint. -/
def rowGraphCoefficients (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) : SSet.{u} where
  obj q := Σ w : (baseRow C n).obj q,
    (z ⟶[SSet.{u}] K ((w.obj 0).obj, (w.obj j).obj)).obj q
  map {q r} f := ↾fun a => ⟨(baseRow C n).map f a.1,
    (z ⟶[SSet.{u}] K ((a.1.obj 0).obj, (a.1.obj j).obj)).map f a.2⟩
  map_id q := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Sigma.ext
    · exact (baseRow C n).map_id_apply q a.1
    · exact heq_of_eq ((z ⟶[SSet.{u}] K ((a.1.obj 0).obj, (a.1.obj j).obj)).map_id_apply q a.2)
  map_comp {q r t} f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Sigma.ext
    · exact (baseRow C n).map_comp_apply f g a.1
    · exact heq_of_eq ((z ⟶[SSet.{u}] K ((a.1.obj 0).obj, (a.1.obj j).obj)).map_comp_apply f g a.2)

/-- Keep the SAME entire original base word. -/
def rowGraphProjection (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphCoefficients C K z n j ⟶ baseRow C n where
  app _ := ↾_root_.Sigma.fst
  naturality _ _ _ := rfl

/-- The complete original coefficient and SAME word-edge simplex at its original pair. -/
def rowGraphFamilyMap (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphCoefficients C K z n j ⟶ coefficientObject C K z where
  app q := ↾fun a =>
    (Sigma.ι (coefficients C K z) ((a.1.obj 0).obj, (a.1.obj j).obj)).app q
      (SSet.componentTensorSimplex q a.2 (a.1.map (homOfLE (Fin.zero_le j))))
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro a
    let i : C × C := ((a.1.obj 0).obj, (a.1.obj j).obj)
    let x : (coefficients C K z i).obj q := (a.2, a.1.map (homOfLE (Fin.zero_le j)))
    exact congr($((Sigma.ι (coefficients C K z) i).naturality f) x)

/-- Both whole original maps retain the SAME original parameter square. -/
lemma rowGraphFamilyMap_projection (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphFamilyMap C K z n j ≫ coefficientProjection C K z =
      rowGraphProjection C K z n j ≫ rowWordEdge C n j := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact SSet.sigmaMap_app_ι_app
    (fun i : C × C => snd (z ⟶[SSet.{u}] K i) (parameters C i)) q.unop.len
    ((a.1.obj 0).obj, (a.1.obj j).obj) (a.2, a.1.map (homOfLE (Fin.zero_le j)))

/-- The SAME complete original row coordinate map into its full native universal pullback. -/
def rowGraphToPullback (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphCoefficients C K z n j ⟶ pullback (coefficientProjection C K z) (rowWordEdge C n j) :=
  pullback.lift (rowGraphFamilyMap C K z n j) (rowGraphProjection C K z n j)
    (rowGraphFamilyMap_projection C K z n j)

/-- The actual first projection retains all original coefficients and the full word edge. -/
@[reassoc]
lemma rowGraphToPullback_fst (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphToPullback C K z n j ≫ pullback.fst _ _ = rowGraphFamilyMap C K z n j :=
  pullback.lift_fst _ _ _

/-- The actual second projection retains the SAME complete original base word. -/
@[reassoc]
lemma rowGraphToPullback_snd (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphToPullback C K z n j ≫ pullback.snd _ _ = rowGraphProjection C K z n j :=
  pullback.lift_snd _ _ _


/-- The SAME entire original graph-coordinate map is an actual Iso onto
the full native universal pullback, preserving all words and coefficients. -/
instance rowGraphToPullback_isIso (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    IsIso (rowGraphToPullback C K z n j) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  let P := coefficientProjection C K z
  let b := rowWordEdge C n j
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj q
  have hpb := (IsPullback.of_hasPullback P b).map E
  have hfst := congrArg (fun f => f.app q) (rowGraphToPullback_fst C K z n j)
  have hsnd := congrArg (fun f => f.app q) (rowGraphToPullback_snd C K z n j)
  constructor
  · rintro ⟨w, h⟩ ⟨w', h'⟩ ha
    have hw : w = w' := (congr($(hsnd) (⟨w, h⟩ : (rowGraphCoefficients C K z n j).obj q))).symm.trans
      ((congrArg (fun a => (pullback.snd P b).app q a) ha).trans
        (congr($(hsnd) (⟨w', h'⟩ : (rowGraphCoefficients C K z n j).obj q))))
    subst w'
    have he :
        (Sigma.ι (coefficients C K z) ((w.obj 0).obj, (w.obj j).obj)).app q
          (h, w.map (homOfLE (Fin.zero_le j))) =
        (Sigma.ι (coefficients C K z) ((w.obj 0).obj, (w.obj j).obj)).app q
          (h', w.map (homOfLE (Fin.zero_le j))) :=
      (congr($(hfst) (⟨w, h⟩ : (rowGraphCoefficients C K z n j).obj q))).symm.trans
        ((congrArg (fun a => (pullback.fst P b).app q a) ha).trans
          (congr($(hfst) (⟨w, h'⟩ : (rowGraphCoefficients C K z n j).obj q))))
    exact congrArg (fun h => (⟨w, h⟩ : (rowGraphCoefficients C K z n j).obj q))
      (congrArg _root_.Prod.fst (SSet.injective_sigma_ι_app q.unop.len _ he))
  · intro a
    obtain ⟨i, x, hx⟩ := SSet.exists_sigma_ι_app_eq q.unop.len ((pullback.fst P b).app q a)
    let w := (pullback.snd P b).app q a
    have hp := congr($(pullback.condition (f := P) (g := b)).app q a)
    have he : (Sigma.ι (parameters C) i).app q x.2 =
        (Sigma.ι (parameters C) ((w.obj 0).obj, (w.obj j).obj)).app q
          (w.map (homOfLE (Fin.zero_le j))) :=
      (SSet.sigmaMap_app_ι_app
        (fun k : C × C => snd (z ⟶[SSet.{u}] K k) (parameters C k)) q.unop.len i x).symm.trans
        ((congrArg (fun x => P.app q x) hx).trans hp)
    have hi : i = ((w.obj 0).obj, (w.obj j).obj) := SSet.eq_of_sigma_ι_app_eq he
    subst i
    have hparam : x.2 = w.map (homOfLE (Fin.zero_le j)) := SSet.injective_sigma_ι_app q.unop.len _ he
    let v : (rowGraphCoefficients C K z n j).obj q := ⟨w, x.1⟩
    refine ⟨v, Types.ext_of_isPullback hpb ?_ ?_⟩
    · have hv : (x.1, w.map (homOfLE (Fin.zero_le j))) = x := by
        rw [← hparam]
        exact _root_.Prod.eta _
      exact (congr($(hfst) v)).trans ((congrArg
        (fun t => (Sigma.ι (coefficients C K z) ((w.obj 0).obj, (w.obj j).obj)).app q t) hv).trans hx)
    · exact congr($(hsnd) v)

/-- Both whole original maps identify graph coordinates with the SAME full native universal pullback. -/
def rowGraphPullbackIso (K : C × C → C) (z : C) (n : ℕ) (j : Fin (n + 1)) :
    rowGraphCoefficients C K z n j ≅ pullback (coefficientProjection C K z) (rowWordEdge C n j) :=
  asIso (rowGraphToPullback C K z n j)

end SSet.ScalarUnderCategory
