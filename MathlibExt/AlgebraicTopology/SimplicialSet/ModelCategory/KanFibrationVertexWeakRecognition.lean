/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceHomGroupComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence

/-!
# Weak-map recognition from the full original Kan fibres

For two actual Kan fibrations over the same Kan base, weakness of all
original strict vertex-fibre maps detects weakness of the original total
map. The complete original fibre inclusions and base square are retained.
The component proof uses the genuine degree-zero pointed set and original
connecting exactness; no group structure on degree zero is assumed.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.KanComplex

/-- The native component equivalence carries the chosen component to the
original distinguished pointed class. -/
lemma π₀EquivπZero_basePoint {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌) :
    π₀EquivπZero x (π₀.mk x) = 1 := by
  rw [π₀EquivπZero_mk]
  change π.mk ((PtSimplex.equiv₀ x).symm x) = π.mk (RelativeMorphism.const)
  apply congrArg π.mk
  apply (PtSimplex.equiv₀ x).injective
  simp [PtSimplex.equiv₀, SSet.yonedaEquiv_const]

/-- Pointed degree-zero naturality for the SAME original simplicial map. -/
lemma piMap_zero_component_naturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y) (a : π₀ X) :
    π.map f h 0 (π₀EquivπZero x a) = π₀EquivπZero y (mapπ₀ f a) :=
  congrFun (mapπ_comp_π₀EquivπZero f x y h) a

/-- Weakness gives each SAME full pointed map with any valid original
point witness. -/
lemma W.bijective_piMap_pointed {X Y : SSet.{u}} {f : X ⟶ Y} (hf : W f)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) (h : f.app _ x = y) (n : ℕ) :
    Function.Bijective (π.map f h n) := by
  subst y
  exact hf.bijective_piMap n x

end SSet.KanComplex

namespace SSet.KanFibrationVertexWeakRecognition

variable {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F)
  (hf : f ≫ q = p) [Fibration p] [Fibration q] [IsFibrant B]

/-- The SAME source fibration with its actual image vertex as basepoint. -/
def sourceSequence (e : E _⦋0⦌) : FibrationSequence.{u} where
  E := E
  B := B
  p := p
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := e
  b := p.app _ e
  hb := rfl

/-- The SAME target fibration at the image of the chosen source point,
with the literal common original base vertex. -/
def targetSequence (e : E _⦋0⦌) : FibrationSequence.{u} where
  E := F
  B := B
  p := q
  fibration_p := inferInstance
  fibrant_B := inferInstance
  e := f.app _ e
  b := p.app _ e
  hb := by change (f ≫ q).app _ e = p.app _ e; rw [hf]

/-- The complete original total map over the identity of the SAME base. -/
def sequenceMap (e : E _⦋0⦌) :
    FibrationSequenceHom (sourceSequence p e) (targetSequence p q f hf e) where
  totalMap := f
  baseMap := 𝟙 B
  comm := by
    change f ≫ q = p ≫ 𝟙 B
    simpa only [Category.comp_id] using hf
  total_pt := rfl
  base_pt := rfl

/-- Its full fibre map is literally the original `Subcomplex.mapFiber`
of the given base square. -/
lemma sequenceMap_fiberMap (e : E _⦋0⦌) :
    (sequenceMap p q f hf e).fiberMap =
      Subcomplex.mapFiber (f := p) (f' := q) f (𝟙 B)
        (by simpa only [Category.comp_id] using hf) (y := p.app _ e) (y' := p.app _ e) rfl := rfl

/-- All original strict fibre maps weak implies that the complete original
map is weak in the Kan-complex class. -/
theorem W_of_vertexFibers
    (hF : ∀ b : B _⦋0⦌, KanComplex.W
      (Subcomplex.mapFiber (f := p) (f' := q) f (𝟙 B)
        (by simpa only [Category.comp_id] using hf) (y := b) (y' := b) rfl)) :
    KanComplex.W f := by
  let _ : IsFibrant E := isFibrant_of_fibration p
  let _ : IsFibrant F := isFibrant_of_fibration q
  apply (KanComplex.W_iff f).mpr
  constructor
  · constructor
    · intro a a' haa
      obtain ⟨e, rfl⟩ := a.mk_surjective
      obtain ⟨e', rfl⟩ := a'.mk_surjective
      let S := sourceSequence p e'
      let T := targetSequence p q f hf e'
      let g := sequenceMap p q f hf e'
      have hB (n : ℕ) : Function.Bijective (KanComplex.π.map g.baseMap g.base_pt n) := by
        change Function.Bijective (KanComplex.π.map (x := p.app _ e') (𝟙 B) rfl n)
        have h : KanComplex.π.map (x := p.app _ e') (𝟙 B) rfl n = id :=
          funext (fun t => KanComplex.π.map_id_apply t)
        rw [h]
        exact Function.bijective_id
      have hFi : Function.Injective (KanComplex.π.map g.fiberMap g.fiberMap_app_basePoint 0) :=
        ((hF (p.app _ e')).bijective_piMap_pointed S.fiberPoint T.fiberPoint
          g.fiberMap_app_basePoint 0).1
      have he : KanComplex.π.map g.totalMap g.total_pt 0
          (KanComplex.π₀EquivπZero S.e (π₀.mk e)) = 1 := by
        rw [KanComplex.piMap_zero_component_naturality]
        exact (congrArg (KanComplex.π₀EquivπZero T.e) haa).trans
          (KanComplex.π₀EquivπZero_basePoint T.e)
      have h := g.piMap_total_eq_one_of_map_eq_one 0 (hB 0).1 (hB 1).2 hFi _ he
      exact (KanComplex.π₀EquivπZero S.e).injective
        (h.trans (KanComplex.π₀EquivπZero_basePoint S.e).symm)
    · intro a
      obtain ⟨y, rfl⟩ := a.mk_surjective
      let b := q.app _ y
      let z := Subcomplex.fiber.basePoint (f := q) y (show q.app _ y = b from rfl)
      obtain ⟨c, hc⟩ := (hF b).bijective_mapπ₀.2 (π₀.mk z)
      refine ⟨mapπ₀ (Subcomplex.fiber p b).ι c, ?_⟩
      calc
        mapπ₀ f (mapπ₀ (Subcomplex.fiber p b).ι c) =
            mapπ₀ (Subcomplex.fiber q b).ι
              (mapπ₀ (Subcomplex.mapFiber f (𝟙 B)
                (by simpa only [Category.comp_id] using hf) (y := b) (y' := b) rfl) c) := by
          rw [← mapπ₀_comp_apply, ← mapπ₀_comp_apply, Subcomplex.mapFiber_ι]
        _ = mapπ₀ (Subcomplex.fiber q b).ι (π₀.mk z) := congrArg _ hc
        _ = π₀.mk y := rfl
  · intro n e
    let g := sequenceMap p q f hf e
    apply g.piMap_total_bijective_succ n
    · intro k
      change Function.Bijective (KanComplex.π.map (x := p.app _ e) (𝟙 B) rfl k)
      have h : KanComplex.π.map (x := p.app _ e) (𝟙 B) rfl k = id :=
        funext (fun t => KanComplex.π.map_id_apply t)
      rw [h]
      exact Function.bijective_id
    · intro k
      exact (hF (p.app _ e)).bijective_piMap_pointed
        (sourceSequence p e).fiberPoint (targetSequence p q f hf e).fiberPoint
        g.fiberMap_app_basePoint k

/-- The detected map lies in the SAME original realization weak class. -/
theorem realizationWeakEquivalences_of_vertexFibers
    (hF : ∀ b : B _⦋0⦌, realizationWeakEquivalences
      (Subcomplex.mapFiber (f := p) (f' := q) f (𝟙 B)
        (by simpa only [Category.comp_id] using hf) (y := b) (y' := b) rfl)) :
    realizationWeakEquivalences f := by
  let _ : IsFibrant E := isFibrant_of_fibration p
  let _ : IsFibrant F := isFibrant_of_fibration q
  apply (KanComplex.W_iff_realizationWeakEquivalence f).mp
  apply W_of_vertexFibers p q f hf
  intro b
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr (hF b)

end SSet.KanFibrationVertexWeakRecognition
