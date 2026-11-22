/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningFibre
import MathlibExt.CategoryTheory.Enriched.StrictComposition

/-!
# The full original coefficient action over a constant coherent base

The actual original ordinal collapse sends every original coherent path
to the original singleton identity path. Restricting the SAME original
coherent vertex therefore gives the whole original constant base
simplex. Its coefficient Hom action is precisely the original coefficient
identity, in every degree. This keeps the actual full marked sections and
operators needed to compare original inverse triangles.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable {C : Type u} [EnrichedCategory SSet.{u} C]

/-- The SAME original unique ordinal map to the original zero-simplex. -/
def originalZeroCollapse (n : ℕ) : Vertex.{u} n →o Vertex.{u} 0 :=
  OrderHom.const _ (ULift.up (0 : Fin 1))

/-- The SAME original constant base simplex is the genuine whole original ordinal restriction of its original
coherent vertex. -/
def originalConstantBase (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) (n : ℕ) :
    EnrichedFunctor SSet.{u} (Index.{u} n) C := (indexMap (originalZeroCollapse n)).comp SSet.{u} v

/-- Every SAME original collapsed coherent Hom is the ENTIRE original singleton identity, in all degrees and with no
path omitted. -/
theorem originalZeroCollapse_map (n : ℕ) (i j : Index.{u} n) :
    (indexMap (originalZeroCollapse n)).map i j =
      CartesianMonoidalCategory.toUnit (i ⟶[SSet.{u}] j) ≫
        eId SSet.{u} (SimplicialThickening.mk (ULift.up (0 : Fin 1))) := by
  ext q p
  refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => by rfl)
  apply SimplicialThickening.Path.ext
  change originalZeroCollapse n '' (p.obj k).I = {ULift.up (0 : Fin 1)}
  ext z
  constructor
  · rintro ⟨a, _, rfl⟩
    exact Set.mem_singleton _
  · intro hz
    have hz' : z = ULift.up (0 : Fin 1) := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨i.as, (p.obj k).left, rfl⟩

/-- Every SAME original operator preserves the entire original constant base, including all its Hom maps. -/
theorem originalConstantBase_pull (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C)
    {m n : ℕ} (f : Vertex.{u} m →o Vertex.{u} n) :
    (indexMap f).comp SSet.{u} (originalConstantBase v n) = originalConstantBase v m := by
  change (indexMap f).comp SSet.{u} ((indexMap (originalZeroCollapse n)).comp SSet.{u} v) = _
  dsimp only [indexMap]
  rw [← EnrichedFunctor.comp_assoc_eq, ← SimplicialThickening.functor_comp]
  rfl

/-- The SAME original zero-dimensional constant base is its entire original coherent vertex. -/
theorem originalConstantBase_zero (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) :
    originalConstantBase v 0 = v := by
  have h : originalZeroCollapse.{u} 0 = (OrderHom.id : Vertex.{u} 0 →o Vertex.{u} 0) := by
    apply OrderHom.ext
    funext a
    apply ULift.ext
    exact (Fin.eq_zero a.down).symm
  rw [originalConstantBase, h, indexMap, SimplicialThickening.functor_id, EnrichedFunctor.id_comp_eq]

/-- The actual original degeneracy is the SAME entire original constant base in the next dimension. -/
theorem originalConstantBase_sigma (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) (n : ℕ) :
    (coherentBase C).σ (0 : Fin (n + 1)) (originalConstantBase v n) =
      originalConstantBase v (n + 1) :=
  originalConstantBase_pull v (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom.uliftMap

/-- The SAME original double-degenerate coherent vertex is the whole original constant two-simplex. -/
theorem originalConstantBase_two (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) :
    (coherentBase C).σ (0 : Fin 2) ((coherentBase C).σ (0 : Fin 1) v) = originalConstantBase v 2 := by
  have h₁ : (coherentBase C).σ (0 : Fin 1) v = originalConstantBase v 1 :=
    (congrArg ((coherentBase C).σ (0 : Fin 1)) (originalConstantBase_zero v).symm).trans
      (originalConstantBase_sigma v 0)
  exact (congrArg ((coherentBase C).σ (0 : Fin 2)) h₁).trans (originalConstantBase_sigma v 1)

/-- The SAME original constant-base coefficient diagram retains the unchanged original marked value. -/
abbrev originalConstantCoefficient (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) (n : ℕ) : EnrichedDiagram (Index.{u} n)ᵒᵖ :=
  simplexCoefficient F (originalConstantBase v n)

/-- Its complete original Hom action is precisely the original coefficient identity, with every whole path parameter
retained. -/
theorem originalConstantCoefficient_action (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) (n : ℕ) (i j : Index.{u} n) :
    enrichedDiagramAction (originalConstantCoefficient F v n) (op i) (op j) =
      prodSnd (max ((op i) ⟶[SSet.{u}] (op j)))
        (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))) := by
  let r : Index.{u} 0 := SimplicialThickening.mk (ULift.up (0 : Fin 1))
  let c := op (v.obj r)
  apply Hom.ext
  ext q z
  have hp : ((indexMap (originalZeroCollapse n)).opposite.map (op i) (op j)).app q z.1 =
      (eId SSet.{u} (op r)).app q PUnit.unit := by
    exact congrArg (fun h => h.app q z.1) (originalZeroCollapse_map n j i)
  have hv : (v.opposite.map (op r) (op r)).app q
      ((eId SSet.{u} (op r)).app q PUnit.unit) = (eId SSet.{u} c).app q PUnit.unit :=
    congrArg (fun h => h.app q PUnit.unit) (v.opposite.map_id (op r))
  change ((F.map c c).app q
      ((v.opposite.map (op r) (op r)).app q
        (((indexMap (originalZeroCollapse n)).opposite.map (op i) (op j)).app q z.1))).hom.app q
      (yonedaEquiv (𝟙 (SSet.stdSimplex.obj q.unop)), z.2) = z.2
  rw [hp, hv]
  exact enrichedDiagramAction_id F c q z.2

/-- The SAME original fixed-section equivalence retains every whole original marked component through its actual
base equality. -/
theorem fixedSectionEquiv_app_heq (F : EnrichedDiagram Cᵒᵖ) {n : ℕ}
    (σ : EnrichedFunctor SSet.{u} (Index.{u} n) C)
    (a : {a : UnstraighteningSimplex F n // a.base = σ}) (i : (Index.{u} n)ᵒᵖ) :
    HEq ((fixedSectionEquiv F σ a).app i) (a.val.sectionMap.app i) := by
  rcases a with ⟨⟨τ, s⟩, h⟩
  cases h
  rfl

/-- A SAME whole original constant-base section restricts by the actual original ordinal operator and its exact full
original base equality. -/
def originalConstantSectionFace (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) {m n : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n)
    (s : EnrichedDiagramMap (coneDiagram n) (originalConstantCoefficient F v n)) :
    EnrichedDiagramMap (coneDiagram m) (originalConstantCoefficient F v m) :=
  fixedSectionEquiv F (originalConstantBase v m)
    ⟨(UnstraighteningSimplex.mk (originalConstantBase v n) s).pull f, originalConstantBase_pull v f⟩

/-- Every SAME original restricted constant-base marked component is the actual original cone-image map followed by
the unchanged original section component. -/
theorem originalConstantSectionFace_app (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) {m n : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n)
    (s : EnrichedDiagramMap (coneDiagram n) (originalConstantCoefficient F v n)) (i : (Index.{u} m)ᵒᵖ) :
    (originalConstantSectionFace F v f s).app i =
      coneImage f i.unop.as ≫ s.app (op ((indexMap f).obj i.unop)) := by
  have h := fixedSectionEquiv_app_heq F (originalConstantBase v m)
    ⟨(UnstraighteningSimplex.mk (originalConstantBase v n) s).pull f, originalConstantBase_pull v f⟩ i
  exact (eq_of_heq h).trans (UnstraighteningSimplex.pull_section f _ i)

/-- The SAME original restricted section reconstructs precisely the whole original restricted unstraightening
simplex, including its entire original base. -/
theorem originalConstantSectionFace_simplex (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) {m n : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n)
    (s : EnrichedDiagramMap (coneDiagram n) (originalConstantCoefficient F v n)) :
    UnstraighteningSimplex.mk (originalConstantBase v m) (originalConstantSectionFace F v f s) =
      (UnstraighteningSimplex.mk (originalConstantBase v n) s).pull f :=
  congrArg Subtype.val ((fixedSectionEquiv F (originalConstantBase v m)).symm_apply_apply
    ⟨(UnstraighteningSimplex.mk (originalConstantBase v n) s).pull f, originalConstantBase_pull v f⟩)

/-- Equal SAME whole original restricted simplices have equal ENTIRE original constant-base sections, with all
marked components and Hom naturality retained. -/
theorem originalConstantSectionFace_eq_of_simplex_eq (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C) {m n k : ℕ}
    (f : Vertex.{u} m →o Vertex.{u} n) (g : Vertex.{u} m →o Vertex.{u} k)
    (s : EnrichedDiagramMap (coneDiagram n) (originalConstantCoefficient F v n))
    (t : EnrichedDiagramMap (coneDiagram k) (originalConstantCoefficient F v k))
    (h : (UnstraighteningSimplex.mk (originalConstantBase v n) s).pull f =
      (UnstraighteningSimplex.mk (originalConstantBase v k) t).pull g) :
    originalConstantSectionFace F v f s = originalConstantSectionFace F v g t := by
  have hs := (originalConstantSectionFace_simplex F v f s).trans
    (h.trans (originalConstantSectionFace_simplex F v g t).symm)
  simp only [UnstraighteningSimplex.mk.injEq] at hs
  exact eq_of_heq hs.2

/-- The SAME original constant-base coefficient read is precisely its unchanged original root coefficient edge. -/
def originalConstantSectionRead (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C)
    (s : EnrichedDiagramMap (coneDiagram 1) (originalConstantCoefficient F v 1)) :
    (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))).toSSet _⦋1⦌ :=
  (s.app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌) coefficientEdge

/-- The SAME first face coefficient read is the original first inclusion edge of the whole original root triangle. -/
theorem originalConstantSectionRead_first (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C)
    (s : EnrichedDiagramMap (coneDiagram 2) (originalConstantCoefficient F v 2)) :
    originalConstantSectionRead F v (originalConstantSectionFace F v
      (coneCofaceEmbedding (2 : Fin 3)).toOrderHom s) =
      (s.app (op (SimplicialThickening.mk rootTriangleZero))).hom.app (op ⦋1⦌)
        (nerve.edgeMk rootTriangleFirst).edge := by
  rw [originalConstantSectionRead, originalConstantSectionFace_app]
  change (s.app (op (SimplicialThickening.mk rootTriangleZero))).hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (2 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌) coefficientEdge) = _
  rw [rootTriangle_first_image]

/-- The SAME long face coefficient read is its entire original direct root inclusion edge. -/
theorem originalConstantSectionRead_direct (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C)
    (s : EnrichedDiagramMap (coneDiagram 2) (originalConstantCoefficient F v 2)) :
    originalConstantSectionRead F v (originalConstantSectionFace F v
      (coneCofaceEmbedding (1 : Fin 3)).toOrderHom s) =
      (s.app (op (SimplicialThickening.mk rootTriangleZero))).hom.app (op ⦋1⦌)
        (nerve.edgeMk rootTriangleDirect).edge := by
  rw [originalConstantSectionRead, originalConstantSectionFace_app]
  change (s.app (op (SimplicialThickening.mk rootTriangleZero))).hom.app (op ⦋1⦌)
    ((coneImage (coneCofaceEmbedding (1 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌) coefficientEdge) = _
  rw [rootTriangle_direct_image]

/-- The SAME zero-face coefficient read is the original middle inclusion edge, by the ENTIRE original identity
action and whole original marked natural section. -/
theorem originalConstantSectionRead_middle (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C)
    (s : EnrichedDiagramMap (coneDiagram 2) (originalConstantCoefficient F v 2)) :
    originalConstantSectionRead F v (originalConstantSectionFace F v
      (coneCofaceEmbedding (0 : Fin 3)).toOrderHom s) =
      (s.app (op (SimplicialThickening.mk rootTriangleZero))).hom.app (op ⦋1⦌)
        (nerve.edgeMk rootTriangleMiddle).edge := by
  let i₀ : Index.{u} 2 := SimplicialThickening.mk rootTriangleZero
  let i₁ : Index.{u} 2 := SimplicialThickening.mk rootTriangleOne
  let w := (coneImage (coneCofaceEmbedding.{u} (0 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌) coefficientEdge
  have hn := enrichedDiagramAction_natural s (op i₁) (op i₀)
  rw [coneDiagram_action, originalConstantCoefficient_action] at hn
  have hr := congrArg (fun f => f.hom.app (op ⦋1⦌) (rootTrianglePathWord.{u}, w)) hn
  change (s.app (op i₀)).hom.app (op ⦋1⦌)
      ((coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌) (rootTrianglePathWord, w)) =
    (s.app (op i₁)).hom.app (op ⦋1⦌) w at hr
  have hw : (coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
    (rootTrianglePathWord, w) = (nerve.edgeMk rootTriangleMiddle).edge := rootTriangle_middle_action
  rw [hw] at hr
  rw [originalConstantSectionRead, originalConstantSectionFace_app]
  exact hr.symm

end SSet.Marked.CoherentWeight
