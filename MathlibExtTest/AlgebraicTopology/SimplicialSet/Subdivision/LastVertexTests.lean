/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.LastVertex

/-!
# Tests for the subdivision last-vertex map

These public-only clients check the representable maximum construction, its
left-Kan descent, canonical vertex lifts, and the two interval subdivision
edge orientations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.Subdivision
namespace LastVertexTests

private def fullChain (n : SimplexCategory) :
    PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len + 1))) where
  finset := Finset.univ
  comparable _ _ := le_total _ _

private def firstTwoChain :
    PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin 3)) where
  finset := {ULift.up 0, ULift.up 1}
  comparable _ _ := le_total _ _

private theorem singleton_le_full (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    SimplexCategory.sdSingletonChain n i ≤ fullChain n := by
  intro x _hx
  exact Finset.mem_univ x

private theorem singleton_zero_le_firstTwo :
    SimplexCategory.sdSingletonChain ⦋2⦌ 0 ≤ firstTwoChain := by
  intro x hx
  have hx' : x = ULift.up (0 : Fin 3) := by
    simpa [SimplexCategory.sdSingletonChain] using hx
  subst x
  simp [firstTwoChain]

private theorem firstTwo_le_full :
    firstTwoChain ≤ fullChain ⦋2⦌ := by
  intro x hx
  exact Finset.mem_univ x

private theorem chainLast_fullChain (n : SimplexCategory) :
    SimplexCategory.sdChainLast n (fullChain n) =
      ULift.up (Fin.last n.len) := by
  unfold SimplexCategory.sdChainLast fullChain
  rw [Finset.max'_eq_iff]
  constructor
  · simp
  · intro b _hb
    exact Fin.le_last b.down

private theorem chainLast_firstTwo :
    SimplexCategory.sdChainLast ⦋2⦌ firstTwoChain =
      ULift.up (1 : Fin 3) := by
  unfold SimplexCategory.sdChainLast firstTwoChain
  rw [Finset.max'_eq_iff]
  constructor
  · simp
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl <;> simp

private def deltaOneLeftEdge :
    (SimplexCategory.sd.{u}.obj ⦋1⦌) _⦋1⦌ :=
  ComposableArrows.mk₁
    (homOfLE (singleton_le_full ⦋1⦌ 0))

private def deltaOneRightEdge :
    (SimplexCategory.sd.{u}.obj ⦋1⦌) _⦋1⦌ :=
  ComposableArrows.mk₁
    (homOfLE (singleton_le_full ⦋1⦌ 1))

private def deltaTwoTopSimplex :
    (SimplexCategory.sd.{u}.obj ⦋2⦌) _⦋2⦌ :=
  ComposableArrows.mk₂
    (homOfLE singleton_zero_le_firstTwo)
    (homOfLE firstTwo_le_full)

section Representables

example {m n : SimplexCategory} (f : m ⟶ n)
    (S : PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (m.len + 1)))) :
    SimplexCategory.sdChainLast n (S.map
        ((SimplexCategory.toPartOrd.map f).hom :
          ULift.{u} (Fin (m.len + 1)) →o
            ULift.{u} (Fin (n.len + 1)))) =
      (SimplexCategory.toPartOrd.map f).hom
        (SimplexCategory.sdChainLast m S) :=
  SimplexCategory.sdChainLast_map f S

example {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.sd.map f ≫
        SimplexCategory.lastVertex.app n =
      SimplexCategory.lastVertex.app m ≫
        SSet.stdSimplex.map f :=
  SimplexCategory.lastVertex.naturality f

example :
    SimplexCategory.sdChainLast ⦋0⦌
      (SimplexCategory.sdSingletonChain ⦋0⦌ 0) =
        ULift.up 0 := by
  simp

/-- The left small interval edge maps from vertex 0 to vertex 1. -/
example (i : Fin 2) :
    SSet.stdSimplex.objEquiv
        ((SimplexCategory.lastVertex.app ⦋1⦌).app
          (op ⦋1⦌) deltaOneLeftEdge) i = i := by
  rw [SimplexCategory.lastVertex_app_objEquiv_apply]
  fin_cases i
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (SimplexCategory.sdSingletonChain ⦋1⦌ 0)).down = 0
    simp
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (fullChain ⦋1⦌)).down = 1
    rw [chainLast_fullChain]
    rfl

/-- The right small interval edge maps constantly to vertex 1. -/
example (i : Fin 2) :
    SSet.stdSimplex.objEquiv
        ((SimplexCategory.lastVertex.app ⦋1⦌).app
          (op ⦋1⦌) deltaOneRightEdge) i = 1 := by
  rw [SimplexCategory.lastVertex_app_objEquiv_apply]
  fin_cases i
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (SimplexCategory.sdSingletonChain ⦋1⦌ 1)).down = 1
    simp
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (fullChain ⦋1⦌)).down = 1
    rw [chainLast_fullChain]
    rfl

/-- The maximal two-simplex flag maps to the top simplex of Delta[2]. -/
example (i : Fin 3) :
    SSet.stdSimplex.objEquiv
        ((SimplexCategory.lastVertex.app ⦋2⦌).app
          (op ⦋2⦌) deltaTwoTopSimplex) i = i := by
  rw [SimplexCategory.lastVertex_app_objEquiv_apply]
  fin_cases i
  · change (SimplexCategory.sdChainLast ⦋2⦌
      (SimplexCategory.sdSingletonChain ⦋2⦌ 0)).down = 0
    simp
  · change (SimplexCategory.sdChainLast ⦋2⦌ firstTwoChain).down = 1
    rw [chainLast_firstTwo]
  · change (SimplexCategory.sdChainLast ⦋2⦌
      (fullChain ⦋2⦌)).down = 2
    rw [chainLast_fullChain]
    rfl

private def intervalVertexOne : (Δ[1] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm 1

private def intervalConstOne : (Δ[1] : SSet.{u}) _⦋1⦌ :=
  SSet.stdSimplex.const 1 1 (op ⦋1⦌)

private theorem intervalConstOne_eq_sigma :
    intervalConstOne.{u} =
      (Δ[1] : SSet.{u}).σ 0 intervalVertexOne.{u} := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

private theorem deltaOneLeftEdge_lastVertex :
    (SSet.lastVertex.app (Δ[1] : SSet.{u})).app (op ⦋1⦌)
        ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app
          (op ⦋1⦌) deltaOneLeftEdge) =
      (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 ⦋1⦌) :
        (Δ[1] : SSet.{u}) _⦋1⦌) := by
  apply SSet.stdSimplex.ext
  intro i
  change SSet.stdSimplex.objEquiv.{u}
      ((SSet.lastVertex.app (Δ[1] : SSet.{u})).app (op ⦋1⦌)
        ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app
          (op ⦋1⦌) deltaOneLeftEdge)) i =
    SSet.stdSimplex.objEquiv.{u}
      (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 ⦋1⦌)) i
  rw [SSet.lastVertex_stdSimplex_apply]
  fin_cases i
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (SimplexCategory.sdSingletonChain ⦋1⦌ 0)).down = 0
    simp
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (fullChain ⦋1⦌)).down = 1
    rw [chainLast_fullChain]
    rfl

private theorem deltaOneRightEdge_lastVertex :
    (SSet.lastVertex.app (Δ[1] : SSet.{u})).app (op ⦋1⦌)
        ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app
          (op ⦋1⦌) deltaOneRightEdge) =
      intervalConstOne.{u} := by
  apply SSet.stdSimplex.ext
  intro i
  change SSet.stdSimplex.objEquiv.{u}
      ((SSet.lastVertex.app (Δ[1] : SSet.{u})).app (op ⦋1⦌)
        ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app
          (op ⦋1⦌) deltaOneRightEdge)) i =
    SSet.stdSimplex.objEquiv.{u} intervalConstOne.{u} i
  rw [SSet.lastVertex_stdSimplex_apply]
  fin_cases i
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (SimplexCategory.sdSingletonChain ⦋1⦌ 1)).down =
        SSet.stdSimplex.objEquiv.{u} intervalConstOne.{u} 0
    rfl
  · change (SimplexCategory.sdChainLast ⦋1⦌
      (fullChain ⦋1⦌)).down =
        SSet.stdSimplex.objEquiv.{u} intervalConstOne.{u} 1
    rw [chainLast_fullChain]
    rfl

end Representables

section SimplicialCircle

private noncomputable def circleDiagram : WalkingParallelPair ⥤ SSet :=
  parallelPair (SSet.stdSimplex.δ 0 : Δ[0] ⟶ Δ[1])
    (SSet.stdSimplex.δ 1)

private noncomputable def circleQuotient : (Δ[1] : SSet) ⟶ SSet.S1 :=
  colimit.ι circleDiagram WalkingParallelPair.one

private def circleSubdivisionEdge
    (e : (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋1⦌) :
    (SSet.sd.obj SSet.S1) _⦋1⦌ :=
  (SSet.sd.map circleQuotient).app (op ⦋1⦌)
    ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app (op ⦋1⦌) e)

private theorem circleSubdivisionEdge_lastVertex
    (e : (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋1⦌) :
    (SSet.lastVertex.app SSet.S1).app (op ⦋1⦌)
        (circleSubdivisionEdge e) =
      circleQuotient.app (op ⦋1⦌)
        ((SSet.lastVertex.app (Δ[1] : SSet)).app (op ⦋1⦌)
          ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app
            (op ⦋1⦌) e)) := by
  let v := (SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app
    (op ⦋1⦌) e
  have h := SSet.lastVertex.naturality circleQuotient
  exact congrArg (fun f => f.app (op ⦋1⦌) v) h

/-- One subdivided circle edge maps to the original loop simplex. -/
example :
    (SSet.lastVertex.app SSet.S1).app (op ⦋1⦌)
        (circleSubdivisionEdge deltaOneLeftEdge) =
      circleQuotient.app (op ⦋1⦌)
        (SSet.stdSimplex.objEquiv.{0}.symm (𝟙 ⦋1⦌)) := by
  rw [circleSubdivisionEdge_lastVertex,
    deltaOneLeftEdge_lastVertex]

/-- The other subdivided circle edge maps to a degenerate identity edge. -/
example :
    (SSet.lastVertex.app SSet.S1).app (op ⦋1⦌)
        (circleSubdivisionEdge deltaOneRightEdge) =
      circleQuotient.app (op ⦋1⦌)
        intervalConstOne.{0} := by
  rw [circleSubdivisionEdge_lastVertex,
    deltaOneRightEdge_lastVertex]

example :
    (circleQuotient.app (op ⦋1⦌) intervalConstOne.{0} :
      SSet.S1 _⦋1⦌) =
      circleQuotient.app (op ⦋1⦌)
        ((Δ[1] : SSet).σ 0 intervalVertexOne.{0}) := by
  rw [intervalConstOne_eq_sigma]

end SimplicialCircle

section NaturalityAndLifts

example :
    (SSet.lastVertex.app (Δ[0] : SSet.{u})).app (op ⦋0⦌)
        (SSet.sdVertexOfVertex
          (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)) =
      SSet.stdSimplex.obj₀Equiv.symm 0 := by
  exact SSet.lastVertex_sdVertexOfVertex _

example :
    (SSet.lastVertex.app (Δ[1] : SSet.{u})).app (op ⦋0⦌)
        (SSet.sdVertexOfVertex
          (SSet.stdSimplex.obj₀Equiv.{u}.symm 1)) =
      SSet.stdSimplex.obj₀Equiv.symm 1 := by
  exact SSet.lastVertex_sdVertexOfVertex _

example :
    (SSet.lastVertex.app (Δ[2] : SSet.{u})).app (op ⦋0⦌)
        (SSet.sdVertexOfVertex
          (SSet.stdSimplex.obj₀Equiv.{u}.symm 2)) =
      SSet.stdSimplex.obj₀Equiv.symm 2 := by
  exact SSet.lastVertex_sdVertexOfVertex _

example {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.sd.map f ≫ SSet.lastVertex.app B =
      SSet.lastVertex.app A ≫ f :=
  SSet.lastVertex.naturality f

example (A : SSet.{u}) : SSet.sdIterLastVertex A 0 = 𝟙 A := by
  simp

example (A : SSet.{u}) (k : ℕ) :
    SSet.sdIterLastVertex A (k + 1) =
      SSet.lastVertex.app ((SSet.sdIter k).obj A) ≫
        SSet.sdIterLastVertex A k := by
  simp

example {A B : SSet.{u}} (f : A ⟶ B) (k : ℕ) :
    (SSet.sdIter k).map f ≫ SSet.sdIterLastVertex B k =
      SSet.sdIterLastVertex A k ≫ f :=
  SSet.sdIterLastVertex_naturality f k

example {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) (k : ℕ) :
    (SSet.sdIter k).map f ≫ SSet.sdIterLastVertex B k ≫ g =
      SSet.sdIterLastVertex A k ≫ f ≫ g :=
  SSet.sdIterLastVertex_naturality_assoc f k g

example {A B : SSet.{u}} (f : A ⟶ B) (x : A _⦋0⦌) :
    (SSet.sd.map f).app (op ⦋0⦌) (SSet.sdVertexOfVertex x) =
      SSet.sdVertexOfVertex (f.app (op ⦋0⦌) x) := by
  simp

example (A : SSet.{u}) (x : A _⦋0⦌) :
    (SSet.lastVertex.app A).app (op ⦋0⦌)
      (SSet.sdVertexOfVertex x) = x :=
  SSet.lastVertex_sdVertexOfVertex x

example (A : SSet.{1}) (x : A _⦋0⦌) :
    (SSet.lastVertex.app A).app (op ⦋0⦌)
      (SSet.sdVertexOfVertex x) = x :=
  SSet.lastVertex_sdVertexOfVertex x

example (A : SSet.{0}) (x : A _⦋0⦌) :
    (SSet.lastVertex.app A).app (op ⦋0⦌)
      (SSet.sdVertexOfVertex x) = x :=
  SSet.lastVertex_sdVertexOfVertex x

end NaturalityAndLifts

#print axioms SimplexCategory.lastVertex
#print axioms SSet.lastVertex
#print axioms SSet.lastVertex_stdSimplex_apply
#print axioms SSet.lastVertex_sdVertexOfVertex

end LastVertexTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.Subdivision

end
