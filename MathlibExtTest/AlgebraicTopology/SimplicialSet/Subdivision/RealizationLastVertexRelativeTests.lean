/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.RealizationLastVertexRelative

import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial Topology MonoidalCategory
open scoped Simplicial unitInterval

universe u

namespace SSet.RealizationLastVertexRelativeTests

private noncomputable def geometricEndpoint (n k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom

private noncomputable def lastVertexEndpoint (n k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  SSet.toTop.map (SSet.sdIterLastVertex (Δ[n] : SSet.{u}) k)

section PublicSurface

example (X : SSet.{u}) (k : ℕ) : (SSet.sdIter k).obj X ⟶ X :=
  SSet.sdIterLastVertex X k

example (n k : ℕ) : TopCat.Homotopy
    (geometricEndpoint.{u} n k) (lastVertexEndpoint.{u} n k) :=
  SSet.toTopSdIterLastVertexHomotopy n k

example (n k : ℕ) (i : Fin (n + 2)) (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    SSet.toTopSdIterLastVertexHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x) =
      SSet.toTop.map (SSet.stdSimplex.δ i)
        (SSet.toTopSdIterLastVertexHomotopy n k (t, x)) :=
  SSet.toTopSdIterLastVertexHomotopy_face n k i t x

example {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ) :
    SSet.Homotopy
      (sSetTopAdj.homEquiv _ _
        ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b))
      (SSet.sdIterLastVertex (Δ[n] : SSet.{u}) k ≫
        sSetTopAdj.homEquiv _ _ b) :=
  SSet.geometricSubdivisionAdjunctRelativeHomotopy b k

example (X : SSet.{u}) : SSet.sdIterLastVertex X 0 = 𝟙 X :=
  SSet.sdIterLastVertex_zero X

example (X : SSet.{u}) (k : ℕ) :
    SSet.sdIterLastVertex X (k + 1) =
      SSet.lastVertex.app ((SSet.sdIter k).obj X) ≫
        SSet.sdIterLastVertex X k :=
  SSet.sdIterLastVertex_succ X k

end PublicSurface

section RelativeControls

private def homotopyEdge
    {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g)
    (x : A _⦋0⦌) : B.Edge (f.app _ x) (g.app _ x) :=
  let h := H.toSimplicialObjectHomotopy
  SSet.Edge.mk (h.h 0 x)
    (by rw [← h.h_last_comp_δ_last 0]; rfl)
    (by rw [← SimplicialObject.Homotopy.h_zero_comp_δ_zero]; rfl)

example {X : TopCat.{u}} {n : ℕ}
    (b : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ X) (k : ℕ)
    (x : ((SSet.sdIter k).obj (Δ[n] : SSet.{u})) _⦋0⦌) :
    (TopCat.toSSet.obj X).Edge
      ((sSetTopAdj.homEquiv _ _
        ((SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫ b)).app _ x)
      ((SSet.sdIterLastVertex (Δ[n] : SSet.{u}) k ≫
        sSetTopAdj.homEquiv _ _ b).app _ x) :=
  homotopyEdge (SSet.geometricSubdivisionAdjunctRelativeHomotopy b k) x

example {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y)
    (t : unitInterval)
    (x : SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) :
    b (SSet.toTopSdIterLastVertexHomotopy (n + 1) k
        (t, SSet.toTop.map
          ((SSet.sdIter k).map (SSet.stdSimplex.δ i)) x)) = y := by
  rw [SSet.toTopSdIterLastVertexHomotopy_face]
  exact ConcreteCategory.congr_hom hb
    (SSet.toTopSdIterLastVertexHomotopy n k (t, x))

private theorem sSetTopAdj_homEquiv_const
    (K : SSet.{u}) (X : TopCat.{u}) (y : X) :
    sSetTopAdj.homEquiv K X
        (TopCat.const (X := SSet.toTop.obj K) y) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y) := by
  rw [Adjunction.homEquiv_unit, TopCat.toSSet_map_const,
    SSet.comp_const]

private theorem geometricAdjunct_face_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y) :
    (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        sSetTopAdj.homEquiv _ _
          ((SSet.toTopSdIterIso (Δ[n + 1] : SSet.{u}) k).hom ≫ b) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y) := by
  let _ : Mono (SSet.stdSimplex.{u}.map (SimplexCategory.δ i)) := by
    change Mono (SSet.stdSimplex.δ i)
    infer_instance
  rw [← sSetTopAdj.homEquiv_naturality_left]
  rw [reassoc_of% SSet.toTopSdIterIso_hom_naturality_of_mono
    (SSet.stdSimplex.δ i) k]
  rw [hb]
  have hconst : (SSet.toTopSdIterIso (Δ[n] : SSet.{u}) k).hom ≫
      TopCat.const y =
      TopCat.const
        (X := SSet.toTop.obj ((SSet.sdIter k).obj (Δ[n] : SSet.{u}))) y := by
    apply TopCat.ext
    intro z
    rfl
  rw [hconst]
  exact sSetTopAdj_homEquiv_const _ _ _

private theorem lastVertexAdjunct_face_constant
    {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y) :
    (SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        (SSet.sdIterLastVertex (Δ[n + 1] : SSet.{u}) k ≫
          sSetTopAdj.homEquiv _ _ b) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y) := by
  rw [← Category.assoc]
  have hnat := congrArg (fun f => f ≫ sSetTopAdj.homEquiv _ _ b)
    (SSet.sdIterLastVertex_naturality (SSet.stdSimplex.δ i) k)
  rw [hnat]
  rw [Category.assoc, ← sSetTopAdj.homEquiv_naturality_left]
  rw [hb, sSetTopAdj_homEquiv_const]
  exact SSet.comp_const _ _

example {X : TopCat.{u}} (n k : ℕ) (i : Fin (n + 2))
    (b : SSet.toTop.obj (Δ[n + 1] : SSet.{u}) ⟶ X) (y : X)
    (hb : SSet.toTop.map (SSet.stdSimplex.δ i) ≫ b = TopCat.const y) :
    ((SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        sSetTopAdj.homEquiv _ _
          ((SSet.toTopSdIterIso (Δ[n + 1] : SSet.{u}) k).hom ≫ b) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y)) ∧
    ((SSet.sdIter k).map (SSet.stdSimplex.δ i) ≫
        (SSet.sdIterLastVertex (Δ[n + 1] : SSet.{u}) k ≫
          sSetTopAdj.homEquiv _ _ b) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm y)) :=
  ⟨geometricAdjunct_face_constant n k i b y hb,
    lastVertexAdjunct_face_constant n k i b y hb⟩

end RelativeControls

section UniverseControls

example (n k : ℕ) : Nonempty <| TopCat.Homotopy
    (geometricEndpoint.{1} n k) (lastVertexEndpoint.{1} n k) :=
  ⟨SSet.toTopSdIterLastVertexHomotopy n k⟩

example (n k : ℕ) : Nonempty <| TopCat.Homotopy
    (geometricEndpoint.{0} n k) (lastVertexEndpoint.{0} n k) :=
  ⟨SSet.toTopSdIterLastVertexHomotopy n k⟩

example (k : ℕ) : Nonempty <| TopCat.Homotopy
    (geometricEndpoint.{u} 0 k) (lastVertexEndpoint.{u} 0 k) :=
  ⟨SSet.toTopSdIterLastVertexHomotopy 0 k⟩

end UniverseControls

section MidpointFalsifier

private abbrev intervalFullFace :
    PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin 2)) where
  finset := Finset.univ
  nonempty := ⟨ULift.up 0, Finset.mem_univ _⟩
  comparable _ _ := le_total _ _

private abbrev intervalFullFaceSimplex :
    (SimplexCategory.sd.{u}.obj ⦋1⦌) _⦋0⦌ :=
  ComposableArrows.mk₀ intervalFullFace

private noncomputable def intervalTopSimplex : (Δ[1] : SSet.{u}).N :=
  SSet.N.mk (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) (by
    rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono]
    change Mono (𝟙 ⦋1⦌)
    infer_instance)

private def intervalFullFaceVertex :
    (SSet.sd.obj (Δ[1] : SSet.{u})) _⦋0⦌ :=
  (SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app _ intervalFullFaceSimplex

private noncomputable def intervalFullFacePoint :
    SSet.toTop.obj (SSet.sd.obj (Δ[1] : SSet.{u})) :=
  SSet.toTop.map
    (SSet.sd.map (SSet.yonedaEquiv.symm intervalTopSimplex.simplex))
    (SSet.toTop.map (SSet.yonedaEquiv.symm intervalFullFaceVertex)
      ((SimplexCategory.toTopHomeo.{u} ⦋0⦌).symm
        (Convexity.StdSimplex.single 0)))

private theorem intervalTop_yoneda :
    SSet.yonedaEquiv.symm intervalTopSimplex.{u}.simplex =
      𝟙 (Δ[1] : SSet.{u}) :=
  SSet.yonedaEquiv.symm_apply_apply _

private theorem intervalPoint_eq_realizedVertex :
    intervalFullFacePoint.{u} = SSet.realizedVertex intervalFullFaceVertex.{u} := by
  let z := SSet.toTop.map (SSet.yonedaEquiv.symm intervalFullFaceVertex.{u})
    ((SimplexCategory.toTopHomeo.{u} ⦋0⦌).symm
      (Convexity.StdSimplex.single 0))
  have hsd := congrArg SSet.sd.map intervalTop_yoneda.{u}
  have htop := congrArg SSet.toTop.map hsd
  have houter := ConcreteCategory.congr_hom htop z
  have hsdId : SSet.sd.map (𝟙 (Δ[1] : SSet.{u})) =
      𝟙 (SSet.sd.obj (Δ[1] : SSet.{u})) := SSet.sd.map_id _
  have hinner := ConcreteCategory.congr_hom (congrArg SSet.toTop.map hsdId) z
  have hmapId : SSet.toTop.map (𝟙 (SSet.sd.obj (Δ[1] : SSet.{u}))) =
      𝟙 (SSet.toTop.obj (SSet.sd.obj (Δ[1] : SSet.{u}))) := SSet.toTop.map_id _
  calc
    intervalFullFacePoint.{u} =
        SSet.toTop.map (SSet.sd.map
          (SSet.yonedaEquiv.symm intervalTopSimplex.{u}.simplex)) z := rfl
    _ = SSet.toTop.map (SSet.sd.map (𝟙 (Δ[1] : SSet.{u}))) z := houter
    _ = SSet.toTop.map (𝟙 (SSet.sd.obj (Δ[1] : SSet.{u}))) z := hinner
    _ = z := ConcreteCategory.congr_hom hmapId z
    _ = SSet.realizedVertex intervalFullFaceVertex.{u} := by
      unfold z SSet.realizedVertex
      apply congrArg
      exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem interval_geometric_barycentric :
    (⦋1⦌.toTopHomeo.{u})
        (geometricEndpoint 1 1 intervalFullFacePoint.{u}) =
      SimplexCategory.sdCellMap intervalFullFaceSimplex.{u}
        (Convexity.StdSimplex.single 0) := by
  have h := SSet.toTopSdIso_hom_cell_apply
    (Δ[1] : SSet.{u}) intervalTopSimplex.{u}
      intervalFullFaceSimplex.{u} (Convexity.StdSimplex.single 0)
  dsimp [intervalTopSimplex, SSet.N.mk] at h
  calc
    (⦋1⦌.toTopHomeo.{u})
        (geometricEndpoint 1 1 intervalFullFacePoint.{u}) =
      (⦋1⦌.toTopHomeo.{u})
        (geometricEndpoint 1 1
          (SSet.toTop.map (SSet.sd.map
              (SSet.yonedaEquiv.symm intervalTopSimplex.{u}.simplex))
            (SSet.toTop.map
              (SSet.yonedaEquiv.symm intervalFullFaceVertex.{u})
              ((SimplexCategory.toTopHomeo.{u} ⦋0⦌).symm
                (Convexity.StdSimplex.single 0))))) := rfl
    _ = (⦋1⦌.toTopHomeo.{u})
        (SSet.toTop.map
          (SSet.yonedaEquiv.symm intervalTopSimplex.{u}.simplex)
          ((SimplexCategory.toTopHomeo.{u} ⦋1⦌).symm
            (SimplexCategory.sdCellMap intervalFullFaceSimplex.{u}
              (Convexity.StdSimplex.single 0)))) :=
      congrArg (⦋1⦌.toTopHomeo.{u}) h
    _ = _ := by
      rw [intervalTop_yoneda]
      let z := (SimplexCategory.toTopHomeo.{u} ⦋1⦌).symm
        (SimplexCategory.sdCellMap intervalFullFaceSimplex.{u}
          (Convexity.StdSimplex.single 0))
      have hid : SSet.toTop.map (𝟙 (Δ[1] : SSet.{u})) =
          𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u})) := SSet.toTop.map_id _
      have happ := ConcreteCategory.congr_hom hid z
      calc
        (⦋1⦌.toTopHomeo.{u})
            (SSet.toTop.map (𝟙 (Δ[1] : SSet.{u})) z) =
          (⦋1⦌.toTopHomeo.{u}) z := congrArg _ happ
        _ = _ := (⦋1⦌.toTopHomeo.{u}).apply_symm_apply _

private theorem intervalFullFace_last :
    SimplexCategory.sdChainLast ⦋1⦌ intervalFullFace.{u} =
      ULift.up (1 : Fin 2) := by
  unfold SimplexCategory.sdChainLast
  apply le_antisymm
  · apply Finset.max'_le
    intro a _
    rcases a with ⟨a⟩
    fin_cases a <;> decide
  · apply Finset.le_max'
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem interval_last_barycentric :
    (⦋1⦌.toTopHomeo.{u})
        (lastVertexEndpoint 1 1 intervalFullFacePoint.{u}) =
      (Convexity.StdSimplex.single (1 : Fin 2) :
        Convexity.StdSimplex ℝ (Fin 2)) := by
  rw [intervalPoint_eq_realizedVertex]
  change (⦋1⦌.toTopHomeo.{u})
      (SSet.toTop.map (SSet.lastVertex.app (Δ[1] : SSet.{u}))
        (SSet.realizedVertex intervalFullFaceVertex.{u})) = _
  rw [← SSet.realizedVertex_naturality]
  rw [show (SSet.lastVertex.app (Δ[1] : SSet.{u})).app _
      intervalFullFaceVertex.{u} =
        SSet.stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2) by
    simpa [intervalFullFaceVertex, intervalFullFaceSimplex,
      intervalFullFace_last] using
      SSet.lastVertex_stdSimplex_vertex ⦋1⦌ intervalFullFace.{u}]
  let f : ⦋0⦌ ⟶ ⦋1⦌ := SimplexCategory.const ⦋0⦌ ⦋1⦌ 1
  unfold SSet.realizedVertex
  change (⦋1⦌.toTopHomeo.{u})
      (SSet.toTop.map (SSet.stdSimplex.map f) default) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (⦋0⦌.toTopHomeo default)
    (Convexity.StdSimplex.single 0), Convexity.StdSimplex.map_single]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem interval_weight_zero :
    (SimplexCategory.sdCellMap intervalFullFaceSimplex.{u}
      (Convexity.StdSimplex.single 0)).weights (0 : Fin 2) =
      (1 / 2 : ℝ) := by
  classical
  let _ : Fintype
      ↑((CategoryTheory.forget₂ FinPartOrd PartOrd).obj
        ((CategoryTheory.forget₂ NonemptyFinLinOrd FinPartOrd).obj
          (SimplexCategory.skeletalFunctor.obj ⦋1⦌))) :=
    NonemptyFinLinOrd.fintype (SimplexCategory.skeletalFunctor.obj ⦋1⦌)
  rw [SimplexCategory.sdCellMap_weights_apply]
  simp [Convexity.StdSimplex.single, Finsupp.single_apply,
    Convexity.StdSimplex.weights_subBarycenter]
  rw [Finset.card_image_of_injective _ ULift.down_injective]
  norm_num [SimplexCategory.skeletalFunctor]

example : geometricEndpoint.{u} 1 1 intervalFullFacePoint.{u} ≠
    lastVertexEndpoint.{u} 1 1 intervalFullFacePoint.{u} := by
  intro h
  have hweight := congrArg
    (fun z : SSet.toTop.obj (Δ[1] : SSet.{u}) =>
      ((⦋1⦌.toTopHomeo.{u}) z).weights (0 : Fin 2)) h
  rw [interval_geometric_barycentric, interval_last_barycentric,
    interval_weight_zero] at hweight
  norm_num at hweight

end MidpointFalsifier

/-! Implementation helpers remain private and stronger conclusions absent. -/

/-- error: Unknown constant `SSet.geometricEndpoint` -/
#guard_msgs (error) in
#check SSet.geometricEndpoint

/-- error: Unknown constant `SSet.subordinateCoverWeakEquivalence` -/
#guard_msgs (error) in
#check SSet.subordinateCoverWeakEquivalence

/-- error: Unknown constant `SSet.geometricSubdivisionAdjunct_eq_lastVertex` -/
#guard_msgs (error) in
#check SSet.geometricSubdivisionAdjunct_eq_lastVertex

#check SSet.sdIterLastVertex
#check SSet.sdIterLastVertex_zero
#check SSet.sdIterLastVertex_succ
#check SSet.sdIterLastVertex_naturality
#check SSet.sdIterLastVertex_naturality_assoc
#check SSet.toTopSdIterLastVertexHomotopy
#check SSet.toTopSdIterLastVertexHomotopy_face
#check SSet.geometricSubdivisionAdjunctRelativeHomotopy

#print axioms SSet.sdIterLastVertex
#print axioms SSet.sdIterLastVertex_zero
#print axioms SSet.sdIterLastVertex_succ
#print axioms SSet.sdIterLastVertex_naturality
#print axioms SSet.toTopSdIterLastVertexHomotopy
#print axioms SSet.toTopSdIterLastVertexHomotopy_face
#print axioms SSet.geometricSubdivisionAdjunctRelativeHomotopy

end SSet.RealizationLastVertexRelativeTests

end
