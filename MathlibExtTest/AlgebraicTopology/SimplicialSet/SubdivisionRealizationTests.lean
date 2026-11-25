/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Realization
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Tests for realization of nonsingular subdivision

Public-only consumers for the one-step and iterated realization isomorphisms,
their naturality and Arrow forms, and concrete low-dimensional affine cells.
-/

@[expose] public section

universe u

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionRealizationTests

section PublicAPI

noncomputable example (X : SSet.{0}) [X.Nonsingular] :
    SSet.toTop.obj (SSet.sd.obj X) ≅ SSet.toTop.obj X :=
  SSet.toTopSdIso X

example (X : SSet.{0}) [X.Nonsingular]
    (x : X.N) {d : ℕ}
    (σ : (SimplexCategory.sd.{0}.obj ⦋x.dim⦌) _⦋d⦌) :
    (SSet.stdSimplex.toTopIso ⦋d⦌).inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (SSet.toTopSdIso X).hom =
      TopCat.ofHom (SimplexCategory.sdCellMap σ) ≫
        (SSet.stdSimplex.toTopIso ⦋x.dim⦌).inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex) :=
  SSet.toTopSdIso_hom_cell X x σ

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y)
    (hf : ∀ {n : ℕ} (x : X _⦋n⦌),
      x ∈ X.nonDegenerate n → f.app _ x ∈ Y.nonDegenerate n) :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIso_hom_naturality f hf

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIso_hom_naturality_of_mono f

noncomputable example (X : SSet.{0}) [X.Nonsingular] (k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj X) ≅ SSet.toTop.obj X :=
  SSet.toTopSdIterIso X k

example (X : SSet.{0}) [X.Nonsingular] :
    SSet.toTopSdIterIso X 0 = Iso.refl _ :=
  SSet.toTopSdIterIso_zero X

example (X : SSet.{0}) [X.Nonsingular] (k : ℕ) :
    SSet.toTopSdIterIso X (k + 1) =
      SSet.toTopSdIso ((SSet.sdIter k).obj X) ≪≫
        SSet.toTopSdIterIso X k :=
  SSet.toTopSdIterIso_succ X k

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    SSet.toTop.map ((SSet.sdIter k).map f) ≫
        (SSet.toTopSdIterIso Y k).hom =
      (SSet.toTopSdIterIso X k).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIterIso_hom_naturality_of_mono f k

noncomputable example {X Y : SSet.{0}}
    [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    Arrow.mk (SSet.toTop.map ((SSet.sdIter k).map f)) ≅
      Arrow.mk (SSet.toTop.map f) :=
  SSet.toTopSdIterArrowIso f k

end PublicAPI

section AllUniverseAPI

noncomputable example (X : SSet.{u}) [X.Nonsingular] :
    SSet.toTop.obj (SSet.sd.obj X) ≅ SSet.toTop.obj X :=
  SSet.toTopSdIso X

example (X : SSet.{u}) [X.Nonsingular]
    (x : X.N) {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (SSet.toTopSdIso X).hom
        (SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex))
          (SSet.toTop.map
            (SSet.yonedaEquiv.symm
              ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ))
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex)
        ((SimplexCategory.toTopHomeo.{u} ⦋x.dim⦌).symm
          (SimplexCategory.sdCellMap σ q)) :=
  SSet.toTopSdIso_hom_cell_apply X x σ q

example {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y)
    (hf : ∀ {n : ℕ} (x : X _⦋n⦌),
      x ∈ X.nonDegenerate n → f.app _ x ∈ Y.nonDegenerate n) :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIso_hom_naturality f hf

example {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIso_hom_naturality_of_mono f

noncomputable example (X : SSet.{u}) [X.Nonsingular] (k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj X) ≅ SSet.toTop.obj X :=
  SSet.toTopSdIterIso X k

example (X : SSet.{u}) [X.Nonsingular] :
    SSet.toTopSdIterIso X 0 = Iso.refl _ :=
  SSet.toTopSdIterIso_zero X

example (X : SSet.{u}) [X.Nonsingular] (k : ℕ) :
    SSet.toTopSdIterIso X (k + 1) =
      SSet.toTopSdIso ((SSet.sdIter k).obj X) ≪≫
        SSet.toTopSdIterIso X k :=
  SSet.toTopSdIterIso_succ X k

example {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    SSet.toTop.map ((SSet.sdIter k).map f) ≫
        (SSet.toTopSdIterIso Y k).hom =
      (SSet.toTopSdIterIso X k).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIterIso_hom_naturality_of_mono f k

noncomputable example {X Y : SSet.{u}}
    [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    Arrow.mk (SSet.toTop.map ((SSet.sdIter k).map f)) ≅
      Arrow.mk (SSet.toTop.map f) :=
  SSet.toTopSdIterArrowIso f k

noncomputable example :
    SSet.toTop.obj (SSet.sd.obj (Δ[0] : SSet.{u})) ≅
      SSet.toTop.obj (Δ[0] : SSet.{u}) :=
  SSet.toTopSdIso (Δ[0] : SSet.{u})

noncomputable example :
    SSet.toTop.obj (SSet.sd.obj (Δ[1] : SSet.{u})) ≅
      SSet.toTop.obj (Δ[1] : SSet.{u}) :=
  SSet.toTopSdIso (Δ[1] : SSet.{u})

noncomputable example :
    SSet.toTop.obj (SSet.sd.obj (Δ[2] : SSet.{u})) ≅
      SSet.toTop.obj (Δ[2] : SSet.{u}) :=
  SSet.toTopSdIso (Δ[2] : SSet.{u})

noncomputable example :
    SSet.toTop.obj
        (SSet.sd.obj
          ((⊥ : SSet.Subcomplex (Δ[0] : SSet.{u})) : SSet.{u})) ≅
      SSet.toTop.obj
        ((⊥ : SSet.Subcomplex (Δ[0] : SSet.{u})) : SSet.{u}) :=
  SSet.toTopSdIso
    ((⊥ : SSet.Subcomplex (Δ[0] : SSet.{u})) : SSet.{u})

example {X Y Z : SSet.{u}}
    [X.Nonsingular] [Y.Nonsingular] [Z.Nonsingular]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] :
    SSet.toTop.map (SSet.sd.map (f ≫ g)) ≫
        (SSet.toTopSdIso Z).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map (f ≫ g) :=
  SSet.toTopSdIso_hom_naturality_of_mono (f ≫ g)

end AllUniverseAPI

section TestData

private def topN (n : ℕ) : (Δ[n] : SSet.{0}).N :=
  SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
    (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate n)

private def faceOnly :
    PartialOrder.NonemptyFiniteChains (ULift (Fin 1)) where
  finset := {ULift.up 0}
  comparable a b := le_total a b

private def faceZero :
    PartialOrder.NonemptyFiniteChains (ULift (Fin 2)) where
  finset := {ULift.up 0}
  comparable a b := le_total a b

private def faceFull :
    PartialOrder.NonemptyFiniteChains (ULift (Fin 2)) where
  finset := {ULift.up 0, ULift.up 1}
  comparable a b := le_total a b

private theorem faceZero_le_faceFull : faceZero ≤ faceFull := by
  intro x hx
  simp only [faceZero, Finset.mem_singleton] at hx
  subst x
  simp [faceFull]

private noncomputable def sdVertexOnly :
    (SimplexCategory.sd.{0}.obj ⦋0⦌) _⦋0⦌ :=
  ComposableArrows.mk₀ faceOnly

private noncomputable def sdVertexFull :
    (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋0⦌ :=
  ComposableArrows.mk₀ faceFull

private noncomputable def sdEdgeZeroFull :
    (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE faceZero_le_faceFull)

private noncomputable def sdEdgeRepeated :
    (SimplexCategory.sd.{0}.obj ⦋1⦌) _⦋1⦌ :=
  (SimplexCategory.sd.obj ⦋1⦌).map
    (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op sdVertexFull

private noncomputable def positiveWeights :
    Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.duple 0 1
    (s := (3 / 4 : ℝ)) (t := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)

private theorem positiveWeights_zero :
    positiveWeights.weights 0 = (3 : ℝ) / 4 := by
  simp [positiveWeights, Convexity.StdSimplex.weights_duple]

private theorem positiveWeights_one :
    positiveWeights.weights 1 = (1 : ℝ) / 4 := by
  simp [positiveWeights, Convexity.StdSimplex.weights_duple]

private theorem positiveWeights_pos (i : Fin 2) :
    0 < positiveWeights.weights i := by
  fin_cases i
  · change 0 < positiveWeights.weights (0 : Fin 2)
    rw [positiveWeights_zero]
    norm_num
  · change 0 < positiveWeights.weights (1 : Fin 2)
    rw [positiveWeights_one]
    norm_num

end TestData

section CellSemantics

example :
    (SimplexCategory.sdCellMap sdVertexOnly
      (Convexity.StdSimplex.single (R := ℝ) 0)).weights 0 = 1 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_one]
  change (Convexity.StdSimplex.single (R := ℝ) 0).weights 0 *
    (Convexity.StdSimplex.subBarycenter
      ({0} : Finset (Fin 1)) (by simp)).weights 0 = 1
  simp

example :
    (SimplexCategory.sdCellMap sdEdgeZeroFull positiveWeights).weights 0 =
      (7 : ℝ) / 8 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change positiveWeights.weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0} : Finset (Fin 2)) (by simp)).weights 0 +
      positiveWeights.weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 0 = _
  rw [positiveWeights_zero, positiveWeights_one]
  simp [Convexity.StdSimplex.weights_subBarycenter]
  norm_num

example :
    (SimplexCategory.sdCellMap sdEdgeZeroFull positiveWeights).weights 1 =
      (1 : ℝ) / 8 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change positiveWeights.weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0} : Finset (Fin 2)) (by simp)).weights 1 +
      positiveWeights.weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 1 = _
  rw [positiveWeights_zero, positiveWeights_one]
  simp [Convexity.StdSimplex.weights_subBarycenter]
  norm_num

example :
    (SimplexCategory.sdCellMap sdEdgeZeroFull
      (Convexity.StdSimplex.single (R := ℝ) 0)).weights 0 = 1 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change (Convexity.StdSimplex.single (R := ℝ) 0).weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0} : Finset (Fin 2)) (by simp)).weights 0 +
      (Convexity.StdSimplex.single (R := ℝ) 0).weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 0 = _
  simp [Convexity.StdSimplex.weights_subBarycenter]

example :
    (SimplexCategory.sdCellMap sdEdgeZeroFull
      (Convexity.StdSimplex.single (R := ℝ) 0)).weights 1 = 0 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change (Convexity.StdSimplex.single (R := ℝ) 0).weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0} : Finset (Fin 2)) (by simp)).weights 1 +
      (Convexity.StdSimplex.single (R := ℝ) 0).weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 1 = _
  simp [Convexity.StdSimplex.weights_subBarycenter]

example :
    (SimplexCategory.sdCellMap sdEdgeZeroFull
      (Convexity.StdSimplex.single (R := ℝ) 1)).weights 0 = (1 : ℝ) / 2 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change (Convexity.StdSimplex.single (R := ℝ) 1).weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0} : Finset (Fin 2)) (by simp)).weights 0 +
      (Convexity.StdSimplex.single (R := ℝ) 1).weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 0 = _
  simp [Convexity.StdSimplex.weights_subBarycenter]

example :
    (SimplexCategory.sdCellMap sdEdgeZeroFull
      (Convexity.StdSimplex.single (R := ℝ) 1)).weights 1 = (1 : ℝ) / 2 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change (Convexity.StdSimplex.single (R := ℝ) 1).weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0} : Finset (Fin 2)) (by simp)).weights 1 +
      (Convexity.StdSimplex.single (R := ℝ) 1).weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 1 = _
  simp [Convexity.StdSimplex.weights_subBarycenter]

example :
    (SimplexCategory.sdCellMap sdEdgeRepeated positiveWeights).weights 0 =
      (1 : ℝ) / 2 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change positiveWeights.weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 0 +
      positiveWeights.weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 0 = _
  rw [positiveWeights_zero, positiveWeights_one]
  simp [Convexity.StdSimplex.weights_subBarycenter]
  norm_num

example :
    (SimplexCategory.sdCellMap sdEdgeRepeated positiveWeights).weights 1 =
      (1 : ℝ) / 2 := by
  rw [SimplexCategory.sdCellMap_weights_apply, Fin.sum_univ_two]
  change positiveWeights.weights 0 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 1 +
      positiveWeights.weights 1 *
        (Convexity.StdSimplex.subBarycenter
          ({0, 1} : Finset (Fin 2)) (by simp)).weights 1 = _
  rw [positiveWeights_zero, positiveWeights_one]
  simp [Convexity.StdSimplex.weights_subBarycenter]
  norm_num

private theorem cellLawAt (X : SSet.{0}) [X.Nonsingular]
    (x : X.N) {d : ℕ}
    (σ : (SimplexCategory.sd.{0}.obj ⦋x.dim⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    ((SSet.stdSimplex.toTopIso ⦋d⦌).inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (SSet.toTopSdIso X).hom) q =
      (TopCat.ofHom (SimplexCategory.sdCellMap σ) ≫
        (SSet.stdSimplex.toTopIso ⦋x.dim⦌).inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex)) q :=
  ConcreteCategory.congr_hom (SSet.toTopSdIso_hom_cell X x σ) q

example :
    ((SSet.stdSimplex.toTopIso ⦋0⦌).inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋0⦌).app _ sdVertexOnly)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm (topN 0).simplex)) ≫
        (SSet.toTopSdIso (Δ[0] : SSet.{0})).hom)
          (Convexity.StdSimplex.single (R := ℝ) 0) =
      (TopCat.ofHom (SimplexCategory.sdCellMap sdVertexOnly) ≫
        (SSet.stdSimplex.toTopIso ⦋0⦌).inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm (topN 0).simplex))
          (Convexity.StdSimplex.single (R := ℝ) 0) := by
  exact cellLawAt (Δ[0] : SSet.{0}) (topN 0) sdVertexOnly
    (Convexity.StdSimplex.single (R := ℝ) 0)

example :
    ((SSet.stdSimplex.toTopIso ⦋1⦌).inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app _ sdEdgeZeroFull)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm (topN 1).simplex)) ≫
        (SSet.toTopSdIso (Δ[1] : SSet.{0})).hom) positiveWeights =
      (TopCat.ofHom (SimplexCategory.sdCellMap sdEdgeZeroFull) ≫
        (SSet.stdSimplex.toTopIso ⦋1⦌).inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm (topN 1).simplex))
          positiveWeights := by
  exact cellLawAt (Δ[1] : SSet.{0}) (topN 1)
    sdEdgeZeroFull positiveWeights

example :
    ((SSet.stdSimplex.toTopIso ⦋1⦌).inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋1⦌).app _ sdEdgeRepeated)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm (topN 1).simplex)) ≫
        (SSet.toTopSdIso (Δ[1] : SSet.{0})).hom) positiveWeights =
      (TopCat.ofHom (SimplexCategory.sdCellMap sdEdgeRepeated) ≫
        (SSet.stdSimplex.toTopIso ⦋1⦌).inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm (topN 1).simplex))
          positiveWeights := by
  exact cellLawAt (Δ[1] : SSet.{0}) (topN 1)
    sdEdgeRepeated positiveWeights

example :
    (SSet.toTopSdIso (Δ[0] : SSet.{0})).hom ≫
        (SSet.toTopSdIso (Δ[0] : SSet.{0})).inv = 𝟙 _ :=
  (SSet.toTopSdIso (Δ[0] : SSet.{0})).hom_inv_id

example :
    (SSet.toTopSdIso (Δ[0] : SSet.{0})).inv ≫
        (SSet.toTopSdIso (Δ[0] : SSet.{0})).hom = 𝟙 _ :=
  (SSet.toTopSdIso (Δ[0] : SSet.{0})).inv_hom_id

end CellSemantics

section NaturalityAndIteration

example (X : SSet.{0}) [X.Nonsingular] :
    SSet.toTop.map (SSet.sd.map (𝟙 X)) ≫ (SSet.toTopSdIso X).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map (𝟙 X) :=
  SSet.toTopSdIso_hom_naturality (𝟙 X) (by
    intro n x hx
    simpa using hx)

private def simplexFaceIncl :
    (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2)) :
      SSet.{0}) ⟶ (Δ[1] : SSet.{0}) :=
  (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2))).ι

private instance : Mono simplexFaceIncl := by
  unfold simplexFaceIncl
  infer_instance

example :
    SSet.toTop.map (SSet.sd.map simplexFaceIncl) ≫
        (SSet.toTopSdIso (Δ[1] : SSet.{0})).hom =
      (SSet.toTopSdIso
          (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2)) :
            SSet.{0})).hom ≫
        SSet.toTop.map simplexFaceIncl :=
  SSet.toTopSdIso_hom_naturality_of_mono simplexFaceIncl

example (X : SSet.{0}) [X.Nonsingular] :
    SSet.toTopSdIterIso X 1 = SSet.toTopSdIso X := by
  simp

example (X : SSet.{0}) [X.Nonsingular] :
    SSet.toTopSdIterIso X 2 =
      SSet.toTopSdIso (SSet.sd.obj X) ≪≫ SSet.toTopSdIso X := by
  simp

example (k : ℕ) :
    SSet.toTop.map ((SSet.sdIter k).map simplexFaceIncl) ≫
        (SSet.toTopSdIterIso (Δ[1] : SSet.{0}) k).hom =
      (SSet.toTopSdIterIso
          (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2)) :
            SSet.{0}) k).hom ≫
        SSet.toTop.map simplexFaceIncl :=
  SSet.toTopSdIterIso_hom_naturality_of_mono simplexFaceIncl k

example :
    SSet.toTop.map ((SSet.sdIter 0).map simplexFaceIncl) ≫
        (SSet.toTopSdIterIso (Δ[1] : SSet.{0}) 0).hom =
      (SSet.toTopSdIterIso
          (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2)) :
            SSet.{0}) 0).hom ≫
        SSet.toTop.map simplexFaceIncl :=
  SSet.toTopSdIterIso_hom_naturality_of_mono simplexFaceIncl 0

example :
    SSet.toTop.map ((SSet.sdIter 1).map simplexFaceIncl) ≫
        (SSet.toTopSdIterIso (Δ[1] : SSet.{0}) 1).hom =
      (SSet.toTopSdIterIso
          (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2)) :
            SSet.{0}) 1).hom ≫
        SSet.toTop.map simplexFaceIncl :=
  SSet.toTopSdIterIso_hom_naturality_of_mono simplexFaceIncl 1

example :
    SSet.toTop.map ((SSet.sdIter 2).map simplexFaceIncl) ≫
        (SSet.toTopSdIterIso (Δ[1] : SSet.{0}) 2).hom =
      (SSet.toTopSdIterIso
          (SSet.stdSimplex.face.{0} (n := 1) ({0} : Finset (Fin 2)) :
            SSet.{0}) 2).hom ≫
        SSet.toTop.map simplexFaceIncl :=
  SSet.toTopSdIterIso_hom_naturality_of_mono simplexFaceIncl 2

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    (SSet.toTopSdIterArrowIso f k).hom.left =
      (SSet.toTopSdIterIso X k).hom :=
  rfl

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    (SSet.toTopSdIterArrowIso f k).hom.right =
      (SSet.toTopSdIterIso Y k).hom :=
  rfl

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    (SSet.toTopSdIterArrowIso f k).hom.left ≫ SSet.toTop.map f =
      SSet.toTop.map ((SSet.sdIter k).map f) ≫
        (SSet.toTopSdIterArrowIso f k).hom.right :=
  (SSet.toTopSdIterArrowIso f k).hom.w

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] :
    (SSet.toTopSdIterArrowIso f 0).hom.left = 𝟙 _ := by
  change (SSet.toTopSdIterIso X 0).hom = 𝟙 _
  rw [SSet.toTopSdIterIso_zero]
  rfl

example {X Y : SSet.{0}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] :
    (SSet.toTopSdIterArrowIso f 0).hom.right = 𝟙 _ := by
  change (SSet.toTopSdIterIso Y 0).hom = 𝟙 _
  rw [SSet.toTopSdIterIso_zero]
  rfl

end NaturalityAndIteration

section Horns

noncomputable example (n : ℕ) (i : Fin (n + 2)) (k : ℕ) :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter k).map (SSet.horn (n + 1) i).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn (n + 1) i).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn (n + 1) i).ι k

noncomputable example :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter 0).map (SSet.horn 1 (0 : Fin 2)).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn 1 (0 : Fin 2)).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn 1 (0 : Fin 2)).ι 0

noncomputable example :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter 0).map (SSet.horn 1 (1 : Fin 2)).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn 1 (1 : Fin 2)).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn 1 (1 : Fin 2)).ι 0

noncomputable example :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter 1).map (SSet.horn 1 (0 : Fin 2)).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn 1 (0 : Fin 2)).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn 1 (0 : Fin 2)).ι 1

noncomputable example :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter 1).map (SSet.horn 1 (1 : Fin 2)).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn 1 (1 : Fin 2)).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn 1 (1 : Fin 2)).ι 1

noncomputable example (n : ℕ) (i : Fin (n + 2)) :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter 2).map (SSet.horn (n + 1) i).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn (n + 1) i).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn (n + 1) i).ι 2

end Horns

section NoninjectiveCounterexample

private def collapseOrderHom : Fin 3 →o Fin 2 where
  toFun i := ![0, 0, 1] i
  monotone' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

private def collapse : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk collapseOrderHom

example : ¬Function.Injective collapse := by
  intro h
  have h01 : (0 : Fin 3) = 1 := h (by rfl)
  norm_num at h01

private lemma pushed_barycenter_weight_zero :
    (Convexity.StdSimplex.map collapse
      (Convexity.StdSimplex.barycenter :
        Convexity.StdSimplex ℝ (Fin 3))).weights 0 = (2 : ℝ) / 3 := by
  classical
  rw [Convexity.StdSimplex.weights_map_apply]
  have hfilter : Finset.univ.filter
      (fun i : Fin 3 => collapse i = (0 : Fin 2)) = {0, 1} := by
    decide
  rw [hfilter]
  simp [Convexity.StdSimplex.weights_barycenter_apply]
  norm_num

private lemma target_barycenter_weight_zero :
    (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin 2)).weights 0 = (1 : ℝ) / 2 := by
  simpa using
    (Convexity.StdSimplex.weights_barycenter_apply (K := ℝ) (0 : Fin 2))

example :
    Convexity.StdSimplex.map collapse
        (Convexity.StdSimplex.barycenter :
          Convexity.StdSimplex ℝ (Fin 3)) ≠
      (Convexity.StdSimplex.barycenter :
        Convexity.StdSimplex ℝ (Fin 2)) := by
  intro h
  have h0 := congrArg
    (fun q : Convexity.StdSimplex ℝ (Fin 2) => q.weights 0) h
  rw [pushed_barycenter_weight_zero,
    target_barycenter_weight_zero] at h0
  norm_num at h0

end NoninjectiveCounterexample

section UniverseBoundary

variable (X₁ Y₁ : SSet.{1}) [X₁.Nonsingular] [Y₁.Nonsingular]

noncomputable example :
    SSet.toTop.obj (SSet.sd.obj X₁) ≅ SSet.toTop.obj X₁ :=
  SSet.toTopSdIso X₁

example (x : X₁.N) {d : ℕ}
    (σ : (SimplexCategory.sd.{1}.obj ⦋x.dim⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (SSet.toTopSdIso X₁).hom
        (SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex))
          (SSet.toTop.map
            (SSet.yonedaEquiv.symm
              ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ))
            ((SimplexCategory.toTopHomeo.{1} ⦋d⦌).symm q))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex)
        ((SimplexCategory.toTopHomeo.{1} ⦋x.dim⦌).symm
          (SimplexCategory.sdCellMap σ q)) :=
  SSet.toTopSdIso_hom_cell_apply X₁ x σ q

example (f : X₁ ⟶ Y₁)
    (hf : ∀ {n : ℕ} (x : X₁ _⦋n⦌),
      x ∈ X₁.nonDegenerate n → f.app _ x ∈ Y₁.nonDegenerate n) :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y₁).hom =
      (SSet.toTopSdIso X₁).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIso_hom_naturality f hf

example (f : X₁ ⟶ Y₁) [Mono f] :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y₁).hom =
      (SSet.toTopSdIso X₁).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIso_hom_naturality_of_mono f

noncomputable example (k : ℕ) :
    SSet.toTop.obj ((SSet.sdIter k).obj X₁) ≅ SSet.toTop.obj X₁ :=
  SSet.toTopSdIterIso X₁ k

example (f : X₁ ⟶ Y₁) [Mono f] (k : ℕ) :
    SSet.toTop.map ((SSet.sdIter k).map f) ≫
        (SSet.toTopSdIterIso Y₁ k).hom =
      (SSet.toTopSdIterIso X₁ k).hom ≫ SSet.toTop.map f :=
  SSet.toTopSdIterIso_hom_naturality_of_mono f k

noncomputable example (f : X₁ ⟶ Y₁) [Mono f] (k : ℕ) :
    Arrow.mk (SSet.toTop.map ((SSet.sdIter k).map f)) ≅
      Arrow.mk (SSet.toTop.map f) :=
  SSet.toTopSdIterArrowIso f k

noncomputable example (k : ℕ) :
    Arrow.mk
        (SSet.toTop.map
          ((SSet.sdIter k).map (SSet.horn.{1} 1 (0 : Fin 2)).ι)) ≅
      Arrow.mk (SSet.toTop.map (SSet.horn.{1} 1 (0 : Fin 2)).ι) :=
  SSet.toTopSdIterArrowIso (SSet.horn.{1} 1 (0 : Fin 2)).ι k

end UniverseBoundary

#print axioms SSet.toTopSdIso
#print axioms SSet.toTopSdIso_hom_cell_apply
#print axioms SSet.toTopSdIso_hom_cell
#print axioms SSet.toTopSdIso_hom_naturality
#print axioms SSet.toTopSdIso_hom_naturality_of_mono
#print axioms SSet.toTopSdIterIso
#print axioms SSet.toTopSdIterIso_zero
#print axioms SSet.toTopSdIterIso_succ
#print axioms SSet.toTopSdIterIso_hom_naturality_of_mono
#print axioms SSet.toTopSdIterArrowIso

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SubdivisionRealizationTests
