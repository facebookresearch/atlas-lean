/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.TrivialFibrationCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoFunctorCategorical

/-!
# Homotopic maps induce naturally isomorphic precomposition (the supporting results)

This module closes the additional comparison obligation of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.TrivialFibrationCategorical`:
a simplicial homotopy `H : SSet.Homotopy f g` between maps `f g : X ⟶ X`
induces, for every simplicial set `C`, a natural transformation between the
precomposition functors `h Fun(f, C)` and `h Fun(g, C)` on homotopy
categories of functor objects, and when `H` and a reverse homotopy lie over a
trivial Kan fibration `p`, this natural transformation is an isomorphism.
Consequently every trivial Kan fibration is a Joyal categorical equivalence:

```text
SSet.modelCategoryQuillen.I.rlp ≤ SSet.categoricalEquivalences.
```
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {X Y Z C : SSet.{u}}

/-!
## Imported generic edge and homotopy algebra

The external product of composition structures
(`SSet.Edge.CompStruct.tensor`, over `SSet.Edge.tensor`), the tensor
square in the homotopy category (`SSet.Edge.tensor_square`), assembly
of a homotopy from a cylinder map (`SSet.Homotopy.mkOfH`), the
constant homotopy (`SSet.Homotopy.reflH`), and the edge dictionary
(`SSet.Homotopy.edgeIhom`) used below are generic simplicial-set
infrastructure of the neutral modules
`MathlibExt.AlgebraicTopology.SimplicialSet.HoComp` and
`MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom`. The
absolute whiskering operations are the canonical
`SSet.Homotopy.precomp` and `SSet.Homotopy.postcomp` of
`MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp`.
-/

/-!
## Vertices of `Δ[1]`, curried faces, and homotopies from edges
-/

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `0` is the Yoneda name of
that vertex. -/
private lemma deltaOne_δ_one_eq :
    stdSimplex.δ (1 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (1 : Fin 2) =
      stdSimplex.δ (1 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `1` is the Yoneda name of
that vertex. -/
private lemma deltaOne_δ_zero_eq :
    stdSimplex.δ (0 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (0 : Fin 2) =
      stdSimplex.δ (0 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

private lemma rightUnitor_hom_comp_ι₀_hoPre :
    (ρ_ X).hom ≫ (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      X ◁ (Δ0IsoUnit.inv ≫ stdSimplex.δ (1 : Fin 2)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, SSet.ι₀_fst, Category.comp_id,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_hom]
  · rw [Category.assoc, SSet.ι₀_snd, CartesianMonoidalCategory.whiskerLeft_snd,
      ← Category.assoc, deltaOne_δ_one_eq, yonedaEquiv_symm_zero]
    simp only [SSet.comp_const]

private lemma rightUnitor_hom_comp_ι₁_hoPre :
    (ρ_ X).hom ≫ (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      X ◁ (Δ0IsoUnit.inv ≫ stdSimplex.δ (0 : Fin 2)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, SSet.ι₁_fst, Category.comp_id,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_hom]
  · rw [Category.assoc, SSet.ι₁_snd, CartesianMonoidalCategory.whiskerLeft_snd,
      ← Category.assoc, deltaOne_δ_zero_eq, yonedaEquiv_symm_zero]
    simp only [SSet.comp_const]

/-- The source vertex of the currying of a cylinder map `K : X ⊗ Δ[1] ⟶ C`
is the vertex classified by its `0`-end. -/
private lemma curry_δ_one_vertex (K : X ⊗ (Δ[1] : SSet.{u}) ⟶ C) :
    ((ihom X).obj C).δ (1 : Fin 2) (yonedaEquiv (MonoidalClosed.curry K)) =
      ihomVertexEquiv X C (SSet.ι₀ ≫ K) := by
  have key : Δ0IsoUnit.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry' (SSet.ι₀ ≫ K) := by
    change Δ0IsoUnit.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry ((ρ_ X).hom ≫ (SSet.ι₀ ≫ K))
    rw [← Category.assoc, ← MonoidalClosed.curry_natural_left,
      ← rightUnitor_hom_comp_ι₀_hoPre, Category.assoc]
  calc ((ihom X).obj C).δ (1 : Fin 2) (yonedaEquiv (MonoidalClosed.curry K))
      = yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry K) :=
        (stdSimplex.yonedaEquiv_δ_comp _ _).symm
    _ = unitHomEquiv _ (Δ0IsoUnit.inv ≫
          (stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry K)) :=
        yonedaEquiv_eq_unitHomEquiv _ _
    _ = unitHomEquiv _ (MonoidalClosed.curry' (SSet.ι₀ ≫ K)) := by rw [key]
    _ = ihomVertexEquiv X C (SSet.ι₀ ≫ K) := (ihomVertexEquiv_eq X C _).symm

/-- The target vertex of the currying of a cylinder map `K : X ⊗ Δ[1] ⟶ C`
is the vertex classified by its `1`-end. -/
private lemma curry_δ_zero_vertex (K : X ⊗ (Δ[1] : SSet.{u}) ⟶ C) :
    ((ihom X).obj C).δ (0 : Fin 2) (yonedaEquiv (MonoidalClosed.curry K)) =
      ihomVertexEquiv X C (SSet.ι₁ ≫ K) := by
  have key : Δ0IsoUnit.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry' (SSet.ι₁ ≫ K) := by
    change Δ0IsoUnit.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry ((ρ_ X).hom ≫ (SSet.ι₁ ≫ K))
    rw [← Category.assoc, ← MonoidalClosed.curry_natural_left,
      ← rightUnitor_hom_comp_ι₁_hoPre, Category.assoc]
  calc ((ihom X).obj C).δ (0 : Fin 2) (yonedaEquiv (MonoidalClosed.curry K))
      = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry K) :=
        (stdSimplex.yonedaEquiv_δ_comp _ _).symm
    _ = unitHomEquiv _ (Δ0IsoUnit.inv ≫
          (stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry K)) :=
        yonedaEquiv_eq_unitHomEquiv _ _
    _ = unitHomEquiv _ (MonoidalClosed.curry' (SSet.ι₁ ≫ K)) := by rw [key]
    _ = ihomVertexEquiv X C (SSet.ι₁ ≫ K) := (ihomVertexEquiv_eq X C _).symm

/-- The homotopy classified by an edge of a functor object, obtained by
uncurrying. Its ends are the maps classified by the endpoints of the edge
(`curry_δ_one_vertex`, `curry_δ_zero_vertex`). -/
private noncomputable def homotopyOfEdge {x y : ((ihom X).obj C) _⦋0⦌}
    (e : ((ihom X).obj C).Edge x y) :
    Homotopy ((ihomVertexEquiv X C).symm x) ((ihomVertexEquiv X C).symm y) :=
  Homotopy.mkOfH (MonoidalClosed.uncurry (yonedaEquiv.symm e.edge))
    (by
      apply (ihomVertexEquiv X C).injective
      rw [Equiv.apply_symm_apply, ← curry_δ_one_vertex,
        MonoidalClosed.curry_uncurry, Equiv.apply_symm_apply, e.src_eq])
    (by
      apply (ihomVertexEquiv X C).injective
      rw [Equiv.apply_symm_apply, ← curry_δ_zero_vertex,
        MonoidalClosed.curry_uncurry, Equiv.apply_symm_apply, e.tgt_eq])

private lemma homotopyOfEdge_h {x y : ((ihom X).obj C) _⦋0⦌}
    (e : ((ihom X).obj C).Edge x y) :
    (homotopyOfEdge e).h = MonoidalClosed.uncurry (yonedaEquiv.symm e.edge) :=
  rfl

private lemma curry_homotopyOfEdge_h {x y : ((ihom X).obj C) _⦋0⦌}
    (e : ((ihom X).obj C).Edge x y) :
    MonoidalClosed.curry (homotopyOfEdge e).h = yonedaEquiv.symm e.edge := by
  rw [homotopyOfEdge_h, MonoidalClosed.curry_uncurry]

/-- The Yoneda name of a pair of `1`-simplices is the pairing of the Yoneda
names. -/
private lemma yonedaEquivSymm_prod (A B : SSet.{u}) (p : (A ⊗ B) _⦋1⦌) :
    yonedaEquiv.symm p =
      CartesianMonoidalCategory.lift (yonedaEquiv.symm p.1)
        (yonedaEquiv.symm p.2) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  · rw [CartesianMonoidalCategory.lift_snd]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

/-- The fundamental edge of `Δ[1]`, classified by the identity. -/
private noncomputable def deltaOneEdge :
    (Δ[1] : SSet.{u}).Edge (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))
      (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) :=
  Edge.mk (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id, deltaOne_δ_one_eq,
      Equiv.apply_symm_apply])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id, deltaOne_δ_zero_eq,
      Equiv.apply_symm_apply])

private lemma deltaOneEdge_edge :
    deltaOneEdge.edge = yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) :=
  rfl

private lemma yonedaEquivSymm_deltaOneEdge :
    yonedaEquiv.symm deltaOneEdge.edge = 𝟙 (Δ[1] : SSet.{u}) := by
  rw [deltaOneEdge_edge, Equiv.symm_apply_apply]

private lemma yonedaEquivSymm_edge_id (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    yonedaEquiv.symm (Edge.id v).edge = const v := by
  rw [Edge.id_edge, ← stdSimplex.σ_comp_yonedaEquiv_symm, yonedaEquiv_symm_zero,
    SSet.comp_const]

/-!
## The component edges
-/

/-- Precomposition on the vertex classified by the map assigned to a vertex
of a functor object. -/
lemma ihomVertex_pre_apply {ψ : X ⟶ X} (x : ((ihom X).obj C) _⦋0⦌) :
    ihomVertexEquiv X C (ψ ≫ (ihomVertexEquiv X C).symm x) =
      ((pre ψ).app C).app _ x := by
  rw [← ihomVertexEquiv_pre_app, Equiv.apply_symm_apply]

namespace Homotopy

variable {f g : X ⟶ X}

/-- **The component edge of the precomposition transformation.** At a vertex
`x` of `Fun(X, C)` classified by `q : X ⟶ C`, this is the edge of `Fun(X, C)`
classified by the postcomposed homotopy `H.postcomp q`, transported to the
endpoints picked out by precomposition with `f` and `g`. Its underlying
`1`-simplex is `SSet.Homotopy.edgeIhom` of the postcomposed homotopy
(`Homotopy.hoPreCompEdge_edge`). -/
noncomputable def hoPreCompEdge (H : Homotopy f g) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    Edge (((pre f).app C).app _ x) (((pre g).app C).app _ x) :=
  (H.postcomp ((ihomVertexEquiv X C).symm x)).edgeIhom.ofEq
    (ihomVertex_pre_apply x) (ihomVertex_pre_apply x)

lemma hoPreCompEdge_edge (H : Homotopy f g) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    (H.hoPreCompEdge C x).edge =
      (H.postcomp ((ihomVertexEquiv X C).symm x)).edgeIhom.edge :=
  rfl

end Homotopy

/-!
## Prism face computations

The four faces of the prism `(α_ X Δ[1] Δ[1]).inv ≫ (H.h ▷ Δ[1]) ≫ K.h`:
whiskering a graph map `Δ[1] ⟶ Δ[1] ⊗ Δ[1]` and reassociating produces on
the nose the postcomposed or precomposed cylinder maps.
-/

private lemma preKeA0 (Hh : X ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    (X ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫ (Hh ▷ (Δ[1] : SSet.{u})) =
      Hh ≫ (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) := by
  have key : (X ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶
        (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) =
        𝟙 (X ⊗ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [CartesianMonoidalCategory.associator_inv_fst_fst,
        CartesianMonoidalCategory.associator_inv_fst_snd]
  apply CartesianMonoidalCategory.hom_ext
  · have step : ((X ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶
          (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (Hh ▷ (Δ[1] : SSet.{u}))) ≫ fst X (Δ[1] : SSet.{u}) =
        ((X ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶
          (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u})) ≫ Hh := by
      simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
    rw [step, key, Category.id_comp, Category.assoc, SSet.ι₀_fst, Category.comp_id]
  · simp

private lemma preKeA1 (Hh : X ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    (X ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫ (Hh ▷ (Δ[1] : SSet.{u})) =
      Hh ≫ (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) := by
  have key : (X ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶
        (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) =
        𝟙 (X ⊗ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [CartesianMonoidalCategory.associator_inv_fst_fst,
        CartesianMonoidalCategory.associator_inv_fst_snd]
  apply CartesianMonoidalCategory.hom_ext
  · have step : ((X ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶
          (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (Hh ▷ (Δ[1] : SSet.{u}))) ≫ fst X (Δ[1] : SSet.{u}) =
        ((X ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶
          (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u})) ≫ Hh := by
      simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
    rw [step, key, Category.id_comp, Category.assoc, SSet.ι₁_fst, Category.comp_id]
  · simp

private lemma preKeB0 (Hh : X ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    (X ◁ CartesianMonoidalCategory.lift
        (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
          (𝟙 (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫ (Hh ▷ (Δ[1] : SSet.{u})) =
      ((SSet.ι₀ ≫ Hh) ▷ (Δ[1] : SSet.{u})) := by
  have key : (X ◁ CartesianMonoidalCategory.lift
        (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
          (𝟙 (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) =
      fst X (Δ[1] : SSet.{u}) ≫ (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [CartesianMonoidalCategory.associator_inv_fst_fst,
        CartesianMonoidalCategory.associator_inv_fst_snd]
  apply CartesianMonoidalCategory.hom_ext
  · have step : ((X ◁ CartesianMonoidalCategory.lift
          (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
            (𝟙 (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (Hh ▷ (Δ[1] : SSet.{u}))) ≫ fst X (Δ[1] : SSet.{u}) =
        ((X ◁ CartesianMonoidalCategory.lift
          (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
            (𝟙 (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u})) ≫ Hh := by
      simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
    rw [step, key, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
  · simp [CartesianMonoidalCategory.associator_inv_snd]

private lemma preKeB1 (Hh : X ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    (X ◁ CartesianMonoidalCategory.lift
        (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))
          (𝟙 (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫ (Hh ▷ (Δ[1] : SSet.{u})) =
      ((SSet.ι₁ ≫ Hh) ▷ (Δ[1] : SSet.{u})) := by
  have key : (X ◁ CartesianMonoidalCategory.lift
        (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))
          (𝟙 (Δ[1] : SSet.{u}))) ≫
        (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u}) =
      fst X (Δ[1] : SSet.{u}) ≫ (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [CartesianMonoidalCategory.associator_inv_fst_fst,
        CartesianMonoidalCategory.associator_inv_fst_snd]
  apply CartesianMonoidalCategory.hom_ext
  · have step : ((X ◁ CartesianMonoidalCategory.lift
          (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))
            (𝟙 (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (Hh ▷ (Δ[1] : SSet.{u}))) ≫ fst X (Δ[1] : SSet.{u}) =
        ((X ◁ CartesianMonoidalCategory.lift
          (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))
            (𝟙 (Δ[1] : SSet.{u}))) ≫
          (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[1] : SSet.{u})) ≫ Hh := by
      simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
    rw [step, key, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
  · simp [CartesianMonoidalCategory.associator_inv_snd]

private lemma yonedaEquivSymm_tensorA0 :
    yonedaEquiv.symm (deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).edge =
      (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) := by
  rw [yonedaEquivSymm_prod]
  change CartesianMonoidalCategory.lift (yonedaEquiv.symm deltaOneEdge.edge)
      (yonedaEquiv.symm (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).edge) = _
  rw [yonedaEquivSymm_deltaOneEdge, yonedaEquivSymm_edge_id]
  rfl

private lemma yonedaEquivSymm_tensorA1 :
    yonedaEquiv.symm (deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).edge =
      (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) := by
  rw [yonedaEquivSymm_prod]
  change CartesianMonoidalCategory.lift (yonedaEquiv.symm deltaOneEdge.edge)
      (yonedaEquiv.symm (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).edge) = _
  rw [yonedaEquivSymm_deltaOneEdge, yonedaEquivSymm_edge_id]
  rfl

private lemma yonedaEquivSymm_tensorB0 :
    yonedaEquiv.symm ((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
        deltaOneEdge).edge =
      CartesianMonoidalCategory.lift
        (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  rw [yonedaEquivSymm_prod]
  change CartesianMonoidalCategory.lift
      (yonedaEquiv.symm (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).edge)
      (yonedaEquiv.symm deltaOneEdge.edge) = _
  rw [yonedaEquivSymm_edge_id, yonedaEquivSymm_deltaOneEdge]

private lemma yonedaEquivSymm_tensorB1 :
    yonedaEquiv.symm ((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
        deltaOneEdge).edge =
      CartesianMonoidalCategory.lift
        (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  rw [yonedaEquivSymm_prod]
  change CartesianMonoidalCategory.lift
      (yonedaEquiv.symm (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).edge)
      (yonedaEquiv.symm deltaOneEdge.edge) = _
  rw [yonedaEquivSymm_edge_id, yonedaEquivSymm_deltaOneEdge]

/-!
## The naturality square
-/

variable {f g : X ⟶ X}

private lemma faceTensorA0 (H : Homotopy f g)
    {x y : ((ihom X).obj C) _⦋0⦌} (e : ((ihom X).obj C).Edge x y) :
    ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map
        (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge =
      (H.hoPreCompEdge C x).edge := by
  calc ((deltaOneEdge.tensor
            (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map
          (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge
      = yonedaEquiv (yonedaEquiv.symm
            (deltaOneEdge.tensor
              (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).edge ≫
          MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        Edge.map_edge_yoneda _ _
    _ = yonedaEquiv (MonoidalClosed.curry
          (H.h ≫ (ihomVertexEquiv X C).symm x)) :=
        congrArg yonedaEquiv (by
          rw [yonedaEquivSymm_tensorA0]
          apply MonoidalClosed.uncurry_injective
          rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
            MonoidalClosed.uncurry_curry]
          calc (X ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶
                  (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
                ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                  (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)
              = ((X ◁ (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶
                  (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
                  (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                    (H.h ▷ (Δ[1] : SSet.{u}))) ≫ (homotopyOfEdge e).h := by
                simp only [Category.assoc]
            _ = (H.h ≫ (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u}))) ≫
                  (homotopyOfEdge e).h := by rw [preKeA0]
            _ = H.h ≫ (SSet.ι₀ ≫ (homotopyOfEdge e).h) := Category.assoc _ _ _
            _ = H.h ≫ (ihomVertexEquiv X C).symm x := by
                rw [(homotopyOfEdge e).h₀])
    _ = (H.hoPreCompEdge C x).edge := by
        rw [Homotopy.hoPreCompEdge_edge, Homotopy.edgeIhom_edge, Homotopy.postcomp_h]

private lemma faceTensorA1 (H : Homotopy f g)
    {x y : ((ihom X).obj C) _⦋0⦌} (e : ((ihom X).obj C).Edge x y) :
    ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map
        (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge =
      (H.hoPreCompEdge C y).edge := by
  calc ((deltaOneEdge.tensor
            (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map
          (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge
      = yonedaEquiv (yonedaEquiv.symm
            (deltaOneEdge.tensor
              (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).edge ≫
          MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        Edge.map_edge_yoneda _ _
    _ = yonedaEquiv (MonoidalClosed.curry
          (H.h ≫ (ihomVertexEquiv X C).symm y)) :=
        congrArg yonedaEquiv (by
          rw [yonedaEquivSymm_tensorA1]
          apply MonoidalClosed.uncurry_injective
          rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
            MonoidalClosed.uncurry_curry]
          calc (X ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶
                  (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
                ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                  (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)
              = ((X ◁ (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶
                  (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}))) ≫
                  (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                    (H.h ▷ (Δ[1] : SSet.{u}))) ≫ (homotopyOfEdge e).h := by
                simp only [Category.assoc]
            _ = (H.h ≫ (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u}))) ≫
                  (homotopyOfEdge e).h := by rw [preKeA1]
            _ = H.h ≫ (SSet.ι₁ ≫ (homotopyOfEdge e).h) := Category.assoc _ _ _
            _ = H.h ≫ (ihomVertexEquiv X C).symm y := by
                rw [(homotopyOfEdge e).h₁])
    _ = (H.hoPreCompEdge C y).edge := by
        rw [Homotopy.hoPreCompEdge_edge, Homotopy.edgeIhom_edge, Homotopy.postcomp_h]

private lemma faceTensorB0 (H : Homotopy f g)
    {x y : ((ihom X).obj C) _⦋0⦌} (e : ((ihom X).obj C).Edge x y) :
    (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
        deltaOneEdge).map
        (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge =
      ((homotopyOfEdge e).precomp f).edgeIhom.edge := by
  calc (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
            deltaOneEdge).map
          (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge
      = yonedaEquiv (yonedaEquiv.symm
            ((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
              deltaOneEdge).edge ≫
          MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        Edge.map_edge_yoneda _ _
    _ = yonedaEquiv (MonoidalClosed.curry
          ((f ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        congrArg yonedaEquiv (by
          rw [yonedaEquivSymm_tensorB0]
          apply MonoidalClosed.uncurry_injective
          rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
            MonoidalClosed.uncurry_curry]
          calc (X ◁ CartesianMonoidalCategory.lift
                  (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
                    (𝟙 (Δ[1] : SSet.{u}))) ≫
                ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                  (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)
              = ((X ◁ CartesianMonoidalCategory.lift
                  (const (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
                    (𝟙 (Δ[1] : SSet.{u}))) ≫
                  (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                    (H.h ▷ (Δ[1] : SSet.{u}))) ≫ (homotopyOfEdge e).h := by
                simp only [Category.assoc]
            _ = ((SSet.ι₀ ≫ H.h) ▷ (Δ[1] : SSet.{u})) ≫
                  (homotopyOfEdge e).h := by rw [preKeB0]
            _ = (f ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h := by rw [H.h₀])
    _ = ((homotopyOfEdge e).precomp f).edgeIhom.edge := by
        rw [Homotopy.edgeIhom_edge, Homotopy.precomp_h]

private lemma faceTensorB1 (H : Homotopy f g)
    {x y : ((ihom X).obj C) _⦋0⦌} (e : ((ihom X).obj C).Edge x y) :
    (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
        deltaOneEdge).map
        (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
          (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge =
      ((homotopyOfEdge e).precomp g).edgeIhom.edge := by
  calc (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
            deltaOneEdge).map
          (MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h))).edge
      = yonedaEquiv (yonedaEquiv.symm
            ((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
              deltaOneEdge).edge ≫
          MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
            (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        Edge.map_edge_yoneda _ _
    _ = yonedaEquiv (MonoidalClosed.curry
          ((g ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        congrArg yonedaEquiv (by
          rw [yonedaEquivSymm_tensorB1]
          apply MonoidalClosed.uncurry_injective
          rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
            MonoidalClosed.uncurry_curry]
          calc (X ◁ CartesianMonoidalCategory.lift
                  (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))
                    (𝟙 (Δ[1] : SSet.{u}))) ≫
                ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                  (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)
              = ((X ◁ CartesianMonoidalCategory.lift
                  (const (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))
                    (𝟙 (Δ[1] : SSet.{u}))) ≫
                  (α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
                    (H.h ▷ (Δ[1] : SSet.{u}))) ≫ (homotopyOfEdge e).h := by
                simp only [Category.assoc]
            _ = ((SSet.ι₁ ≫ H.h) ▷ (Δ[1] : SSet.{u})) ≫
                  (homotopyOfEdge e).h := by rw [preKeB1]
            _ = (g ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h := by rw [H.h₁])
    _ = ((homotopyOfEdge e).precomp g).edgeIhom.edge := by
        rw [Homotopy.edgeIhom_edge, Homotopy.precomp_h]

private lemma edge_map_pre_edge (ψ : X ⟶ X)
    {x y : ((ihom X).obj C) _⦋0⦌} (e : ((ihom X).obj C).Edge x y) :
    (e.map ((pre ψ).app C)).edge =
      ((homotopyOfEdge e).precomp ψ).edgeIhom.edge := by
  calc (e.map ((pre ψ).app C)).edge
      = yonedaEquiv (yonedaEquiv.symm e.edge ≫ (pre ψ).app C) :=
        Edge.map_edge_yoneda _ _
    _ = yonedaEquiv (MonoidalClosed.curry
          ((ψ ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)) :=
        congrArg yonedaEquiv (by
          rw [← curry_homotopyOfEdge_h]
          exact MonoidalClosed.curry_pre_app ψ _)
    _ = ((homotopyOfEdge e).precomp ψ).edgeIhom.edge := by
        rw [Homotopy.edgeIhom_edge, Homotopy.precomp_h]

private lemma homMk_ofEq {W : SSet.{u}} {a b a' b' : W _⦋0⦌} (e : Edge a b)
    (ha : a = a') (hb : b = b') :
    HomotopyCategory.homMk (e.ofEq ha hb) =
      eqToHom (congrArg HomotopyCategory.mk ha).symm ≫
        HomotopyCategory.homMk e ≫ eqToHom (congrArg HomotopyCategory.mk hb) := by
  cases ha; cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private lemma eqToHom_comp_symm_hoPre {D : Type u} [Category.{u} D] {a b : D}
    (h : a = b) : eqToHom h ≫ eqToHom h.symm = 𝟙 a := by
  cases h; simp

namespace Homotopy

/-- **Naturality of the component edges.** The components
`Homotopy.hoPreCompEdge` are natural with respect to every edge of the
functor object: this is the transport of `SSet.Edge.tensor_square` along
the curried prism map, with the four sides identified by the face lemmas. -/
theorem hoPre_square (H : Homotopy f g) (C : SSet.{u})
    {x y : ((ihom X).obj C) _⦋0⦌} (e : ((ihom X).obj C).Edge x y) :
    HomotopyCategory.homMk (e.map ((pre f).app C)) ≫
        HomotopyCategory.homMk (H.hoPreCompEdge C y) =
      HomotopyCategory.homMk (H.hoPreCompEdge C x) ≫
        HomotopyCategory.homMk (e.map ((pre g).app C)) := by
  set Θ : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom X).obj C :=
    MonoidalClosed.curry ((α_ X (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).inv ≫
      (H.h ▷ (Δ[1] : SSet.{u})) ≫ (homotopyOfEdge e).h)
  have fA0 : ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ).edge =
      (H.hoPreCompEdge C x).edge :=
    faceTensorA0 H e
  have fA1 : ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ).edge =
      (H.hoPreCompEdge C y).edge :=
    faceTensorA1 H e
  have fB0 : (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
        deltaOneEdge).map Θ).edge =
      ((homotopyOfEdge e).precomp f).edgeIhom.edge :=
    faceTensorB0 H e
  have fB1 : (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
        deltaOneEdge).map Θ).edge =
      ((homotopyOfEdge e).precomp g).edgeIhom.edge :=
    faceTensorB1 H e
  have c00 : Θ.app _ (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2),
        stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      ((pre f).app C).app _ x :=
    ((deltaOneEdge.tensor
      (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ).src_eq.symm.trans
      (by rw [fA0]; exact (H.hoPreCompEdge C x).src_eq)
  have c10 : Θ.app _ (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      ((pre g).app C).app _ x :=
    ((deltaOneEdge.tensor
      (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ).tgt_eq.symm.trans
      (by rw [fA0]; exact (H.hoPreCompEdge C x).tgt_eq)
  have c01 : Θ.app _ (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2),
        stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) =
      ((pre f).app C).app _ y :=
    ((deltaOneEdge.tensor
      (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ).src_eq.symm.trans
      (by rw [fA1]; exact (H.hoPreCompEdge C y).src_eq)
  have c11 : Θ.app _ (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2),
        stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) =
      ((pre g).app C).app _ y :=
    ((deltaOneEdge.tensor
      (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ).tgt_eq.symm.trans
      (by rw [fA1]; exact (H.hoPreCompEdge C y).tgt_eq)
  have eA0 : ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ).ofEq c00 c10 =
      H.hoPreCompEdge C x :=
    Edge.ext fA0
  have eA1 : ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ).ofEq c01 c11 =
      H.hoPreCompEdge C y :=
    Edge.ext fA1
  have eB0 : (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
        deltaOneEdge).map Θ).ofEq c00 c01 =
      e.map ((pre f).app C) :=
    Edge.ext (fB0.trans (edge_map_pre_edge f e).symm)
  have eB1 : (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
        deltaOneEdge).map Θ).ofEq c10 c11 =
      e.map ((pre g).app C) :=
    Edge.ext (fB1.trans (edge_map_pre_edge g e).symm)
  have hsq := congrArg (mapHomotopyCategory Θ).map
    (Edge.tensor_square deltaOneEdge deltaOneEdge)
  rw [Functor.map_comp, Functor.map_comp] at hsq
  change HomotopyCategory.homMk ((deltaOneEdge.tensor
        (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ) ≫
        HomotopyCategory.homMk
          (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
            deltaOneEdge).map Θ) =
      HomotopyCategory.homMk
          (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
            deltaOneEdge).map Θ) ≫
        HomotopyCategory.homMk ((deltaOneEdge.tensor
          (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ) at hsq
  rw [← eB0, ← eA1, ← eA0, ← eB1,
    homMk_ofEq (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
      deltaOneEdge).map Θ) c00 c01,
    homMk_ofEq ((deltaOneEdge.tensor
      (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ) c01 c11,
    homMk_ofEq ((deltaOneEdge.tensor
      (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ) c00 c10,
    homMk_ofEq (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
      deltaOneEdge).map Θ) c10 c11]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom (congrArg HomotopyCategory.mk c01))
        (eqToHom (congrArg HomotopyCategory.mk c01).symm),
    ← Category.assoc (eqToHom (congrArg HomotopyCategory.mk c10))
        (eqToHom (congrArg HomotopyCategory.mk c10).symm),
    eqToHom_comp_symm_hoPre, eqToHom_comp_symm_hoPre,
    Category.id_comp, Category.id_comp,
    ← Category.assoc (HomotopyCategory.homMk
        (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))).tensor
          deltaOneEdge).map Θ))
        (HomotopyCategory.homMk ((deltaOneEdge.tensor
          (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))).map Θ)),
    ← Category.assoc (HomotopyCategory.homMk ((deltaOneEdge.tensor
          (Edge.id (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))).map Θ))
        (HomotopyCategory.homMk
          (((Edge.id (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))).tensor
            deltaOneEdge).map Θ)),
    ← hsq]

/-- **The natural transformation between precomposition functors.** A
homotopy `H : SSet.Homotopy f g` induces a natural transformation
`h Fun(f, C) ⟶ h Fun(g, C)` with components the morphisms represented by
`Homotopy.hoPreCompEdge`. -/
noncomputable def hoPreNatTrans (H : Homotopy f g) (C : SSet.{u}) :
    (hoFunctor.map ((pre f).app C)).toFunctor ⟶
      (hoFunctor.map ((pre g).app C)).toFunctor :=
  Truncated.HomotopyCategory.mkNatTrans (V := (truncation 2).obj ((ihom X).obj C))
    (fun x => HomotopyCategory.homMk (H.hoPreCompEdge C x))
    (by
      intro x y e
      exact H.hoPre_square C (Edge.ofTruncated e))

lemma hoPreNatTrans_app_mk (H : Homotopy f g) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    (H.hoPreNatTrans C).app (HomotopyCategory.mk x) =
      HomotopyCategory.homMk (H.hoPreCompEdge C x) :=
  rfl

end Homotopy

/-!
## Coherent `2`-homotopies over a trivial Kan fibration

The boundary of the desired `2`-simplex is assembled after currying, by
`SSet.boundary.twoDesc`, and then uncurried to the top map of the lifting
square against `X ◁ (boundary 2).ι`.
-/

/-- The cylinder boundary inclusion at level `2` is a monomorphism: it is,
up to the product-subcomplex isomorphism, the inclusion of the subcomplex
`⊤.prod (boundary 2)` of `X ⊗ Δ[2]`. -/
lemma mono_whiskerLeft_boundary_two_ι :
    Mono (X ◁ (boundary 2).ι) := by
  let e := (Subcomplex.prodIso (⊤ : X.Subcomplex) (boundary 2)) ≪≫
    whiskerRightIso (Subcomplex.topIso X) ((boundary 2 : SSet.{u}) : SSet.{u})
  have hfac : e.hom ≫ (X ◁ (boundary 2).ι) =
      ((⊤ : X.Subcomplex).prod (boundary 2)).ι := rfl
  have hEq : X ◁ (boundary 2).ι =
      e.inv ≫ ((⊤ : X.Subcomplex).prod (boundary 2)).ι := by
    rw [← hfac, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hEq]
  infer_instance

variable {p : X ⟶ Y}

/-- Three homotopies over a trivial Kan fibration with a common bottom
compose in the functor object `Fun(X, X)`: the lift of `p` against
`X ◁ (boundary 2).ι` curries to a `2`-simplex whose faces are the three
`SSet.Homotopy.edgeIhom` edges. -/
noncomputable def compStruct_edgeIhom_of_homotopies_over
    (hp : modelCategoryQuillen.I.rlp p) {a b c : X ⟶ X} {q : X ⟶ Y}
    (hab : Homotopy a b) (hbc : Homotopy b c) (hac : Homotopy a c)
    (habp : hab.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ q)
    (hbcp : hbc.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ q)
    (hacp : hac.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ q) :
    Edge.CompStruct hab.edgeIhom hbc.edgeIhom hac.edgeIhom := by
  have c0 : stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry hab.h =
      stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry hac.h := by
    apply yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      ← Homotopy.edgeIhom_edge, ← Homotopy.edgeIhom_edge,
      hab.edgeIhom.src_eq, hac.edgeIhom.src_eq]
  have c1 : stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry hab.h =
      stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry hbc.h := by
    apply yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      ← Homotopy.edgeIhom_edge, ← Homotopy.edgeIhom_edge,
      hab.edgeIhom.tgt_eq, hbc.edgeIhom.src_eq]
  have c2 : stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry hac.h =
      stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry hbc.h := by
    apply yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      ← Homotopy.edgeIhom_edge, ← Homotopy.edgeIhom_edge,
      hac.edgeIhom.tgt_eq, hbc.edgeIhom.tgt_eq]
  set topC : (∂Δ[2] : SSet.{u}) ⟶ (ihom X).obj X :=
    boundary.twoDesc (MonoidalClosed.curry hab.h) (MonoidalClosed.curry hac.h)
      (MonoidalClosed.curry hbc.h) c0 c1 c2 with htopC
  have hw : MonoidalClosed.uncurry topC ≫ p =
      (X ◁ (boundary 2).ι) ≫ (fst X (Δ[2] : SSet.{u}) ≫ q) := by
    rw [htopC]
    apply MonoidalClosed.curry_injective
    rw [MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry,
      MonoidalClosed.curry_natural_left]
    apply boundary.hom_ext_two
    · calc boundary.ι (0 : Fin 3) ≫ (boundary.twoDesc (MonoidalClosed.curry hab.h)
            (MonoidalClosed.curry hac.h) (MonoidalClosed.curry hbc.h) c0 c1 c2 ≫
              (ihom X).map p)
          = MonoidalClosed.curry (hbc.h ≫ p) := by
            rw [← Category.assoc, boundary.twoDesc_ι_zero,
              ← MonoidalClosed.curry_natural_right]
        _ = MonoidalClosed.curry (fst X (Δ[1] : SSet.{u}) ≫ q) := by rw [hbcp]
        _ = boundary.ι (0 : Fin 3) ≫ ((boundary 2).ι ≫
              MonoidalClosed.curry (fst X (Δ[2] : SSet.{u}) ≫ q)) := by
            rw [← Category.assoc, boundary.ι_ι,
              ← MonoidalClosed.curry_natural_left, ← Category.assoc,
              CartesianMonoidalCategory.whiskerLeft_fst]
    · calc boundary.ι (1 : Fin 3) ≫ (boundary.twoDesc (MonoidalClosed.curry hab.h)
            (MonoidalClosed.curry hac.h) (MonoidalClosed.curry hbc.h) c0 c1 c2 ≫
              (ihom X).map p)
          = MonoidalClosed.curry (hac.h ≫ p) := by
            rw [← Category.assoc, boundary.twoDesc_ι_one,
              ← MonoidalClosed.curry_natural_right]
        _ = MonoidalClosed.curry (fst X (Δ[1] : SSet.{u}) ≫ q) := by rw [hacp]
        _ = boundary.ι (1 : Fin 3) ≫ ((boundary 2).ι ≫
              MonoidalClosed.curry (fst X (Δ[2] : SSet.{u}) ≫ q)) := by
            rw [← Category.assoc, boundary.ι_ι,
              ← MonoidalClosed.curry_natural_left, ← Category.assoc,
              CartesianMonoidalCategory.whiskerLeft_fst]
    · calc boundary.ι (2 : Fin 3) ≫ (boundary.twoDesc (MonoidalClosed.curry hab.h)
            (MonoidalClosed.curry hac.h) (MonoidalClosed.curry hbc.h) c0 c1 c2 ≫
              (ihom X).map p)
          = MonoidalClosed.curry (hab.h ≫ p) := by
            rw [← Category.assoc, boundary.twoDesc_ι_two,
              ← MonoidalClosed.curry_natural_right]
        _ = MonoidalClosed.curry (fst X (Δ[1] : SSet.{u}) ≫ q) := by rw [habp]
        _ = boundary.ι (2 : Fin 3) ≫ ((boundary 2).ι ≫
              MonoidalClosed.curry (fst X (Δ[2] : SSet.{u}) ≫ q)) := by
            rw [← Category.assoc, boundary.ι_ι,
              ← MonoidalClosed.curry_natural_left, ← Category.assoc,
              CartesianMonoidalCategory.whiskerLeft_fst]
  have hpMono := rlp_monomorphisms_of_rlp_I hp
  have : Mono (X ◁ (boundary 2).ι) := mono_whiskerLeft_boundary_two_ι
  have : HasLiftingProperty (X ◁ (boundary 2).ι) p :=
    hpMono _ (MorphismProperty.monomorphisms.infer_property _)
  let sq : CommSq (MonoidalClosed.uncurry topC) (X ◁ (boundary 2).ι) p
      (fst X (Δ[2] : SSet.{u}) ≫ q) := ⟨hw⟩
  have hιK : (boundary 2).ι ≫ MonoidalClosed.curry sq.lift = topC := by
    rw [← MonoidalClosed.curry_natural_left, sq.fac_left,
      MonoidalClosed.curry_uncurry]
  have face2 : stdSimplex.δ (2 : Fin 3) ≫ MonoidalClosed.curry sq.lift =
      MonoidalClosed.curry hab.h := by
    calc stdSimplex.δ (2 : Fin 3) ≫ MonoidalClosed.curry sq.lift
        = boundary.ι (2 : Fin 3) ≫ ((boundary 2).ι ≫
            MonoidalClosed.curry sq.lift) := by
          rw [← boundary.ι_ι, Category.assoc]
      _ = boundary.ι (2 : Fin 3) ≫ topC := by rw [hιK]
      _ = MonoidalClosed.curry hab.h := by rw [htopC, boundary.twoDesc_ι_two]
  have face0 : stdSimplex.δ (0 : Fin 3) ≫ MonoidalClosed.curry sq.lift =
      MonoidalClosed.curry hbc.h := by
    calc stdSimplex.δ (0 : Fin 3) ≫ MonoidalClosed.curry sq.lift
        = boundary.ι (0 : Fin 3) ≫ ((boundary 2).ι ≫
            MonoidalClosed.curry sq.lift) := by
          rw [← boundary.ι_ι, Category.assoc]
      _ = boundary.ι (0 : Fin 3) ≫ topC := by rw [hιK]
      _ = MonoidalClosed.curry hbc.h := by rw [htopC, boundary.twoDesc_ι_zero]
  have face1 : stdSimplex.δ (1 : Fin 3) ≫ MonoidalClosed.curry sq.lift =
      MonoidalClosed.curry hac.h := by
    calc stdSimplex.δ (1 : Fin 3) ≫ MonoidalClosed.curry sq.lift
        = boundary.ι (1 : Fin 3) ≫ ((boundary 2).ι ≫
            MonoidalClosed.curry sq.lift) := by
          rw [← boundary.ι_ι, Category.assoc]
      _ = boundary.ι (1 : Fin 3) ≫ topC := by rw [hιK]
      _ = MonoidalClosed.curry hac.h := by rw [htopC, boundary.twoDesc_ι_one]
  exact Edge.CompStruct.mk (yonedaEquiv (MonoidalClosed.curry sq.lift))
    (by rw [Homotopy.edgeIhom_edge, ← stdSimplex.yonedaEquiv_δ_comp, face2])
    (by rw [Homotopy.edgeIhom_edge, ← stdSimplex.yonedaEquiv_δ_comp, face0])
    (by rw [Homotopy.edgeIhom_edge, ← stdSimplex.yonedaEquiv_δ_comp, face1])

namespace Homotopy

variable {a b : X ⟶ X}

/-- **Inverse data for the edge classified by a homotopy over a trivial
fibration.** If `H : SSet.Homotopy a b` and a reverse homotopy both lie over
the trivial Kan fibration `p` with bottom `a ≫ p`, then the edge of
`Fun(X, X)` classified by `H` has an `SSet.Edge.InvStruct` with inverse the
edge classified by the reverse homotopy. -/
noncomputable def edgeIhom_invStruct_of_over (hp : modelCategoryQuillen.I.rlp p)
    (H : Homotopy a b) (Hrev : Homotopy b a)
    (hH : H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))
    (hHrev : Hrev.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p)) :
    H.edgeIhom.InvStruct := by
  have habp : b ≫ p = a ≫ p := by
    calc b ≫ p = (SSet.ι₁ ≫ H.h) ≫ p := by rw [H.h₁]
      _ = SSet.ι₁ ≫ (fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p)) := by
          rw [Category.assoc, hH]
      _ = a ≫ p := by
          rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  have hRa : (reflH a).h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p) := by
    rw [Homotopy.reflH_h, Category.assoc]
  have hRb : (reflH b).h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (b ≫ p) := by
    rw [Homotopy.reflH_h, Category.assoc]
  have hH' : H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (b ≫ p) := by
    rw [habp]; exact hH
  have hHrev' : Hrev.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (b ≫ p) := by
    rw [habp]; exact hHrev
  refine ⟨Hrev.edgeIhom,
    (compStruct_edgeIhom_of_homotopies_over hp H Hrev (reflH a) hH hHrev
      hRa).ofEq rfl rfl (congrArg Edge.edge (edgeIhom_reflH a)),
    (compStruct_edgeIhom_of_homotopies_over hp Hrev H (reflH b) hHrev' hH'
      hRb).ofEq rfl rfl (congrArg Edge.edge (edgeIhom_reflH b))⟩

/-- **The component isomorphism of the precomposition transformation.** At
every vertex of `Fun(X, C)`, the component edge is an isomorphism in the
homotopy category, with inverse from the transported `InvStruct`. -/
noncomputable def hoPreCompIso (H : Homotopy a b)
    (I : H.edgeIhom.InvStruct) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    HomotopyCategory.mk (((pre a).app C).app _ x) ≅
      HomotopyCategory.mk (((pre b).app C).app _ x) where
  hom := HomotopyCategory.homMk (H.hoPreCompEdge C x)
  inv := HomotopyCategory.homMk
    ((I.map ((ihom X).map ((ihomVertexEquiv X C).symm x))).ofEq
      ((edgeIhom_map_ihomMap_edge H _).trans
        (Homotopy.hoPreCompEdge_edge H C x).symm)).inv
  hom_inv_id := by
    rw [HomotopyCategory.homMk_comp_homMk
      ((I.map ((ihom X).map ((ihomVertexEquiv X C).symm x))).ofEq
        ((edgeIhom_map_ihomMap_edge H _).trans
          (Homotopy.hoPreCompEdge_edge H C x).symm)).homInvId,
      HomotopyCategory.homMk_id]
  inv_hom_id := by
    rw [HomotopyCategory.homMk_comp_homMk
      ((I.map ((ihom X).map ((ihomVertexEquiv X C).symm x))).ofEq
        ((edgeIhom_map_ihomMap_edge H _).trans
          (Homotopy.hoPreCompEdge_edge H C x).symm)).invHomId,
      HomotopyCategory.homMk_id]

end Homotopy

/-- **Homotopies over a trivial fibration induce a natural isomorphism of
precomposition functors.** If `H : SSet.Homotopy a b` and a reverse homotopy
both lie over the trivial Kan fibration `p` with bottom `a ≫ p`, then for
every simplicial set `C` the functors `h Fun(a, C)` and `h Fun(b, C)` are
naturally isomorphic, with components the morphisms represented by
`Homotopy.hoPreCompEdge`. This is the missing lemma the additional comparison obligation. -/
noncomputable def hoPreNatIso_of_homotopy_over_of_rlp_I {p : X ⟶ Y}
    (hp : modelCategoryQuillen.I.rlp p) {a b : X ⟶ X}
    (H : Homotopy a b) (Hrev : Homotopy b a)
    (hH : H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))
    (hHrev : Hrev.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p)) (C : SSet.{u}) :
    (hoFunctor.map ((pre a).app C)).toFunctor ≅
      (hoFunctor.map ((pre b).app C)).toFunctor :=
  Truncated.HomotopyCategory.mkNatIso (V := (truncation 2).obj ((ihom X).obj C))
    (fun x => H.hoPreCompIso
      (H.edgeIhom_invStruct_of_over hp Hrev hH hHrev) C x)
    (by
      intro x y e
      exact H.hoPre_square C (Edge.ofTruncated e))

/-- The components of `SSet.hoPreNatIso_of_homotopy_over_of_rlp_I` at a
vertex are the morphisms represented by the postcomposed `edgeIhom` edges. -/
lemma hoPreNatIso_of_homotopy_over_of_rlp_I_hom_app_mk {p : X ⟶ Y}
    (hp : modelCategoryQuillen.I.rlp p) {a b : X ⟶ X}
    (H : Homotopy a b) (Hrev : Homotopy b a)
    (hH : H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))
    (hHrev : Hrev.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p)) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    (hoPreNatIso_of_homotopy_over_of_rlp_I hp H Hrev hH hHrev C).hom.app
        (HomotopyCategory.mk x) =
      HomotopyCategory.homMk (H.hoPreCompEdge C x) :=
  rfl

/-- **A trivial Kan fibration is a Joyal categorical equivalence.** The
section and coherent homotopies over `p` from
`SSet.exists_section_and_homotopies_of_rlp_I` feed
`SSet.hoPreNatIso_of_homotopy_over_of_rlp_I` and the assembly
`SSet.categoricalEquivalences.of_section_of_hoPre_id_natIso`. -/
theorem categoricalEquivalences.of_rlp_I {p : X ⟶ Y}
    (hp : modelCategoryQuillen.I.rlp p) : categoricalEquivalences p := by
  obtain ⟨s, hs, ⟨H₁, hH₁⟩, ⟨H₂, hH₂⟩⟩ :=
    exists_section_and_homotopies_of_rlp_I hp
  apply categoricalEquivalences.of_section_of_hoPre_id_natIso hs
  intro C _
  have hH₁' : H₁.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ ((𝟙 X) ≫ p) := by
    rw [Category.id_comp]; exact hH₁
  have hH₂' : H₂.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ ((𝟙 X) ≫ p) := by
    rw [Category.id_comp]; exact hH₂
  exact ⟨(eqToIso (hoFunctor_pre_id C)).symm ≪≫
    hoPreNatIso_of_homotopy_over_of_rlp_I hp H₁ H₂ hH₁' hH₂' C⟩

/-- **Trivial Kan fibrations are Joyal categorical equivalences**: the target
inclusion of the supporting results, closed by
`SSet.categoricalEquivalences.of_rlp_I`. -/
theorem modelCategoryQuillen_I_rlp_le_categoricalEquivalences :
    modelCategoryQuillen.I.rlp ≤ categoricalEquivalences.{u} := by
  intro P Q f hf
  exact categoricalEquivalences.of_rlp_I hf

end SSet
