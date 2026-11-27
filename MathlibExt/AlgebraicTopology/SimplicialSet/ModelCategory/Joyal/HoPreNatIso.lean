/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
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
# Homotopies and precomposition on functor homotopy categories

Let X,C be simplicial sets in universe u, and let f,g:X→X be endomorphisms. A homotopy H:f≃g has
H:X⊗Δ[1]→X with endpoints f,g. For every C, precomposition by f,g gives endofunctors F_f,F_g of
ho(C^X). The edge obtained by postcomposing H with each map X→C supplies a natural
transformation F_f→F_g.

Let p:X→Y in universe u lift every boundary inclusion. For a,b:X→X, let H:a≃b and Hrev:b≃a
satisfy H≫p=pr_X≫a≫p and Hrev≫p=pr_X≫a≫p. These two homotopies give inverse composition
triangles in X^X. The induced transformation is therefore a natural isomorphism on ho(C^X) for
every C. Applying this construction to a section of p proves that boundary-lifting maps are
categorical equivalences.

References: A. Joyal, The Theory of Quasi-Categories and its Applications; J. Lurie, Higher
Topos Theory, §2.2.5.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {X Y Z C : SSet.{u}}

/-!
## Tensor edges and cylinder homotopies

The tensor product of two edges and their composition triangles gives a commuting square in the
homotopy category. A cylinder map X⊗Δ[1]→C corresponds by currying to an edge of C^X, whose
endpoints are its restrictions at interval vertices 0 and 1.
-/

/-!
## Endpoint maps and currying

The coface δ₁ selects vertex 0 of Δ[1], and δ₀ selects vertex 1. Currying a cylinder map
therefore sends these cofaces to the vertices represented by its 0- and 1-end maps.
-/

/-- In simplicial-set universe u, δ₁:Δ[0]→Δ[1] is the Yoneda map represented by geometric vertex 0
of Δ[1]. -/
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

/-- In simplicial-set universe u, δ₀:Δ[0]→Δ[1] is the Yoneda map represented by geometric vertex 1
of Δ[1]. -/
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

/-- For X,C in universe u and K:X⊗Δ[1]→C, the δ₁ face of the edge represented by curry(K) is the
vertex of C^X classified by ι₀≫K:X→C. -/
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

/-- For X,C in universe u and K:X⊗Δ[1]→C, the δ₀ face of the edge represented by curry(K) is the
vertex of C^X classified by ι₁≫K:X→C. -/
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

/-- For X,C in universe u and an edge e:x→y of C^X, uncurrying its representing Δ[1]→C^X gives a
homotopy m_x≃m_y, where m_x,m_y:X→C are the maps classified by its endpoint vertices. -/
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

/-- For A,B in universe u and a one-simplex p=(p_A,p_B) of A⊗B, its represented map Δ[1]→A⊗B is the
pairing of the represented maps Δ[1]→A and Δ[1]→B of p_A,p_B. -/
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

/-- In simplicial-set universe u, the identity map of Δ[1] represents its edge from geometric vertex
0 to geometric vertex 1. -/
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
## Component edges for precomposition

At a vertex of C^X represented by m:X→C, the component associated to H:f≃g is the edge
represented by H followed by m, from f≫m to g≫m.
-/

/-- For X,C in universe u, ψ:X→X and a vertex x of C^X represented by m_x:X→C, precomposition by ψ
sends x to the vertex classified by ψ≫m_x. -/
lemma ihomVertex_pre_apply {ψ : X ⟶ X} (x : ((ihom X).obj C) _⦋0⦌) :
    ihomVertexEquiv X C (ψ ≫ (ihomVertexEquiv X C).symm x) =
      ((pre ψ).app C).app _ x := by
  rw [← ihomVertexEquiv_pre_app, Equiv.apply_symm_apply]

namespace Homotopy

variable {f g : X ⟶ X}

/-- Let X,C be simplicial sets in universe u, and let f,g:X→X be endomorphisms. A homotopy H:f≃g has
H:X⊗Δ[1]→X with endpoints f,g. For a vertex x of C^X represented by m_x:X→C, postcomposing H by
m_x gives the component edge F_f(x)→F_g(x), with endpoints classified by f≫m_x and g≫m_x. -/
noncomputable def hoPreCompEdge (H : Homotopy f g) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    Edge (((pre f).app C).app _ x) (((pre g).app C).app _ x) :=
  (H.postcomp ((ihomVertexEquiv X C).symm x)).edgeIhom.ofEq
    (ihomVertex_pre_apply x) (ihomVertex_pre_apply x)

/-- Let X,C be simplicial sets in universe u, and let f,g:X→X be endomorphisms. A homotopy H:f≃g has
H:X⊗Δ[1]→X with endpoints f,g. At x represented by m_x:X→C, the one-simplex underlying the
component edge is the edge represented by the cylinder H≫m_x, with its canonical precomposition
endpoint identifications. -/
lemma hoPreCompEdge_edge (H : Homotopy f g) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    (H.hoPreCompEdge C x).edge =
      (H.postcomp ((ihomVertexEquiv X C).symm x)).edgeIhom.edge :=
  rfl

end Homotopy

/-!
## Faces of a two-parameter prism

Given H:X⊗Δ[1]→X and K:X⊗Δ[1]→C, the prism (α_{X,Δ[1],Δ[1]})⁻¹≫(H⊗id)≫K has four sides obtained
by fixing either interval coordinate. These sides express postcomposition of H and
precomposition of K.
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
## Naturality of the component edge morphisms

For an edge e:m₀→m₁ of C^X, its precomposition image under f followed by the H-component at m₁
equals the H-component at m₀ followed by its precomposition image under g, as morphisms in
ho(C^X).
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

/-- Let X,C be simplicial sets in universe u, and let f,g:X→X be endomorphisms. A homotopy H:f≃g has
H:X⊗Δ[1]→X with endpoints f,g. For an edge e:x→y in C^X and component morphisms η_x,η_y
represented by H, F_f([e])≫η_y=η_x≫F_g([e]) in ho(C^X). -/
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

/-- Let X,C be simplicial sets in universe u, and let f,g:X→X be endomorphisms. A homotopy H:f≃g has
H:X⊗Δ[1]→X with endpoints f,g. The component edges formed by H followed by each represented map
X→C give a natural transformation F_f→F_g of endofunctors of ho(C^X). -/
noncomputable def hoPreNatTrans (H : Homotopy f g) (C : SSet.{u}) :
    (hoFunctor.map ((pre f).app C)).toFunctor ⟶
      (hoFunctor.map ((pre g).app C)).toFunctor :=
  Truncated.HomotopyCategory.mkNatTrans (V := (truncation 2).obj ((ihom X).obj C))
    (fun x => HomotopyCategory.homMk (H.hoPreCompEdge C x))
    (by
      intro x y e
      exact H.hoPre_square C (Edge.ofTruncated e))

/-- Let X,C be simplicial sets in universe u, and let f,g:X→X be endomorphisms. A homotopy H:f≃g has
H:X⊗Δ[1]→X with endpoints f,g. At a vertex object [x] of ho(C^X), the induced natural
transformation has component [H.hoPreCompEdge(C,x)], the morphism represented by the
postcomposed homotopy edge. -/
lemma hoPreNatTrans_app_mk (H : Homotopy f g) (C : SSet.{u})
    (x : ((ihom X).obj C) _⦋0⦌) :
    (H.hoPreNatTrans C).app (HomotopyCategory.mk x) =
      HomotopyCategory.homMk (H.hoPreCompEdge C x) :=
  rfl

end Homotopy

/-!
## Composition and inverse triangles over a boundary-lifting map

Three cylinder homotopies with a common base map can be assembled on X⊗∂Δ[2] and lifted through
p to X⊗Δ[2]. Their curried faces give the composition triangles used to invert a homotopy edge
when a reverse homotopy over p is supplied.
-/

/-- For every X in simplicial-set universe u, id_X⊗(∂Δ[2]→Δ[2]) is a monomorphism X⊗∂Δ[2]→X⊗Δ[2]. -/
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

/-- For p:X→Y in universe u lifting all boundaries, a,b,c:X→X and q:X→Y, suppose homotopies
H_ab,H_bc,H_ac all satisfy H_ij≫p=pr_X≫q. They give a composition triangle in X^X for their
curried edges, with H_ab followed by H_bc composing to H_ac. -/
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

/-- Let p:X→Y in universe u lift every boundary inclusion. For a,b:X→X, let H:a≃b and Hrev:b≃a
satisfy H≫p=pr_X≫a≫p and Hrev≫p=pr_X≫a≫p. The curried edge of H in X^X has inverse data, with
inverse the curried edge of Hrev and two composition triangles to the identity edges. -/
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

/-- For X,C in universe u, H:a≃b between endomorphisms of X and inverse data for its curried edge in
X^X, each vertex x of C^X gives an isomorphism F_a([x])≅F_b([x]) in ho(C^X). Its hom is
represented by the H-component edge. -/
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

/-- Let p:X→Y in universe u lift every boundary inclusion. For a,b:X→X, let H:a≃b and Hrev:b≃a
satisfy H≫p=pr_X≫a≫p and Hrev≫p=pr_X≫a≫p. For every simplicial set C in universe u,
precomposition by a and b gives naturally isomorphic endofunctors F_a≅F_b of ho(C^X). -/
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

/-- Let p:X→Y in universe u lift every boundary inclusion. For a,b:X→X, let H:a≃b and Hrev:b≃a
satisfy H≫p=pr_X≫a≫p and Hrev≫p=pr_X≫a≫p. At a vertex object [x] of ho(C^X), the hom component
of F_a≅F_b is the morphism represented by the edge of H postcomposed with the map X→C classified
by x. -/
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

/-- For p:X→Y in universe u lifting every ∂Δ[n]→Δ[n], n≥0, precomposition ho(C^Y)→ho(C^X) is an
equivalence for every quasicategory C in that universe. Thus p is a categorical equivalence. -/
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

/-- In every simplicial-set universe u, the class of maps lifting all boundary inclusions
∂Δ[n]→Δ[n], n≥0, is contained in the class of categorical equivalences tested by
quasicategory-target precomposition functors. -/
theorem modelCategoryQuillen_I_rlp_le_categoricalEquivalences :
    modelCategoryQuillen.I.rlp ≤ categoricalEquivalences.{u} := by
  intro P Q f hf
  exact categoricalEquivalences.of_rlp_I hf

end SSet
