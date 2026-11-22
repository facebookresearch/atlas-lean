/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.ZerothRow
public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-!
# The raw core/function Gamma diagram

Outer degree `m` is `core(Q^Δ[m])`. All core and vertex operations are
unconditional; Kan/CSS fibrancy and weak replacement are separate results.
The map from the discrete embedding is obtained from the actual zeroth-row
adjunction, not from a second extension construction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
noncomputable section
universe u
open CategoryTheory Opposite MonoidalClosed
open scoped Simplicial

namespace SSet.Rezk

/-- The core/function diagram, natural in every raw simplicial set. -/
abbrev gammaDiagram : SSet.{u} ⥤ SimplicialObject SSet.{u} where
  obj Q :=
    { obj := fun m => (core ((ihom (stdSimplex.obj m.unop)).obj Q) : SSet.{u})
      map := fun a => core.map ((pre (stdSimplex.map a.unop)).app Q)
      map_id := by intro m; simp
      map_comp := by intro m n p a b; simp [pre_map] }
  map q :=
    { app := fun m => core.map ((ihom (stdSimplex.obj m.unop)).map q)
      naturality := by
        intro m n a
        rw [← core.map_comp, ← core.map_comp]
        exact congrArg core.map (pre_comm_ihom_map (stdSimplex.map a.unop) q) }
  map_id := by intro Q; ext m; simp
  map_comp := by intro Q Q' Q'' q r; ext m; simp

/-- The outer operator is literal function restriction followed by core. -/
@[simp]
lemma gammaDiagram_obj_map (Q : SSet.{u}) {m n : SimplexCategoryᵒᵖ}
    (a : m ⟶ n) :
    (gammaDiagram.obj Q).map a = core.map ((pre (stdSimplex.map a.unop)).app Q) := rfl

/-- A raw target map acts by literal postcomposition followed by core. -/
@[simp]
lemma gammaDiagram_map_app {Q Q' : SSet.{u}} (q : Q ⟶ Q')
    (m : SimplexCategoryᵒᵖ) :
    (gammaDiagram.map q).app m = core.map ((ihom (stdSimplex.obj m.unop)).map q) := rfl

private def coreVertexEquiv (X : SSet.{u}) :
    (core X : SSet.{u}) _⦋0⦌ ≃ X _⦋0⦌ where
  toFun x := x.1
  invFun x := ⟨x, mem_core_obj_zero x⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv _ := rfl

private def rowEquiv (Q : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    (zerothRow.obj (gammaDiagram.obj Q)).obj m ≃ Q.obj m :=
  (coreVertexEquiv _).trans ((ihomVertexEquiv _ Q).symm.trans yonedaEquiv)

private lemma core_map_vertex {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : (core X : SSet.{u}) _⦋0⦌) :
    ((core.map f).app (op ⦋0⦌) x).1 = f.app (op ⦋0⦌) x.1 := by
  exact ConcreteCategory.congr_hom (congr_app (core.map_ι f) (op ⦋0⦌)) x

private lemma rowEquiv_apply (Q : SSet.{u}) (m : SimplexCategoryᵒᵖ)
    (f : stdSimplex.obj m.unop ⟶ Q) :
    rowEquiv Q m ⟨ihomVertexEquiv _ Q f, mem_core_obj_zero _⟩ = yonedaEquiv f := by
  exact congrArg yonedaEquiv ((ihomVertexEquiv _ Q).symm_apply_apply f)

/-- The canonical natural isomorphism from Gamma's zeroth row to the original set. -/
def gammaZerothRowIso : gammaDiagram.{u} ⋙ zerothRow.{u} ≅ 𝟭 SSet.{u} :=
  NatIso.ofComponents (fun Q => NatIso.ofComponents
    (fun m => (rowEquiv Q m).toIso)
    (by
      intro m n a
      apply ConcreteCategory.hom_ext
      intro x
      change rowEquiv Q n ((core.map ((pre (stdSimplex.map a.unop)).app Q)).app _ x) =
        Q.map a ((rowEquiv Q m) x)
      obtain ⟨f, hf⟩ := (ihomVertexEquiv (stdSimplex.obj m.unop) Q).surjective x.1
      have hsub : x = ⟨ihomVertexEquiv _ _ f, mem_core_obj_zero _⟩ := by
        apply Subtype.ext
        exact hf.symm
      subst x
      have hx : (core.map ((pre (stdSimplex.map a.unop)).app Q)).app (op ⦋0⦌)
          ⟨ihomVertexEquiv _ Q f, mem_core_obj_zero _⟩ =
          ⟨ihomVertexEquiv _ Q (stdSimplex.map a.unop ≫ f), mem_core_obj_zero _⟩ := by
        apply Subtype.ext
        rw [core_map_vertex, ihomVertexEquiv_pre_app]
      rw [hx, rowEquiv_apply, rowEquiv_apply]
      exact (yonedaEquiv_naturality a.unop f).symm))
    (by
      intro Q Q' q
      ext m x
      change rowEquiv Q' m ((core.map ((ihom (stdSimplex.obj m.unop)).map q)).app _ x) =
        q.app m (rowEquiv Q m x)
      obtain ⟨f, hf⟩ := (ihomVertexEquiv (stdSimplex.obj m.unop) Q).surjective x.1
      have hsub : x = ⟨ihomVertexEquiv _ _ f, mem_core_obj_zero _⟩ := by
        apply Subtype.ext
        exact hf.symm
      subst x
      have hx : (core.map ((ihom (stdSimplex.obj m.unop)).map q)).app (op ⦋0⦌)
          ⟨ihomVertexEquiv _ Q f, mem_core_obj_zero _⟩ =
          ⟨ihomVertexEquiv _ Q' (f ≫ q), mem_core_obj_zero _⟩ := by
        apply Subtype.ext
        rw [core_map_vertex, ihomVertexEquiv_ihom_map]
      rw [hx, rowEquiv_apply, rowEquiv_apply]
      exact yonedaEquiv_comp f q)

/-- Gamma's unit map is the adjunct of the inverse canonical row isomorphism. -/
def gammaUnit : simplicialSpaceDiscrete.{u} ⟶ gammaDiagram.{u} where
  app Q := (zerothRowAdjunction.homEquiv Q (gammaDiagram.obj Q)).symm
    (gammaZerothRowIso.inv.app Q)
  naturality := by
    intro Q Q' q
    apply (zerothRowAdjunction.homEquiv Q (gammaDiagram.obj Q')).injective
    rw [zerothRowAdjunction.homEquiv_naturality_left,
      zerothRowAdjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact gammaZerothRowIso.inv.naturality q

/-- The canonical row isomorphism reads the original Yoneda simplex. -/
lemma gammaZerothRowIso_hom_app (Q : SSet.{u}) (m : SimplexCategoryᵒᵖ)
    (f : stdSimplex.obj m.unop ⟶ Q) :
    (gammaZerothRowIso.hom.app Q).app m
      ⟨ihomVertexEquiv _ Q f, mem_core_obj_zero _⟩ = yonedaEquiv f :=
  rowEquiv_apply Q m f

/-- Eta's actual bidegree map is the existing adjunction's inner degeneracy. -/
lemma gammaUnit_app (Q : SSet.{u}) (m n : SimplexCategoryᵒᵖ) :
    ((gammaUnit.app Q).app m).app n =
      (gammaZerothRowIso.inv.app Q).app m ≫
        ((gammaDiagram.obj Q).obj m).map (SimplexCategory.const n.unop ⦋0⦌ 0).op := by
  change (((zerothRowAdjunction.homEquiv Q (gammaDiagram.obj Q)).symm
    (gammaZerothRowIso.inv.app Q)).app m).app n = _
  rw [zerothRowAdjunction.homEquiv_counit]
  change ((simplicialSpaceDiscrete.map (gammaZerothRowIso.inv.app Q)).app m).app n ≫
      ((zerothRowAdjunction.counit.app (gammaDiagram.obj Q)).app m).app n = _
  rw [zerothRowAdjunction_counit_app]
  rfl

private lemma gammaUnit_row (Q : SSet.{u}) :
    zerothRowAdjunction.unit.app Q ≫ zerothRow.map (gammaUnit.app Q) =
      gammaZerothRowIso.inv.app Q := by
  exact (zerothRowAdjunction.homEquiv Q (gammaDiagram.obj Q)).apply_symm_apply _

/-- The original canonical row map followed by phi is the identity. -/
lemma gammaUnit_row_hom (Q : SSet.{u}) :
    zerothRowAdjunction.unit.app Q ≫ zerothRow.map (gammaUnit.app Q) ≫
      gammaZerothRowIso.hom.app Q = 𝟙 Q := by
  calc
    _ = gammaZerothRowIso.inv.app Q ≫ gammaZerothRowIso.hom.app Q :=
      congrArg (fun f => f ≫ gammaZerothRowIso.hom.app Q) (gammaUnit_row Q)
    _ = _ := gammaZerothRowIso.inv_hom_id_app Q

/-- The opposite original row equation also retains the chosen unit identification. -/
lemma gammaUnit_row_inv (Q : SSet.{u}) :
    gammaZerothRowIso.hom.app Q ≫ zerothRowAdjunction.unit.app Q ≫
      zerothRow.map (gammaUnit.app Q) = 𝟙 (zerothRow.obj (gammaDiagram.obj Q)) := by
  calc
    _ = gammaZerothRowIso.hom.app Q ≫ gammaZerothRowIso.inv.app Q :=
      congrArg (fun f => gammaZerothRowIso.hom.app Q ≫ f) (gammaUnit_row Q)
    _ = _ := gammaZerothRowIso.hom_inv_id_app Q

end SSet.Rezk
