/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveData
public import MathlibExt.CategoryTheory.ComposableArrows.Opposite
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRevToSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso

/-!
# Nerve of an opposite category via simplex reversal

Degreewise equivalence `ComposableArrows Cᵒᵖ n ≃ ComposableArrows C n`
via `ComposableArrows.unop`/`ComposableArrows.op`, promoted to a simplicial
`Data` isomorphism `nerveData Cᵒᵖ ≅ Data.rev (nerveData C)` and to a genuine
simplicial isomorphism `nerve Cᵒᵖ ≅ opFunctor.obj (nerve C)`.

References (orientation only; no exact proposition correspondence is claimed):
Goerss–Jardine, *Simplicial Homotopy Theory*
(https://link.springer.com/book/10.1007/978-3-0348-8707-6), for nerve/opposite
background.

Source-to-Lean map: the classical reversal `nerve (𝒞ᵒᵖ) ≅ rev (nerve 𝒞)` is
`nerveOppositeSimplicialIso` against `SimplicialObject.opFunctor`.

Nonclaims: no comma/category-of-elements/Grothendieck comparison, no bar
comparison, no contraction, no homotopy, no realization, and no KQ consequence.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory

/-- Heterogeneous equality of `homOfLE` maps under endpoint equalities. -/
private theorem nerveOpposite_homOfLE_heq {n : ℕ} {a b c d : Fin (n + 1)}
    (ha : a = c) (hb : b = d) (h1 : a ≤ b) (h2 : c ≤ d) :
    (homOfLE h1 : a ⟶ b) ≍ (homOfLE h2 : c ⟶ d) := by
  subst ha
  subst hb
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Degreewise equivalence between composable arrows in `Cᵒᵖ` and in `C`,
via `unop`/`op`. -/
noncomputable def nerveOppositeEquiv (C : Type u) [Category.{v} C] (n : ℕ) :
    ComposableArrows Cᵒᵖ n ≃ ComposableArrows C n where
  toFun := ComposableArrows.unop
  invFun := ComposableArrows.op
  left_inv S := by
    have h_obj : ∀ i, (S.unop.op).obj i = S.obj i := fun i => by simp
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    refine (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).mpr ?_
    simp only [ComposableArrows.map', ComposableArrows.op_map,
      ComposableArrows.unop_map]
    have e1 : (⟨i, by omega⟩ : Fin (n + 1)).rev.rev = ⟨i, by omega⟩ :=
      Fin.rev_rev _
    have e2 : (⟨i + 1, by omega⟩ : Fin (n + 1)).rev.rev = ⟨i + 1, by omega⟩ :=
      Fin.rev_rev _
    congr 1
    case e_3 => simp only [ComposableArrows.unop_obj, Fin.rev_rev]
    case e_4 => simp only [ComposableArrows.unop_obj, Fin.rev_rev]
    case e_5 =>
      congr 1
      case e_3 => simp only [Fin.rev_rev]
      case e_4 => simp only [Fin.rev_rev]
      case e_5 =>
        congr 1
        exact nerveOpposite_homOfLE_heq e1 e2 _ _
  right_inv S := by
    have h_obj : ∀ i, (S.op.unop).obj i = S.obj i := fun i => by simp
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    refine (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).mpr ?_
    simp only [ComposableArrows.map', ComposableArrows.op_map,
      ComposableArrows.unop_map]
    have e1 : (⟨i, by omega⟩ : Fin (n + 1)).rev.rev = ⟨i, by omega⟩ :=
      Fin.rev_rev _
    have e2 : (⟨i + 1, by omega⟩ : Fin (n + 1)).rev.rev = ⟨i + 1, by omega⟩ :=
      Fin.rev_rev _
    congr 1
    case e_3 => simp only [ComposableArrows.op_obj, Fin.rev_rev]
    case e_4 => simp only [ComposableArrows.op_obj, Fin.rev_rev]
    case e_5 =>
      congr 1
      case e_3 => simp only [Fin.rev_rev]
      case e_4 => simp only [Fin.rev_rev]
      case e_5 =>
        congr 1
        exact nerveOpposite_homOfLE_heq e1 e2 _ _

/-- Face compatibility for the `Data` isomorphism. -/
theorem nerveOpposite_face_compat (C : Type u) [Category.{v} C] {n : ℕ}
    (i : Fin (n + 2)) :
    (Equiv.toIso (nerveOppositeEquiv C (n + 1))).hom ≫
        (SimplicialObject.Data.rev (nerveData C)).δ i =
      (nerveData Cᵒᵖ).δ i ≫ (Equiv.toIso (nerveOppositeEquiv C n)).hom := by
  ext S
  change (nerve C).δ i.rev (S.unop) = (((nerve Cᵒᵖ).δ i) S).unop
  have h_obj : ∀ (j : Fin (n + 1)),
      ((nerve C).δ i.rev (S.unop)).obj j =
        ((((nerve Cᵒᵖ).δ i) S).unop).obj j := fun j => by
    change Opposite.unop (S.obj ((i.rev.succAbove j).rev)) =
      Opposite.unop (S.obj (i.succAbove j.rev))
    simp only [Fin.rev_succAbove, Fin.rev_rev]
  refine ComposableArrows.ext h_obj (fun k hk => ?_)
  refine (conj_eqToHom_iff_heq _ _
    (h_obj ⟨k, lt_of_lt_of_le (hk : k < n) (Nat.le_succ n)⟩)
    (h_obj ⟨k + 1, Nat.succ_lt_succ (hk : k < n)⟩)).mpr ?_
  have keyS : ∀ {a b c d : Fin (n + 2)} (ha : a = c) (hb : b = d)
      {f : a ⟶ b} {g : c ⟶ d},
      (S.map f).unop ≍ (S.map g).unop := by
    intro a b c d ha hb f g
    subst ha
    subst hb
    exact heq_of_eq (congrArg Quiver.Hom.unop (congrArg (S.map) (Subsingleton.elim _ _)))
  have hrev : ∀ (j : Fin (n + 1)),
      Fin.rev ((i.rev).succAbove j) = i.succAbove j.rev := by
    intro j
    rw [Fin.rev_succAbove, Fin.rev_rev]
  exact keyS (hrev ⟨k + 1, Nat.succ_lt_succ (hk : k < n)⟩)
    (hrev ⟨k, lt_of_lt_of_le (hk : k < n) (Nat.le_succ n)⟩)

/-- Degeneracy compatibility for the `Data` isomorphism. -/
theorem nerveOpposite_degeneracy_compat (C : Type u) [Category.{v} C]
    {n : ℕ} (i : Fin (n + 1)) :
    (Equiv.toIso (nerveOppositeEquiv C n)).hom ≫
        (SimplicialObject.Data.rev (nerveData C)).σ i =
      (nerveData Cᵒᵖ).σ i ≫ (Equiv.toIso (nerveOppositeEquiv C (n + 1))).hom := by
  ext S
  change (nerve C).σ i.rev (S.unop) = (((nerve Cᵒᵖ).σ i) S).unop
  have h_obj : ∀ (j : Fin (n + 2)),
      ((nerve C).σ i.rev (S.unop)).obj j =
        ((((nerve Cᵒᵖ).σ i) S).unop).obj j := fun j => by
    change Opposite.unop (S.obj ((i.rev.predAbove j).rev)) =
      Opposite.unop (S.obj (i.predAbove j.rev))
    simp only [Fin.rev_predAbove, Fin.rev_rev]
  refine ComposableArrows.ext h_obj (fun k hk => ?_)
  refine (conj_eqToHom_iff_heq _ _
    (h_obj ⟨k, lt_of_lt_of_le (hk : k < n + 1) (Nat.le_succ (n + 1))⟩)
    (h_obj ⟨k + 1, Nat.succ_lt_succ (hk : k < n + 1)⟩)).mpr ?_
  have keyS : ∀ {a b c d : Fin (n + 1)} (ha : a = c) (hb : b = d)
      {f : a ⟶ b} {g : c ⟶ d},
      (S.map f).unop ≍ (S.map g).unop := by
    intro a b c d ha hb f g
    subst ha
    subst hb
    exact heq_of_eq (congrArg Quiver.Hom.unop (congrArg (S.map) (Subsingleton.elim _ _)))
  have hrev : ∀ (j : Fin (n + 2)),
      Fin.rev ((i.rev).predAbove j) = i.predAbove j.rev := by
    intro j
    rw [Fin.rev_predAbove, Fin.rev_rev]
  exact keyS (hrev ⟨k + 1, Nat.succ_lt_succ (hk : k < n + 1)⟩)
    (hrev ⟨k, lt_of_lt_of_le (hk : k < n + 1) (Nat.le_succ (n + 1))⟩)

/-- Simplicial `Data` isomorphism between `nerveData Cᵒᵖ` and reversed nerve data. -/
noncomputable def nerveOppositeDataIso (C : Type u) [Category.{v} C] :
    nerveData Cᵒᵖ ≅ SimplicialObject.Data.rev (nerveData C) :=
  SimplicialObject.Data.isoOfIso (fun n => Equiv.toIso (nerveOppositeEquiv C n))
    (fun i => nerveOpposite_face_compat C i)
    (fun i => nerveOpposite_degeneracy_compat C i)

/-- Genuine simplicial isomorphism between `nerve Cᵒᵖ` and reversed `nerve C`. -/
noncomputable def nerveOppositeSimplicialIso (C : Type u) [Category.{v} C] :
    nerve Cᵒᵖ ≅ SimplicialObject.opFunctor.obj (nerve C) :=
  (nerveDataSimplicialIso Cᵒᵖ).symm.trans
    ((SimplicialObject.Data.toSimplicialFunctor.mapIso (nerveOppositeDataIso C)).trans
      ((SimplicialObject.Data.toSimplicialObject_revIso (nerveData C)).trans
        (SimplicialObject.opFunctor.mapIso (nerveDataSimplicialIso C))))

/-- Forward component of `nerveOppositeSimplicialIso` at `op (mk n)`.

Pointwise, the forward map sends a composable arrow in `Cᵒᵖ` to its
underlying arrow in `C` via `ComposableArrows.unop`. -/
@[simp]
theorem nerveOppositeSimplicialIso_hom_app_mk (C : Type u) [Category.{v} C]
    (n : ℕ) (S : ComposableArrows Cᵒᵖ n) :
    ((nerveOppositeSimplicialIso C).hom.app
      (Opposite.op (SimplexCategory.mk n))) S = S.unop :=
  rfl

/-- Inverse component of `nerveOppositeSimplicialIso` at `op (mk n)`.

Pointwise, the inverse map sends a composable arrow in `C` to its opposite
arrow in `Cᵒᵖ` via `ComposableArrows.op`. -/
@[simp]
theorem nerveOppositeSimplicialIso_inv_app_mk (C : Type u) [Category.{v} C]
    (n : ℕ) (S : ComposableArrows C n) :
    ((nerveOppositeSimplicialIso C).inv.app
      (Opposite.op (SimplexCategory.mk n))) S = S.op :=
  rfl

end CategoryTheory
