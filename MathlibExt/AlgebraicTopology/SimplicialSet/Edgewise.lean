/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Edgewise subdivision of simplicial sets

Edgewise subdivision first appeared in G. Segal, *Configuration-spaces and
iterated loop-spaces*, Invent. Math. 21 (1973), Appendix 1, pp. 213--221,
where Segal attributes the construction to Quillen.
We use the opposite-first convention of F. Waldhausen, *Algebraic K-theory of
spaces*, Lecture Notes in Mathematics 1126 (1985), Section 1.9, pp. 318--419.
The ordinal adapter doubles each simplex with the first block reversed and the
second block straight, sending `⦋n⦌` to `⦋2 * n + 1⦌`. Low degrees compute as
`Q ⦋0⦌ = ⦋1⦌` and `Q ⦋1⦌ = ⦋3⦌`.

The morphism part is the ordinal sum of the reversed map on the first
block with the straight map on the second block, via the pinned
augmented ordinal-sum machinery. Edgewise subdivision `esd` is
precomposition with `edgewiseQ.op`.

The straight/right ordinal-sum inclusion is natural in the simplex, and
contravariant precomposition gives the comparison `esd X ⟶ X`. In degree
zero this selects the target vertex `δ 0` of a one-simplex.

Nonclaims: no realization or weak-equivalence theorem, no outer-bisimplicial
or Stage comparison, no basepoint or pointed-map claim, no additivity, no
homotopy-group or `K₀` identification, no spectra, no Q/S comparison, no
Bloch–Kato work.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u

namespace SimplexCategory

/-- Twisted edgewise ordinal functor `Q : Δ ⥤ Δ`, `⦋n⦌ ↦ ⦋2 * n + 1⦌`.

In `tensorHomOf (rev.map f) f`, the opposite/reversed copy is the first
ordinal-sum block and the ordinary copy is the second. In particular, the
edgewise image of the later `δ 1` has values `0 ↦ 1` and `1 ↦ 2`, fixing the
orientation used by the Quillen `δ₁` face-cell construction. -/
def edgewiseQ : SimplexCategory ⥤ SimplexCategory where
  obj a := AugmentedSimplexCategory.tensorObjOf a a
  map {a b} f :=
    AugmentedSimplexCategory.tensorHomOf (rev.map f) f
  map_id := by
    intro a
    change AugmentedSimplexCategory.tensorHomOf (rev.map (𝟙 a)) (𝟙 a) =
      𝟙 (AugmentedSimplexCategory.tensorObjOf a a)
    rw [CategoryTheory.Functor.map_id]
    exact AugmentedSimplexCategory.tensor_id (WithInitial.of a) (WithInitial.of a)
  map_comp := by
    intro a b c f g
    change AugmentedSimplexCategory.tensorHomOf (rev.map (f ≫ g)) (f ≫ g) =
      AugmentedSimplexCategory.tensorHomOf (rev.map f) f ≫
        AugmentedSimplexCategory.tensorHomOf (rev.map g) g
    rw [CategoryTheory.Functor.map_comp]
    exact (AugmentedSimplexCategory.tensorHom_comp_tensorHom
      (x₁ := WithInitial.of (rev.obj a)) (y₁ := WithInitial.of (rev.obj b))
      (z₁ := WithInitial.of (rev.obj c)) (x₂ := WithInitial.of a)
      (y₂ := WithInitial.of b) (z₂ := WithInitial.of c)
      (rev.map f) f (rev.map g) g).symm

@[simp]
theorem edgewiseQ_map {a b : SimplexCategory} (f : a ⟶ b) :
    edgewiseQ.map f =
      AugmentedSimplexCategory.tensorHomOf (rev.map f) f :=
  rfl

/-- Face inclusion under edgewise subdivision is the ordinal sum of the
reversed inclusion on the first block with the straight inclusion on the
second block. -/
@[simp]
theorem edgewiseQ_map_δ {n : ℕ} (k : Fin (n + 2)) :
    edgewiseQ.map (δ k) =
      AugmentedSimplexCategory.tensorHomOf (δ k.rev) (δ k) := by
  rw [edgewiseQ_map, rev_map_δ]

/-- Degeneracy under edgewise subdivision is the ordinal sum of the
reversed degeneracy on the first block with the straight degeneracy on the
second block. -/
@[simp]
theorem edgewiseQ_map_σ {n : ℕ} (i : Fin (n + 1)) :
    edgewiseQ.map (σ i) =
      AugmentedSimplexCategory.tensorHomOf (σ i.rev) (σ i) := by
  rw [edgewiseQ_map, rev_map_σ]

@[simp]
theorem edgewiseQ_obj (a : SimplexCategory) :
    edgewiseQ.obj a = ⦋2 * a.len + 1⦌ := by
  change AugmentedSimplexCategory.tensorObjOf a a = ⦋2 * a.len + 1⦌
  simp only [AugmentedSimplexCategory.tensorObjOf]
  congr 1
  omega

@[simp]
theorem edgewiseQ_obj_len (a : SimplexCategory) :
    (edgewiseQ.obj a).len = 2 * a.len + 1 := by
  change a.len + a.len + 1 = 2 * a.len + 1
  omega

/-- Low degree `Q ⦋0⦌ = ⦋1⦌`. -/
@[simp]
theorem edgewiseQ_obj_zero : edgewiseQ.obj ⦋0⦌ = ⦋1⦌ :=
  rfl

/-- Low degree `Q ⦋1⦌ = ⦋3⦌`. -/
@[simp]
theorem edgewiseQ_obj_one : edgewiseQ.obj ⦋1⦌ = ⦋3⦌ :=
  rfl

/-- The natural inclusion of the straight/right copy of a simplex into its
opposite-first edgewise ordinal sum. -/
def edgewiseRightInclusion : 𝟭 SimplexCategory ⟶ edgewiseQ where
  app a := AugmentedSimplexCategory.inr' a a
  naturality := by
    intro a b f
    exact (AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of a) (y₁ := WithInitial.of b)
      (x₂ := WithInitial.of a) (y₂ := WithInitial.of b)
      (rev.map f) f).symm

/-- The component of the right inclusion is the augmented ordinal-sum
right-block inclusion. -/
theorem edgewiseRightInclusion_app (a : SimplexCategory) :
    edgewiseRightInclusion.app a = AugmentedSimplexCategory.inr' a a :=
  rfl

/-- The right-block inclusion sends `i` to `a.len + 1 + i`. -/
@[simp]
theorem edgewiseRightInclusion_app_apply_val (a : SimplexCategory)
    (i : Fin (a.len + 1)) :
    ((edgewiseRightInclusion.app a).toOrderHom i).val =
      a.len + 1 + i.val := by
  change ((AugmentedSimplexCategory.inr' a a).toOrderHom i).val = _
  rw [AugmentedSimplexCategory.inr'_eval]
  rfl

/-- In degree zero, the right-block inclusion is the target coface. -/
@[simp]
theorem edgewiseRightInclusion_app_zero :
    edgewiseRightInclusion.app ⦋0⦌ = δ (0 : Fin 2) := by
  ext i
  fin_cases i
  rfl

/-- In degree one, the right-block inclusion successively omits vertices zero
and one, hence is `δ 0 ≫ δ 0`. -/
@[simp]
theorem edgewiseRightInclusion_app_one :
    edgewiseRightInclusion.app ⦋1⦌ =
      δ (0 : Fin 3) ≫ δ (0 : Fin 4) := by
  ext i
  fin_cases i <;> rfl

/-- The first vertex of the degree-one simplex enters at right-block index
two. -/
@[simp]
theorem edgewiseRightInclusion_app_one_apply_zero :
    ((edgewiseRightInclusion.app ⦋1⦌).toOrderHom (0 : Fin 2)).val = 2 := by
  simpa using edgewiseRightInclusion_app_apply_val ⦋1⦌ (0 : Fin 2)

/-- The second vertex of the degree-one simplex enters at right-block index
three. -/
@[simp]
theorem edgewiseRightInclusion_app_one_apply_one :
    ((edgewiseRightInclusion.app ⦋1⦌).toOrderHom (1 : Fin 2)).val = 3 := by
  simpa using edgewiseRightInclusion_app_apply_val ⦋1⦌ (1 : Fin 2)

end SimplexCategory

namespace SSet

/-- Simplicial edgewise subdivision endofunctor by precomposition with
`edgewiseQ.op`. This definition alone makes no realization or weak-equivalence
claim. -/
def esd : SSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.edgewiseQ.op

@[simp]
theorem esd_obj_obj (X : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (esd.obj X).obj n = X.obj (SimplexCategory.edgewiseQ.op.obj n) :=
  rfl

@[simp]
theorem esd_obj_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (esd.obj X).map f = X.map (SimplexCategory.edgewiseQ.op.map f) :=
  rfl

@[simp]
theorem esd_map_app {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (esd.map f).app n = f.app (SimplexCategory.edgewiseQ.op.obj n) :=
  rfl

@[simp]
theorem esd_obj_op_mk (X : SSet.{u}) (n : ℕ) :
    (esd.obj X).obj (Opposite.op ⦋n⦌) = X.obj (Opposite.op ⦋2 * n + 1⦌) := by
  simp [esd, SimplexCategory.edgewiseQ_obj]

/-- Degree zero: `(esd X)₀ = X₁`. -/
@[simp]
theorem esd_zero_eq_one (X : SSet.{u}) :
    (esd.obj X).obj (Opposite.op ⦋0⦌) = X.obj (Opposite.op ⦋1⦌) :=
  esd_obj_op_mk X 0

/-- Degree one: `(esd X)₁ = X₃`. -/
@[simp]
theorem esd_one_eq_three (X : SSet.{u}) :
    (esd.obj X).obj (Opposite.op ⦋1⦌) = X.obj (Opposite.op ⦋3⦌) :=
  esd_obj_op_mk X 1

/-- The canonical comparison from edgewise subdivision to the original
simplicial set, induced by the straight/right ordinal-sum inclusion. -/
def esdComparison : esd.{u} ⟶ 𝟭 SSet.{u} where
  app X :=
    { app := fun a =>
        X.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op
      naturality := by
        intro a b f
        change X.map (SimplexCategory.edgewiseQ.op.map f) ≫
            X.map (SimplexCategory.edgewiseRightInclusion.app b.unop).op =
          X.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op ≫
            X.map f
        rw [← X.map_comp, ← X.map_comp]
        apply congrArg X.map
        apply Quiver.Hom.unop_inj
        exact
          (SimplexCategory.edgewiseRightInclusion.naturality f.unop).symm }
  naturality X Y f := by
    ext a x
    exact ConcreteCategory.congr_hom
      (f.naturality
        (SimplexCategory.edgewiseRightInclusion.app a.unop).op).symm x

/-- Component formula for the edgewise comparison. -/
@[simp]
theorem esdComparison_app_app (X : SSet.{u})
    (a : SimplexCategoryᵒᵖ) :
    (esdComparison.app X).app a =
      X.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op :=
  rfl

/-- On zero-simplices, the edgewise comparison takes a one-simplex to its
target vertex. -/
@[simp]
theorem esdComparison_app_zero (X : SSet.{u})
    (x : X.obj (op ⦋1⦌)) :
    (esdComparison.app X).app (op ⦋0⦌) x = X.δ 0 x := by
  rw [esdComparison_app_app,
    SimplexCategory.edgewiseRightInclusion_app_zero]
  rfl

end SSet
