/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplex
public import Mathlib.CategoryTheory.Thin

/-!
# Original full-J vertex coordinates

The native free groupoid of a nonempty ordinal has a unique arrow between
each pair of original vertices. Its full nerve simplices are arbitrary
ordered vertex tuples. Both original operator actions and the original
standard-simplex inclusion retain these coordinates.

Source: Joyal, The Theory of Quasi-Categories, Volume I, the full-J family
preceding Theorem 9.13 and the original face square of Lemma 9.15;
Joyal–Tierney, Quasi-categories vs Segal spaces, Section 1.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.FreeGroupoidSimplex

/-- The original ordinal arrow from zero, inside its actual free groupoid. -/
def baseArrow (n : SimplexCategory) (i : Fin (n.len + 1)) :
    FreeGroupoid.mk (C := ordinal.{u}.obj n) (ULift.up (0 : Fin (n.len + 1))) ⟶
      FreeGroupoid.mk (C := ordinal.{u}.obj n) (ULift.up i) := by
  change FreeGroupoid.mk (C := ULift.{u} (Fin (n.len + 1)))
      (ULift.up (0 : Fin (n.len + 1))) ⟶
    FreeGroupoid.mk (C := ULift.{u} (Fin (n.len + 1))) (ULift.up i)
  exact FreeGroupoid.homMk
    (homOfLE (by change (0 : Fin (n.len + 1)) ≤ i; exact Fin.zero_le i))

private def baseArrowTo (n : SimplexCategory) (x : FreeGroupoid (ordinal.{u}.obj n)) :
    FreeGroupoid.mk (C := ordinal.{u}.obj n) (ULift.up (0 : Fin (n.len + 1))) ⟶ x :=
  baseArrow n x.as.as.down

private theorem normalForm (n : SimplexCategory)
    {x y : FreeGroupoid (ordinal.{u}.obj n)} (f : x ⟶ y) :
    f = inv (baseArrowTo n x) ≫ baseArrowTo n y := by
  refine FreeGroupoid.hom_rec (C := ordinal.{u}.obj n)
    (motive := fun {x y : FreeGroupoid (ordinal.{u}.obj n)} (f : x ⟶ y) =>
      f = inv (baseArrowTo n x) ≫ baseArrowTo n y) ?_ ?_ ?_ f
  · intro x y g
    have hc : baseArrowTo n (FreeGroupoid.mk x) ≫ FreeGroupoid.homMk g =
        baseArrowTo n (FreeGroupoid.mk y) := by
      change (FreeGroupoid.of (ULift.{u} (Fin (n.len + 1)))).map
          (homOfLE (show (ULift.up (0 : Fin (n.len + 1))) ≤ x from Fin.zero_le x.down)) ≫
        (FreeGroupoid.of (ULift.{u} (Fin (n.len + 1)))).map g =
        (FreeGroupoid.of (ULift.{u} (Fin (n.len + 1)))).map
          (homOfLE (show (ULift.up (0 : Fin (n.len + 1))) ≤ y from Fin.zero_le y.down))
      exact ((FreeGroupoid.of (ULift.{u} (Fin (n.len + 1)))).map_comp _ g).symm.trans
        (congrArg (fun h : (ULift.up (0 : Fin (n.len + 1))) ⟶ y =>
          (FreeGroupoid.of (ULift.{u} (Fin (n.len + 1)))).map h) (by
            apply ULift.ext
            apply PLift.ext
            exact Subsingleton.elim _ _))
    calc
      FreeGroupoid.homMk g = inv (baseArrowTo n (FreeGroupoid.mk x)) ≫
          (baseArrowTo n (FreeGroupoid.mk x) ≫ FreeGroupoid.homMk g) := by simp
      _ = _ := by rw [hc]
  · intro x y g hg
    rw [hg]
    simp
  · intro x y z g h hg hh
    rw [hg, hh]
    simp [Category.assoc]

/-- Every original arrow is the exact inverse-zero-arrow normal form. -/
theorem hom_normalForm (n : SimplexCategory) (i j : Fin (n.len + 1))
    (f : FreeGroupoid.mk (C := ordinal.{u}.obj n) (ULift.up i) ⟶
      FreeGroupoid.mk (C := ordinal.{u}.obj n) (ULift.up j)) :
    f = inv (baseArrow n i) ≫ baseArrow n j :=
  normalForm n f

/-- The same original normal form covers every actual native groupoid object. -/
theorem hom_normalForm_all (n : SimplexCategory)
    {x y : FreeGroupoid (ordinal.{u}.obj n)} (f : x ⟶ y) :
    f = inv (baseArrow n x.as.as.down) ≫ baseArrow n y.as.as.down :=
  normalForm n f

/-- Only the actual ordinal free groupoid acquires the proved thinness instance. -/
instance freeOrdinal_isThin (n : SimplexCategory) :
    Quiver.IsThin (FreeGroupoid (ordinal.{u}.obj n)) := by
  intro x y
  exact ⟨fun f g => (normalForm n f).trans (normalForm n g).symm⟩

/-- Actual full-J simplices correspond to arbitrary original ordered vertex tuples. -/
def simplexVertexEquiv (n : SimplexCategory) (d : ℕ) :
    (J.{u}.obj n).obj (op ⦋d⦌) ≃ (Fin (d + 1) → Fin (n.len + 1)) where
  toFun x := fun i => (x.obj i).as.as.down
  invFun v := by
    change ComposableArrows (FreeGroupoid (ordinal.{u}.obj n)) d
    exact
      { obj := fun i => FreeGroupoid.mk (ULift.up (v i))
        map := fun {i j} _ => inv (baseArrow n (v i)) ≫ baseArrow n (v j)
        map_id := fun _ => by simp
        map_comp := fun _ _ => by simp [Category.assoc] }
  left_inv x := by
    let : Quiver.IsThin (FreeGroupoid (ordinal.{u}.obj n)) := freeOrdinal_isThin n
    apply CategoryTheory.nerve.ext_of_isThin (C := FreeGroupoid (ordinal.{u}.obj n))
    funext i
    rfl
  right_inv v := by
    funext i
    rfl

/-- Forward coordinates are the exact original native vertex objects. -/
@[simp]
theorem simplexVertexEquiv_apply (n : SimplexCategory) (d : ℕ)
    (x : (J.{u}.obj n).obj (op ⦋d⦌)) (i : Fin (d + 1)) :
    simplexVertexEquiv n d x i = (x.obj i).as.as.down := rfl

/-- Inverse coordinates retain each supplied original vertex. -/
@[simp]
theorem simplexVertexEquiv_symm_obj (n : SimplexCategory) (d : ℕ)
    (v : Fin (d + 1) → Fin (n.len + 1)) (i : Fin (d + 1)) :
    ((simplexVertexEquiv n d).symm v).obj i =
      FreeGroupoid.mk (C := ordinal.{u}.obj n) (ULift.up (v i)) := rfl

/-- Every original ordered-pair arrow of the inverse simplex is its canonical normal form. -/
theorem simplexVertexEquiv_symm_map (n : SimplexCategory) (d : ℕ)
    (v : Fin (d + 1) → Fin (n.len + 1)) {i j : Fin (d + 1)} (h : i ⟶ j) :
    ((simplexVertexEquiv.{u} n d).symm v).map h =
      inv (baseArrow.{u} n (v i)) ≫ baseArrow n (v j) := rfl

/-- Every original simplicial operator precomposes the full vertex tuple. -/
theorem simplexVertexEquiv_operator (n : SimplexCategory) {d e : ℕ}
    (g : ⦋d⦌ ⟶ ⦋e⦌) (x : (J.{u}.obj n).obj (op ⦋e⦌)) :
    simplexVertexEquiv n d ((J.obj n).map g.op x) =
      fun i => simplexVertexEquiv n e x (g i) := rfl

/-- The inverse tuple commutes with every same original simplicial operator. -/
theorem simplexVertexEquiv_symm_operator (n : SimplexCategory) {d e : ℕ}
    (g : ⦋d⦌ ⟶ ⦋e⦌) (v : Fin (e + 1) → Fin (n.len + 1)) :
    (J.{u}.obj n).map g.op ((simplexVertexEquiv n e).symm v) =
      (simplexVertexEquiv n d).symm (fun i => v (g i)) := by
  apply (simplexVertexEquiv n d).injective
  rw [simplexVertexEquiv_operator]
  simp only [Equiv.apply_symm_apply]

/-- Every original site map postcomposes the full vertex tuple, even when it moves zero. -/
theorem simplexVertexEquiv_site {n m : SimplexCategory} (f : n ⟶ m) (d : ℕ)
    (x : (J.{u}.obj n).obj (op ⦋d⦌)) :
    simplexVertexEquiv m d ((J.map f).app (op ⦋d⦌) x) =
      fun i => f (simplexVertexEquiv n d x i) := by
  funext i
  rfl

/-- The inverse tuple commutes with the same arbitrary original site map. -/
theorem simplexVertexEquiv_symm_site {n m : SimplexCategory} (f : n ⟶ m) (d : ℕ)
    (v : Fin (d + 1) → Fin (n.len + 1)) :
    (J.{u}.map f).app (op ⦋d⦌) ((simplexVertexEquiv n d).symm v) =
      (simplexVertexEquiv m d).symm (fun i => f (v i)) := by
  apply (simplexVertexEquiv m d).injective
  rw [simplexVertexEquiv_site]
  simp only [Equiv.apply_symm_apply]

/-- The original standard-simplex inclusion retains exactly its original vertex function. -/
theorem simplexVertexEquiv_inclusion (n : SimplexCategory) (d : ℕ) (s : ⦋d⦌ ⟶ n) :
    simplexVertexEquiv.{u} n d
        ((simplexInclusion.{u}.app n).app (op ⦋d⦌) (ULift.up s)) = fun i => s i := by
  funext i
  rfl

/-- Inverting those coordinates returns that same original inclusion simplex. -/
theorem simplexVertexEquiv_symm_inclusion (n : SimplexCategory) (d : ℕ)
    (s : ⦋d⦌ ⟶ n) :
    (simplexVertexEquiv n d).symm (fun i => s i) =
      (simplexInclusion.{u}.app n).app (op ⦋d⦌) (ULift.up s) := by
  apply (simplexVertexEquiv n d).injective
  rw [Equiv.apply_symm_apply, simplexVertexEquiv_inclusion]

/-- Degree-zero coordinates are the exact previously defined original vertices. -/
theorem simplexVertexEquiv_vertex (n : SimplexCategory) (i : Fin (n.len + 1)) :
    simplexVertexEquiv n 0 (vertex.{u} n i) = fun _ => i := rfl

end SSet.FreeGroupoidSimplex
