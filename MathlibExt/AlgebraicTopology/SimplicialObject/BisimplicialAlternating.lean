/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Alternating bicomplex of a bisimplicial object

Applying the alternating-face complex first in the outer simplicial
direction and then degreewise in the inner direction gives a first-quadrant
bicomplex.  Mathlib's total-complex construction then provides its signed
direct-sum totalization.

This is the algebraic bicomplex layer only.  No diagonal comparison,
spectral-sequence page identification, or convergence result is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe v u

namespace AlgebraicTopology

variable (A : Type u) [Category.{v} A] [Preadditive A]

/-- Functor sending a bisimplicial object to its alternating-face
bicomplex. -/
noncomputable def bisimplicialAlternatingBicomplexFunctor :
    SimplicialObject (SimplicialObject A) ⥤
      HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  alternatingFaceMapComplex (SimplicialObject A) ⋙
    (alternatingFaceMapComplex A).mapHomologicalComplex
      (ComplexShape.down ℕ)

/-- Alternating-face bicomplex of a bisimplicial object. -/
noncomputable abbrev bisimplicialAlternatingBicomplex
    (B : SimplicialObject (SimplicialObject A)) :
    HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (bisimplicialAlternatingBicomplexFunctor A).obj B

/-- Bidegree `(p,q)` is the `(p,q)` object of the original bisimplicial
object. -/
@[simp]
theorem bisimplicialAlternatingBicomplex_X_X
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).X p).X q =
      (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  rfl

/-- A bisimplicial map acts in bidegree `(p,q)` by its `(p,q)`
component. -/
@[simp]
theorem bisimplicialAlternatingBicomplex_map_f_f
    {B B' : SimplicialObject (SimplicialObject A)}
    (f : B ⟶ B') (p q : ℕ) :
    ((((bisimplicialAlternatingBicomplexFunctor A).map f).f p).f q) =
      (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) :=
  rfl

/-- The vertical differential is the inner alternating-face
differential. -/
@[simp]
theorem bisimplicialAlternatingBicomplex_vertical_d
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).X p).d (q + 1) q =
      AlternatingFaceMapComplex.objD
        (B.obj (Opposite.op ⦋p⦌)) q := by
  simp [bisimplicialAlternatingBicomplex,
    bisimplicialAlternatingBicomplexFunctor]

/-- Expanded vertical differential as the alternating sum of inner
faces. -/
theorem bisimplicialAlternatingBicomplex_vertical_d_eq_sum
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).X p).d (q + 1) q =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
        (B.obj (Opposite.op ⦋p⦌)).δ i := by
  rw [bisimplicialAlternatingBicomplex_vertical_d]
  rfl

/-- The horizontal differential in inner degree `q` is the component of
the outer alternating-face differential. -/
@[simp]
theorem bisimplicialAlternatingBicomplex_horizontal_d_f
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).d (p + 1) p).f q =
      (AlternatingFaceMapComplex.objD B p).app
        (Opposite.op ⦋q⦌) := by
  simp only [bisimplicialAlternatingBicomplex,
    bisimplicialAlternatingBicomplexFunctor, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_X,
    alternatingFaceMapComplex_obj_X,
    Functor.mapHomologicalComplex_obj_d,
    alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, Int.reduceNeg,
    Functor.map_sum, NatTrans.app_sum, NatTrans.app_zsmul]
  change (HomologicalComplex.Hom.fAddMonoidHom q)
      (∑ a : Fin (p + 2), (alternatingFaceMapComplex A).map
        ((-1 : ℤ) ^ (a : ℕ) • B.δ a)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Functor.map_zsmul, map_zsmul]
  rfl

/-- Expanded horizontal differential as the alternating sum of outer
faces. -/
theorem bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    ((bisimplicialAlternatingBicomplex A B).d (p + 1) p).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (B.δ i).app (Opposite.op ⦋q⦌) := by
  rw [bisimplicialAlternatingBicomplex_horizontal_d_f]
  simp [AlternatingFaceMapComplex.objD]

/-- The horizontal chain-map differential is the alternating sum of the
inner alternating-complex maps induced by the outer faces. -/
theorem bisimplicialAlternatingBicomplex_horizontal_d_eq_sum
    (B : SimplicialObject (SimplicialObject A)) (p : ℕ) :
    (bisimplicialAlternatingBicomplex A B).d (p + 1) p =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (alternatingFaceMapComplex A).map (B.δ i) := by
  apply HomologicalComplex.Hom.ext
  funext q
  rw [bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum]
  change (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
      (B.δ i).app (Opposite.op ⦋q⦌)) =
    (HomologicalComplex.Hom.fAddMonoidHom q)
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (alternatingFaceMapComplex A).map (B.δ i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  rfl

section Total

variable [Limits.HasCountableCoproducts A]

/-- Functorial signed direct-sum total complex of the alternating
bicomplex. -/
noncomputable def bisimplicialAlternatingTotalComplexFunctor :
    SimplicialObject (SimplicialObject A) ⥤ ChainComplex A ℕ :=
  bisimplicialAlternatingBicomplexFunctor A ⋙
    HomologicalComplex₂.totalFunctor A (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- Direct-sum total complex of one bisimplicial object. -/
noncomputable abbrev bisimplicialAlternatingTotalComplex
    (B : SimplicialObject (SimplicialObject A)) : ChainComplex A ℕ :=
  (bisimplicialAlternatingTotalComplexFunctor A).obj B

/-- Inclusion of bidegree `(p,q)` into total degree `p+q`. -/
noncomputable def bisimplicialAlternatingTotalι
    (B : SimplicialObject (SimplicialObject A)) (p q : ℕ) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (bisimplicialAlternatingTotalComplex A B).X (p + q) :=
  (bisimplicialAlternatingBicomplex A B).ιTotal
    (ComplexShape.down ℕ) p q (p + q) rfl

end Total

end AlgebraicTopology

end
