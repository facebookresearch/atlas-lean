/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting
public import Mathlib.Algebra.Homology.Opposite
public import MathlibExt.CategoryTheory.Functor.Opposite

/-!
# Splitting transport through the native opposite complex

The inverse family is reversed through the native opposite or unop complex.
Raw transport, round trips and the split predicate require only zero morphisms.
For the already proved normalization, the opposite inverse retains its
reflexive and square-zero laws; neither law is assumed of the raw family.
Object, morphism and index universes are independent, and the complex shape is
arbitrary. In particular, no abelian or homology structure is required.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}

namespace Splitting

variable {K : HomologicalComplex C c}

/-- Reverse the actual inverse components through the native opposite complex. -/
def op (s : Splitting K) : Splitting K.op where
  hom i j := (s.hom j i).op
  zero i j hij := by
    change (s.hom j i).op = 0
    rw [s.zero j i hij, op_zero]
  d_h_d i j := by
    apply Quiver.Hom.unop_inj
    simpa only [HomologicalComplex.op_d, unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using s.d_h_d j i

/-- Opposite splitting components are the literal reversed original components. -/
@[simp]
lemma op_hom (s : Splitting K) (i j : ι) :
    s.op.hom i j = (s.hom j i).op := rfl

variable {K' : HomologicalComplex Cᵒᵖ c}

/-- Reverse the actual inverse components through the native unop complex. -/
def unop (s : Splitting K') : Splitting K'.unop where
  hom i j := (s.hom j i).unop
  zero i j hij := by
    change (s.hom j i).unop = 0
    rw [s.zero j i hij, unop_zero]
  d_h_d i j := by
    apply Quiver.Hom.op_inj
    simpa only [HomologicalComplex.unop_d, op_comp, Quiver.Hom.op_unop,
      Category.assoc] using s.d_h_d j i

/-- Unop splitting components are the literal reversed original components. -/
@[simp]
lemma unop_hom (s : Splitting K') (i j : ι) :
    s.unop.hom i j = (s.hom j i).unop := rfl

/-- Taking the opposite and then unop restores the complete splitting data. -/
@[simp]
lemma unop_op (s : Splitting K) : s.op.unop = s := by
  ext i j
  rfl

/-- Taking unop and then the opposite restores the complete splitting data. -/
@[simp]
lemma op_unop (s : Splitting K') : s.unop.op = s := by
  ext i j
  rfl

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]

/-- Native opposite and zero-preserving functor transport keep the same components. -/
lemma map_op (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    (s.map F).op = s.op.map F.op := by
  ext i j
  rfl

end Splitting

/-- A raw splitting gives the native opposite complex a raw splitting. -/
lemma IsSplit.op {K : HomologicalComplex C c} (h : IsSplit K) : IsSplit K.op := by
  obtain ⟨s⟩ := h
  exact ⟨s.op⟩

/-- A raw splitting gives the native unop complex a raw splitting. -/
lemma IsSplit.unop {K : HomologicalComplex Cᵒᵖ c} (h : IsSplit K) : IsSplit K.unop := by
  obtain ⟨s⟩ := h
  exact ⟨s.unop⟩

/-- The raw split predicate is equivalent for the complex and its native opposite. -/
lemma isSplit_op_iff (K : HomologicalComplex C c) : IsSplit K.op ↔ IsSplit K :=
  ⟨fun h => h.unop, fun h => h.op⟩

end HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- The native opposite of the proved normalization retains its square-zero composites. -/
lemma normalize_op_hom_comp_hom (s : Splitting K) (i j k : ι) :
    s.normalize.op.hom i j ≫ s.normalize.op.hom j k = 0 := by
  apply Quiver.Hom.unop_inj
  simpa only [op_hom, unop_comp, Quiver.Hom.unop_op, unop_zero] using
    s.normalize_hom_comp_hom k j i

/-- The native opposite of the proved normalization retains its reflexive inverse law. -/
lemma normalize_op_h_d_h (s : Splitting K) (i j : ι) :
    s.normalize.op.hom i j ≫ K.op.d j i ≫ s.normalize.op.hom i j =
      s.normalize.op.hom i j := by
  apply Quiver.Hom.unop_inj
  simpa only [op_hom, HomologicalComplex.op_d, unop_comp,
    Quiver.Hom.unop_op, Category.assoc] using s.normalize_h_d_h j i

end HomologicalComplex.Splitting
