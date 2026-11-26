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
# Splittings in opposite categories

Taking the opposite category reverses both the differential shape and
the inverse components of a splitting. The component from i to j becomes
the opposite of the original component from j to i. Double reversal
restores the splitting, and zero-preserving functors commute with this
duality. Normalized inverse identities are retained.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}

namespace Splitting

variable {K : HomologicalComplex C c}

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and let s be a splitting of K.
The opposite complex K.op lies in Cᵒᵖ with reversed shape c.symm. The maps (s.hom j i).op
define a splitting of K.op, reversing the original inverse components and preserving d h d=d.
-/
def op (s : Splitting K) : Splitting K.op where
  hom i j := (s.hom j i).op
  zero i j hij := by
    change (s.hom j i).op = 0
    rw [s.zero j i hij, op_zero]
  d_h_d i j := by
    apply Quiver.Hom.unop_inj
    simpa only [HomologicalComplex.op_d, unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using s.d_h_d j i

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and let s be a splitting of K.
The opposite complex K.op lies in Cᵒᵖ with reversed shape c.symm. The degree-(i,j) component
is s.op.hom i j=(s.hom j i).op:Kᵢ.op→Kⱼ.op.
-/
@[simp]
lemma op_hom (s : Splitting K) (i j : ι) :
    s.op.hom i j = (s.hom j i).op := rfl

variable {K' : HomologicalComplex Cᵒᵖ c}

/--
Let C have zero morphisms, let K' be a c-complex in Cᵒᵖ, and let s be a splitting of K'. Its
unop complex has values in C and shape c.symm. The maps (s.hom j i).unop define its splitting,
with the generalized-inverse and reverse-support laws carried through the duality.
-/
def unop (s : Splitting K') : Splitting K'.unop where
  hom i j := (s.hom j i).unop
  zero i j hij := by
    change (s.hom j i).unop = 0
    rw [s.zero j i hij, unop_zero]
  d_h_d i j := by
    apply Quiver.Hom.op_inj
    simpa only [HomologicalComplex.unop_d, op_comp, Quiver.Hom.op_unop,
      Category.assoc] using s.d_h_d j i

/--
Let C have zero morphisms, let K' be a c-complex in Cᵒᵖ, and let s be a splitting of K'. Its
unop complex has values in C and shape c.symm. The unop component is s.unop.hom i j=(s.hom j
i).unop:K'ᵢ.unop→K'ⱼ.unop.
-/
@[simp]
lemma unop_hom (s : Splitting K') (i j : ι) :
    s.unop.hom i j = (s.hom j i).unop := rfl

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and let s be a splitting of K.
The opposite complex K.op lies in Cᵒᵖ with reversed shape c.symm. Under the canonical
double-reversal identification with K, taking opposite and then unop restores all splitting
components: s.op.unop=s.
-/
@[simp]
lemma unop_op (s : Splitting K) : s.op.unop = s := by
  ext i j
  rfl

/--
Let C have zero morphisms, let K' be a c-complex in Cᵒᵖ, and let s be a splitting of K'. Its
unop complex has values in C and shape c.symm. Under the canonical double-reversal
identification with K', taking unop and then opposite restores the splitting: s.unop.op=s.
-/
@[simp]
lemma op_unop (s : Splitting K') : s.unop.op = s := by
  ext i j
  rfl

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and let s be a splitting of K.
The opposite complex K.op lies in Cᵒᵖ with reversed shape c.symm. For a zero-preserving
functor F:C⥤D, with zero morphisms in D, functor mapping and duality commute: (s.map
F).op=s.op.map F.op.
-/
lemma map_op (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    (s.map F).op = s.op.map F.op := by
  ext i j
  rfl

end Splitting

/--
Let K be a complex of shape c in a category C with zero morphisms. If K admits a
generalized-inverse splitting, the opposite complex K.op of reversed shape c.symm also admits
one.
-/
lemma IsSplit.op {K : HomologicalComplex C c} (h : IsSplit K) : IsSplit K.op := by
  obtain ⟨s⟩ := h
  exact ⟨s.op⟩

/--
Let K be a c-complex in Cᵒᵖ, where C has zero morphisms. If K is split, then its unop complex
in C with reversed shape c.symm is split.
-/
lemma IsSplit.unop {K : HomologicalComplex Cᵒᵖ c} (h : IsSplit K) : IsSplit K.unop := by
  obtain ⟨s⟩ := h
  exact ⟨s.unop⟩

/--
For a c-complex K in a category C with zero morphisms, IsSplit(K.op) is equivalent to
IsSplit(K), using opposite and unop on the generalized-inverse data.
-/
lemma isSplit_op_iff (K : HomologicalComplex C c) : IsSplit K.op ↔ IsSplit K :=
  ⟨fun h => h.unop, fun h => h.op⟩

end HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let C be preadditive, K a c-complex and s a splitting. Let n=s.normalize be its square-zero
normalization, and consider n.op as a splitting of K.op in Cᵒᵖ. Every consecutive pair of
inverse components remains square-zero: n.op.hom i j≫n.op.hom j k=0 for all i,j,k.
-/
lemma normalize_op_hom_comp_hom (s : Splitting K) (i j k : ι) :
    s.normalize.op.hom i j ≫ s.normalize.op.hom j k = 0 := by
  apply Quiver.Hom.unop_inj
  simpa only [op_hom, unop_comp, Quiver.Hom.unop_op, unop_zero] using
    s.normalize_hom_comp_hom k j i

/--
Let C be preadditive, K a c-complex and s a splitting. Let n=s.normalize be its square-zero
normalization, and consider n.op as a splitting of K.op in Cᵒᵖ. The opposite normalized
components retain the reflexive identity h'ᵢⱼ≫K.op.d j i≫h'ᵢⱼ=h'ᵢⱼ, where h'ᵢⱼ=n.op.hom i j.
-/
lemma normalize_op_h_d_h (s : Splitting K) (i j : ι) :
    s.normalize.op.hom i j ≫ K.op.d j i ≫ s.normalize.op.hom i j =
      s.normalize.op.hom i j := by
  apply Quiver.Hom.unop_inj
  simpa only [op_hom, HomologicalComplex.op_d, unop_comp,
    Quiver.Hom.unop_op, Category.assoc] using s.normalize_h_d_h j i

end HomologicalComplex.Splitting
