/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesImage
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The canonical cycles, term and outgoing-image complex sequence

Every graded family has a complex with zero differentials. Applied to actual
cycles and outgoing images, this gives a natural short exact sequence with the
complex in the middle. All shapes and index universes are allowed.
Projectivity is used only to split a degree or to infer projective cycles from
an projective term; chosen degreewise sections are not chain maps.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

universe u v w
variable {C : Type u} [Category.{v} C] {ι : Type w} {c : ComplexShape ι}

section Zero

variable [HasZeroMorphisms C]

/-- Retain every graded object and map, with zero differentials in the given shape. -/
def zeroDifferentialFunctor (c : ComplexShape ι) : GradedObject ι C ⥤ HomologicalComplex C c where
  obj A :=
    { X := A
      d _ _ := 0
      shape _ _ _ := rfl
      d_comp_d' _ _ _ _ _ := CategoryTheory.Limits.zero_comp }
  map f :=
    { f := f
      comm' _ _ _ := by
        simp only [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp] }
  map_id A := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl

/-- The graded object is the literal term of its zero-differential complex. -/
theorem zeroDifferentialFunctor_obj_X (A : GradedObject ι C) (i : ι) :
    ((zeroDifferentialFunctor (C := C) c).obj A).X i = A i := rfl

/-- Its differential is zero at every pair, without any shape restriction. -/
theorem zeroDifferentialFunctor_obj_d (A : GradedObject ι C) (i j : ι) :
    ((zeroDifferentialFunctor (C := C) c).obj A).d i j = 0 := rfl

/-- The induced map is the graded map at every index. -/
theorem zeroDifferentialFunctor_map_f {A B : GradedObject ι C} (f : A ⟶ B) (i : ι) :
    ((zeroDifferentialFunctor (C := C) c).map f).f i = f i := rfl

end Zero

section Abelian

variable [Abelian C]

/-- The cycles functors, assembled by pi' and given zero differentials. -/
def cyclesZeroComplexFunctor : HomologicalComplex C c ⥤ HomologicalComplex C c :=
  (Functor.pi' (fun i : ι => cyclesFunctor C c i)) ⋙ zeroDifferentialFunctor (C := C) c

/-- Outgoing images and their image maps, with zero differentials. -/
def outgoingImageZeroComplexFunctor : HomologicalComplex C c ⥤ HomologicalComplex C c :=
  (Functor.pi' (fun i : ι =>
    cyclesImageArrowFunctor (C := C) (c := c) i (c.next i) ⋙ Abelian.im)) ⋙
      zeroDifferentialFunctor (C := C) c

/-- The zero-differential complex of the cycles. -/
def cyclesZeroComplex (P : HomologicalComplex C c) : HomologicalComplex C c :=
  (cyclesZeroComplexFunctor (C := C) (c := c)).obj P

/-- The zero-differential complex of images of the outgoing differentials. -/
def outgoingImageZeroComplex (P : HomologicalComplex C c) : HomologicalComplex C c :=
  (outgoingImageZeroComplexFunctor (C := C) (c := c)).obj P

/-- Its cycles term keeps the object. -/
theorem cyclesZeroComplex_X (P : HomologicalComplex C c) (i : ι) :
    (cyclesZeroComplex P).X i = P.cycles i := rfl

/-- Its image term is the image of the outgoing differential. -/
theorem outgoingImageZeroComplex_X (P : HomologicalComplex C c) (i : ι) :
    (outgoingImageZeroComplex P).X i = Abelian.image (P.d i (c.next i)) := rfl

/-- The literal cycles inclusions give a natural map into the complex. -/
def cyclesComplexInclusion :
    cyclesZeroComplexFunctor (C := C) (c := c) ⟶ 𝟭 (HomologicalComplex C c) where
  app P :=
    { f i := P.iCycles i
      comm' i j _ := by
        change P.iCycles i ≫ P.d i j = 0 ≫ P.iCycles j
        exact (P.iCycles_d i j).trans CategoryTheory.Limits.zero_comp.symm }
  naturality P Q φ := by
    apply HomologicalComplex.hom_ext
    intro i
    exact cyclesMap_i φ i

/-- Quotients onto outgoing images give the natural projection. -/
def cyclesComplexProjection :
    𝟭 (HomologicalComplex C c) ⟶ outgoingImageZeroComplexFunctor (C := C) (c := c) where
  app P :=
    { f i := Abelian.factorThruImage (P.d i (c.next i))
      comm' i j _ := by
        change Abelian.factorThruImage (P.d i (c.next i)) ≫ 0 =
          P.d i j ≫ Abelian.factorThruImage (P.d j (c.next j))
        have h : (P.d i j ≫ Abelian.factorThruImage (P.d j (c.next j))) ≫
            Abelian.image.ι (P.d j (c.next j)) = 0 := by
          rw [Category.assoc, Abelian.image.fac]
          exact P.d_comp_d i j (c.next j)
        exact CategoryTheory.Limits.comp_zero.trans (zero_of_comp_mono _ h).symm }
  naturality P Q φ := by
    apply HomologicalComplex.hom_ext
    intro i
    let a : Arrow.mk (P.d i (c.next i)) ⟶ Arrow.mk (Q.d i (c.next i)) :=
      (cyclesImageArrowFunctor (C := C) (c := c) i (c.next i)).map φ
    change φ.f i ≫ Abelian.factorThruImage (Q.d i (c.next i)) =
      Abelian.factorThruImage (P.d i (c.next i)) ≫ (Abelian.im (C := C)).map a
    exact (Abelian.factorThruImageNatTrans (C := C)).naturality a

/-- FunctorEquivalence packages the canonical complex sequence naturally. -/
def cyclesComplexSequenceFunctor :
    HomologicalComplex C c ⥤ ShortComplex (HomologicalComplex C c) :=
  (ShortComplex.functorEquivalence (HomologicalComplex C c) (HomologicalComplex C c)).functor.obj
    (ShortComplex.mk (cyclesComplexInclusion (C := C) (c := c))
      (cyclesComplexProjection (C := C) (c := c)) (by
        apply NatTrans.ext
        funext P
        apply HomologicalComplex.hom_ext
        intro i
        change P.iCycles i ≫ Abelian.factorThruImage (P.d i (c.next i)) = 0
        exact (cyclesImageSequence P i (c.next i)).zero))

/-- The complex and its canonical zero-differential end complexes. -/
def cyclesComplexSequence (P : HomologicalComplex C c) :
    ShortComplex (HomologicalComplex C c) :=
  (cyclesComplexSequenceFunctor (C := C) (c := c)).obj P

/-- Evaluation gives precisely the previously constructed canonical point sequence. -/
theorem cyclesComplexSequence_eval (P : HomologicalComplex C c) (i : ι) :
    (cyclesComplexSequence P).map (eval C c i) = cyclesImageSequence P i (c.next i) := rfl

/-- Its first map is the cycles inclusion. -/
theorem cyclesComplexSequence_f_f (P : HomologicalComplex C c) (i : ι) :
    (cyclesComplexSequence P).f.f i = P.iCycles i := rfl

/-- Its second map is the quotient onto the outgoing image. -/
theorem cyclesComplexSequence_g_f (P : HomologicalComplex C c) (i : ι) :
    (cyclesComplexSequence P).g.f i = Abelian.factorThruImage (P.d i (c.next i)) := rfl

/-- Degreewise exactness gives the short exact complex sequence. -/
theorem cyclesComplexSequence_shortExact (P : HomologicalComplex C c) :
    (cyclesComplexSequence P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  rw [cyclesComplexSequence_eval]
  exact cyclesImageSequence_shortExact P i (c.next i) rfl

/-- The middle component of a canonical sequence map is the complex map. -/
theorem cyclesComplexSequenceFunctor_map_τ₂ {P Q : HomologicalComplex C c} (f : P ⟶ Q) :
    ((cyclesComplexSequenceFunctor (C := C) (c := c)).map f).τ₂ = f := rfl

/-- The left component is the cycles map, at every degree. -/
theorem cyclesComplexSequenceFunctor_map_τ₁_f {P Q : HomologicalComplex C c}
    (f : P ⟶ Q) (i : ι) :
    (((cyclesComplexSequenceFunctor (C := C) (c := c)).map f).τ₁).f i =
      cyclesMap f i := rfl

/-- The right component is the image map of the differential square. -/
theorem cyclesComplexSequenceFunctor_map_τ₃_f {P Q : HomologicalComplex C c}
    (f : P ⟶ Q) (i : ι) :
    (((cyclesComplexSequenceFunctor (C := C) (c := c)).map f).τ₃).f i =
      (Abelian.im (C := C)).map
        ((cyclesImageArrowFunctor (C := C) (c := c) i (c.next i)).map f) := rfl

/-- A projective term and its projective outgoing image give projective cycles by retract. -/
theorem projective_cycles (P : HomologicalComplex C c) (i : ι) [Projective (P.X i)]
    [Projective (Abelian.image (P.d i (c.next i)))] : Projective (P.cycles i) := by
  let s := cyclesImageSequenceSplitting P i (c.next i) rfl
  let h : Retract (P.cycles i) (P.X i) :=
    { i := P.iCycles i
      r := s.r
      retract := s.f_r }
  exact h.projective

end Abelian
end HomologicalComplex
