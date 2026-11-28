/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelComp
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelCompFunctor
public import MathlibExt.Algebra.Homology.HomologySequenceFunctor

/-!
# Connecting maps for composite-cokernel sequences

Let C be abelian, c any complex shape, and X —f→ Y —g→ Z a composable
pair of complexes with g monic. Its cokernel triple
Coker(f) → Coker(g∘f) → Coker(g) is short exact and functorial in maps
of such pairs.

For c.Rel(i,j), the homology connecting map is
H_i(Coker(g)) → H_j(Coker(f)).
These maps form a natural transformation on the category of composable
complex maps whose second map is monic. The category and complex-index
universes are independent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type w} {c : ComplexShape ι}

/-- For complexes of any shape c in an abelian category C, the property on
a composable pair X —f→ Y —g→ Z that its second map g is a monomorphism. -/
def secondMapMonomorphisms :
    ObjectProperty (ComposableArrows (HomologicalComplex C c) 2) :=
  fun S => Mono (S.map' 1 2)

/-- For complexes of shape c in an abelian category, the functor from
composable pairs X —f→ Y —g→ Z with g monic to short complexes,
sending the pair to Coker(f) → Coker(g∘f) → Coker(g). -/
noncomputable def cokernelCompMonoFunctor :
    (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory ⥤
      ShortComplex (HomologicalComplex C c) :=
  secondMapMonomorphisms.ι ⋙ cokernelCompFunctor

@[simp]
lemma cokernelCompMonoFunctor_obj_X₁
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).X₁ =
      cokernel (S.obj.map' 0 1) :=
  rfl

@[simp]
lemma cokernelCompMonoFunctor_obj_X₂
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).X₂ =
      cokernel (S.obj.map' 0 2) :=
  rfl

@[simp]
lemma cokernelCompMonoFunctor_obj_X₃
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).X₃ =
      cokernel (S.obj.map' 1 2) :=
  rfl

private abbrev map01
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :=
  S.obj.map' 0 1 (by omega) (by omega)

private abbrev map02
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :=
  S.obj.map' 0 2 (by omega) (by omega)

private abbrev map12
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :=
  S.obj.map' 1 2 (by omega) (by omega)

private noncomputable def middleIso
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    cokernel (map02 S) ≅ cokernel (map01 S ≫ map12 S) :=
  cokernelIsoOfEq
    (ComposableArrows.map'_comp S.obj 0 1 2 (by omega) (by omega) (by omega))

private lemma seq_f_π_aux {X Y Z : HomologicalComplex C c}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    cokernel.π f ≫ (cokernelCompSequence f g).f =
      g ≫ cokernel.π (f ≫ g) := by
  change cokernel.π f ≫
      cokernel.map f (f ≫ g) (𝟙 X) g (by simp) =
    g ≫ cokernel.π (f ≫ g)
  exact cokernel.π_desc _ _ _

private lemma seq_g_π_aux {X Y Z : HomologicalComplex C c}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    cokernel.π (f ≫ g) ≫ (cokernelCompSequence f g).g = cokernel.π g := by
  change cokernel.π (f ≫ g) ≫
      cokernel.map (f ≫ g) g f (𝟙 Z) (by simp) = cokernel.π g
  change cokernel.π (f ≫ g) ≫
      cokernel.desc (f ≫ g) (𝟙 Z ≫ cokernel.π g) _ = cokernel.π g
  rw [cokernel.π_desc]
  simp

private lemma pi02_comp_g
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    cokernel.π (map02 S) ≫
        (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).g =
      cokernel.π (map12 S) := by
  have h := cokernelCompFunctor_obj_g (C := HomologicalComplex C c) S.obj
  have hg :
      (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).g =
        (cokernelCompFunctor (C := HomologicalComplex C c) |>.obj S.obj).g :=
    rfl
  rw [hg]
  exact h

private lemma comm12
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (cokernelCompSequence (map01 S) (map12 S)).f =
      (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f ≫
        (middleIso S).hom := by
  let f01 := map01 S
  let f02 := map02 S
  let g12 := map12 S
  let hEq : f02 = f01 ≫ g12 :=
    ComposableArrows.map'_comp S.obj 0 1 2 (by omega) (by omega) (by omega)
  let e : cokernel f02 ≅ cokernel (f01 ≫ g12) := cokernelIsoOfEq hEq
  change (cokernelCompSequence f01 g12).f =
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f ≫ e.hom
  have hπ :
      cokernel.π f01 ≫
          (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f =
        g12 ≫ cokernel.π f02 := by
    have h0 := cokernelCompFunctor_obj_f
      (C := HomologicalComplex C c) S.obj
    have hf :
        (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f =
          (cokernelCompFunctor
            (C := HomologicalComplex C c) |>.obj S.obj).f :=
      rfl
    rw [hf]
    exact h0
  apply (cancel_epi (cokernel.π f01)).mp
  have h1 : cokernel.π f01 ≫ (cokernelCompSequence f01 g12).f =
        g12 ≫ cokernel.π (f01 ≫ g12) := seq_f_π_aux f01 g12
  have hIso : cokernel.π f02 ≫ e.hom = cokernel.π (f01 ≫ g12) :=
    CategoryTheory.Limits.π_comp_cokernelIsoOfEq_hom hEq
  have h2 : g12 ≫ cokernel.π (f01 ≫ g12) =
        g12 ≫ (cokernel.π f02 ≫ e.hom) := by
    rw [← hIso]
  have h3 : g12 ≫ (cokernel.π f02 ≫ e.hom) =
        (g12 ≫ cokernel.π f02) ≫ e.hom := by
    rw [Category.assoc]
  have h4 : (g12 ≫ cokernel.π f02) ≫ e.hom =
        (cokernel.π f01 ≫
          (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f) ≫ e.hom :=
    congrArg (· ≫ e.hom) hπ.symm
  have h5 : (cokernel.π f01 ≫
          (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f) ≫ e.hom =
        cokernel.π f01 ≫
          ((cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).f ≫ e.hom) :=
    Category.assoc _ _ _
  exact (h1.trans (h2.trans (h3.trans (h4.trans h5))))

private lemma comm23
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (middleIso S).hom ≫ (cokernelCompSequence (map01 S) (map12 S)).g =
      (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).g := by
  let f01 := map01 S
  let f02 := map02 S
  let g12 := map12 S
  let hEq : f02 = f01 ≫ g12 :=
    ComposableArrows.map'_comp S.obj 0 1 2 (by omega) (by omega) (by omega)
  let e : cokernel f02 ≅ cokernel (f01 ≫ g12) := cokernelIsoOfEq hEq
  change e.hom ≫ (cokernelCompSequence f01 g12).g =
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).g
  apply (cancel_epi (cokernel.π f02)).mp
  have hIso : cokernel.π f02 ≫ e.hom = cokernel.π (f01 ≫ g12) :=
    CategoryTheory.Limits.π_comp_cokernelIsoOfEq_hom hEq
  have hLeft_assoc :
      cokernel.π f02 ≫ (e.hom ≫ (cokernelCompSequence f01 g12).g) =
        (cokernel.π f02 ≫ e.hom) ≫ (cokernelCompSequence f01 g12).g :=
    (Category.assoc _ _ _).symm
  have hLeft_iso :
      (cokernel.π f02 ≫ e.hom) ≫ (cokernelCompSequence f01 g12).g =
        cokernel.π (f01 ≫ g12) ≫ (cokernelCompSequence f01 g12).g := by
    rw [hIso]
  have hLeft_seq :
      cokernel.π (f01 ≫ g12) ≫ (cokernelCompSequence f01 g12).g =
        cokernel.π g12 :=
    seq_g_π_aux f01 g12
  have hRight :
      cokernel.π f02 ≫
          (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).g =
        cokernel.π g12 :=
    pi02_comp_g (C := C) (c := c) S
  have h123 :
      cokernel.π f02 ≫ (e.hom ≫ (cokernelCompSequence f01 g12).g) =
        cokernel.π g12 :=
    (hLeft_assoc.trans (hLeft_iso.trans hLeft_seq))
  exact h123.trans hRight.symm

private noncomputable def cokernelCompMonoFunctorIso
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S) ≅
      cokernelCompSequence (map01 S) (map12 S) :=
  ShortComplex.isoMk (Iso.refl _) (middleIso S) (Iso.refl _)
    (by
      exact ((Category.id_comp _).trans (comm12 S)))
    (by
      exact ((comm23 S).trans (Category.comp_id _).symm))

/-- Let C be abelian and X —f→ Y —g→ Z a composable pair of complexes of
shape c with g monic. Its functorial cokernel triple
Coker(f) → Coker(g∘f) → Coker(g) is short exact. -/
lemma cokernelCompMonoFunctor_shortExact
    (S : (secondMapMonomorphisms (C := C) (c := c)).FullSubcategory) :
    (cokernelCompMonoFunctor (C := C) (c := c) |>.obj S).ShortExact := by
  have : Mono (map12 S) := S.property
  exact shortExact_of_iso (cokernelCompMonoFunctorIso S).symm
    (cokernelCompSequence_shortExact (map01 S) (map12 S))

end ShortComplex

end CategoryTheory

namespace HomologicalComplex

namespace HomologySequence

open CategoryTheory CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type w} {c : ComplexShape ι}

/-- For a composable pair X —f→ Y —g→ Z of complexes in an abelian category,
with g monic and c.Rel(i,j), the connecting map
H_i(Coker(g)) → H_j(Coker(f)) of the short exact cokernel triple. -/
noncomputable def cokernelCompδ
    (S : (CategoryTheory.ShortComplex.secondMapMonomorphisms
      (C := C) (c := c)).FullSubcategory)
    (i j : ι) (hij : c.Rel i j) :
    ((CategoryTheory.ShortComplex.cokernelCompMonoFunctor
        (C := C) (c := c) |>.obj S).X₃.homology i ⟶
      (CategoryTheory.ShortComplex.cokernelCompMonoFunctor
        (C := C) (c := c) |>.obj S).X₁.homology j) :=
  (CategoryTheory.ShortComplex.cokernelCompMonoFunctor_shortExact
    (C := C) (c := c) S).δ i j hij

/-- In an abelian category C, fix a complex shape c and c.Rel(i,j).
The connecting maps H_i(Coker(g)) → H_j(Coker(f)) form a natural
transformation on composable complex pairs X —f→ Y —g→ Z with g monic. -/
noncomputable def cokernelCompδNatTrans
    (i j : ι) (hij : c.Rel i j) :
    (CategoryTheory.ShortComplex.cokernelCompMonoFunctor (C := C) (c := c) ⋙
        CategoryTheory.ShortComplex.π₃ ⋙
          HomologicalComplex.homologyFunctor C c i) ⟶
      (CategoryTheory.ShortComplex.cokernelCompMonoFunctor (C := C) (c := c) ⋙
        CategoryTheory.ShortComplex.π₁ ⋙
          HomologicalComplex.homologyFunctor C c j) :=
  δNatTransOfFamily
    (CategoryTheory.ShortComplex.cokernelCompMonoFunctor (C := C) (c := c))
    CategoryTheory.ShortComplex.cokernelCompMonoFunctor_shortExact i j hij

@[simp]
lemma cokernelCompδNatTrans_app
    (i j : ι) (hij : c.Rel i j)
    (S : (CategoryTheory.ShortComplex.secondMapMonomorphisms
      (C := C) (c := c)).FullSubcategory) :
    (cokernelCompδNatTrans (C := C) (c := c) i j hij).app S =
      cokernelCompδ (C := C) (c := c) S i j hij :=
  rfl

end HomologySequence

end HomologicalComplex
