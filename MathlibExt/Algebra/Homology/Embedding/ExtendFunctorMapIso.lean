/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-!
# Extension of complexes commutes naturally with a functor preserving zero morphisms

The component in a supported degree is the identity on the actual mapped
object. Outside the embedding, the comparison is the unique isomorphism
between the native zero object and the functor image of the native zero.
This identifies the same extended differentials and chain maps for arbitrary
category and complex-shape worlds. Additivity is unnecessary.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ i j

namespace HomologicalComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
  {ι : Type i} {ι' : Type j} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The canonical comparison on the actual optional extension component. -/
def extendMapComponentIso (K : HomologicalComplex C c) :
    ∀ a : Option ι, extend.X ((F.mapHomologicalComplex c).obj K) a ≅ F.obj (extend.X K a)
  | some _ => Iso.refl _
  | none => (Limits.isZero_zero D).iso (F.map_isZero (Limits.isZero_zero C))

/-- The component comparison preserves the actual extended differentials. -/
theorem extendMapComponentIso_d (K : HomologicalComplex C c) (a b : Option ι) :
    (extendMapComponentIso F K a).hom ≫ F.map (extend.d K a b) =
      extend.d ((F.mapHomologicalComplex c).obj K) a b ≫
        (extendMapComponentIso F K b).hom := by
  cases a with
  | none => exact (Limits.isZero_zero D).eq_of_src _ _
  | some a =>
    cases b with
    | none => exact (F.map_isZero (Limits.isZero_zero C)).eq_of_tgt _ _
    | some b =>
      change 𝟙 _ ≫ F.map (K.d a b) = F.map (K.d a b) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]

/-- The native extension of mapped complexes is the mapped native extension. -/
def extendMapIso (e : c.Embedding c') (K : HomologicalComplex C c) :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  Hom.isoOfComponents (fun n => extendMapComponentIso F K (e.r n)) (by
    intro n m _
    exact extendMapComponentIso_d F K (e.r n) (e.r m))

/-- The comparison commutes with every actual chain map of the original complex. -/
@[reassoc]
theorem extendMapIso_naturality (e : c.Embedding c') {K L : HomologicalComplex C c} (a : K ⟶ L) :
    extendMap ((F.mapHomologicalComplex c).map a) e ≫ (extendMapIso F e L).hom =
      (extendMapIso F e K).hom ≫ (F.mapHomologicalComplex c').map (extendMap a e) := by
  apply Hom.ext
  funext n
  change extend.mapX ((F.mapHomologicalComplex c).map a) (e.r n) ≫
      (extendMapComponentIso F L (e.r n)).hom =
    (extendMapComponentIso F K (e.r n)).hom ≫ F.map (extend.mapX a (e.r n))
  cases e.r n with
  | none => exact (Limits.isZero_zero D).eq_of_src _ _
  | some i =>
    change F.map (a.f i) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (a.f i)
    simp only [Category.comp_id, Category.id_comp]

end HomologicalComplex

namespace ComplexShape.Embedding

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
  {ι : Type i} {ι' : Type j} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The natural extension comparison uses the original functor and embedding. -/
def extendFunctorMapIso (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    F.mapHomologicalComplex c ⋙ e.extendFunctor D ≅
      e.extendFunctor C ⋙ F.mapHomologicalComplex c' :=
  NatIso.ofComponents (fun K => HomologicalComplex.extendMapIso F e K) (by
    intro K L a
    exact HomologicalComplex.extendMapIso_naturality F e a)

end ComplexShape.Embedding

end
