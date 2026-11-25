/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.TotalComplexExact
public import MathlibExt.Algebra.Homology.TotalComplexDownNat
public import MathlibExt.CategoryTheory.GradedObject.FiniteFibers
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Functors and total complexes

An additive functor commutes with totalization when it preserves the
coproduct over each total-shape fiber. The fibers may be infinite.
Summand formulas characterize the comparison and give its naturality;
finite-fiber totalization is a specialization.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w₁ w₂ w₁₂ v₁ u₁ v₂ u₂

namespace HomologicalComplex₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) C]
  [∀ i₁₂, HasColimitsOfShape (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) D]
  [∀ i₁₂, PreservesColimitsOfShape
    (Discrete (TotalFiber c₁ c₂ c₁₂ i₁₂)) F]

/-- Map both directions of a bicomplex through an additive functor. -/
abbrev mapBicomplexFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ :=
  (F.mapHomologicalComplex c₂).mapHomologicalComplex c₁

/-- The bicomplex obtained by applying an additive functor in both
directions. -/
abbrev mapBicomplex
    (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ D c₁ c₂ :=
  (mapBicomplexFunctor F).obj K

/-- Canonical comparison between mapping one total-degree object and the
same total-degree object of the mapped bicomplex. -/
noncomputable def mapTotalXIso
    (K : HomologicalComplex₂ C c₁ c₂) (i₁₂ : I₁₂) :
    F.obj ((K.total c₁₂).X i₁₂) ≅ ((mapBicomplex F K).total c₁₂).X i₁₂ := by
  let Fib := TotalFiber c₁ c₂ c₁₂ i₁₂
  change F.obj (∐ fun i : Fib => (K.X i.val.1).X i.val.2) ≅
    ∐ fun i : Fib => F.obj ((K.X i.val.1).X i.val.2)
  exact PreservesCoproduct.iso F (fun i : Fib => (K.X i.val.1).X i.val.2)

/-- The degreewise total comparison carries every mapped summand
inclusion to the corresponding inclusion of the mapped bicomplex. -/
@[reassoc (attr := simp)]
theorem map_ιTotal_comp_mapTotalXIso_hom
    (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    F.map (K.ιTotal c₁₂ i₁ i₂ i₁₂ h) ≫ (mapTotalXIso F c₁₂ K i₁₂).hom =
      (mapBicomplex F K).ιTotal c₁₂ i₁ i₂ i₁₂ h := by
  change F.map (Sigma.ι
      (fun i : TotalFiber c₁ c₂ c₁₂ i₁₂ =>
        (K.X i.val.1).X i.val.2) ⟨(i₁, i₂), h⟩) ≫
      (PreservesCoproduct.iso F (fun i : TotalFiber c₁ c₂ c₁₂ i₁₂ =>
        (K.X i.val.1).X i.val.2)).hom =
    Sigma.ι (fun i : TotalFiber c₁ c₂ c₁₂ i₁₂ =>
      F.obj ((K.X i.val.1).X i.val.2)) ⟨(i₁, i₂), h⟩
  rw [← cancel_mono
    (PreservesCoproduct.iso F (fun i : TotalFiber c₁ c₂ c₁₂ i₁₂ =>
      (K.X i.val.1).X i.val.2)).inv]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [PreservesCoproduct.inv_hom] using
    (ι_comp_sigmaComparison F (fun i : TotalFiber c₁ c₂ c₁₂ i₁₂ =>
      (K.X i.val.1).X i.val.2) ⟨(i₁, i₂), h⟩).symm

/-- The inverse comparison restricts to the mapped inclusion on every summand. -/
@[reassoc (attr := simp)]
theorem mapped_ιTotal_comp_mapTotalXIso_inv
    (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    (mapBicomplex F K).ιTotal c₁₂ i₁ i₂ i₁₂ h ≫
        (mapTotalXIso F c₁₂ K i₁₂).inv =
      F.map (K.ιTotal c₁₂ i₁ i₂ i₁₂ h) := by
  rw [← map_ιTotal_comp_mapTotalXIso_hom F c₁₂ K i₁ i₂ i₁₂ h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The degreewise comparison also intertwines the possibly-zero inclusion
used in the total differential. -/
@[reassoc (attr := simp)]
theorem map_ιTotalOrZero_comp_mapTotalXIso_hom
    (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    F.map (K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂) ≫
        (mapTotalXIso F c₁₂ K i₁₂).hom =
      (mapBicomplex F K).ιTotalOrZero c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂
  · rw [K.ιTotalOrZero_eq c₁₂ i₁ i₂ i₁₂ h,
      (mapBicomplex F K).ιTotalOrZero_eq c₁₂ i₁ i₂ i₁₂ h]
    exact map_ιTotal_comp_mapTotalXIso_hom F c₁₂ K i₁ i₂ i₁₂ h
  · rw [K.ιTotalOrZero_eq_zero c₁₂ i₁ i₂ i₁₂ h,
      (mapBicomplex F K).ιTotalOrZero_eq_zero c₁₂ i₁ i₂ i₁₂ h,
      F.map_zero, CategoryTheory.Limits.zero_comp]

/-- Mapping a horizontal total-differential component and then applying the
coproduct comparison gives the corresponding mapped component. -/
@[reassoc (attr := simp)]
theorem map_d₁_comp_mapTotalXIso_hom
    (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    F.map (K.d₁ c₁₂ i₁ i₂ i₁₂) ≫ (mapTotalXIso F c₁₂ K i₁₂).hom =
      (mapBicomplex F K).d₁ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq' c₁₂ h₁ i₂ i₁₂,
      (mapBicomplex F K).d₁_eq' c₁₂ h₁ i₂ i₁₂]
    simp only [Functor.map_units_smul, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc,
      map_ιTotalOrZero_comp_mapTotalXIso_hom]
    rfl
  · rw [K.d₁_eq_zero c₁₂ i₁ i₂ i₁₂ h₁,
      (mapBicomplex F K).d₁_eq_zero c₁₂ i₁ i₂ i₁₂ h₁,
      F.map_zero, CategoryTheory.Limits.zero_comp]

/-- Mapping a vertical total-differential component and then applying the
coproduct comparison gives the corresponding mapped component. -/
@[reassoc (attr := simp)]
theorem map_d₂_comp_mapTotalXIso_hom
    (K : HomologicalComplex₂ C c₁ c₂) (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    F.map (K.d₂ c₁₂ i₁ i₂ i₁₂) ≫ (mapTotalXIso F c₁₂ K i₁₂).hom =
      (mapBicomplex F K).d₂ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq' c₁₂ i₁ h₂ i₁₂,
      (mapBicomplex F K).d₂_eq' c₁₂ i₁ h₂ i₁₂]
    simp only [Functor.map_units_smul, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc,
      map_ιTotalOrZero_comp_mapTotalXIso_hom]
    rfl
  · rw [K.d₂_eq_zero c₁₂ i₁ i₂ i₁₂ h₂,
      (mapBicomplex F K).d₂_eq_zero c₁₂ i₁ i₂ i₁₂ h₂,
      F.map_zero, CategoryTheory.Limits.zero_comp]

/-- The degreewise fiber-coproduct comparison commutes with the total
differentials. -/
theorem mapTotalXIso_hom_d
    (K : HomologicalComplex₂ C c₁ c₂) (i j : I₁₂) :
    (mapTotalXIso F c₁₂ K i).hom ≫
        ((mapBicomplex F K).total c₁₂).d i j =
      F.map ((K.total c₁₂).d i j) ≫ (mapTotalXIso F c₁₂ K j).hom := by
  rw [← cancel_epi (mapTotalXIso F c₁₂ K i).inv,
    Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  rw [mapped_ιTotal_comp_mapTotalXIso_inv_assoc,
    ← Category.assoc, ← F.map_comp]
  simp only [HomologicalComplex₂.total_d,
    Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂, Functor.map_add,
    Preadditive.add_comp,
    map_d₁_comp_mapTotalXIso_hom,
    map_d₂_comp_mapTotalXIso_hom]

/-- An additive functor preserving every total fiber coproduct commutes with
totalization. -/
@[simps! hom_f inv_f]
noncomputable def mapTotalIso
    (K : HomologicalComplex₂ C c₁ c₂) :
    (F.mapHomologicalComplex c₁₂).obj (K.total c₁₂) ≅
      (mapBicomplex F K).total c₁₂ :=
  HomologicalComplex.Hom.isoOfComponents
    (mapTotalXIso F c₁₂ K)
    (fun i j _ ↦ mapTotalXIso_hom_d F c₁₂ K i j)

/-- Naturality of the total-complex comparison for a bicomplex map. -/
theorem mapTotalIso_hom_naturality
    {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) :
    (F.mapHomologicalComplex c₁₂).map (HomologicalComplex₂.total.map f c₁₂) ≫
        (mapTotalIso F c₁₂ L).hom =
      (mapTotalIso F c₁₂ K).hom ≫ HomologicalComplex₂.total.map
        ((mapBicomplexFunctor F).map f) c₁₂ := by
  ext n
  change F.map ((HomologicalComplex₂.total.map f c₁₂).f n) ≫
        (mapTotalXIso F c₁₂ L n).hom =
      (mapTotalXIso F c₁₂ K n).hom ≫
        (HomologicalComplex₂.total.map ((mapBicomplexFunctor F).map f) c₁₂).f n
  rw [← cancel_epi (mapTotalXIso F c₁₂ K n).inv,
    Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  rw [mapped_ιTotal_comp_mapTotalXIso_inv_assoc,
    ← Category.assoc, ← F.map_comp,
    HomologicalComplex₂.ιTotal_map, F.map_comp,
    Category.assoc,
    map_ιTotal_comp_mapTotalXIso_hom,
    HomologicalComplex₂.ιTotal_map]
  rfl

/-- The functor obtained by totalizing first and then applying `F`. -/
abbrev mapAfterTotalFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex D c₁₂ :=
  HomologicalComplex₂.totalFunctor C c₁ c₂ c₁₂ ⋙ F.mapHomologicalComplex c₁₂

/-- The functor obtained by applying `F` in both bicomplex directions and
then totalizing. -/
abbrev totalAfterMapFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex D c₁₂ :=
  mapBicomplexFunctor F ⋙ HomologicalComplex₂.totalFunctor D c₁ c₂ c₁₂

/-- Natural form of the fact that an additive functor preserving every total
fiber coproduct commutes with totalization. -/
noncomputable def mapTotalNatIso :
    mapAfterTotalFunctor (c₁ := c₁) (c₂ := c₂) F c₁₂ ≅
      totalAfterMapFunctor (c₁ := c₁) (c₂ := c₂) F c₁₂ :=
  NatIso.ofComponents (mapTotalIso (c₁ := c₁) (c₂ := c₂) F c₁₂)
    (mapTotalIso_hom_naturality (c₁ := c₁) (c₂ := c₂) F c₁₂)

section FiniteFibersOfHasTotal

variable {C' : Type u₁} [Category.{v₁} C'] [Preadditive C']
variable {D' : Type u₂} [Category.{v₂} D'] [Preadditive D']
variable (G : C' ⥤ D') [G.Additive]
variable {J₁ : Type w₁} {J₂ : Type w₂} {J₁₂ : Type w₁₂}
  {s₁ : ComplexShape J₁} {s₂ : ComplexShape J₂} (s₁₂ : ComplexShape J₁₂)
  [TotalComplexShape s₁ s₂ s₁₂] [DecidableEq J₁₂]
  [FiniteTotalFibers s₁ s₂ s₁₂]
variable (L : HomologicalComplex₂ C' s₁ s₂) [L.HasTotal s₁₂]
  [(mapBicomplex G L).HasTotal s₁₂]

/-- Per-bicomplex comparison between mapping a finite-fiber total degree and
totalizing the mapped bicomplex. Unlike `mapTotalXIso`, this only assumes that
the two totals in question exist; it does not require all fiber coproducts in
either ambient category. -/
noncomputable def mapTotalXIsoOfHasTotal (j₁₂ : J₁₂) :
    G.obj ((L.total s₁₂).X j₁₂) ≅ ((mapBicomplex G L).total s₁₂).X j₁₂ := by
  letI : Finite (TotalFiber s₁ s₂ s₁₂ j₁₂) := inferInstance
  letI : HasCoproduct (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) := inferInstance
  letI : HasCoproduct ((mapBicomplex G L).toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) := inferInstance
  letI : HasCoproduct (fun j => G.obj (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂ j)) := by
    change HasCoproduct ((mapBicomplex G L).toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂)
    infer_instance
  letI : PreservesColimit (Discrete.functor
      (L.toGradedObject.mapObjFun
        (ComplexShape.π s₁ s₂ s₁₂) j₁₂)) G := inferInstance
  change G.obj (∐ L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) ≅
    ∐ fun j => G.obj (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂ j)
  exact PreservesCoproduct.iso G
    (L.toGradedObject.mapObjFun (ComplexShape.π s₁ s₂ s₁₂) j₁₂)

/-- The per-bicomplex comparison carries each mapped summand inclusion to the
corresponding inclusion in the mapped total. -/
@[reassoc (attr := simp)]
theorem map_ιTotal_comp_mapTotalXIsoOfHasTotal_hom
    (j₁ : J₁) (j₂ : J₂) (j₁₂ : J₁₂)
    (h : ComplexShape.π s₁ s₂ s₁₂ (j₁, j₂) = j₁₂) :
    G.map (L.ιTotal s₁₂ j₁ j₂ j₁₂ h) ≫
        (mapTotalXIsoOfHasTotal G s₁₂ L j₁₂).hom =
      (mapBicomplex G L).ιTotal s₁₂ j₁ j₂ j₁₂ h := by
  let : Finite (TotalFiber s₁ s₂ s₁₂ j₁₂) := inferInstance
  let : HasCoproduct (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) := inferInstance
  let : HasCoproduct ((mapBicomplex G L).toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) := inferInstance
  let : HasCoproduct (fun j => G.obj (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂ j)) := by
    change HasCoproduct ((mapBicomplex G L).toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂)
    infer_instance
  let : PreservesColimit (Discrete.functor
      (L.toGradedObject.mapObjFun
        (ComplexShape.π s₁ s₂ s₁₂) j₁₂)) G := inferInstance
  change G.map (Sigma.ι (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) ⟨(j₁, j₂), h⟩) ≫
      (PreservesCoproduct.iso G (L.toGradedObject.mapObjFun
        (ComplexShape.π s₁ s₂ s₁₂) j₁₂)).hom =
    Sigma.ι (fun j => G.obj (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂ j)) ⟨(j₁, j₂), h⟩
  rw [← cancel_mono
    (PreservesCoproduct.iso G (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂)).inv]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [PreservesCoproduct.inv_hom] using
    (ι_comp_sigmaComparison G (L.toGradedObject.mapObjFun
      (ComplexShape.π s₁ s₂ s₁₂) j₁₂) ⟨(j₁, j₂), h⟩).symm

/-- The inverse per-bicomplex comparison restricts to the mapped inclusion on
each summand. -/
@[reassoc (attr := simp)]
theorem mapped_ιTotal_comp_mapTotalXIsoOfHasTotal_inv
    (j₁ : J₁) (j₂ : J₂) (j₁₂ : J₁₂)
    (h : ComplexShape.π s₁ s₂ s₁₂ (j₁, j₂) = j₁₂) :
    (mapBicomplex G L).ιTotal s₁₂ j₁ j₂ j₁₂ h ≫
        (mapTotalXIsoOfHasTotal G s₁₂ L j₁₂).inv =
      G.map (L.ιTotal s₁₂ j₁ j₂ j₁₂ h) := by
  rw [← map_ιTotal_comp_mapTotalXIsoOfHasTotal_hom G s₁₂ L j₁ j₂ j₁₂ h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The per-bicomplex comparison intertwines the possibly-zero inclusion used
in the total differential. -/
@[reassoc (attr := simp)]
theorem map_ιTotalOrZero_comp_mapTotalXIsoOfHasTotal_hom
    (j₁ : J₁) (j₂ : J₂) (j₁₂ : J₁₂) :
    G.map (L.ιTotalOrZero s₁₂ j₁ j₂ j₁₂) ≫
        (mapTotalXIsoOfHasTotal G s₁₂ L j₁₂).hom =
      (mapBicomplex G L).ιTotalOrZero s₁₂ j₁ j₂ j₁₂ := by
  by_cases h : ComplexShape.π s₁ s₂ s₁₂ (j₁, j₂) = j₁₂
  · rw [L.ιTotalOrZero_eq s₁₂ j₁ j₂ j₁₂ h,
      (mapBicomplex G L).ιTotalOrZero_eq s₁₂ j₁ j₂ j₁₂ h]
    exact map_ιTotal_comp_mapTotalXIsoOfHasTotal_hom
      G s₁₂ L j₁ j₂ j₁₂ h
  · rw [L.ιTotalOrZero_eq_zero s₁₂ j₁ j₂ j₁₂ h,
      (mapBicomplex G L).ιTotalOrZero_eq_zero s₁₂ j₁ j₂ j₁₂ h,
      G.map_zero, CategoryTheory.Limits.zero_comp]

/-- Mapping a horizontal differential component and then applying the
per-bicomplex comparison gives the corresponding mapped component. -/
@[reassoc (attr := simp)]
theorem map_d₁_comp_mapTotalXIsoOfHasTotal_hom
    (j₁ : J₁) (j₂ : J₂) (j₁₂ : J₁₂) :
    G.map (L.d₁ s₁₂ j₁ j₂ j₁₂) ≫
        (mapTotalXIsoOfHasTotal G s₁₂ L j₁₂).hom =
      (mapBicomplex G L).d₁ s₁₂ j₁ j₂ j₁₂ := by
  by_cases h₁ : s₁.Rel j₁ (s₁.next j₁)
  · rw [L.d₁_eq' s₁₂ h₁ j₂ j₁₂,
      (mapBicomplex G L).d₁_eq' s₁₂ h₁ j₂ j₁₂]
    simp only [Functor.map_units_smul, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc,
      map_ιTotalOrZero_comp_mapTotalXIsoOfHasTotal_hom]
    rfl
  · rw [L.d₁_eq_zero s₁₂ j₁ j₂ j₁₂ h₁,
      (mapBicomplex G L).d₁_eq_zero s₁₂ j₁ j₂ j₁₂ h₁,
      G.map_zero, CategoryTheory.Limits.zero_comp]

/-- Mapping a vertical differential component and then applying the
per-bicomplex comparison gives the corresponding mapped component. -/
@[reassoc (attr := simp)]
theorem map_d₂_comp_mapTotalXIsoOfHasTotal_hom
    (j₁ : J₁) (j₂ : J₂) (j₁₂ : J₁₂) :
    G.map (L.d₂ s₁₂ j₁ j₂ j₁₂) ≫
        (mapTotalXIsoOfHasTotal G s₁₂ L j₁₂).hom =
      (mapBicomplex G L).d₂ s₁₂ j₁ j₂ j₁₂ := by
  by_cases h₂ : s₂.Rel j₂ (s₂.next j₂)
  · rw [L.d₂_eq' s₁₂ j₁ h₂ j₁₂,
      (mapBicomplex G L).d₂_eq' s₁₂ j₁ h₂ j₁₂]
    simp only [Functor.map_units_smul, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc,
      map_ιTotalOrZero_comp_mapTotalXIsoOfHasTotal_hom]
    rfl
  · rw [L.d₂_eq_zero s₁₂ j₁ j₂ j₁₂ h₂,
      (mapBicomplex G L).d₂_eq_zero s₁₂ j₁ j₂ j₁₂ h₂,
      G.map_zero, CategoryTheory.Limits.zero_comp]

/-- The degreewise per-bicomplex comparison commutes with total
differentials. -/
theorem mapTotalXIsoOfHasTotal_hom_d (i j : J₁₂) :
    (mapTotalXIsoOfHasTotal G s₁₂ L i).hom ≫
        ((mapBicomplex G L).total s₁₂).d i j =
      G.map ((L.total s₁₂).d i j) ≫
        (mapTotalXIsoOfHasTotal G s₁₂ L j).hom := by
  rw [← cancel_epi (mapTotalXIsoOfHasTotal G s₁₂ L i).inv,
    Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro j₁ j₂ h
  rw [mapped_ιTotal_comp_mapTotalXIsoOfHasTotal_inv_assoc,
    ← Category.assoc, ← G.map_comp]
  simp only [HomologicalComplex₂.total_d,
    Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
    HomologicalComplex₂.ι_D₂, Functor.map_add,
    Preadditive.add_comp,
    map_d₁_comp_mapTotalXIsoOfHasTotal_hom,
    map_d₂_comp_mapTotalXIsoOfHasTotal_hom]

/-- An additive functor commutes with a specified finite-fiber total whenever
the source and mapped totals both exist. -/
@[simps! hom_f inv_f]
noncomputable def mapTotalIsoOfHasTotal :
    (G.mapHomologicalComplex s₁₂).obj (L.total s₁₂) ≅
      (mapBicomplex G L).total s₁₂ :=
  HomologicalComplex.Hom.isoOfComponents
    (mapTotalXIsoOfHasTotal G s₁₂ L)
    (fun i j _ ↦ mapTotalXIsoOfHasTotal_hom_d G s₁₂ L i j)

end FiniteFibersOfHasTotal

end HomologicalComplex₂

end


noncomputable section

namespace HomologicalComplex₂

universe uF vF uG vG w₁F w₂F wTF

open CategoryTheory Limits

variable {C : Type uF} [Category.{vF} C] [Preadditive C]
  {D : Type uG} [Category.{vG} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  {I₁ : Type w₁F} {I₂ : Type w₂F} {I : Type wTF}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c : ComplexShape I)
  [TotalComplexShape c₁ c₂ c] [DecidableEq I] [FiniteTotalFibers c₁ c₂ c]
  (K L : HomologicalComplex₂ C c₁ c₂)
  [K.HasTotal c] [(mapBicomplex F K).HasTotal c]
  [L.HasTotal c] [(mapBicomplex F L).HasTotal c]

/-- The existing finite per-bicomplex total comparison is natural for the actual
bicomplex morphism; no ambient fiber-colimit hypotheses are needed. -/
theorem mapTotalIsoOfHasTotal_hom_naturality (f : K ⟶ L) :
    (F.mapHomologicalComplex c).map (HomologicalComplex₂.total.map f c) ≫
        (mapTotalIsoOfHasTotal F c L).hom =
      (mapTotalIsoOfHasTotal F c K).hom ≫
        HomologicalComplex₂.total.map ((mapBicomplexFunctor F).map f) c := by
  apply HomologicalComplex.hom_ext
  intro n
  change F.map ((HomologicalComplex₂.total.map f c).f n) ≫
      (mapTotalXIsoOfHasTotal F c L n).hom =
    (mapTotalXIsoOfHasTotal F c K n).hom ≫
      (HomologicalComplex₂.total.map ((mapBicomplexFunctor F).map f) c).f n
  rw [← cancel_epi (mapTotalXIsoOfHasTotal F c K n).inv, Iso.inv_hom_id_assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  rw [mapped_ιTotal_comp_mapTotalXIsoOfHasTotal_inv_assoc,
    ← Category.assoc, ← F.map_comp,
    HomologicalComplex₂.ιTotal_map, F.map_comp, Category.assoc,
    map_ιTotal_comp_mapTotalXIsoOfHasTotal_hom,
    HomologicalComplex₂.ιTotal_map]
  rfl

end HomologicalComplex₂

end


noncomputable section

namespace HomologicalComplex₂

universe u v uT vT

open CategoryTheory Limits

section FunctorTotalCompatibility

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type uT} [Category.{vT} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [K.HasTotal (ComplexShape.down ℕ)]
  [∀ n, PreservesColimit
    (Discrete.functor (K.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) F]

/-- Compatibility name for the finite per-bicomplex total-degree comparison. -/
def functorTotalIsoComponent (n : ℕ) :
    letI :
        (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
      CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
        (fun pq : ℕ × ℕ => pq.1 + pq.2)
    F.obj ((K.total (ComplexShape.down ℕ)).X n) ≅
      ((mapBicomplex F K).total (ComplexShape.down ℕ)).X n := by
  letI : (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
    CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
      (fun pq : ℕ × ℕ => pq.1 + pq.2)
  exact mapTotalXIsoOfHasTotal F (ComplexShape.down ℕ) K n

/-- The compatibility comparison retains each mapped summand inclusion. -/
@[reassoc]
theorem map_ιTotal_functorTotalIsoComponent_hom (p q n : ℕ) (h : p + q = n) :
    letI :
        (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
      CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
        (fun pq : ℕ × ℕ => pq.1 + pq.2)
    F.map (K.ιTotal (ComplexShape.down ℕ) p q n h) ≫
        (functorTotalIsoComponent F K n).hom =
      (mapBicomplex F K).ιTotal (ComplexShape.down ℕ) p q n h := by
  let _ : (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
    CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
      (fun pq : ℕ × ℕ => pq.1 + pq.2)
  exact map_ιTotal_comp_mapTotalXIsoOfHasTotal_hom F (ComplexShape.down ℕ) K p q n h

/-- Compatibility name for the existing finite per-bicomplex total comparison. -/
def functorTotalIso :
    letI :
        (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
      CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
        (fun pq : ℕ × ℕ => pq.1 + pq.2)
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (K.total (ComplexShape.down ℕ)) ≅
      (mapBicomplex F K).total (ComplexShape.down ℕ) := by
  letI : (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
    CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
      (fun pq : ℕ × ℕ => pq.1 + pq.2)
  exact mapTotalIsoOfHasTotal F (ComplexShape.down ℕ) K

variable (L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  [L.HasTotal (ComplexShape.down ℕ)]
  [∀ n, PreservesColimit
    (Discrete.functor (L.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) F]

/-- Naturality of the compatibility comparison forwards to the finite per-object API. -/
@[reassoc]
theorem functorTotalIso_hom_naturality (φ : K ⟶ L) :
    letI : (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
        CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
          (fun pq : ℕ × ℕ => pq.1 + pq.2)
    letI : (mapBicomplex F L).HasTotal (ComplexShape.down ℕ) :=
        CategoryTheory.GradedObject.hasMap_of_preserves F L.toGradedObject
          (fun pq : ℕ × ℕ => pq.1 + pq.2)
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) ≫
          (functorTotalIso F L).hom =
      (functorTotalIso F K).hom ≫ HomologicalComplex₂.total.map
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ) (ComplexShape.down ℕ) := by
  let _ : (mapBicomplex F K).HasTotal (ComplexShape.down ℕ) :=
    CategoryTheory.GradedObject.hasMap_of_preserves F K.toGradedObject
      (fun pq : ℕ × ℕ => pq.1 + pq.2)
  let _ : (mapBicomplex F L).HasTotal (ComplexShape.down ℕ) :=
    CategoryTheory.GradedObject.hasMap_of_preserves F L.toGradedObject
      (fun pq : ℕ × ℕ => pq.1 + pq.2)
  exact mapTotalIsoOfHasTotal_hom_naturality F (ComplexShape.down ℕ) K L φ

end FunctorTotalCompatibility

end HomologicalComplex₂

end
