/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.Kunneth.Braiding
public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Diagonal
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Canonical coalgebras on the homology of chain comonoids

Every chain comonoid has a canonical diagonal into homology of its actual
tensor square. If the canonical Künneth map for its square and for its
right-associated tensor cube are isomorphisms, that diagonal is an actual
graded comonoid. Only invertibility of named canonical maps is a hypothesis;
associator, unit and braiding coherence are proved in `Kunneth.Coherence`
and `Kunneth.Braiding`. Flat terms and flat homology in the original complex
suffice, by the existing collapse theorem. Over a field the existing native
comonoid transport is also packaged as a functor.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace HomologicalComplex.HomologyCoalgebra

variable {R : Type u} [CommRing R]


variable (C : (ChainComplex (ModuleCat.{u} R) ℕ)) [ComonObj C]

private theorem unitMap_eq_unitIso_hom : Kunneth.unitMap (R := R) =
    (Kunneth.unitIso (R := R)).hom := rfl

private theorem laxMonoidal_ε :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (Kunneth.homologyFunctor (R := R))
      Kunneth.laxMonoidal = Kunneth.unitMap (R := R) := rfl

private theorem laxMonoidal_μ (A B : ChainComplex (ModuleCat.{u} R) ℕ) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (Kunneth.homologyFunctor (R := R))
      Kunneth.laxMonoidal A B = Kunneth.tensorator A B := rfl

@[reassoc]
private theorem tensorator_natural_left {A B : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : A ⟶ B) (D : ChainComplex (ModuleCat.{u} R) ℕ) :
    (Kunneth.homologyFunctor.map f ▷ Kunneth.homologyFunctor.obj D) ≫
      Kunneth.tensorator B D =
    Kunneth.tensorator A D ≫ Kunneth.homologyFunctor.map (f ▷ D) := by
  have h := Kunneth.tensorator_naturality f (𝟙 D)
  rw [(Kunneth.homologyFunctor (R := R)).map_id D, tensorHom_id] at h
  simpa only [tensorHom_id] using h

@[reassoc]
private theorem tensorator_natural_right (D : ChainComplex (ModuleCat.{u} R) ℕ)
    {A B : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B) :
    (Kunneth.homologyFunctor.obj D ◁ Kunneth.homologyFunctor.map f) ≫
      Kunneth.tensorator D B =
    Kunneth.tensorator D A ≫ Kunneth.homologyFunctor.map (D ◁ f) := by
  have h := Kunneth.tensorator_naturality (𝟙 D) f
  rw [(Kunneth.homologyFunctor (R := R)).map_id D, id_tensorHom] at h
  simpa only [id_tensorHom] using h

/-- The canonical homology counit uses the actual homology of the single
scalar-unit complex. -/
def counit : (Kunneth.homologyFunctor (R := R)).obj C ⟶ 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) :=
  (Kunneth.homologyFunctor (R := R)).map ε[C] ≫ (Kunneth.unitIso (R := R)).inv

@[reassoc (attr := simp)]
theorem counit_unitMap : counit C ≫ Kunneth.unitMap = (Kunneth.homologyFunctor (R := R)).map ε[C] := by
  simp only [counit, unitMap_eq_unitIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical coaugmentation of homology, from an actual chain
coaugmentation. -/
def coaug (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) : 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) ⟶
  (Kunneth.homologyFunctor (R := R)).obj C :=
  Kunneth.unitMap ≫ (Kunneth.homologyFunctor (R := R)).map η

omit [ComonObj C] in
theorem coaug_apply (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) (n : ℕ) :
    coaug C η n = (Kunneth.unitComparison n).hom ≫ homologyMap η n := rfl

omit [ComonObj C] in
@[reassoc]
theorem coaug_naturality {D : (ChainComplex (ModuleCat.{u} R) ℕ)} (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) (η'
  : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ D)
    (f : C ⟶ D) (hη : η ≫ f = η') : coaug C η ≫ (Kunneth.homologyFunctor (R := R)).map f = coaug D η' := by
  simp only [coaug, Category.assoc, ← Functor.map_comp, hη]

section SquareIsIso

variable [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]

/-- The inverse of the canonical cycle Künneth tensorator defines the
graded homology diagonal. -/
def comul : (Kunneth.homologyFunctor (R := R)).obj C ⟶ (Kunneth.homologyFunctor (R := R)).obj C ⊗
  (Kunneth.homologyFunctor (R := R)).obj C :=
  canonicalToTensorHomology C ≫ inv (Kunneth.tensorator C C)

@[reassoc (attr := simp)]
theorem comul_tensorator : comul C ≫ Kunneth.tensorator C C =
    canonicalToTensorHomology C := by
  simp [comul]

@[reassoc]
theorem comul_naturality {D : (ChainComplex (ModuleCat.{u} R) ℕ)} [ComonObj D]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap D D n)]
    (f : C ⟶ D) [IsComonHom f] :
    (Kunneth.homologyFunctor (R := R)).map f ≫ comul D = comul C ≫ ((Kunneth.homologyFunctor (R := R)).map f ⊗ₘ
      (Kunneth.homologyFunctor (R := R)).map f) := by
  apply (cancel_mono (Kunneth.tensorator D D)).1
  simp only [Category.assoc]
  rw [comul_tensorator]
  have ht := congrArg (fun z => comul C ≫ z) (Kunneth.tensorator_naturality f f)
  rw [ht, comul_tensorator_assoc]
  exact canonicalToTensorHomology_naturality C f

private theorem leftUnitComparison (C : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    Kunneth.unitMap ▷ (Kunneth.homologyFunctor (R := R)).obj C ≫ Kunneth.tensorator (𝟙_ (ChainComplex (ModuleCat.{u}
      R) ℕ)) C =
      (λ_ ((Kunneth.homologyFunctor (R := R)).obj C)).hom ≫ (Kunneth.homologyFunctor (R := R)).map (λ_ C).inv := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  rw [← cancel_epi (λ_ ((Kunneth.homologyFunctor (R := R)).obj C)).inv]
  simpa only [laxMonoidal_ε, laxMonoidal_μ, Category.assoc, Iso.inv_hom_id_assoc] using
    Functor.LaxMonoidal.left_unitality_inv (Kunneth.homologyFunctor (R := R)) C

private theorem rightUnitComparison (C : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    (Kunneth.homologyFunctor (R := R)).obj C ◁ Kunneth.unitMap ≫ Kunneth.tensorator C (𝟙_ (ChainComplex (ModuleCat.{u}
      R) ℕ)) =
      (ρ_ ((Kunneth.homologyFunctor (R := R)).obj C)).hom ≫ (Kunneth.homologyFunctor (R := R)).map (ρ_ C).inv := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  rw [← cancel_epi (ρ_ ((Kunneth.homologyFunctor (R := R)).obj C)).inv]
  simpa only [laxMonoidal_ε, laxMonoidal_μ, Category.assoc, Iso.inv_hom_id_assoc] using
    Functor.LaxMonoidal.right_unitality_inv (Kunneth.homologyFunctor (R := R)) C

/-- The transported diagonal satisfies the actual left counit law. -/
theorem counit_comul : comul C ≫ counit C ▷ (Kunneth.homologyFunctor (R := R)).obj C = (λ_ ((Kunneth.homologyFunctor
  (R := R)).obj C)).inv := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  let ν := Kunneth.unitMap ▷ (Kunneth.homologyFunctor (R := R)).obj C ≫ Kunneth.tensorator (𝟙_ (ChainComplex
    (ModuleCat.{u} R) ℕ)) C
  letI : IsIso ν := by
    dsimp only [ν]
    rw [leftUnitComparison]
    infer_instance
  apply (cancel_mono ν).1
  simp only [comul, counit, ν, comp_whiskerRight, Category.assoc]
  have hu := congrArg (fun z => z ▷ (Kunneth.homologyFunctor (R := R)).obj C)
    (Kunneth.unitIso (R := R)).inv_hom_id
  simp only [comp_whiskerRight, id_whiskerRight] at hu
  rw [unitMap_eq_unitIso_hom]
  rw [reassoc_of% hu]
  have hn := congrArg (fun z => canonicalToTensorHomology C ≫
    inv (Kunneth.tensorator C C) ≫ z)
    (tensorator_natural_left ε[C] C)
  rw [hn,

    IsIso.inv_hom_id_assoc]
  unfold canonicalToTensorHomology
  rw [← Functor.map_comp]
  rw [ComonObj.counit_comul]
  simpa only [laxMonoidal_ε, laxMonoidal_μ, unitMap_eq_unitIso_hom] using
    (Functor.LaxMonoidal.left_unitality_inv (Kunneth.homologyFunctor (R := R)) C).symm

/-- The transported diagonal satisfies the actual right counit law. -/
theorem comul_counit : comul C ≫ (Kunneth.homologyFunctor (R := R)).obj C ◁ counit C = (ρ_ ((Kunneth.homologyFunctor
  (R := R)).obj C)).inv := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  let ν := (Kunneth.homologyFunctor (R := R)).obj C ◁ Kunneth.unitMap ≫ Kunneth.tensorator C (𝟙_ (ChainComplex
    (ModuleCat.{u} R) ℕ))
  letI : IsIso ν := by
    dsimp only [ν]
    rw [rightUnitComparison]
    infer_instance
  apply (cancel_mono ν).1
  simp only [comul, counit, ν, MonoidalCategory.whiskerLeft_comp, Category.assoc, laxMonoidal_ε, laxMonoidal_μ]
  have hu := congrArg (fun z => (Kunneth.homologyFunctor (R := R)).obj C ◁ z)
    (Kunneth.unitIso (R := R)).inv_hom_id
  simp only [whiskerLeft_comp, whiskerLeft_id] at hu
  rw [unitMap_eq_unitIso_hom]
  rw [reassoc_of% hu]
  have hn := congrArg (fun z => canonicalToTensorHomology C ≫
    inv (Kunneth.tensorator C C) ≫ z)
    (tensorator_natural_right C ε[C])
  rw [hn,

    IsIso.inv_hom_id_assoc]
  unfold canonicalToTensorHomology
  rw [← Functor.map_comp]
  rw [ComonObj.comul_counit]
  simpa only [laxMonoidal_ε, laxMonoidal_μ, unitMap_eq_unitIso_hom] using
    (Functor.LaxMonoidal.right_unitality_inv (Kunneth.homologyFunctor (R := R)) C).symm

/-- Coassociativity needs only the square comparison and the canonical
right-associated cube comparison to be invertible. -/
theorem comul_assoc
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)] :
    comul C ≫ (Kunneth.homologyFunctor (R := R)).obj C ◁ comul C =
      comul C ≫ comul C ▷ (Kunneth.homologyFunctor (R := R)).obj C ≫ (α_ ((Kunneth.homologyFunctor (R := R)).obj C)
        ((Kunneth.homologyFunctor (R := R)).obj C) ((Kunneth.homologyFunctor (R := R)).obj C)).hom := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  let χ := (Kunneth.homologyFunctor (R := R)).obj C ◁ Kunneth.tensorator C C ≫ Kunneth.tensorator C (C ⊗ C)
  letI : IsIso χ := inferInstance
  apply (cancel_mono χ).1
  have hl : (comul C ≫ (Kunneth.homologyFunctor (R := R)).obj C ◁ comul C) ≫ χ = (Kunneth.homologyFunctor (R :=
    R)).map (Δ[C] ≫ C ◁ Δ[C]) := by
    simp only [comul, canonicalToTensorHomology, χ,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, laxMonoidal_ε, laxMonoidal_μ]
    have hu := congrArg (fun z => (Kunneth.homologyFunctor (R := R)).obj C ◁ z)
      (IsIso.inv_hom_id (Kunneth.tensorator C C))
    simp only [whiskerLeft_comp, whiskerLeft_id] at hu
    rw [reassoc_of% hu]
    have hn := congrArg (fun z => (Kunneth.homologyFunctor (R := R)).map Δ[C] ≫
      inv (Kunneth.tensorator C C) ≫ z) (tensorator_natural_right C Δ[C])
    rw [hn, IsIso.inv_hom_id_assoc, ← Functor.map_comp]
  have hr : (comul C ≫ comul C ▷ (Kunneth.homologyFunctor (R := R)).obj C ≫
      (α_ ((Kunneth.homologyFunctor (R := R)).obj C) ((Kunneth.homologyFunctor (R := R)).obj C)
        ((Kunneth.homologyFunctor (R := R)).obj C)).hom) ≫ χ =
      (Kunneth.homologyFunctor (R := R)).map (Δ[C] ≫ Δ[C] ▷ C ≫ (α_ C C C).hom) := by
    simp only [comul, canonicalToTensorHomology, χ, comp_whiskerRight, Category.assoc, laxMonoidal_ε, laxMonoidal_μ]
    have ht := congrArg (fun z => (Kunneth.homologyFunctor (R := R)).map Δ[C] ≫
      inv (Kunneth.tensorator C C) ≫
      (Kunneth.homologyFunctor (R := R)).map Δ[C] ▷ (Kunneth.homologyFunctor (R := R)).obj C ≫
      inv (Kunneth.tensorator C C) ▷ (Kunneth.homologyFunctor (R := R)).obj C ≫ z)
      (Kunneth.tensorator_associativity C C C).symm
    rw [ht]
    have hu := congrArg (fun z => z ▷ (Kunneth.homologyFunctor (R := R)).obj C)
      (IsIso.inv_hom_id (Kunneth.tensorator C C))
    simp only [comp_whiskerRight, id_whiskerRight] at hu
    rw [reassoc_of% hu, tensorator_natural_left_assoc,
      IsIso.inv_hom_id_assoc, ← Functor.map_comp, ← Functor.map_comp]
  rw [hl, hr, ComonObj.comul_assoc]

/-- The genuine graded comonoid on homology under invertibility hypotheses
on the two relevant named canonical Künneth maps. -/
def comonObj [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)] : ComonObj ((Kunneth.homologyFunctor (R :=
  R)).obj C) where
  counit := counit C
  comul := comul C
  counit_comul := counit_comul C
  comul_counit := comul_counit C
  comul_assoc := comul_assoc C

/-- Signed cocommutativity is transported along the actual canonical cycle
Künneth comparison. This uses the Koszul interchange, not the unsigned
graded-object braiding. -/
theorem comul_cocommutative
    (hC : Δ[C] ≫ (koszulTensorBraidingIso C C).hom = Δ[C]) :
    comul C ≫ (Kunneth.koszulSwap ((Kunneth.homologyFunctor (R := R)).obj C) ((Kunneth.homologyFunctor (R := R)).obj
      C)).hom = comul C := by
  apply (cancel_mono (Kunneth.tensorator C C)).1
  simp only [Category.assoc]
  rw [← Kunneth.tensorator_braiding, comul_tensorator_assoc, comul_tensorator]
  simp only [canonicalToTensorHomology, ← Functor.map_comp, hC]

end SquareIsIso

/-- Flat terms and flat homology supply both necessary comparisons through
the existing first-factor collapse theorem. -/
def comonObjOfFlatHomology
    (hC : ∀ n : ℕ, Module.Flat R (C.X n))
    (hHC : ∀ n : ℕ, Module.Flat R (C.homology n)) : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := by
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_flat_homology C C hC hHC n
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_flat_homology C (C ⊗ C) hC hHC n
  exact comonObj C

attribute [local instance] ComonObj.instTensorUnit

private theorem unitMap_comul :
    Kunneth.unitMap (R := R) ≫ (Kunneth.homologyFunctor (R := R)).map Δ[𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)] =
      Δ[𝟙_ (GradedObject ℕ (ModuleCat.{u} R))] ≫ (Kunneth.unitMap ⊗ₘ Kunneth.unitMap) ≫
        Kunneth.tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  change Kunneth.unitMap ≫ (Kunneth.homologyFunctor (R := R)).map (λ_ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))).inv =
    (λ_ (𝟙_ (GradedObject ℕ (ModuleCat.{u} R)))).inv ≫ (Kunneth.unitMap ⊗ₘ Kunneth.unitMap) ≫
      Kunneth.tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
  have hu := Functor.LaxMonoidal.left_unitality_inv (Kunneth.homologyFunctor (R := R))
    (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
  simp only [laxMonoidal_ε, laxMonoidal_μ] at hu
  rw [← hu]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id, tensorHom_def]
  exact congrArg (fun z => (λ_ (𝟙_ (GradedObject ℕ (ModuleCat.{u} R)))).inv ≫ z ≫
    Kunneth.tensorator (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
      (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)))
    (whisker_exchange (Kunneth.unitMap (R := R)) (Kunneth.unitMap (R := R)))

/-- The canonical coaugmentation satisfies its actual counit equation. -/
theorem coaug_counit (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] :
    coaug C η ≫ counit C = 𝟙 (𝟙_ (GradedObject ℕ (ModuleCat.{u} R))) := by
  simp only [coaug, counit, Category.assoc, ← Functor.map_comp_assoc,
    IsComonHom.hom_counit, ComonObj.instTensorUnit_counit, Functor.map_id,
    Category.id_comp, unitMap_eq_unitIso_hom]
  rw [(Kunneth.homologyFunctor (R := R)).map_id, Category.id_comp]
  exact (Kunneth.unitIso (R := R)).hom_inv_id

/-- The canonical coaugmentation satisfies its actual coproduct equation. -/
theorem coaug_comul [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] :
    coaug C η ≫ comul C = Δ[𝟙_ (GradedObject ℕ (ModuleCat.{u} R))] ≫ (coaug C η ⊗ₘ coaug C η) := by
  apply (cancel_mono (Kunneth.tensorator C C)).1
  rw [Category.assoc, comul_tensorator]
  simp only [coaug, canonicalToTensorHomology, Category.assoc, ← Functor.map_comp]
  rw [IsComonHom.hom_comul, Functor.map_comp, ← Category.assoc, unitMap_comul]
  simp only [Category.assoc]
  have ht := congrArg (fun z => Δ[𝟙_ (GradedObject ℕ (ModuleCat.{u} R))] ≫
    (Kunneth.unitMap ⊗ₘ Kunneth.unitMap) ≫ z) (Kunneth.tensorator_naturality η η).symm
  rw [ht]
  simp only [← tensorHom_comp_tensorHom_assoc, Category.assoc]

/-- The homology coaugmentation is a native comonoid morphism. -/
theorem coaugIsComonHom
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)]
    (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] :
    letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
    IsComonHom (coaug C η) := by
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
  exact ⟨coaug_counit C η, coaug_comul C η⟩

/-- A chain comonoid morphism induces a genuine graded homology comonoid
morphism whenever both actual homology comonoids are defined. -/
theorem mapIsComonHom {D : (ChainComplex (ModuleCat.{u} R) ℕ)} [ComonObj D]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap D D n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap D (D ⊗ D) n)]
    (f : C ⟶ D) [IsComonHom f] :
    letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
    letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj D) := comonObj D
    IsComonHom ((Kunneth.homologyFunctor (R := R)).map f) := by
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj D) := comonObj D
  exact
    { hom_counit := by
        change (Kunneth.homologyFunctor (R := R)).map f ≫ counit D = counit C
        simp only [counit, Category.assoc, ← Functor.map_comp_assoc, IsComonHom.hom_counit]
      hom_comul := comul_naturality C f }

/-- The native generic pointed-comonoid object: an actual comonoid map
from the canonical trivial comonoid. The homology comonoid and its point
are constructed from the input chain comonoid and its actual point. -/
def coaugmentedComon
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)]
    (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] : Under (Comon.trivial (GradedObject ℕ
      (ModuleCat.{u} R))) := by
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
  letI : IsComonHom (coaug C η) := coaugIsComonHom C η
  let HC : Comon (GradedObject ℕ (ModuleCat.{u} R)) :=
    { X := (Kunneth.homologyFunctor (R := R)).obj C
      comon := comonObj C }
  have hPoint : @IsComonHom (GradedObject ℕ (ModuleCat.{u} R)) _ _
      (Comon.trivial (GradedObject ℕ (ModuleCat.{u} R))).X HC.X
      (Comon.trivial (GradedObject ℕ (ModuleCat.{u} R))).comon HC.comon (coaug C η) :=
    coaugIsComonHom C η
  exact Under.mk (Comon.Hom.mk (M := Comon.trivial (GradedObject ℕ (ModuleCat.{u} R)))
    (N := HC) (coaug C η) (isComonHom_hom := hPoint))

@[simp]
theorem coaugmentedComon_point
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)]
    (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] :
    (coaugmentedComon C η).hom.hom = coaug C η := rfl

/-- Actual point-preserving chain comonoid morphisms induce native
morphisms of the constructed pointed homology comonoids. -/
def coaugmentedComonMap {D : (ChainComplex (ModuleCat.{u} R) ℕ)} [ComonObj D]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap D D n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap D (D ⊗ D) n)]
    (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] (η' : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ D)
      [IsComonHom η']
    (f : C ⟶ D) [IsComonHom f] (hη : η ≫ f = η') :
    coaugmentedComon C η ⟶ coaugmentedComon D η' := by
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj D) := comonObj D
  letI : IsComonHom ((Kunneth.homologyFunctor (R := R)).map f) := mapIsComonHom C f
  have hMap : @IsComonHom (GradedObject ℕ (ModuleCat.{u} R)) _ _
      (coaugmentedComon C η).right.X (coaugmentedComon D η').right.X
      (coaugmentedComon C η).right.comon (coaugmentedComon D η').right.comon
      ((Kunneth.homologyFunctor (R := R)).map f) := mapIsComonHom C f
  exact Under.homMk (Comon.Hom.mk (M := (coaugmentedComon C η).right)
    (N := (coaugmentedComon D η').right) ((Kunneth.homologyFunctor (R := R)).map f)
    (isComonHom_hom := hMap)) (by
    apply Comon.Hom.ext
    exact coaug_naturality C η η' f hη)

section Field

variable {k : Type u} [Field k]


/-- The canonical field Künneth maps give the earned native monoidal
structure on graded homology. -/
def fieldMonoidal : (Kunneth.homologyFunctor (R := k)).Monoidal := by
  letI : (Kunneth.homologyFunctor (R := k)).LaxMonoidal := Kunneth.laxMonoidal
  letI : ∀ A B : (ChainComplex (ModuleCat.{u} k) ℕ), ∀ n : ℕ, IsIso (kunnethHomologyTensorMap A B n) :=
    fun A B n => isIso_kunnethHomologyTensorMap_of_field A B n
  letI : ∀ A B : (ChainComplex (ModuleCat.{u} k) ℕ), IsIso (Kunneth.tensorator A B) := fun A B => inferInstance
  letI : IsIso (Functor.LaxMonoidal.ε (Kunneth.homologyFunctor (R := k))) := by
    change IsIso (Kunneth.unitMap (R := k))
    infer_instance
  letI : ∀ A B, IsIso (Functor.LaxMonoidal.μ (Kunneth.homologyFunctor (R := k)) A B) := by
    intro A B
    change IsIso (Kunneth.tensorator A B)
    infer_instance
  exact Functor.Monoidal.ofLaxMonoidal (Kunneth.homologyFunctor (R := k))

/-- The existing native comonoid transport, applied to the earned field
homology monoidal functor. -/
def fieldComonFunctor : Comon (ChainComplex (ModuleCat.{u} k) ℕ) ⥤ Comon (GradedObject ℕ (ModuleCat.{u} k)) := by
  letI : (Kunneth.homologyFunctor (R := k)).Monoidal := fieldMonoidal
  exact (Kunneth.homologyFunctor (R := k)).mapComon

@[simp]
theorem fieldComonFunctor_carrier (C : Comon (ChainComplex (ModuleCat.{u} k) ℕ)) :
    (fieldComonFunctor.obj C).X = (Kunneth.homologyFunctor (R := k)).obj C.X := rfl

@[simp]
theorem fieldComonFunctor_map_hom {C D : Comon (ChainComplex (ModuleCat.{u} k) ℕ)} (f : C ⟶ D) :
    (fieldComonFunctor.map f).hom = (Kunneth.homologyFunctor (R := k)).map f.hom := rfl

/-- Native functor transport retains the actual canonical tensorator
specification, rather than substituting a chosen tensor comparison. -/
@[reassoc]
theorem fieldComonFunctor_comul_tensorator (C : Comon (ChainComplex (ModuleCat.{u} k) ℕ)) :
    Δ[(fieldComonFunctor.obj C).X] ≫ Kunneth.tensorator C.X C.X =
      canonicalToTensorHomology C.X := by
  letI : (Kunneth.homologyFunctor (R := k)).Monoidal := fieldMonoidal
  change ((Kunneth.homologyFunctor (R := k)).map Δ[C.X] ≫ Functor.OplaxMonoidal.δ (Kunneth.homologyFunctor (R := k))
    C.X C.X) ≫
    Functor.LaxMonoidal.μ (Kunneth.homologyFunctor (R := k)) C.X C.X = (Kunneth.homologyFunctor (R := k)).map Δ[C.X]
  rw [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]

/-- The actual native homology counit uses the inverse of the canonical
single-complex unit map. -/
@[reassoc]
theorem fieldComonFunctor_counit_unitMap (C : Comon (ChainComplex (ModuleCat.{u} k) ℕ)) :
    ε[(fieldComonFunctor.obj C).X] ≫ Kunneth.unitMap = (Kunneth.homologyFunctor (R := k)).map ε[C.X] := by
  letI : (Kunneth.homologyFunctor (R := k)).Monoidal := fieldMonoidal
  change ((Kunneth.homologyFunctor (R := k)).map ε[C.X] ≫ Functor.OplaxMonoidal.η (Kunneth.homologyFunctor (R := k))) ≫
    Functor.LaxMonoidal.ε (Kunneth.homologyFunctor (R := k)) = (Kunneth.homologyFunctor (R := k)).map ε[C.X]
  rw [Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]

/-- A field specialization of the general pointwise transport. -/
def comonObjOfField (C : (ChainComplex (ModuleCat.{u} k) ℕ)) [ComonObj C] : ComonObj ((Kunneth.homologyFunctor (R :=
  k)).obj C) := by
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_field C C n
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_field C (C ⊗ C) n
  exact comonObj C

/-- The field case of the native generic pointed-comonoid construction. -/
def coaugmentedComonOfField (C : (ChainComplex (ModuleCat.{u} k) ℕ)) [ComonObj C] (η : 𝟙_ (ChainComplex (ModuleCat.{u}
  k) ℕ) ⟶ C)
    [IsComonHom η] : Under (Comon.trivial (GradedObject ℕ (ModuleCat.{u} k))) := by
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_field C C n
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_field C (C ⊗ C) n
  exact coaugmentedComon C η

end Field

end HomologicalComplex.HomologyCoalgebra
