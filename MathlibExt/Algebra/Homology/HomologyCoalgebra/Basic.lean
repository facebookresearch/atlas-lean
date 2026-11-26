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
# Coalgebra structures on homology through canonical Künneth comparisons

Let R be a commutative ring and C a comonoid in nonnegative R-module
chain complexes. Write H for graded homology, μ for its canonical
cycle Künneth tensorator and e:𝟙_Gr≅H(𝟙_Ch) for the unit comparison.
The counit is e⁻¹H(ε_C), and a unit-to-C chain map η gives the
graded point H(η)e.

If μ_(C,C) is invertible in every degree, the diagonal is
Δ_H=μ_(C,C)⁻¹H(Δ_C). It satisfies both counit laws.
If μ_(C,C⊗C) is also invertible in every degree, Δ_H is
coassociative and defines a graded comonoid.
These are the named square and right-associated cube comparisons.

Flat terms and flat homology of C supply both comparisons.
Over a field, the canonical graded homology functor is strong
monoidal and transports chain comonoids functorially.
Signed cocommutativity is expressed by the Koszul interchange
(−1)^(pq) on graded summands. All module carriers here have the
same world u as the coefficient ring.
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

/-- For a chain comonoid C over a commutative ring R, the
graded homology counit is H(C)→𝟙_Gr, obtained by H(ε_C) followed
by the inverse unit comparison H(𝟙_Ch)≅𝟙_Gr.
No square Künneth invertibility is needed for this definition. -/
def counit : (Kunneth.homologyFunctor (R := R)).obj C ⟶ 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) :=
  (Kunneth.homologyFunctor (R := R)).map ε[C] ≫ (Kunneth.unitIso (R := R)).inv

@[reassoc (attr := simp)]
theorem counit_unitMap : counit C ≫ Kunneth.unitMap = (Kunneth.homologyFunctor (R := R)).map ε[C] := by
  simp only [counit, unitMap_eq_unitIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For a nonnegative R-module chain complex C and a chain map
η:𝟙_Ch→C, the graded map 𝟙_Gr→H(C) is H(η)∘e, where
e:𝟙_Gr≅H(𝟙_Ch) is the scalar-unit homology comparison. -/
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

/-- For a chain comonoid C over a commutative ring R, assume
the canonical square tensorator μ_(C,C) is invertible in every
degree. The graded diagonal is
Δ_H=μ_(C,C)⁻¹ ∘ H(Δ_C):H(C)→H(C)⊗H(C). -/
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

/-- For a chain comonoid C over a commutative ring R with
invertible square Künneth tensorator, its homology diagonal
satisfies (ε_H⊗id) ∘ Δ_H=λ_(H(C))⁻¹.
The counit ε_H uses the inverse scalar-unit homology comparison. -/
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

/-- For a chain comonoid C over a commutative ring R with
invertible square Künneth tensorator, its homology diagonal
satisfies (id⊗ε_H) ∘ Δ_H=ρ_(H(C))⁻¹. -/
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

/-- For a chain comonoid C over a commutative ring R, assume
μ_(C,C) and μ_(C,C⊗C) are invertible in every degree.
Then (id⊗Δ_H) ∘ Δ_H =
α_(H(C),H(C),H(C)) ∘ (Δ_H⊗id) ∘ Δ_H.
These are precisely the square and right-associated cube
canonical Künneth comparisons. -/
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

/-- For a chain comonoid C over a commutative ring R, if
μ_(C,C) and μ_(C,C⊗C) are invertible in every degree, the
canonical homology diagonal and counit define a comonoid on H(C).
The maps are μ_(C,C)⁻¹H(Δ_C) and e⁻¹H(ε_C). -/
def comonObj [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)] : ComonObj ((Kunneth.homologyFunctor (R :=
  R)).obj C) where
  counit := counit C
  comul := comul C
  counit_comul := counit_comul C
  comul_counit := comul_counit C
  comul_assoc := comul_assoc C

/-- For a chain comonoid C over a commutative ring R with
invertible square tensorator, suppose β_Ch ∘ Δ_C=Δ_C
for the signed chain Koszul interchange.
Then β_Koszul ∘ Δ_H=Δ_H on graded homology, with coefficient
(−1)^(pq) on a bidegree (p,q). -/
theorem comul_cocommutative
    (hC : Δ[C] ≫ (koszulTensorBraidingIso C C).hom = Δ[C]) :
    comul C ≫ (Kunneth.koszulSwap ((Kunneth.homologyFunctor (R := R)).obj C) ((Kunneth.homologyFunctor (R := R)).obj
      C)).hom = comul C := by
  apply (cancel_mono (Kunneth.tensorator C C)).1
  simp only [Category.assoc]
  rw [← Kunneth.tensorator_braiding, comul_tensorator_assoc, comul_tensorator]
  simp only [canonicalToTensorHomology, ← Functor.map_comp, hC]

end SquareIsIso

/-- For a nonnegative R-module chain comonoid C, suppose
every term C_n and every homology module H_n(C) is flat over R.
The canonical Künneth maps for C⊗C and C⊗(C⊗C) are then
invertible, so the canonical diagonal and counit define a
graded homology comonoid. -/
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

/-- For a chain comonoid C over a commutative ring R and a
comonoid map η:𝟙_Ch→C, its graded point η_H=H(η)e satisfies
ε_H ∘ η_H=id_(𝟙_Gr).
This equation does not require square or cube Künneth invertibility. -/
theorem coaug_counit (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] :
    coaug C η ≫ counit C = 𝟙 (𝟙_ (GradedObject ℕ (ModuleCat.{u} R))) := by
  simp only [coaug, counit, Category.assoc, ← Functor.map_comp_assoc,
    IsComonHom.hom_counit, ComonObj.instTensorUnit_counit, Functor.map_id,
    Category.id_comp, unitMap_eq_unitIso_hom]
  rw [(Kunneth.homologyFunctor (R := R)).map_id, Category.id_comp]
  exact (Kunneth.unitIso (R := R)).hom_inv_id

/-- For a chain comonoid C over a commutative ring R with
invertible square tensorator, a comonoid map η:𝟙_Ch→C gives
Δ_H ∘ η_H=(η_H⊗η_H) ∘ Δ_(𝟙_Gr).
The point is the unit homology comparison followed by H(η). -/
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

/-- For a chain comonoid C over a commutative ring R, assume
the square μ_(C,C) and right-cube μ_(C,C⊗C) comparisons are
invertible in every degree. A comonoid map η:𝟙_Ch→C then
induces a comonoid map η_H:𝟙_Gr→H(C) for the constructed
graded homology comonoid. -/
theorem coaugIsComonHom
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
    [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n)]
    (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C) [IsComonHom η] :
    letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
    IsComonHom (coaug C η) := by
  letI : ComonObj ((Kunneth.homologyFunctor (R := R)).obj C) := comonObj C
  exact ⟨coaug_counit C η, coaug_comul C η⟩

/-- For chain comonoids C,D over a commutative ring R, assume
their respective square and right-associated cube Künneth maps
are invertible in every degree. If f:C→D is a comonoid morphism,
then H(f):H(C)→H(D) is a comonoid morphism for the canonical
homology structures. -/
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

/-- For a chain comonoid C over a commutative ring R with
invertible square and right-cube Künneth comparisons, a comonoid
map η:𝟙_Ch→C gives the pointed graded comonoid
η_H:𝟙_Gr→H(C).
It is an object under the trivial graded unit comonoid. -/
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

/-- For chain comonoids C,D with invertible square and
right-cube Künneth comparisons, let η,η′ be comonoid maps from
the chain unit. A comonoid map f:C→D with f∘η=η′ induces
the pointed graded homology map H(C)→H(D).
The equality H(f)∘η_H=η′_H preserves the constructed points. -/
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


/-- For a field k and nonnegative chains in ModuleCat^u(k),
the canonical cycle tensorator and scalar-unit homology map
give the graded homology functor a strong monoidal structure.
All canonical Künneth tensorators are invertible over k. -/
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

/-- For a field k, the strong monoidal graded homology functor
induces Comon(ChainComplex(ModuleCat^u(k),ℕ))→
Comon(GradedObject(ℕ,ModuleCat^u(k))).
It sends a chain comonoid to its canonical graded homology comonoid. -/
def fieldComonFunctor : Comon (ChainComplex (ModuleCat.{u} k) ℕ) ⥤ Comon (GradedObject ℕ (ModuleCat.{u} k)) := by
  letI : (Kunneth.homologyFunctor (R := k)).Monoidal := fieldMonoidal
  exact (Kunneth.homologyFunctor (R := k)).mapComon

@[simp]
theorem fieldComonFunctor_carrier (C : Comon (ChainComplex (ModuleCat.{u} k) ℕ)) :
    (fieldComonFunctor.obj C).X = (Kunneth.homologyFunctor (R := k)).obj C.X := rfl

@[simp]
theorem fieldComonFunctor_map_hom {C D : Comon (ChainComplex (ModuleCat.{u} k) ℕ)} (f : C ⟶ D) :
    (fieldComonFunctor.map f).hom = (Kunneth.homologyFunctor (R := k)).map f.hom := rfl

/-- For a chain comonoid C over a field k, its transported
homology diagonal satisfies μ_(C,C) ∘ Δ_H=H(Δ_C).
Thus the image under the canonical tensorator is the homology
map into the chain tensor square. -/
@[reassoc]
theorem fieldComonFunctor_comul_tensorator (C : Comon (ChainComplex (ModuleCat.{u} k) ℕ)) :
    Δ[(fieldComonFunctor.obj C).X] ≫ Kunneth.tensorator C.X C.X =
      canonicalToTensorHomology C.X := by
  letI : (Kunneth.homologyFunctor (R := k)).Monoidal := fieldMonoidal
  change ((Kunneth.homologyFunctor (R := k)).map Δ[C.X] ≫ Functor.OplaxMonoidal.δ (Kunneth.homologyFunctor (R := k))
    C.X C.X) ≫
    Functor.LaxMonoidal.μ (Kunneth.homologyFunctor (R := k)) C.X C.X = (Kunneth.homologyFunctor (R := k)).map Δ[C.X]
  rw [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]

/-- For a chain comonoid C over a field k, its transported
homology counit satisfies e ∘ ε_H=H(ε_C),
where e:𝟙_Gr≅H(𝟙_Ch) is the canonical unit comparison. -/
@[reassoc]
theorem fieldComonFunctor_counit_unitMap (C : Comon (ChainComplex (ModuleCat.{u} k) ℕ)) :
    ε[(fieldComonFunctor.obj C).X] ≫ Kunneth.unitMap = (Kunneth.homologyFunctor (R := k)).map ε[C.X] := by
  letI : (Kunneth.homologyFunctor (R := k)).Monoidal := fieldMonoidal
  change ((Kunneth.homologyFunctor (R := k)).map ε[C.X] ≫ Functor.OplaxMonoidal.η (Kunneth.homologyFunctor (R := k))) ≫
    Functor.LaxMonoidal.ε (Kunneth.homologyFunctor (R := k)) = (Kunneth.homologyFunctor (R := k)).map ε[C.X]
  rw [Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]

/-- For a field k and a nonnegative k-module chain comonoid C,
the canonical Künneth comparisons give the graded comonoid
on H(C), with diagonal μ_(C,C)⁻¹H(Δ_C) and counit e⁻¹H(ε_C). -/
def comonObjOfField (C : (ChainComplex (ModuleCat.{u} k) ℕ)) [ComonObj C] : ComonObj ((Kunneth.homologyFunctor (R :=
  k)).obj C) := by
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_field C C n
  letI : ∀ n : ℕ, IsIso (kunnethHomologyTensorMap C (C ⊗ C) n) :=
    fun n => isIso_kunnethHomologyTensorMap_of_field C (C ⊗ C) n
  exact comonObj C

/-- For a field k, a chain comonoid C and a comonoid map
η:𝟙_Ch→C, the canonical homology comonoid with point H(η)e
is an object under the trivial graded unit comonoid.
The module carriers remain in world u. -/
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
