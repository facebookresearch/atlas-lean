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

public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import MathlibExt.CategoryTheory.GradedObject.Kernels

/-!
# The canonical primitive/homology comparison

The chain primitive equation is the actual coproduct minus its two
coaugmentation terms. Its native kernel is a chain complex. Mapping the
kernel inclusion to homology and using canonical Künneth unit coherence
gives a map to the kernel of the graded homology primitive equation.

This constructs a map. It does not assert that kernels commute with
homology, or that this map is injective, surjective, or an isomorphism.
Only the square Künneth comparison is needed to construct the map; the
cube comparison is needed separately for a homology comonoid structure.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace HomologicalComplex.HomologyCoalgebra

variable {R : Type u} [CommRing R]

private theorem lax_ε :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (Kunneth.homologyFunctor (R := R))
      Kunneth.laxMonoidal = Kunneth.unitMap (R := R) := rfl

private theorem lax_μ (A B : ChainComplex (ModuleCat.{u} R) ℕ) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (Kunneth.homologyFunctor (R := R))
      Kunneth.laxMonoidal A B = Kunneth.tensorator A B := rfl


variable (C : (ChainComplex (ModuleCat.{u} R) ℕ)) [ComonObj C] (η : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ C)

/-- The actual primitive equation in chain complexes. -/
def primitiveEquation : C ⟶ C ⊗ C :=
  Δ[C] - ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C))

/-- The native kernel of the actual chain primitive equation. -/
def primitiveComplex : (ChainComplex (ModuleCat.{u} R) ℕ) := kernel (primitiveEquation C η)

/-- The actual inclusion of the primitive kernel into the original complex. -/
def primitiveInclusion : primitiveComplex C η ⟶ C := kernel.ι (primitiveEquation C η)

@[reassoc (attr := simp)]
theorem primitiveInclusion_equation : primitiveInclusion C η ≫ primitiveEquation C η = 0 :=
  kernel.condition (primitiveEquation C η)

private theorem graded_map_sub {A B : (ChainComplex (ModuleCat.{u} R) ℕ)} (f g : A ⟶ B) : (Kunneth.homologyFunctor (R
  := R)).map (f - g) = (Kunneth.homologyFunctor (R := R)).map f - (Kunneth.homologyFunctor (R := R)).map g := by
  funext n
  exact homologyMap_sub f g n

private theorem graded_map_add {A B : (ChainComplex (ModuleCat.{u} R) ℕ)} (f g : A ⟶ B) : (Kunneth.homologyFunctor (R
  := R)).map (f + g) = (Kunneth.homologyFunctor (R := R)).map f + (Kunneth.homologyFunctor (R := R)).map g := by
  funext n
  exact homologyMap_add f g n

private theorem graded_map_zero (A B : (ChainComplex (ModuleCat.{u} R) ℕ)) : (Kunneth.homologyFunctor (R := R)).map (0
  : A ⟶ B) = 0 := by
  funext n
  exact homologyMap_zero _ _ n

/-- A zero central component of an actual chain map induces a zero
homology map in that degree. This uses the original cycle mono and the
original homology quotient epi. -/
theorem homologyMap_eq_zero_of_component {A B : (ChainComplex (ModuleCat.{u} R) ℕ)} (f : A ⟶ B) (n : ℕ)
    (h : f.f n = 0) : homologyMap f n = 0 := by
  have hc : cyclesMap f n = 0 := by
    apply (cancel_mono (B.iCycles n)).1
    rw [cyclesMap_i, h, comp_zero, zero_comp]
  apply (cancel_epi (A.homologyπ n)).1
  rw [homologyπ_naturality, hc, zero_comp, comp_zero]

section SquareIsIso

variable [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]

/-- The actual primitive equation for the transported graded diagonal and
the canonical homology coaugmentation. -/
def homologyPrimitiveEquation : (Kunneth.homologyFunctor (R := R)).obj C ⟶ (Kunneth.homologyFunctor (R := R)).obj C ⊗
  (Kunneth.homologyFunctor (R := R)).obj C :=
  comul C - ((ρ_ ((Kunneth.homologyFunctor (R := R)).obj C)).inv ≫ (𝟙 ((Kunneth.homologyFunctor (R := R)).obj C) ⊗ₘ
    coaug C η) +
    (λ_ ((Kunneth.homologyFunctor (R := R)).obj C)).inv ≫ (coaug C η ⊗ₘ 𝟙 ((Kunneth.homologyFunctor (R := R)).obj C)))

/-- The native graded primitive kernel. -/
def homologyPrimitives : (GradedObject ℕ (ModuleCat.{u} R)) := kernel (homologyPrimitiveEquation C η)

omit [ComonObj C] in
private theorem rightUnitTerm_transport :
    (Kunneth.homologyFunctor (R := R)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η)) ≫ inv (Kunneth.tensorator C C) =
      (ρ_ ((Kunneth.homologyFunctor (R := R)).obj C)).inv ≫ (𝟙 ((Kunneth.homologyFunctor (R := R)).obj C) ⊗ₘ coaug C
        η) := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  apply (cancel_mono (Kunneth.tensorator C C)).1
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Functor.map_comp]
  have hu := Functor.LaxMonoidal.right_unitality_inv
    (Kunneth.homologyFunctor (R := R)) C
  simp only [lax_ε, lax_μ] at hu
  rw [← hu]
  have hn := Kunneth.tensorator_naturality (𝟙 C) η
  rw [(Kunneth.homologyFunctor (R := R)).map_id C] at hn
  have hn' := congrArg (fun x => (ρ_ (Kunneth.homologyFunctor.obj C)).inv ≫
    (Kunneth.homologyFunctor.obj C ◁ Kunneth.unitMap) ≫ x) hn.symm
  simp only [Category.assoc, id_tensorHom, tensorHom_id] at hn'
  exact (Category.assoc _ _ _).trans (hn'.trans (by
    simp only [coaug, Functor.map_id, ← tensorHom_comp_tensorHom_assoc,
      Category.id_comp, tensorHom_def, Category.assoc, id_whiskerRight, whiskerLeft_comp]))

omit [ComonObj C] in
private theorem leftUnitTerm_transport :
    (Kunneth.homologyFunctor (R := R)).map ((λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) ≫ inv (Kunneth.tensorator C C) =
      (λ_ ((Kunneth.homologyFunctor (R := R)).obj C)).inv ≫ (coaug C η ⊗ₘ 𝟙 ((Kunneth.homologyFunctor (R := R)).obj
        C)) := by
  letI : (Kunneth.homologyFunctor (R := R)).LaxMonoidal := Kunneth.laxMonoidal
  apply (cancel_mono (Kunneth.tensorator C C)).1
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Functor.map_comp]
  have hu := Functor.LaxMonoidal.left_unitality_inv
    (Kunneth.homologyFunctor (R := R)) C
  simp only [lax_ε, lax_μ] at hu
  rw [← hu]
  have hn := Kunneth.tensorator_naturality η (𝟙 C)
  rw [(Kunneth.homologyFunctor (R := R)).map_id C] at hn
  have hn' := congrArg (fun x => (λ_ (Kunneth.homologyFunctor.obj C)).inv ≫
    (Kunneth.unitMap ▷ Kunneth.homologyFunctor.obj C) ≫ x) hn.symm
  simp only [Category.assoc, id_tensorHom, tensorHom_id] at hn'
  exact (Category.assoc _ _ _).trans (hn'.trans (by
    simp only [coaug, Functor.map_id, ← tensorHom_comp_tensorHom_assoc,
      Category.id_comp, tensorHom_def', Category.assoc, whiskerLeft_id, comp_whiskerRight]))

/-- The chain primitive equation maps to the literal homology primitive
equation under the inverse canonical Künneth map. -/
@[reassoc]
theorem primitiveEquation_transport :
    (Kunneth.homologyFunctor (R := R)).map (primitiveEquation C η) ≫ inv (Kunneth.tensorator C C) =
      homologyPrimitiveEquation C η := by
  rw [primitiveEquation, graded_map_sub, graded_map_add,
    Preadditive.sub_comp, Preadditive.add_comp,
    rightUnitTerm_transport, leftUnitTerm_transport]
  rfl

/-- The actual homology of the chain primitive inclusion satisfies the
actual graded primitive equation. -/
theorem homologyInclusion_primitive :
    (Kunneth.homologyFunctor (R := R)).map (primitiveInclusion C η) ≫ homologyPrimitiveEquation C η = 0 := by
  rw [← primitiveEquation_transport, ← Category.assoc, ← Functor.map_comp,
    primitiveInclusion_equation, graded_map_zero, zero_comp]

/-- The canonical comparison from homology of the actual primitive chain
kernel to the actual primitive kernel in graded homology. -/
def primitiveComparison : (Kunneth.homologyFunctor (R := R)).obj (primitiveComplex C η) ⟶ homologyPrimitives C η :=
  kernel.lift (homologyPrimitiveEquation C η) ((Kunneth.homologyFunctor (R := R)).map (primitiveInclusion C η))
    (homologyInclusion_primitive C η)

@[reassoc]
theorem primitiveComparison_ι :
    primitiveComparison C η ≫ kernel.ι (homologyPrimitiveEquation C η) =
      (Kunneth.homologyFunctor (R := R)).map (primitiveInclusion C η) :=
  kernel.lift_ι _ _ _

/-- On each original cycle object, the comparison followed by inclusion is
the ordinary homology class of its image in the original complex. -/
@[reassoc]
theorem primitiveComparison_on_cycles (n : ℕ) :
    (primitiveComplex C η).homologyπ n ≫ primitiveComparison C η n ≫
      (kernel.ι (homologyPrimitiveEquation C η)) n =
      cyclesMap (primitiveInclusion C η) n ≫ C.homologyπ n := by
  have h := congrFun (primitiveComparison_ι C η) n
  have hp := congrArg (fun x => (primitiveComplex C η).homologyπ n ≫ x) h
  exact (Category.assoc _ _ _).symm.trans (hp.trans
    (homologyπ_naturality (primitiveInclusion C η) n))

end SquareIsIso

variable {D : (ChainComplex (ModuleCat.{u} R) ℕ)} [ComonObj D] (η' : 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ⟶ D)

/-- A coaugmentation-preserving chain comonoid morphism intertwines the
two actual chain primitive equations. -/
@[reassoc]
theorem primitiveEquation_naturality (f : C ⟶ D) [IsComonHom f]
    (hη : η ≫ f = η') :
    primitiveEquation C η ≫ (f ⊗ₘ f) = f ≫ primitiveEquation D η' := by
  simp only [primitiveEquation, Preadditive.sub_comp, Preadditive.add_comp,
    Preadditive.comp_sub, Preadditive.comp_add, Category.assoc,
    ← IsComonHom.hom_comul]
  congr 1
  congr 1
  · have ht := tensorHom_comp_tensorHom (𝟙 C) f η f
    have h := congrArg (fun x => (ρ_ C).inv ≫ x) ht
    simp only [Category.id_comp, hη] at h
    have hUnit := rightUnitor_inv_naturality f
    have hUnit' := congrArg (fun x => x ≫ (D ◁ η')) hUnit.symm
    change (ρ_ C).inv ≫ (f ▷ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ≫ D ◁ η' =
      f ≫ (ρ_ D).inv ≫ D ◁ η' at hUnit'
    have hTensor : (f ⊗ₘ η') = f ▷ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ≫ D ◁ η' :=
      tensorHom_def f η'
    exact (Category.assoc _ _ _).symm.trans (h.trans
      ((congrArg (fun x => (ρ_ C).inv ≫ x) hTensor).trans hUnit'))
  · have ht := tensorHom_comp_tensorHom η f (𝟙 C) f
    have h := congrArg (fun x => (λ_ C).inv ≫ x) ht
    simp only [Category.id_comp, hη] at h
    have hUnit := leftUnitor_inv_naturality f
    have hUnit' := congrArg (fun x => x ≫ (η' ▷ D)) hUnit.symm
    change (λ_ C).inv ≫ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ◁ f) ≫ η' ▷ D =
      f ≫ (λ_ D).inv ≫ η' ▷ D at hUnit'
    have hTensor : (η' ⊗ₘ f) = 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ) ◁ f ≫ η' ▷ D :=
      tensorHom_def' η' f
    exact (Category.assoc _ _ _).symm.trans (h.trans
      ((congrArg (fun x => (λ_ C).inv ≫ x) hTensor).trans hUnit'))

/-- The genuine map on native primitive chain kernels. -/
def primitiveComplexMap (f : C ⟶ D) [IsComonHom f] (hη : η ≫ f = η') :
    primitiveComplex C η ⟶ primitiveComplex D η' :=
  kernel.lift (primitiveEquation D η') (primitiveInclusion C η ≫ f) (by
    rw [Category.assoc, ← primitiveEquation_naturality C η η' f hη,
      ← Category.assoc, primitiveInclusion_equation, zero_comp])

@[reassoc (attr := simp)]
theorem primitiveComplexMap_ι (f : C ⟶ D) [IsComonHom f] (hη : η ≫ f = η') :
    primitiveComplexMap C η η' f hη ≫ primitiveInclusion D η' =
      primitiveInclusion C η ≫ f :=
  kernel.lift_ι _ _ _

section BothSquaresIsIso

variable [∀ n : ℕ, IsIso (kunnethHomologyTensorMap C C n)]
  [∀ n : ℕ, IsIso (kunnethHomologyTensorMap D D n)]

/-- The actual homology primitive equation is natural under an actual
coaugmentation-preserving chain comonoid map. -/
@[reassoc]
theorem homologyPrimitiveEquation_naturality (f : C ⟶ D) [IsComonHom f]
    (hη : η ≫ f = η') :
    homologyPrimitiveEquation C η ≫ ((Kunneth.homologyFunctor (R := R)).map f ⊗ₘ (Kunneth.homologyFunctor (R :=
      R)).map f) =
      (Kunneth.homologyFunctor (R := R)).map f ≫ homologyPrimitiveEquation D η' := by
  apply (cancel_mono (Kunneth.tensorator D D)).1
  have ht := congrArg (fun x => homologyPrimitiveEquation C η ≫ x)
    (Kunneth.tensorator_naturality f f)
  have hpC := primitiveEquation_transport C η
  have hpD := primitiveEquation_transport D η'
  rw [Category.assoc, ht]
  rw [← hpC, ← hpD]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp, primitiveEquation_naturality C η η' f hη]

/-- The genuine map on native graded primitive kernels. -/
def homologyPrimitivesMap (f : C ⟶ D) [IsComonHom f] (hη : η ≫ f = η') :
    homologyPrimitives C η ⟶ homologyPrimitives D η' :=
  kernel.lift (homologyPrimitiveEquation D η')
    (kernel.ι (homologyPrimitiveEquation C η) ≫ (Kunneth.homologyFunctor (R := R)).map f) (by
      let i : kernel (homologyPrimitiveEquation C η) ⟶ Kunneth.homologyFunctor.obj C :=
        kernel.ι (homologyPrimitiveEquation C η)
      change (i ≫ (Kunneth.homologyFunctor (R := R)).map f) ≫
        homologyPrimitiveEquation D η' = 0
      rw [Category.assoc, ← homologyPrimitiveEquation_naturality C η η' f hη,
        ← Category.assoc, kernel.condition, zero_comp])

@[reassoc]
theorem homologyPrimitivesMap_ι (f : C ⟶ D) [IsComonHom f] (hη : η ≫ f = η') :
    homologyPrimitivesMap C η η' f hη ≫ kernel.ι (homologyPrimitiveEquation D η') =
      kernel.ι (homologyPrimitiveEquation C η) ≫ (Kunneth.homologyFunctor (R := R)).map f :=
  kernel.lift_ι _ _ _

/-- Naturality of the actual primitive/homology comparison. -/
@[reassoc]
theorem primitiveComparison_naturality (f : C ⟶ D) [IsComonHom f]
    (hη : η ≫ f = η') :
    (Kunneth.homologyFunctor (R := R)).map (primitiveComplexMap C η η' f hη) ≫ primitiveComparison D η' =
      primitiveComparison C η ≫ homologyPrimitivesMap C η η' f hη := by
  apply (cancel_mono (kernel.ι (homologyPrimitiveEquation D η'))).1
  change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
  have hLeft := congrArg (fun x => Kunneth.homologyFunctor.map
    (primitiveComplexMap C η η' f hη) ≫ x) (primitiveComparison_ι D η')
  have hRight := congrArg (fun x => primitiveComparison C η ≫ x)
    (homologyPrimitivesMap_ι C η η' f hη)
  have hCore : Kunneth.homologyFunctor.map (primitiveComplexMap C η η' f hη) ≫
      Kunneth.homologyFunctor.map (primitiveInclusion D η') =
    Kunneth.homologyFunctor.map (primitiveInclusion C η) ≫ Kunneth.homologyFunctor.map f := by
    rw [← Functor.map_comp, ← Functor.map_comp, primitiveComplexMap_ι]
  exact (Category.assoc _ _ _).trans (hLeft.trans (hCore.trans
    ((congrArg (fun x => x ≫ Kunneth.homologyFunctor.map f)
      (primitiveComparison_ι C η)).symm.trans
        ((Category.assoc _ _ _).trans (hRight.symm.trans (Category.assoc _ _ _).symm)))))

end BothSquaresIsIso

end HomologicalComplex.HomologyCoalgebra
