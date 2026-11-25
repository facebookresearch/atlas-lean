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

public import MathlibExt.Algebra.Homology.UniverseKunneth.Field
public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Diagonal
public import MathlibExt.CategoryTheory.GradedObject.Kernels
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Actual field homology coalgebras over the original larger-world field

The earned canonical larger-world cycle tensorator is monoidal over a
field. Native comonoid transport gives the homology coalgebra. Its unit,
counit, coaugmentation and primitive comparison use the original field
and exact offset-v dictionary. The primitive comparison is an actual
kernel lift and is not asserted to be an isomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace HomologicalComplex.UniverseKunneth

variable {k : Type u} [Field k]

private theorem monoidal_ε :
    @Functor.LaxMonoidal.ε _ _ _ _ _ _ (homologyFunctor (R := k))
      (monoidalOfField (k := k)).toLaxMonoidal = unitMap.{u,v} (R := k) := rfl

private theorem monoidal_μ (A B : ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) :
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ (homologyFunctor (R := k))
      (monoidalOfField (k := k)).toLaxMonoidal A B = tensorator A B := rfl


/-- The monoidal homology structure earned by the original-field Künneth theorem. -/
local instance canonicalHomologyMonoidal : (homologyFunctor (R := k)).Monoidal := monoidalOfField
local instance canonicalTensoratorIsIso (K L : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
  : IsIso (tensorator K L) :=
  isIso_tensorator_of_field K L

/-- Native comonoid transport under the earned original-field monoidal
homology functor, in the actual larger coefficient world. -/
def comonFunctor : Comon (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⥤ Comon (GradedObject
  ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  exact (homologyFunctor (R := k)).mapComon

/-- The actual native homology comonoid for an actual input chain comonoid. -/
def comonObj (C : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) [ComonObj C] : ComonObj
  ((homologyFunctor (R := k)).obj C) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  exact Functor.obj.instComonObj C (homologyFunctor (R := k))

variable (C : (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) [ComonObj C]

/-- The native transported comultiplication is pinned by the canonical
original-field cycle Künneth tensorator. -/
@[reassoc]
theorem comul_tensorator :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    Δ[(homologyFunctor (R := k)).obj C] ≫ tensorator C C = HomologyCoalgebra.canonicalToTensorHomology C := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  change ((homologyFunctor (R := k)).map Δ[C] ≫ Functor.OplaxMonoidal.δ (homologyFunctor (R := k)) C C) ≫
    Functor.LaxMonoidal.μ (homologyFunctor (R := k)) C C = (homologyFunctor (R := k)).map Δ[C]
  rw [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]

/-- The native transported counit uses the inverse canonical single-unit map. -/
@[reassoc]
theorem counit_unitMap :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    ε[(homologyFunctor (R := k)).obj C] ≫ unitMap = (homologyFunctor (R := k)).map ε[C] := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  change ((homologyFunctor (R := k)).map ε[C] ≫ Functor.OplaxMonoidal.η (homologyFunctor (R := k))) ≫
    Functor.LaxMonoidal.ε (homologyFunctor (R := k)) = (homologyFunctor (R := k)).map ε[C]
  rw [Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]

attribute [local instance] ComonObj.instTensorUnit

private theorem unitMap_comul :
    unitMap (R := k) ≫ (homologyFunctor (R := k)).map Δ[𝟙_ (ChainComplex
      (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)] =
      Δ[𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))] ≫ (unitMap ⊗ₘ unitMap) ≫ tensorator
        (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) (𝟙_ (ChainComplex
          (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  change unitMap ≫ (homologyFunctor (R := k)).map (λ_ (𝟙_ (ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))).inv =
    (λ_ (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)))).inv ≫ (unitMap ⊗ₘ unitMap) ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) (𝟙_ (ChainComplex
        (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
  have hU := Functor.LaxMonoidal.left_unitality_inv (homologyFunctor (R := k))
    (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
  simp only [monoidal_ε, monoidal_μ] at hU
  rw [← hU]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, tensorHom_def, monoidal_ε, monoidal_μ]
  exact congrArg (fun x =>
    (λ_ (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)))).inv ≫ x ≫
      tensorator (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
        (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)))
    (whisker_exchange (unitMap.{u,v} (R := k)) (unitMap.{u,v} (R := k)))

/-- The canonical original-field homology coaugmentation. -/
def coaug (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) : 𝟙_ (GradedObject ℕ
  (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) ⟶ (homologyFunctor (R := k)).obj C := unitMap ≫
    (homologyFunctor (R := k)).map η

theorem coaugIsComonHom (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C)
  [IsComonHom η] :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    IsComonHom (coaug C η) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  exact
    { hom_counit := by
        change (unitMap ≫ (homologyFunctor (R := k)).map η) ≫ ((homologyFunctor (R := k)).map ε[C] ≫
          Functor.OplaxMonoidal.η (homologyFunctor (R := k))) = 𝟙 _
        simp only [Category.assoc, ← Functor.map_comp_assoc, IsComonHom.hom_counit,
          ComonObj.instTensorUnit_counit, Functor.map_id, Category.id_comp]
        rw [(homologyFunctor (R := k)).map_id, Category.id_comp]
        simpa only [monoidal_ε] using Functor.Monoidal.ε_η (homologyFunctor (R := k))
      hom_comul := by
        apply (cancel_mono (tensorator C C)).1
        rw [Category.assoc, comul_tensorator]
        simp only [coaug, HomologyCoalgebra.canonicalToTensorHomology,
          Category.assoc, ← Functor.map_comp]
        rw [IsComonHom.hom_comul, Functor.map_comp, ← Category.assoc, unitMap_comul]
        have hT := congrArg (fun x =>
          Δ[𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))] ≫
            (unitMap ⊗ₘ unitMap) ≫ x) (tensorator_naturality η η).symm
        simpa only [Category.assoc, ← MonoidalCategory.tensorHom_comp_tensorHom] using hT
        }

/-- The actual coaugmented field homology coalgebra is a native pointed
comonoid object, rather than a caller-supplied record of desired laws. -/
def coaugmented (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) [IsComonHom η] :
  Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))) := by
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  letI : IsComonHom (coaug C η) := coaugIsComonHom C η
  exact Under.mk
    (show Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) ⟶
      ({ X := (homologyFunctor (R := k)).obj C, comon := comonObj C } :
        Comon (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))) from
      Comon.Hom.mk (coaug C η) (isComonHom_hom := coaugIsComonHom C η))

/-- Signed cocommutativity is the actual original-field Koszul equation. -/
theorem comul_cocommutative (h : Δ[C] ≫ (koszulTensorBraidingIso C C).hom = Δ[C]) :
    letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
    Δ[(homologyFunctor (R := k)).obj C] ≫ (koszulSwap ((homologyFunctor (R := k)).obj C) ((homologyFunctor (R :=
      k)).obj C)).hom = Δ[(homologyFunctor (R := k)).obj C] := by
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  apply (cancel_mono (tensorator C C)).1
  rw [Category.assoc, ← tensorator_braiding, ← Category.assoc, comul_tensorator]
  change HomologyCoalgebra.canonicalToTensorHomology C ≫ _ =
    HomologyCoalgebra.canonicalToTensorHomology C
  simp only [HomologyCoalgebra.canonicalToTensorHomology, ← Functor.map_comp, h]

/-- The actual chain coproduct minus the two coaugmentation terms. -/
def primitiveEquation (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) : C ⟶ C ⊗ C :=
  Δ[C] - ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C))

/-- The native kernel of the actual original-field primitive equation. -/
def primitiveComplex (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
  (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) := kernel (primitiveEquation C η)

/-- The actual primitive equation in the earned homology comonoid. -/
def homologyPrimitiveEquation (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
  (homologyFunctor (R := k)).obj C ⟶ (homologyFunctor (R := k)).obj C ⊗ (homologyFunctor (R := k)).obj C := by
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  exact Δ[(homologyFunctor (R := k)).obj C] - ((ρ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (𝟙 ((homologyFunctor (R
    := k)).obj C) ⊗ₘ coaug C η) +
    (λ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (coaug C η ⊗ₘ 𝟙 ((homologyFunctor (R := k)).obj C)))

omit [ComonObj C] in
private theorem unitTerms_transport (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶
  C) :
    (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) ≫
      inv (tensorator C C) =
    (ρ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (𝟙 ((homologyFunctor (R := k)).obj C) ⊗ₘ coaug C η) +
      (λ_ ((homologyFunctor (R := k)).obj C)).inv ≫ (coaug C η ⊗ₘ 𝟙 ((homologyFunctor (R := k)).obj C)) := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  apply (cancel_mono (tensorator C C)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Preadditive.add_comp]
  have ha : (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) =
      (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η)) + (homologyFunctor (R := k)).map ((λ_ C).inv ≫ (η ⊗ₘ 𝟙
        C)) := by
    funext n
    exact homologyMap_add _ _ n
  rw [ha, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.right_unitality_inv, ← Functor.LaxMonoidal.left_unitality_inv]
  simp only [monoidal_ε, monoidal_μ, Category.assoc]
  have hRight := tensorator_naturality (𝟙 C) η
  have hLeft := tensorator_naturality η (𝟙 C)
  rw [(homologyFunctor (R := k)).map_id C] at hRight hLeft
  rw [← hRight, ← hLeft]
  simp only [coaug, Functor.map_id, ← tensorHom_comp_tensorHom_assoc,
    Category.id_comp, tensorHom_def, tensorHom_def', Category.assoc,
    id_whiskerRight, whiskerLeft_id, whiskerLeft_comp, comp_whiskerRight]

/-- The actual primitive equation is transported under the actual canonical
original-field Künneth tensorator. -/
theorem primitiveEquation_transport (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶
  C) :
    (homologyFunctor (R := k)).map (primitiveEquation C η) ≫ inv (tensorator C C) = homologyPrimitiveEquation C η := by
  letI : (homologyFunctor (R := k)).Monoidal := monoidalOfField
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  letI : ComonObj ((homologyFunctor (R := k)).obj C) := comonObj C
  have hs : (homologyFunctor (R := k)).map (primitiveEquation C η) = (homologyFunctor (R := k)).map Δ[C] -
      (homologyFunctor (R := k)).map ((ρ_ C).inv ≫ (𝟙 C ⊗ₘ η) + (λ_ C).inv ≫ (η ⊗ₘ 𝟙 C)) := by
    funext n
    exact homologyMap_sub _ _ n
  have hd : (homologyFunctor (R := k)).map Δ[C] ≫ inv (tensorator C C) = Δ[(homologyFunctor (R := k)).obj C] := by
    have h := comul_tensorator C
    apply (cancel_mono (tensorator C C)).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact h.symm
  rw [hs, Preadditive.sub_comp, hd, unitTerms_transport]
  rfl

/-- The genuine comparison to the actual graded primitive kernel. It is
not asserted to be injective, surjective or an isomorphism. -/
def primitiveComparison (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
    (homologyFunctor (R := k)).obj (primitiveComplex C η) ⟶ kernel (homologyPrimitiveEquation C η) := by
  letI : IsIso (tensorator C C) := isIso_tensorator_of_field C C
  let i : kernel (primitiveEquation C η) ⟶ C := kernel.ι (primitiveEquation C η)
  have hK : i ≫ primitiveEquation C η = 0 := kernel.condition _
  have hMap := congrArg (homologyFunctor (R := k)).map hK
  rw [Functor.map_comp] at hMap
  have hz : homologyFunctor.map (0 : kernel (primitiveEquation C η) ⟶ C ⊗ C) = 0 := by
    funext n
    exact homologyMap_zero _ _ n
  have hLift : homologyFunctor.map i ≫ homologyPrimitiveEquation C η = 0 := by
    rw [← primitiveEquation_transport]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun x => x ≫ inv (tensorator C C)) hMap).trans
        ((congrArg (fun x => x ≫ inv (tensorator C C)) hz).trans zero_comp))
  exact kernel.lift (homologyPrimitiveEquation C η) (homologyFunctor.map i) hLift

@[reassoc (attr := simp)]
theorem primitiveComparison_ι (η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C) :
    primitiveComparison C η ≫ kernel.ι (homologyPrimitiveEquation C η) =
      (homologyFunctor (R := k)).map (kernel.ι (primitiveEquation C η)) := by
  unfold primitiveComparison
  exact kernel.lift_ι _ _ _

end HomologicalComplex.UniverseKunneth
