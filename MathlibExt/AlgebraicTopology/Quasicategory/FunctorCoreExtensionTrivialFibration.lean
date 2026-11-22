/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreExtensionWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Actual trivial restriction moduli and whole relative extension prisms

The source inclusion is genuinely monic and a categorical equivalence. Neither
source is assumed Kan or a quasicategory. The same core restriction and chosen
extension projection are trivial Kan fibrations. Actual coefficient base change
and prescribed partial-family lifts retain both original projections and prisms.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FunctorCore.Extension

variable {A₀ A Q K : SSet.{u}}

/-- The original core restriction is trivial from the genuine source equivalence and monicity. -/
theorem restriction_mem_trivialFibrations (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) (Q : SSet.{u}) [Quasicategory Q] :
    trivialFibrations SSet.{u} (restriction i Q) := by
  let _ : WeakEquivalence (restriction i Q) :=
    (weakEquivalence_iff _).mpr (FunctorCore.sourceMap_realizationWeak i hi Q)
  exact mem_trivialFibrations _

/-- The original extension projection is a trivial fibration for every actual coefficient family. -/
theorem coefficientProjection_mem_trivialFibrations (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    trivialFibrations SSet.{u} (coefficientProjection i α) := by
  let _ : WeakEquivalence (restriction i Q) :=
    (mem_trivialFibrations_iff _).mp (restriction_mem_trivialFibrations i hi Q) |>.2
  change trivialFibrations SSet.{u} (pullback.snd (restriction i Q) α)
  exact mem_trivialFibrations _

/-- The actual extension projection has the canonical boundary lifting property. -/
theorem coefficientProjection_rlp_I (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    modelCategoryQuillen.I.rlp (coefficientProjection i α) := by
  rw [← rlp_monomorphisms, ← modelCategoryQuillen.cofibrations_eq, cofibrations_rlp]
  exact coefficientProjection_mem_trivialFibrations i hi α

/-- For an actual Kan coefficient the same projection is a Kan moduli weak equivalence. -/
theorem coefficientProjection_mem_W (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q] [KanComplex K]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    KanComplex.W (coefficientProjection i α) := by
  let _ : KanComplex (object i α) := object_isKan i α
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (coefficientProjection_mem_trivialFibrations i hi α).2

/-- The whole coefficient base change is the original canonical nested pullback Iso. -/
def coefficientBaseChangeIso {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (c : L ⟶ K) :
    object i (c ≫ α) ≅ pullback (coefficientProjection i α) c :=
  (pullbackLeftPullbackSndIso (restriction i Q) α c).symm

/-- The actual base-change Iso has the same entire coefficient-change first leg. -/
@[reassoc]
theorem coefficientBaseChangeIso_fst {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (c : L ⟶ K) :
    (coefficientBaseChangeIso i α c).hom ≫ pullback.fst _ _ =
      coefficientMap i (c ≫ α) α c rfl := by
  apply pullback.hom_ext
  · change ((pullbackLeftPullbackSndIso (restriction i Q) α c).inv ≫
        pullback.fst (pullback.snd (restriction i Q) α) c) ≫ pullback.fst (restriction i Q) α = _
    rw [Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst, coefficientMap_fst]
  · change ((pullbackLeftPullbackSndIso (restriction i Q) α c).inv ≫
        pullback.fst (pullback.snd (restriction i Q) α) c) ≫ pullback.snd (restriction i Q) α = _
    rw [Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd, coefficientMap_snd]

/-- The actual base-change Iso retains the original complete coefficient projection. -/
@[reassoc]
theorem coefficientBaseChangeIso_snd {L : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (c : L ⟶ K) :
    (coefficientBaseChangeIso i α c).hom ≫ pullback.snd _ _ =
      coefficientProjection i (c ≫ α) :=
  pullbackLeftPullbackSndIso_inv_snd_snd _ _ _

/-- The same actual coefficient-change maps compose with their original full coefficient maps. -/
theorem coefficientMap_comp {L M : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (c : L ⟶ K) (d : M ⟶ L) :
    coefficientMap i ((d ≫ c) ≫ α) (c ≫ α) d (Category.assoc d c α) ≫
        coefficientMap i (c ≫ α) α c rfl =
      coefficientMap i ((d ≫ c) ≫ α) α (d ≫ c) rfl := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientMap_fst]
  · simp only [Category.assoc, coefficientMap_snd_assoc, coefficientMap_snd]

/-- Whole coefficient base change is natural under the actual original parameter maps. -/
theorem coefficientBaseChangeIso_naturality {L M : SSet.{u}} (i : A₀ ⟶ A)
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (c : L ⟶ K) (d : M ⟶ L) :
    coefficientMap i ((d ≫ c) ≫ α) (c ≫ α) d (Category.assoc d c α) ≫
        (coefficientBaseChangeIso i α c).hom =
      (coefficientBaseChangeIso i α (d ≫ c)).hom ≫
        pullback.map (coefficientProjection i α) (d ≫ c) (coefficientProjection i α) c
          (𝟙 _) d (𝟙 K) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientBaseChangeIso_fst,
      pullback.map, pullback.lift_fst, Category.comp_id]
    exact coefficientMap_comp i α c d
  · simp only [Category.assoc, coefficientBaseChangeIso_snd_assoc, coefficientBaseChangeIso_snd,
      pullback.map, pullback.lift_snd, coefficientMap_snd]

/-- A genuinely trivial original restriction supplies a section of the whole coefficient family. -/
theorem exists_familySection (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) :
    ∃ s : K ⟶ object i α, s ≫ coefficientProjection i α = 𝟙 K :=
  exists_section_of_rlp_I (coefficientProjection_rlp_I i hi α)

/-- The actual partial extension square has a whole lift along every original mono parameter attachment. -/
def parameterLift {L₀ L : SSet.{u}} (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (j : L₀ ⟶ L) [Mono j]
    {f₀ : L₀ ⟶ object i α} {γ : L ⟶ K}
    (sq : CommSq f₀ j (coefficientProjection i α) γ) : L ⟶ object i α := by
  let _ : Cofibration j := modelCategoryQuillen.cofibration_of_mono j
  let _ : WeakEquivalence (coefficientProjection i α) :=
    (mem_trivialFibrations_iff _).mp (coefficientProjection_mem_trivialFibrations i hi α) |>.2
  let _ : HasLiftingProperty j (coefficientProjection i α) := ModelCategory.cm4b _ _
  exact sq.lift

/-- The derived whole lift retains the original prescribed partial-family map. -/
@[reassoc]
theorem parameterLift_left {L₀ L : SSet.{u}} (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (j : L₀ ⟶ L) [Mono j]
    {f₀ : L₀ ⟶ object i α} {γ : L ⟶ K}
    (sq : CommSq f₀ j (coefficientProjection i α) γ) :
    j ≫ parameterLift i hi α j sq = f₀ := by
  let _ : Cofibration j := modelCategoryQuillen.cofibration_of_mono j
  let _ : WeakEquivalence (coefficientProjection i α) :=
    (mem_trivialFibrations_iff _).mp (coefficientProjection_mem_trivialFibrations i hi α) |>.2
  let _ : HasLiftingProperty j (coefficientProjection i α) := ModelCategory.cm4b _ _
  unfold parameterLift
  exact sq.fac_left

/-- The derived whole lift retains the original complete coefficient map. -/
@[reassoc]
theorem parameterLift_right {L₀ L : SSet.{u}} (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (j : L₀ ⟶ L) [Mono j]
    {f₀ : L₀ ⟶ object i α} {γ : L ⟶ K}
    (sq : CommSq f₀ j (coefficientProjection i α) γ) :
    parameterLift i hi α j sq ≫ coefficientProjection i α = γ := by
  let _ : Cofibration j := modelCategoryQuillen.cofibration_of_mono j
  let _ : WeakEquivalence (coefficientProjection i α) :=
    (mem_trivialFibrations_iff _).mp (coefficientProjection_mem_trivialFibrations i hi α) |>.2
  let _ : HasLiftingProperty j (coefficientProjection i α) := ModelCategory.cm4b _ _
  unfold parameterLift
  exact sq.fac_right

/-- The original prism of the whole lift restricts to the entire prescribed partial prism. -/
theorem parameterLift_prism_left {L₀ L : SSet.{u}} (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (j : L₀ ⟶ L) [Mono j]
    {f₀ : L₀ ⟶ object i α} {γ : L ⟶ K}
    (sq : CommSq f₀ j (coefficientProjection i α) γ) :
    A ◁ j ≫ prism i α (parameterLift i hi α j sq) = prism i α f₀ := by
  apply curry_injective
  rw [curry_natural_left, prism_curry, prism_curry, ← Category.assoc,
    parameterLift_left]

/-- The same lifted prism retains the full original source boundary and coefficient family. -/
theorem parameterLift_prism_boundary {L₀ L : SSet.{u}} (i : A₀ ⟶ A) [Mono i]
    (hi : categoricalEquivalences i) [Quasicategory Q]
    (α : K ⟶ (FunctorCore.functor A₀).obj Q) (j : L₀ ⟶ L) [Mono j]
    {f₀ : L₀ ⟶ object i α} {γ : L ⟶ K}
    (sq : CommSq f₀ j (coefficientProjection i α) γ) :
    i ▷ L ≫ prism i α (parameterLift i hi α j sq) =
      uncurry (γ ≫ α ≫ (core ((ihom A₀).obj Q)).ι) := by
  rw [prism_restriction, ← Category.assoc, parameterLift_right]

end SSet.FunctorCore.Extension
