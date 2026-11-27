/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOneExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The nonsplit integer coefficient sequence as an inverse tower

The coefficient sequence `ℤ —×2→ ℤ → ℤ/2ℤ` is short exact and has no
linear section of its final map. The corresponding constant inverse
towers retain that nonsplitting. Their canonical six-term limit/lim¹
sequence is exact, without supplying exactness or a connecting value
as an input.

The compatible unit families give concrete limit elements. The first
limit map sends their integer coordinate one to two, and the second
limit map sends coordinate one to the nonzero residue one. Thus both
canonical limit maps are nonzero. The unit family retains coordinate one
in the product and the difference kernel. On the product family `a_n = n`,
the identity-minus-shift difference has coordinate minus one. The nonzero
reduction image lies in the kernel of the actual connecting map.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace SequentialLimOneIntegerTwoTests

private abbrev C := ModuleCat.{0} ℤ
private abbrev Z : C := ModuleCat.of ℤ ℤ
private abbrev Q₂ : C := ModuleCat.of ℤ (ZMod 2)

private def twice : Z ⟶ Z :=
  ModuleCat.ofHom ((2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private def reduction : Z ⟶ Q₂ :=
  ModuleCat.ofHom ((Int.castAddHom (ZMod 2)).toIntLinearMap)

private lemma twice_apply (x : ℤ) : twice.hom x = 2 * x := rfl
private lemma reduction_apply (x : ℤ) : reduction.hom x = (x : ZMod 2) := rfl

private lemma twice_reduction : twice ≫ reduction = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((2 * x : ℤ) : ZMod 2) = 0
  rw [Int.cast_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

private abbrev coefficientRow : ShortComplex C :=
  ShortComplex.mk twice reduction twice_reduction

private lemma coefficientRow_shortExact : coefficientRow.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff coefficientRow).mpr
    intro x hx
    change (x : ZMod 2) = 0 at hx
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    refine ⟨y, ?_⟩
    change 2 * y = x
    exact hy.symm
  · apply (ModuleCat.mono_iff_injective twice).mpr
    intro x y h
    change (2 : ℤ) * x = 2 * y at h
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h
  · apply (ModuleCat.epi_iff_surjective reduction).mpr
    exact ZMod.intCast_surjective

private lemma reduction_no_section (s : Q₂ ⟶ Z) : s ≫ reduction ≠ 𝟙 Q₂ := by
  intro hs
  have hadd := s.hom.map_add (1 : ZMod 2) (1 : ZMod 2)
  rw [show (1 : ZMod 2) + 1 = 0 from by decide, map_zero] at hadd
  have htwo : (2 : ℤ) * s.hom (1 : ZMod 2) = 0 := by
    rw [two_mul]
    exact hadd.symm
  have hzero : s.hom (1 : ZMod 2) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℤ) ≠ 0)
  have h := ConcreteCategory.congr_hom hs (1 : ZMod 2)
  change reduction.hom (s.hom (1 : ZMod 2)) = 1 at h
  rw [hzero, map_zero] at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

private abbrev towerRow : ShortComplex (ℕᵒᵖ ⥤ C) :=
  coefficientRow.map (Functor.const ℕᵒᵖ)

private lemma towerRow_shortExact : towerRow.ShortExact :=
  coefficientRow_shortExact.map_of_exact (Functor.const ℕᵒᵖ)

local instance : HasLimit towerRow.X₁ :=
  hasLimit_of_sequential_product_and_kernel towerRow.X₁
local instance : HasLimit towerRow.X₂ :=
  hasLimit_of_sequential_product_and_kernel towerRow.X₂
local instance : HasLimit towerRow.X₃ :=
  hasLimit_of_sequential_product_and_kernel towerRow.X₃

private def firstCone : Cone towerRow.X₁ where
  pt := Z
  π := 𝟙 towerRow.X₁

private def secondCone : Cone towerRow.X₂ where
  pt := Z
  π := 𝟙 towerRow.X₂

private def firstOne : limit towerRow.X₁ :=
  (limit.lift towerRow.X₁ firstCone).hom (1 : ℤ)

private def secondOne : limit towerRow.X₂ :=
  (limit.lift towerRow.X₂ secondCone).hom (1 : ℤ)

private lemma firstOne_component (n : ℕ) :
    (limit.π towerRow.X₁ (op n)).hom firstOne = 1 := by
  have h := ConcreteCategory.congr_hom (limit.lift_π firstCone (op n)) (1 : ℤ)
  change (limit.π towerRow.X₁ (op n)).hom
    ((limit.lift towerRow.X₁ firstCone).hom (1 : ℤ)) = 1 at h
  exact h

private lemma secondOne_component (n : ℕ) :
    (limit.π towerRow.X₂ (op n)).hom secondOne = 1 := by
  have h := ConcreteCategory.congr_hom (limit.lift_π secondCone (op n)) (1 : ℤ)
  change (limit.π towerRow.X₂ (op n)).hom
    ((limit.lift towerRow.X₂ secondCone).hom (1 : ℤ)) = 1 at h
  exact h

private lemma firstLimitMap_component (n : ℕ) :
    (limit.π towerRow.X₂ (op n)).hom ((limMap towerRow.f).hom firstOne) = 2 := by
  have h := ConcreteCategory.congr_hom (limMap_π towerRow.f (op n)) firstOne
  change (limit.π towerRow.X₂ (op n)).hom ((limMap towerRow.f).hom firstOne) =
    twice.hom ((limit.π towerRow.X₁ (op n)).hom firstOne) at h
  rw [firstOne_component, twice_apply, mul_one] at h
  exact h

private lemma secondLimitMap_component (n : ℕ) :
    (limit.π towerRow.X₃ (op n)).hom ((limMap towerRow.g).hom secondOne) = 1 := by
  have h := ConcreteCategory.congr_hom (limMap_π towerRow.g (op n)) secondOne
  change (limit.π towerRow.X₃ (op n)).hom ((limMap towerRow.g).hom secondOne) =
    reduction.hom ((limit.π towerRow.X₂ (op n)).hom secondOne) at h
  rw [secondOne_component, reduction_apply, Int.cast_one] at h
  exact h

private abbrev exactSequence : ComposableArrows C 5 :=
  sequentialLimOneExactSequence towerRow towerRow_shortExact

private abbrev productOne : sequentialProduct towerRow.X₁ :=
  (sequentialLimitToProduct towerRow.X₁).hom firstOne

private lemma productOne_component (n : ℕ) :
    (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom productOne = 1 := by
  have h := ConcreteCategory.congr_hom
    (sequentialLimitToProduct_π towerRow.X₁ n) firstOne
  change (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom productOne =
    (limit.π towerRow.X₁ (op n)).hom firstOne at h
  exact h.trans (firstOne_component n)

private abbrev kernelOne : kernel (sequentialDifference towerRow.X₁) :=
  (sequentialLimitKernelIso towerRow.X₁).hom.hom firstOne

private lemma kernelOne_product :
    (kernel.ι (sequentialDifference towerRow.X₁)).hom kernelOne = productOne := by
  have h := ConcreteCategory.congr_hom
    (sequentialLimitKernelIso_hom_ι towerRow.X₁) firstOne
  exact h

private def integerCoordinateMap (n : ℕ) : Z ⟶ towerRow.X₁.obj (op n) :=
  ModuleCat.ofHom ((n : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

private def indexFamily : sequentialProduct towerRow.X₁ :=
  (Pi.lift integerCoordinateMap).hom (1 : ℤ)

private lemma indexFamily_component (n : ℕ) :
    (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom indexFamily = (n : ℤ) := by
  have h := ConcreteCategory.congr_hom (Pi.lift_comp_π integerCoordinateMap n) (1 : ℤ)
  change (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom indexFamily =
    (n : ℤ) * 1 at h
  exact h.trans (mul_one _)

private lemma indexFamily_difference (n : ℕ) :
    (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom
      ((sequentialDifference towerRow.X₁).hom indexFamily) = -1 := by
  have h := ConcreteCategory.congr_hom (sequentialDifference_π towerRow.X₁ n) indexFamily
  change (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom
      ((sequentialDifference towerRow.X₁).hom indexFamily) =
    (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom indexFamily -
      (towerRow.X₁.map (homOfLE (Nat.le_succ n)).op).hom
        ((Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) (n + 1)).hom indexFamily) at h
  rw [indexFamily_component, indexFamily_component] at h
  change (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom
      ((sequentialDifference towerRow.X₁).hom indexFamily) =
    (n : ℤ) - ((n + 1 : ℕ) : ℤ) at h
  exact h.trans (by rw [Nat.cast_add, Nat.cast_one]; ring)

private abbrev connecting : limit towerRow.X₃ ⟶ sequentialLimOne towerRow.X₁ :=
  sequentialLimOneConnecting towerRow towerRow_shortExact

private lemma middle_connecting_zero : limMap towerRow.g ≫ connecting = 0 := by
  have h := (sequentialLimOneExactSequence_exact towerRow towerRow_shortExact).toIsComplex.zero 1
  change limMap towerRow.g ≫ connecting = 0 at h
  exact h

private abbrev middleOne : limit towerRow.X₃ := (limMap towerRow.g).hom secondOne

private lemma connecting_middleOne : connecting.hom middleOne = 0 := by
  have h := ConcreteCategory.congr_hom middle_connecting_zero secondOne
  exact h

/-- Integer multiplication and reduction define a short exact coefficient row. -/
example : coefficientRow.ShortExact := coefficientRow_shortExact

/-- The coefficient reduction has no integer-linear section. -/
example : ¬ ∃ s : Q₂ ⟶ Z, s ≫ reduction = 𝟙 Q₂ := by
  rintro ⟨s, hs⟩
  exact reduction_no_section s hs

/-- The corresponding constant inverse-tower row is short exact. -/
example : towerRow.ShortExact := towerRow_shortExact

/-- The inverse-tower reduction also has no natural section. -/
example : ¬ ∃ s : towerRow.X₃ ⟶ towerRow.X₂, s ≫ towerRow.g = 𝟙 towerRow.X₃ := by
  rintro ⟨s, hs⟩
  apply reduction_no_section (s.app (op 0))
  have h := congrArg (fun f : towerRow.X₃ ⟶ towerRow.X₃ => f.app (op 0)) hs
  exact h

/-- Multiplication by two is retained at every tower level. -/
example (n : ℕ) : (towerRow.f.app (op n)).hom (1 : ℤ) = 2 := by
  change twice.hom (1 : ℤ) = 2
  rw [twice_apply, mul_one]

/-- The second tower map has nonzero residue-one value. -/
example (n : ℕ) : (towerRow.g.app (op n)).hom (1 : ℤ) = (1 : ZMod 2) := by
  change reduction.hom (1 : ℤ) = 1
  rw [reduction_apply, Int.cast_one]

/-- The first canonical inverse-limit map has coordinate two on the unit family. -/
example (n : ℕ) :
    (limit.π towerRow.X₂ (op n)).hom ((limMap towerRow.f).hom firstOne) = 2 :=
  firstLimitMap_component n

/-- The second canonical inverse-limit map has coordinate one on the unit family. -/
example (n : ℕ) :
    (limit.π towerRow.X₃ (op n)).hom ((limMap towerRow.g).hom secondOne) = 1 :=
  secondLimitMap_component n

/-- The integer inverse-limit unit family is nonzero. -/
example : firstOne ≠ 0 := by
  intro h
  have hc := firstOne_component 0
  rw [h, map_zero] at hc
  exact (by norm_num : (0 : ℤ) ≠ 1) hc

/-- The first inverse-limit map is nonzero. -/
example : limMap towerRow.f ≠ 0 := by
  intro h
  have hc := firstLimitMap_component 0
  rw [h, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] at hc
  exact (by norm_num : (0 : ℤ) ≠ 2) hc

/-- The second inverse-limit map is nonzero. -/
example : limMap towerRow.g ≠ 0 := by
  intro h
  have hc := secondLimitMap_component 0
  rw [h, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] at hc
  exact (by decide : (0 : ZMod 2) ≠ 1) hc

/-- The canonical six-object limit/lim¹ sequence of this nonsplit row is exact. -/
example : exactSequence.Exact :=
  sequentialLimOneExactSequence_exact towerRow towerRow_shortExact

/-- The first map of that exact sequence has a nonzero coordinate-two value. -/
example : (limit.π towerRow.X₂ (op 0)).hom
    ((exactSequence.map' 0 1).hom firstOne) = 2 := by
  change (limit.π towerRow.X₂ (op 0)).hom
    ((limMap towerRow.f).hom firstOne) = 2
  exact firstLimitMap_component 0

/-- The chosen inverse-limit unit keeps coordinate one in the actual product. -/
example (n : ℕ) :
    (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom productOne = 1 :=
  productOne_component n

/-- Its actual difference-kernel inclusion has the same unit coordinates. -/
example (n : ℕ) :
    (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) n).hom
      ((kernel.ι (sequentialDifference towerRow.X₁)).hom kernelOne) = 1 := by
  rw [kernelOne_product]
  exact productOne_component n

/-- Identity minus shift has value minus one on the indexed integer family. -/
example : (Pi.π (fun n : ℕ => towerRow.X₁.obj (op n)) 0).hom
    ((sequentialDifference towerRow.X₁).hom indexFamily) = (-1 : ℤ) :=
  indexFamily_difference 0

/-- The nonzero middle limit-map image has residue coordinate one and connecting value zero. -/
example : (limit.π towerRow.X₃ (op 0)).hom middleOne = (1 : ZMod 2) ∧
    middleOne ≠ 0 ∧ connecting.hom middleOne = 0 := by
  refine ⟨secondLimitMap_component 0, ?_, connecting_middleOne⟩
  intro h
  have hc := secondLimitMap_component 0
  change (limit.π towerRow.X₃ (op 0)).hom middleOne = (1 : ZMod 2) at hc
  rw [h, map_zero] at hc
  exact (by decide : (0 : ZMod 2) ≠ 1) hc

end SequentialLimOneIntegerTwoTests
