/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua, Codex -/
module

import MathlibExt.Algebra.Homology.FunctorComplex
import MathlibExt.Algebra.Homology.HomologySequenceIsoTransport
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Algebra.Field.Rat
meta import Mathlib.Tactic.NormNum

/-!
# Rational diagrams and connecting maps under a change of coordinates

The two-term rational complex has a specified differential `r`. Its degree-zero subcomplex
and degree-one quotient form an actual short exact sequence of complexes. Cycle coordinates
compute its connecting map as multiplication by `r`, including a nonzero value. Negating the
three terms gives a nonidentity short-complex isomorphism; the general transport API retains
the computed connecting map.

A diagram with two parallel arrows, multiplication by two and by three, becomes a complex of
functors. Its differential and a fivefold natural transformation are checked on coefficients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MathlibExtTest.ComplexTransportTests

private abbrev C := ModuleCat.{0} ℚ
private abbrev Q : C := ModuleCat.of ℚ ℚ
private abbrev shape := ComplexShape.down ℕ

private lemma rel10 : shape.Rel 1 0 := rfl
private lemma next10 : shape.next 1 = 0 := shape.next_eq' rel10

private def scalar (r : ℚ) : Q ⟶ Q :=
  ModuleCat.ofHom (r • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))

@[simp] private lemma scalar_apply (r x : ℚ) : (scalar r).hom x = r * x := by
  simp [scalar]

private abbrev lowerX : ℕ → C
  | 0 => Q
  | _ + 1 => 0

private abbrev upperX : ℕ → C
  | 0 => 0
  | 1 => Q
  | _ + 2 => 0

private abbrev middleX : ℕ → C
  | 0 => Q
  | 1 => Q
  | _ + 2 => 0

private abbrev lower : ChainComplex C ℕ :=
  ChainComplex.of lowerX (fun _ => 0) (by intro n; simp)

private abbrev upper : ChainComplex C ℕ :=
  ChainComplex.of upperX (fun _ => 0) (by intro n; simp)

private def middleD (r : ℚ) : (n : ℕ) → middleX (n + 1) ⟶ middleX n
  | 0 => scalar r
  | _ + 1 => 0

private abbrev middle (r : ℚ) : ChainComplex C ℕ :=
  ChainComplex.of middleX (middleD r) (by intro n; cases n <;> simp [middleD])

@[simp] private lemma lower_d (i j : ℕ) : lower.d i j = 0 := by
  simp [lower, ChainComplex.of.d]

@[simp] private lemma upper_d (i j : ℕ) : upper.d i j = 0 := by
  simp [upper, ChainComplex.of.d]

@[simp] private lemma middle_d (r : ℚ) : (middle r).d 1 0 = scalar r :=
  ChainComplex.of_d middleX (middleD r) 0

private def inclusion (r : ℚ) : lower ⟶ middle r :=
  ChainComplex.ofHom
    (fun n => match n with
      | 0 => 𝟙 Q
      | _ + 1 => 0)
    (by intro n; cases n <;> simp [middle, middleD, ChainComplex.of_d])

private def quotient (r : ℚ) : middle r ⟶ upper :=
  ChainComplex.ofHom
    (fun n => match n with
      | 0 => 0
      | 1 => 𝟙 Q
      | _ + 2 => 0)
    (by
      intro n
      cases n with
      | zero => simp
      | succ n => cases n <;> simp [middle, middleD, ChainComplex.of_d])

private abbrev sequence (r : ℚ) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (inclusion r) (quotient r) (by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => simp [inclusion, quotient, HomologicalComplex.comp_f]
    | succ n => cases n <;> simp [inclusion, quotient, HomologicalComplex.comp_f])

private lemma sequence_shortExact (r : ℚ) : (sequence r).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · apply (((sequence r).map (HomologicalComplex.eval C shape 0)).exact_iff_epi
          (by rfl)).2
        change Epi (𝟙 Q)
        infer_instance
      · change Mono (𝟙 Q)
        infer_instance
      · change Epi (0 : Q ⟶ (0 : C))
        infer_instance
  | succ n =>
      cases n with
      | zero =>
          refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
          · apply (((sequence r).map (HomologicalComplex.eval C shape 1)).exact_iff_mono
              (by rfl)).2
            change Mono (𝟙 Q)
            infer_instance
          · change Mono (0 : (0 : C) ⟶ Q)
            infer_instance
          · change Epi (𝟙 Q)
            infer_instance
      | succ n =>
          refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
          · apply ShortComplex.exact_of_isZero_X₂
            change IsZero (0 : C)
            exact isZero_zero C
          · change Mono (0 : (0 : C) ⟶ (0 : C))
            infer_instance
          · change Epi (0 : (0 : C) ⟶ (0 : C))
            infer_instance

private def zeroCoordinate (K : ChainComplex C ℕ) (i : ℕ)
    (h : ∀ a b, K.d a b = 0) : K.homology i ≅ K.X i :=
  (ShortComplex.HomologyData.ofZeros (K.sc i) (h _ _) (h _ _)).left.homologyIso

private lemma cycle_coordinate (K : ChainComplex C ℕ) (i : ℕ)
    (h : ∀ a b, K.d a b = 0) {A : C} (x : A ⟶ K.X i) :
    K.liftCycles (i := i) x (shape.next i) rfl (by rw [h, comp_zero]) ≫ K.homologyπ i ≫
      (zeroCoordinate K i h).hom = x := by
  let hd := ShortComplex.HomologyData.ofZeros (K.sc i) (h _ _) (h _ _)
  change (K.sc i).liftCycles x _ ≫ (K.sc i).homologyπ ≫ hd.left.homologyIso.hom = x
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.liftCycles_comp_cyclesIso_hom]
  simpa only [hd, ShortComplex.HomologyData.ofZeros, ShortComplex.LeftHomologyData.ofZeros]
    using hd.left.liftK_i x _

private def sourceCoordinate : upper.homology 1 ≅ Q := zeroCoordinate upper 1 upper_d
private def targetCoordinate : lower.homology 0 ≅ Q := zeroCoordinate lower 0 lower_d

private def sourceClass : Q ⟶ upper.homology 1 :=
  upper.liftCycles (i := 1) (𝟙 Q) 0 next10 (by simp) ≫ upper.homologyπ 1

private lemma sourceClass_inverse : sourceClass = sourceCoordinate.inv := by
  apply (cancel_mono sourceCoordinate.hom).1
  rw [Iso.inv_hom_id]
  simpa only [sourceClass, sourceCoordinate, next10] using
    cycle_coordinate upper 1 upper_d (𝟙 Q)

example : sourceClass.hom (1 : ℚ) ≠ 0 := by
  intro hzero
  have hc : sourceCoordinate.hom.hom (sourceClass.hom (1 : ℚ)) = 1 := by
    rw [sourceClass_inverse]
    exact ConcreteCategory.congr_hom sourceCoordinate.inv_hom_id (1 : ℚ)
  rw [hzero, map_zero] at hc
  exact zero_ne_one hc

private lemma connecting_coordinate (r : ℚ) :
    sourceCoordinate.inv ≫ (sequence_shortExact r).δ 1 0 rel10 ≫
      targetCoordinate.hom = scalar r := by
  have hδ := (sequence_shortExact r).δ_eq 1 0 rel10 (𝟙 Q) (by simp)
    (𝟙 Q) (by simp [sequence, quotient]) (scalar r)
    (by simp [sequence, inclusion]) (shape.next 0) rfl
  change sourceClass ≫ (sequence_shortExact r).δ 1 0 rel10 = _ at hδ
  rw [← sourceClass_inverse]
  calc
    _ = lower.liftCycles (i := 0) (scalar r) (shape.next 0) rfl (by simp) ≫ lower.homologyπ 0 ≫
        targetCoordinate.hom := by
      simpa only [Category.assoc] using congrArg
        (fun z : Q ⟶ lower.homology 0 => z ≫ targetCoordinate.hom) hδ
    _ = scalar r := cycle_coordinate lower 0 lower_d (scalar r)

private def negationIso (r : ℚ) : sequence r ≅ sequence r where
  hom := -𝟙 (sequence r)
  inv := -𝟙 (sequence r)
  hom_inv_id := by simp
  inv_hom_id := by simp

-- A genuine nonidentity change of coordinates on the degree-one quotient.
example : (((negationIso 3).hom.τ₃.f 1).hom (1 : ℚ)) = (-1 : ℚ) := by
  change ((-𝟙 Q : Q ⟶ Q).hom (1 : ℚ)) = -1
  simp

/-- Transport through the nonidentity short-complex isomorphism retains the computed map. -/
private lemma transported_coordinate (r : ℚ) :
    sourceCoordinate.inv ≫
      (sequence_shortExact r).connectingIsoTransport (negationIso r) 1 0 rel10 ≫
      targetCoordinate.hom = scalar r := by
  rw [ShortComplex.ShortExact.connectingIsoTransport_eq]
  exact connecting_coordinate r

example : (sourceCoordinate.inv ≫
    (sequence_shortExact 3).connectingIsoTransport (negationIso 3) 1 0 rel10 ≫
    targetCoordinate.hom).hom (2 : ℚ) = 6 := by
  rw [transported_coordinate, scalar_apply]
  norm_num

example : (sourceCoordinate.inv ≫
    (sequence_shortExact 0).connectingIsoTransport (negationIso 0) 1 0 rel10 ≫
    targetCoordinate.hom).hom (2 : ℚ) = 0 := by
  rw [transported_coordinate, scalar_apply]
  norm_num

example : (sequence_shortExact 3).connectingIsoTransport (negationIso 3) 1 0 rel10 ≠ 0 := by
  intro hzero
  have hc := transported_coordinate 3
  rw [hzero] at hc
  simp only [zero_comp, comp_zero] at hc
  have hx := congrArg (fun z : Q ⟶ Q => z.hom (1 : ℚ)) hc
  norm_num [scalar] at hx

private abbrev diagram : WalkingParallelPair ⥤ ChainComplex C ℕ :=
  parallelPair ((2 : ℕ) • (𝟙 (middle 2))) ((3 : ℕ) • (𝟙 (middle 2)))

private abbrev transposed : ChainComplex (WalkingParallelPair ⥤ C) ℕ :=
  (HomologicalComplex.functorToComplexToComplexOfFunctors shape).obj diagram

private def fivefold : diagram ⟶ diagram := (5 : ℕ) • (𝟙 diagram)

-- The two diagram arrows retain different nonzero coefficient actions.
example : (((transposed.X 1).map WalkingParallelPairHom.left).hom (1 : ℚ)) = (2 : ℚ) := by
  change (((2 : ℕ) • (𝟙 Q : Q ⟶ Q)).hom (1 : ℚ)) = (2 : ℚ)
  norm_num [ModuleCat.hom_nsmul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply]

example : (((transposed.X 1).map WalkingParallelPairHom.right).hom (1 : ℚ)) = (3 : ℚ) := by
  change (((3 : ℕ) • (𝟙 Q : Q ⟶ Q)).hom (1 : ℚ)) = (3 : ℚ)
  norm_num [ModuleCat.hom_nsmul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply]

example : (((transposed.d 1 0).app WalkingParallelPair.zero).hom (1 : ℚ)) = (2 : ℚ) := by
  change ((middle 2).d 1 0).hom (1 : ℚ) = 2
  rw [middle_d, scalar_apply]
  norm_num

example : ((((HomologicalComplex.functorToComplexToComplexOfFunctors shape).map
    fivefold).f 1).app WalkingParallelPair.zero).hom (1 : ℚ) = (5 : ℚ) := by
  change (((5 : ℕ) • (𝟙 Q : Q ⟶ Q)).hom (1 : ℚ)) = (5 : ℚ)
  norm_num [ModuleCat.hom_nsmul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply]

end MathlibExtTest.ComplexTransportTests
