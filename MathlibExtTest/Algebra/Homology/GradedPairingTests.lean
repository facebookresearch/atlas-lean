/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
import MathlibExt.CategoryTheory.Monoidal.PreservesColimits
import MathlibExt.Algebra.Homology.GradedPairingHomology
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nonzero homology classes and the odd Leibniz sign

Constant integer terms with zero differentials give a degree-zero product whose
value on the classes of two and three reads back as six. The second example pairs
degree one with a complex whose even differentials are multiplication by three.
Its target has odd differential minus three: the odd Leibniz sign is detected on
elements, and the product of degree-one classes reads back as one modulo three.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct

namespace MathlibExtTest.GradedPairing

private abbrev Z : Ab.{0} := AddCommGrpCat.of ℤ
private abbrev T : Ab.{0} := AddCommGrpCat.of (ZMod 3)

private def scalar (a : ℤ) : Z ⟶ Z :=
  AddCommGrpCat.ofHom
    { toFun := fun x => a * x
      map_zero' := by simp
      map_add' := by intro x y; exact mul_add a x y }

@[simp] private lemma scalar_apply (a x : ℤ) : scalar a x = a * x := rfl
@[simp] private lemma scalar_zero : scalar 0 = 0 := by
  apply ConcreteCategory.ext_apply
  intro x
  change (0 : ℤ) * x = 0
  simp

private abbrev coefficientComplex (a : ℕ → ℤ) (ha : ∀ n, a n * a (n + 1) = 0) :
    CochainComplex Ab.{0} ℕ :=
  CochainComplex.of (fun _ => Z) (fun n => scalar (a n)) (by
    intro n
    apply ConcreteCategory.ext_apply
    intro x
    change a (n + 1) * (a n * x) = 0
    rw [← mul_assoc, mul_comm (a (n + 1)) (a n), ha n, zero_mul])

@[simp] private lemma coefficient_d (a : ℕ → ℤ) (ha) (n : ℕ) :
    (coefficientComplex a ha).d n (n + 1) = scalar (a n) :=
  CochainComplex.of_d (fun _ => Z) (fun n => scalar (a n)) n

@[simp] private lemma coefficient_iso_apply (a : ℕ → ℤ) (ha)
    {p q : ℕ} (h : p = q) (x : ℤ) :
    ((coefficientComplex a ha).XIsoOfEq h).hom x = x := by
  cases h
  rfl

private abbrev zeroComplex := coefficientComplex (fun _ => 0) (by intro n; simp)

private def evenThree (n : ℕ) : ℤ := if n % 2 = 0 then 3 else 0
private def oddMinusThree (n : ℕ) : ℤ := if n % 2 = 1 then -3 else 0

private lemma evenThree_square (n : ℕ) : evenThree n * evenThree (n + 1) = 0 := by
  by_cases h : n % 2 = 0
  · have hn : (n + 1) % 2 ≠ 0 := by omega
    simp [evenThree, h, hn]
  · simp [evenThree, h]

private lemma oddMinusThree_square (n : ℕ) :
    oddMinusThree n * oddMinusThree (n + 1) = 0 := by
  by_cases h : n % 2 = 1
  · have hn : (n + 1) % 2 ≠ 1 := by omega
    simp [oddMinusThree, h, hn]
  · simp [oddMinusThree, h]

private lemma odd_shift (q : ℕ) : oddMinusThree (1 + q) = -evenThree q := by
  by_cases h : q % 2 = 0
  · have hn : (1 + q) % 2 = 1 := by omega
    simp [oddMinusThree, evenThree, h, hn]
  · have hn : (1 + q) % 2 ≠ 1 := by omega
    simp [oddMinusThree, evenThree, h, hn]

private abbrev evenComplex := coefficientComplex evenThree evenThree_square
private abbrev oddComplex := coefficientComplex oddMinusThree oddMinusThree_square

private def multiply : Z ⊗ Z ⟶ Z :=
  AddCommGrpCat.ofHom (LinearMap.mul' ℤ ℤ).toAddMonoidHom

@[simp] private lemma multiply_tmul (x y : ℤ) : multiply (x ⊗ₜ[ℤ] y) = x * y := by
  change (LinearMap.mul' ℤ ℤ) (x ⊗ₜ[ℤ] y) = x * y
  rw [LinearMap.mul'_apply]

private theorem tensor_ext {X Y D : Ab.{0}} {f g : X ⊗ Y ⟶ D}
    (h : ∀ x y, f (x ⊗ₜ[ℤ] y) = g (x ⊗ₜ[ℤ] y)) : f = g := by
  apply ConcreteCategory.ext_apply
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy => simp only [map_add, hx, hy]

private def zeroPairing : CochainGradedPairing zeroComplex zeroComplex zeroComplex where
  pair _ _ := multiply
  leibniz p q := by simp [zeroComplex, coefficient_d, MonoidalPreadditive.zero_tensor,
    MonoidalPreadditive.tensor_zero, comp_zero, zero_comp]

private def oddComponent (p _q : ℕ) : Z ⊗ Z ⟶ Z := if p = 1 then multiply else 0

private def oddPairing : CochainGradedPairing zeroComplex evenComplex oddComplex where
  pair := oddComponent
  leibniz p q := by
    by_cases hp : p = 1
    · subst p
      apply tensor_ext (X := Z) (Y := Z) (D := Z)
      intro x y
      simp only [oddComponent, ite_eq_left rfl, ite_eq_right (by omega : 1 + 1 ≠ 1),
        zeroComplex, evenComplex, oddComplex, coefficient_d, scalar_zero,
        AddCommGrpCat.tensorHom_apply, coefficient_iso_apply, multiply_tmul]
      change oddMinusThree (1 + q) * (x * y) =
        0 + ((-1 : ℤ) ^ 1) • (x * (evenThree q * y))
      rw [odd_shift]
      simp only [pow_one, zsmul_eq_mul]
      ring
    · simp [oddComponent, hp, zeroComplex, coefficient_d,
        MonoidalPreadditive.zero_tensor, MonoidalPreadditive.tensor_zero, comp_zero, zero_comp]

private def cycleSection (a : ℕ → ℤ) (ha) (n : ℕ) (hn : a n = 0) :
    Z ⟶ (coefficientComplex a ha).cycles n :=
  (coefficientComplex a ha).liftCycles (𝟙 Z) (n + 1) (by simp)
    (by simp [coefficient_d, hn])

@[reassoc (attr := simp)] private lemma cycleSection_i (a : ℕ → ℤ) (ha)
    (n : ℕ) (hn : a n = 0) :
    cycleSection a ha n hn ≫ (coefficientComplex a ha).iCycles n = 𝟙 Z := by
  exact (coefficientComplex a ha).liftCycles_i _ _ (by simp) _

private def classMap (a : ℕ → ℤ) (ha) (n : ℕ) (hn : a n = 0) :
    Z ⟶ (coefficientComplex a ha).homology n :=
  cycleSection a ha n hn ≫ (coefficientComplex a ha).homologyπ n

private def readback {D : Ab.{0}} (K : CochainComplex Ab.{0} ℕ) (n : ℕ)
    (f : K.X n ⟶ D) (hf : K.d ((ComplexShape.up ℕ).prev n) n ≫ f = 0) :
    K.homology n ⟶ D :=
  (K.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ (K.iCycles n ≫ f) (by
      rw [← Category.assoc, K.toCycles_i]
      exact hf))

@[reassoc (attr := simp)] private lemma readback_fac {D : Ab.{0}}
    (K : CochainComplex Ab.{0} ℕ) (n : ℕ) (f : K.X n ⟶ D) (hf) :
    K.homologyπ n ≫ readback K n f hf = K.iCycles n ≫ f :=
  (K.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac _
    WalkingParallelPair.one

private lemma pairing_readback (a b c : ℕ → ℤ) (ha hb hc)
    (P : CochainGradedPairing (coefficientComplex a ha)
      (coefficientComplex b hb) (coefficientComplex c hc))
    (p q : ℕ) (hp : a p = 0) (hq : b q = 0) {D : Ab.{0}} (f : Z ⟶ D)
    (hf : (coefficientComplex c hc).d ((ComplexShape.up ℕ).prev (p + q))
      (p + q) ≫ f = 0) :
    (classMap a ha p hp ⊗ₘ classMap b hb q hq) ≫ P.pairHomology p q ≫
      readback (coefficientComplex c hc) (p + q) f hf = P.pair p q ≫ f := by
  simp only [classMap, ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  rw [P.tensor_homologyπ_comp_pairHomology_assoc]
  rw [readback_fac, P.pairCycles_i_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, cycleSection_i, cycleSection_i]
  simp

private lemma zero_d (i j : ℕ) : zeroComplex.d i j = 0 := by
  simp [zeroComplex, coefficientComplex, CochainComplex.of.d]

private def zeroReadback : zeroComplex.homology 0 ⟶ Z :=
  readback zeroComplex 0 (𝟙 Z) (by rw [zero_d, zero_comp])

example : (ComplexShape.up ℕ).prev 0 = 0 := CochainComplex.prev_nat_zero
example : zeroComplex.toCycles 0 0 = 0 :=
  zeroComplex.toCycles_eq_zero (by simp [ComplexShape.up])

example :
    ((classMap (fun _ => 0) (by intro n; simp) 0 rfl ⊗ₘ
        classMap (fun _ => 0) (by intro n; simp) 0 rfl) ≫
      zeroPairing.pairHomology 0 0 ≫ zeroReadback) ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ)) = 6 := by
  have h := pairing_readback (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (by intro n; simp) (by intro n; simp) (by intro n; simp)
    zeroPairing 0 0 rfl rfl (𝟙 Z) (by rw [zero_d, zero_comp])
  have he := congrArg (fun g : MonoidalCategory.tensorObj Z Z ⟶ Z => g ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ))) h
  simpa [zeroReadback, zeroPairing] using he

example : (oddPairing.pair 1 0 ≫ oddComplex.d 1 2) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = -3 := by
  norm_num [oddPairing, oddComponent, oddComplex, coefficient_d]

example : ((𝟙 Z ⊗ₘ evenComplex.d 0 1) ≫ oddPairing.pair 1 1)
    ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = 3 := by
  norm_num [oddPairing, oddComponent, evenComplex, coefficient_d, evenThree,
    AddCommGrpCat.tensorHom_apply]

example : (3 : ℤ) ≠ -3 := by norm_num

private def reduceThree : Z ⟶ T :=
  AddCommGrpCat.ofHom (Int.castRingHom (ZMod 3)).toAddMonoidHom

private lemma reduced_boundary : oddComplex.d 1 2 ≫ reduceThree = 0 := by
  change scalar (-3) ≫ reduceThree = 0
  apply ConcreteCategory.ext_apply
  intro x
  change (((-3 : ℤ) * x : ℤ) : ZMod 3) = 0
  norm_num

private def oddReadback : oddComplex.homology 2 ⟶ T :=
  readback oddComplex 2 reduceThree (by
    change oddComplex.d 1 2 ≫ reduceThree = 0
    exact reduced_boundary)

example :
    ((classMap (fun _ => 0) (by intro n; simp) 1 rfl ⊗ₘ
        classMap evenThree evenThree_square 1 (by norm_num [evenThree])) ≫
      oddPairing.pairHomology 1 1 ≫ oddReadback) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = (1 : ZMod 3) := by
  have h := pairing_readback (fun _ => 0) evenThree oddMinusThree
    (by intro n; simp) evenThree_square oddMinusThree_square
    oddPairing 1 1 rfl (by norm_num [evenThree]) reduceThree
    (by
      change oddComplex.d 1 2 ≫ reduceThree = 0
      exact reduced_boundary)
  have he := congrArg (fun g : MonoidalCategory.tensorObj Z Z ⟶ T => g ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ))) h
  simpa [oddReadback, oddPairing, oddComponent, reduceThree] using he

example : (1 : ZMod 3) ≠ 0 := by norm_num

end MathlibExtTest.GradedPairing
