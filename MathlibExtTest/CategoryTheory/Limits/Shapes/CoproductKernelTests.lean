/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/
module

import MathlibExt.CategoryTheory.Limits.Shapes.CoproductKernel
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Tactic.NormNum

/-!
# An infinite coproduct of nonzero kernels

In the category of integer modules, take the family indexed by ℤ of maps
fᵢ : ℤ×ℤ → ℤ, fᵢ(a,b)=2a. Its kernels are the second-coordinate summands.
A kernel element supported at indices −1 and 2 has coordinate values
one and minus three. These remain distinct and nonzero under the
comparison with the kernel of the full coproduct map.

The maps uᵢ(a,b)=(a,−3b) on the source and the identity on the target
give commuting squares with fᵢ. Naturality of the coproduct kernel
comparison sends the two detected values to minus three and nine.
-/

noncomputable section

open CategoryTheory Limits

namespace MathlibExtTest.CoproductKernel

private abbrev Z : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev A : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ℤ × ℤ)

private def f : A ⟶ Z := ModuleCat.ofHom ((2 : ℤ) • LinearMap.fst ℤ ℤ ℤ)
private def b : Z ⟶ A := ModuleCat.ofHom (LinearMap.inr ℤ ℤ ℤ)
private def q : A ⟶ Z := ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ)

private theorem b_f : b ≫ f = 0 := by rfl
private theorem b_q : b ≫ q = 𝟙 Z := by rfl

private def k : Z ⟶ kernel f := kernel.lift f b b_f

private abbrev X : ℤ → ModuleCat.{0} ℤ := fun _ => A
private abbrev Y : ℤ → ModuleCat.{0} ℤ := fun _ => Z
private abbrev K : ℤ → ModuleCat.{0} ℤ := fun _ => kernel f
private def F : ∀ i : ℤ, X i ⟶ Y i := fun _ => f

private def e : ((∐ K) : ModuleCat.{0} ℤ) ≅ kernel (CategoryTheory.Limits.Sigma.map F) :=
  coproductKernelIso F

private def projection (j : ℤ) : ((∐ X) : ModuleCat.{0} ℤ) ⟶ Z :=
  CategoryTheory.Limits.Sigma.desc (fun i : ℤ => if i = j then q else 0)

private def evaluate (j : ℤ) : kernel (CategoryTheory.Limits.Sigma.map F) ⟶ Z :=
  kernel.ι (CategoryTheory.Limits.Sigma.map F) ≫ projection j

private theorem component_value (i j a : ℤ) :
    (evaluate j).hom (e.hom.hom ((CategoryTheory.Limits.Sigma.ι K i).hom (k.hom a))) =
      if i = j then a else 0 := by
  have hκ : CategoryTheory.Limits.Sigma.ι K i ≫ e.hom ≫ kernel.ι (CategoryTheory.Limits.Sigma.map
    F) =
      kernel.ι f ≫ CategoryTheory.Limits.Sigma.ι X i :=
    coproductKernelIso_hom_ι F i
  have hk : k ≫ kernel.ι f = b := kernel.lift_ι f b b_f
  have hp : CategoryTheory.Limits.Sigma.ι X i ≫ projection j = if i = j then q else 0 :=
    CategoryTheory.Limits.Sigma.ι_comp_desc (fun i : ℤ => if i = j then q else 0) i
  have h :
      k ≫ CategoryTheory.Limits.Sigma.ι K i ≫ e.hom ≫ kernel.ι (CategoryTheory.Limits.Sigma.map F)
        ≫ projection j =
        if i = j then 𝟙 Z else 0 := by
    calc
      _ = (k ≫ kernel.ι f) ≫ CategoryTheory.Limits.Sigma.ι X i ≫ projection j := by
        simpa only [Category.assoc] using
          congrArg (fun z : kernel f ⟶ ∐ X => k ≫ z ≫ projection j) hκ
      _ = b ≫ (if i = j then q else 0) := by rw [hk, hp]
      _ = _ := by
        by_cases hi : i = j
        · simpa only [ite_eq_left hi] using b_q
        · simp only [ite_eq_right hi, comp_zero]
  have hpoint := ConcreteCategory.congr_hom h a
  change (evaluate j).hom (e.hom.hom ((CategoryTheory.Limits.Sigma.ι K i).hom (k.hom a))) =
    (if i = j then (𝟙 Z) else 0).hom a at hpoint
  by_cases hi : i = j
  · simpa only [ite_eq_left hi, ModuleCat.hom_id, LinearMap.id_apply] using hpoint
  · simpa only [ite_eq_right hi, ModuleCat.hom_zero, LinearMap.zero_apply] using hpoint

private def source (a b : ℤ) : ((∐ K) : ModuleCat.{0} ℤ) :=
  (CategoryTheory.Limits.Sigma.ι K (-1)).hom (k.hom a) + (CategoryTheory.Limits.Sigma.ι K 2).hom
    (k.hom b)

private def totalKernel (a b : ℤ) :
    (kernel (CategoryTheory.Limits.Sigma.map F) : ModuleCat.{0} ℤ) := e.hom.hom (source a b)

theorem negative_coordinate (a b : ℤ) : (evaluate (-1)).hom (totalKernel a b) = a := by
  change (evaluate (-1)).hom
    (e.hom.hom ((CategoryTheory.Limits.Sigma.ι K (-1)).hom (k.hom a) +
      (CategoryTheory.Limits.Sigma.ι K 2).hom (k.hom
      b))) = a
  rw [map_add, map_add, component_value, component_value]
  norm_num

theorem positive_coordinate (a b : ℤ) : (evaluate 2).hom (totalKernel a b) = b := by
  change (evaluate 2).hom
    (e.hom.hom ((CategoryTheory.Limits.Sigma.ι K (-1)).hom (k.hom a) +
      (CategoryTheory.Limits.Sigma.ι K 2).hom (k.hom
      b))) = b
  rw [map_add, map_add, component_value, component_value]
  norm_num

theorem nonzero_full_kernel : totalKernel 1 (-3) ≠ 0 := by
  intro h
  have hv := congrArg (evaluate (-1)).hom h
  rw [negative_coordinate, map_zero] at hv
  norm_num at hv

private def u : A ⟶ A :=
  ModuleCat.ofHom ((LinearMap.fst ℤ ℤ ℤ).prod ((-3 : ℤ) • LinearMap.snd ℤ ℤ ℤ))

private theorem square : f ≫ 𝟙 Z = u ≫ f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private def m : kernel f ⟶ kernel f := kernel.map f f u (𝟙 Z) square
private def scale : Z ⟶ Z := ModuleCat.ofHom ((-3 : ℤ) • LinearMap.id)

private theorem k_scale : k ≫ m = scale ≫ k := by
  apply (cancel_mono (kernel.ι f)).1
  calc
    _ = b ≫ u := by
      simp only [k, m, kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    _ = scale ≫ b := by rfl
    _ = _ := by
      simp only [k, Category.assoc, kernel.lift_ι]

private theorem m_value (a : ℤ) : m.hom (k.hom a) = k.hom (-3 * a) := by
  have h := ConcreteCategory.congr_hom k_scale a
  exact h

private def totalMap : kernel (CategoryTheory.Limits.Sigma.map F) ⟶ kernel
  (CategoryTheory.Limits.Sigma.map F) :=
  kernel.map (CategoryTheory.Limits.Sigma.map F) (CategoryTheory.Limits.Sigma.map F)
    (CategoryTheory.Limits.Sigma.map
    (fun _ => u))
    (CategoryTheory.Limits.Sigma.map (fun _ => 𝟙 Z)) (by
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      simpa only [F, X, Y, Category.assoc, CategoryTheory.Limits.Sigma.ι_map,
        CategoryTheory.Limits.Sigma.ι_map_assoc] using
        congrArg (fun z : A ⟶ Z => z ≫ CategoryTheory.Limits.Sigma.ι Y i) square)

private theorem naturality : CategoryTheory.Limits.Sigma.map (fun _ : ℤ => m) ≫ e.hom = e.hom ≫
  totalMap :=
  coproductKernelIso_naturality F F (fun _ => u) (fun _ => 𝟙 Z) (fun _ => square)

private theorem component_map (i a : ℤ) :
    (CategoryTheory.Limits.Sigma.map (fun _ : ℤ => m)).hom ((CategoryTheory.Limits.Sigma.ι K
      i).hom (k.hom a)) =
      (CategoryTheory.Limits.Sigma.ι K i).hom (k.hom (-3 * a)) := by
  have h := ConcreteCategory.congr_hom (CategoryTheory.Limits.Sigma.ι_map (fun _ : ℤ => m) i)
    (k.hom a)
  exact h.trans (congrArg (CategoryTheory.Limits.Sigma.ι K i).hom (m_value a))

private theorem source_map (a b : ℤ) :
    (CategoryTheory.Limits.Sigma.map (fun _ : ℤ => m)).hom (source a b) = source (-3 * a) (-3 * b)
      := by
  change (CategoryTheory.Limits.Sigma.map (fun _ : ℤ => m)).hom
      ((CategoryTheory.Limits.Sigma.ι K (-1)).hom (k.hom a) + (CategoryTheory.Limits.Sigma.ι K
        2).hom (k.hom b)) =
    (CategoryTheory.Limits.Sigma.ι K (-1)).hom (k.hom (-3 * a)) + (CategoryTheory.Limits.Sigma.ι K
      2).hom (k.hom (-3 *
      b))
  rw [map_add, component_map, component_map]

private theorem total_map (a b : ℤ) :
    totalMap.hom (totalKernel a b) = totalKernel (-3 * a) (-3 * b) := by
  have h := ConcreteCategory.congr_hom naturality (source a b)
  change e.hom.hom ((CategoryTheory.Limits.Sigma.map (fun _ : ℤ => m)).hom (source a b)) =
    totalMap.hom (totalKernel a b) at h
  rw [source_map] at h
  exact h.symm

theorem naturality_negative_value :
    (evaluate (-1)).hom (totalMap.hom (totalKernel 1 (-3))) = -3 := by
  rw [total_map, negative_coordinate]
  norm_num

theorem naturality_positive_value :
    (evaluate 2).hom (totalMap.hom (totalKernel 1 (-3))) = 9 := by
  rw [total_map, positive_coordinate]
  norm_num

end MathlibExtTest.CoproductKernel
