/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Topology.Instances.Complex
import Mathlib.Order.Interval.Set.Infinite





open Metric Set

noncomputable section


theorem complex_ball_infinite (z : Complex) {r : Real} (hr : 0 < r) :
    (ball z r).Infinite := by
  let shift : Real → Complex := fun t ↦ z + (t : Complex)
  have hinj : Function.Injective shift := by
    intro s t hst
    apply_fun Complex.re at hst
    simpa [shift] using hst
  have himage : shift '' Ioo (0 : Real) r ⊆ ball z r := by
    rintro w ⟨t, ht, rfl⟩
    rw [mem_ball]
    rw [show shift t = z + (t : Complex) by rfl, dist_self_add_left]
    simpa [Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
  exact ((Set.Ioo_infinite hr).image hinj.injOn).mono himage



theorem exists_injective_perturbation
    {α : Type} [Fintype α] (f : α → Complex) {r : Real} (hr : 0 < r) :
    ∃ g : α → Complex, Function.Injective g ∧ ∀ a, dist (g a) (f a) < r := by
  classical
  let P := fun (α : Type) [Fintype α] ↦ ∀ f : α → Complex,
    ∃ g : α → Complex, Function.Injective g ∧
      ∀ a, dist (g a) (f a) < r
  have hP : P α := by
    apply Fintype.induction_empty_option (P := P)
    · intro β γ _ e hβ fγ
      obtain ⟨gβ, hgβ, hnearβ⟩ := hβ (fγ ∘ e)
      refine ⟨gβ ∘ e.symm, hgβ.comp e.symm.injective, ?_⟩
      intro c
      simpa using hnearβ (e.symm c)
    · intro f
      let g : PEmpty → Complex := fun x ↦ nomatch x
      refine ⟨g, ?_⟩
      constructor
      · intro x
        exact nomatch x
      · intro x
        exact nomatch x
    · intro β _ hβ fβ
      obtain ⟨g, hg, hnear⟩ := hβ (fun b ↦ fβ (some b))
      obtain ⟨z, hzball, hzrange⟩ :=
        (complex_ball_infinite (fβ none) hr).exists_notMem_finset
          (Finset.univ.image g)
      let g' : Option β → Complex
        | none => z
        | some b => g b
      refine ⟨g', ?_, ?_⟩
      · intro x y hxy
        cases x with
        | none =>
            cases y with
            | none => rfl
            | some b =>
                exfalso
                apply hzrange
                exact Finset.mem_image.mpr
                  ⟨b, Finset.mem_univ b, by simpa [g'] using hxy.symm⟩
        | some a =>
            cases y with
            | none =>
                exfalso
                apply hzrange
                exact Finset.mem_image.mpr
                  ⟨a, Finset.mem_univ a, by simpa [g'] using hxy⟩
            | some b =>
                exact congrArg some (hg (by simpa [g'] using hxy))
      · intro x
        cases x with
        | none => exact hzball
        | some b => exact hnear b
  exact hP f

end
