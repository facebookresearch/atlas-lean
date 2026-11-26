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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialMittagLefflerLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
/-!
# Eventual isomorphisms in finite inverse sequences

For an inverse sequence of abelian groups with monic successor maps, every transition is
monic. If every stage group is finite, the images in stage zero stabilize by the
Mittag–Leffler condition. Their injective projections then force every sufficiently late
successor map to be an isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AddCommGrpCat

/-- Monic successor maps make every inverse-sequence transition monic.

For n≤m, the transition F_m → F_n is monic when each F_{k+1} → F_k is monic. -/
theorem finiteCoefficient_mono_map
    (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hMono : ∀ k : ℕ, Mono (F.map (homOfLE (Nat.le_succ k)).op))
    (n m : ℕ) (hnm : n ≤ m) : Mono (F.map (homOfLE hnm).op) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      have hi : (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) := Subsingleton.elim _ _
      rw [hi, F.map_id]
      infer_instance
  | succ m hnm ih =>
      have hh : (homOfLE (Nat.le.step hnm)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
      rw [hh, F.map_comp]
      letI := ih
      letI := hMono m
      infer_instance

/-- Finite inverse sequences with monic transitions become stationary.

If every stage is finite and every successor map is monic, there exists N after which every
successor map is an isomorphism. -/
theorem finiteCoefficient_eventually_isIso_transition
    (F : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hFinite : ∀ k : ℕ, _root_.Finite (F.obj (op k)))
    (hMono : ∀ k : ℕ, Mono (F.map (homOfLE (Nat.le_succ k)).op)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → IsIso (F.map (homOfLE (Nat.le_succ k)).op) := by
  let U := F ⋙ forget AddCommGrpCat.{u}
  have hML : F.IsSequentialMittagLeffler := by
    apply U.isMittagLeffler_of_exists_finite_range
    rintro ⟨k⟩
    letI : _root_.Finite (U.obj (op k)) := hFinite k
    exact ⟨op k, 𝟙 _, Set.toFinite _⟩
  obtain ⟨N, h0N, hN⟩ :=
    (CategoryTheory.Functor.isSequentialMittagLeffler_iff_range_stabilizes F).mp hML 0
  refine ⟨N, fun k hk => ?_⟩
  have hRange : Set.range (U.map (homOfLE (Nat.zero_le (k + 1))).op) =
      Set.range (U.map (homOfLE (Nat.zero_le k)).op) :=
    (hN (k + 1) (by omega)).trans (hN k hk).symm
  have hSurj : Function.Surjective (F.map (homOfLE (Nat.le_succ k)).op) := by
    intro y
    have hy : U.map (homOfLE (Nat.zero_le k)).op y ∈
        Set.range (U.map (homOfLE (Nat.zero_le (k + 1))).op) := by
      rw [hRange]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    letI : Mono (F.map (homOfLE (Nat.zero_le k)).op) :=
      finiteCoefficient_mono_map F hMono 0 k (Nat.zero_le k)
    have hInjective : Function.Injective (F.map (homOfLE (Nat.zero_le k)).op) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    apply hInjective
    change F.map (homOfLE (Nat.zero_le k)).op
      (F.map (homOfLE (Nat.le_succ k)).op x) = F.map (homOfLE (Nat.zero_le k)).op y
    change F.map (homOfLE (Nat.zero_le (k + 1))).op x =
      F.map (homOfLE (Nat.zero_le k)).op y at hx
    have hh : (homOfLE (Nat.zero_le (k + 1))).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE (Nat.zero_le k)).op := Subsingleton.elim _ _
    rw [hh, F.map_comp, ConcreteCategory.comp_apply] at hx
    exact hx
  letI : Epi (F.map (homOfLE (Nat.le_succ k)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hSurj
  letI := hMono k
  exact isIso_of_mono_of_epi _

end AddCommGrpCat


end
