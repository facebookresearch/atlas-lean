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

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Length

/-!
# Length Euler identities for actual complexes with finite support

The actual kernel and quotient computing homology give the middle-module
length as homology length plus the two differential-range lengths. Finite
support then permits cancellation of the actual incoming and outgoing ranges.
Ring and module universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{v} R))

/-- Actual homology and differential ranges decompose the middle module's extended length. -/
theorem moduleCat_length_X₂_eq :
    Module.length R S.X₂ = Module.length R S.homology +
      Module.length R S.f.hom.range + Module.length R S.g.hom.range := by
  let P : Submodule R S.g.hom.ker := S.moduleCatToCycles.range
  have hk : S.moduleCatToCycles.ker = S.f.hom.ker :=
    LinearMap.ker_codRestrict _ _ _
  let e : S.moduleCatToCycles.range ≃ₗ[R] S.f.hom.range :=
    S.moduleCatToCycles.quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq _ _ hk).trans S.f.hom.quotKerEquivRange)
  have hp : Module.length R P = Module.length R S.f.hom.range := e.length_eq
  have hh : Module.length R S.homology = Module.length R (S.g.hom.ker ⧸ P) :=
    S.moduleCatHomologyIso.toLinearEquiv.length_eq
  have hker : Module.length R S.g.hom.ker =
      Module.length R P + Module.length R (S.g.hom.ker ⧸ P) :=
    Module.length_eq_add_of_exact P.subtype P.mkQ P.injective_subtype P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)
  have hm : Module.length R S.X₂ =
      Module.length R S.g.hom.ker + Module.length R S.g.hom.range :=
    Module.length_eq_add_of_exact S.g.hom.ker.subtype S.g.hom.rangeRestrict
      (Submodule.injective_subtype _) S.g.hom.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  rw [hm, hker, hp, ← hh,
    add_comm (Module.length R S.f.hom.range) (Module.length R S.homology)]

/-- Finite middle-module length earns finite length of the actual homology. -/
theorem moduleCat_homology_length_ne_top (hM : Module.length R S.X₂ ≠ ⊤) :
    Module.length R S.homology ≠ ⊤ := by
  apply ne_top_of_le_ne_top hM
  rw [S.moduleCat_length_X₂_eq]
  exact le_self_add.trans le_self_add

/-- The actual middle length is the sum of finite homology and the two finite ranges. -/
theorem moduleCat_length_X₂_toNat (hM : Module.length R S.X₂ ≠ ⊤) :
    (Module.length R S.X₂).toNat = (Module.length R S.homology).toNat +
      (Module.length R S.f.hom.range).toNat + (Module.length R S.g.hom.range).toNat := by
  have hH := S.moduleCat_homology_length_ne_top hM
  have hF : Module.length R S.f.hom.range ≠ ⊤ := ne_top_of_le_ne_top hM
    (Module.length_le_of_injective S.f.hom.range.subtype (Submodule.injective_subtype _))
  have hG : Module.length R S.g.hom.range ≠ ⊤ := ne_top_of_le_ne_top hM
    (Module.length_le_of_surjective S.g.hom.rangeRestrict S.g.hom.surjective_rangeRestrict)
  have hHF : Module.length R S.homology + Module.length R S.f.hom.range ≠ ⊤ := by
    apply ne_top_of_le_ne_top hM
    rw [S.moduleCat_length_X₂_eq]
    exact le_self_add
  rw [S.moduleCat_length_X₂_eq, ENat.toNat_add hHF hG, ENat.toNat_add hH hF]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c)

/-- Genuine finite support and opposite arrow weights give the actual homology Euler sum. -/
theorem lengthEuler_eq_homology_of_finite_support (s : Finset ι) (ε : ι → ℤ)
    (hzero : ∀ i, i ∉ s → IsZero (K.X i))
    (hlen : ∀ i ∈ s, Module.length R (K.X i) ≠ ⊤)
    (hε : ∀ i j, c.Rel i j → ε i + ε j = 0) :
    (∀ i ∈ s, Module.length R (K.homology i) ≠ ⊤) ∧
    (∀ i, i ∉ s → IsZero (K.homology i)) ∧
    (∑ i ∈ s, ε i * (Module.length R (K.X i)).toNat) =
      ∑ i ∈ s, ε i * (Module.length R (K.homology i)).toNat := by
  classical
  have hH (i : ι) (hi : i ∈ s) : Module.length R (K.homology i) ≠ ⊤ :=
    (K.sc i).moduleCat_homology_length_ne_top (hlen i hi)
  have hzH (i : ι) (hi : i ∉ s) : IsZero (K.homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (K.sc i) (hzero i hi)
  refine ⟨hH, hzH, ?_⟩
  let b (i j : ι) : ℤ := (Module.length R (K.d i j).hom.range).toNat
  have hb0 (i j : ι) (h : K.d i j = 0) : b i j = 0 := by
    have hz : Module.length R (⊥ : Submodule R (K.X j)) = 0 := Module.length_eq_zero
    dsimp only [b]
    rw [h, ModuleCat.hom_zero, LinearMap.range_zero, hz]
    rfl
  have hbshape (i j : ι) (h : ¬ c.Rel i j) : b i j = 0 := hb0 i j (K.shape i j h)
  have hbsource (i j : ι) (hi : i ∉ s) : b i j = 0 :=
    hb0 i j ((hzero i hi).eq_of_src _ _)
  have hbtarget (i j : ι) (hj : j ∉ s) : b i j = 0 :=
    hb0 i j ((hzero j hj).eq_of_tgt _ _)
  have hIn (i : ι) : (∑ j ∈ s, b j i) = b (c.prev i) i := by
    apply Finset.sum_eq_single (c.prev i)
    · intro j _ hj
      exact hbshape j i (fun h => hj (c.prev_eq' h).symm)
    · intro h
      exact hbsource (c.prev i) i h
  have hOut (i : ι) : (∑ j ∈ s, b i j) = b i (c.next i) := by
    apply Finset.sum_eq_single (c.next i)
    · intro j _ hj
      exact hbshape i j (fun h => hj (c.next_eq' h).symm)
    · intro h
      exact hbtarget i (c.next i) h
  have hPointLength (i : ι) (hi : i ∈ s) :
      ((Module.length R (K.X i)).toNat : ℤ) =
        (Module.length R (K.homology i)).toNat + b (c.prev i) i + b i (c.next i) := by
    have hNat : (Module.length R (K.X i)).toNat =
        (Module.length R (K.homology i)).toNat +
          (Module.length R (K.d (c.prev i) i).hom.range).toNat +
          (Module.length R (K.d i (c.next i)).hom.range).toNat :=
      (K.sc i).moduleCat_length_X₂_toNat.{u, v} (hlen i hi)
    dsimp only [b]
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℤ)) hNat
  have hPoint (i : ι) (hi : i ∈ s) :
      ε i * (Module.length R (K.X i)).toNat =
        ε i * (Module.length R (K.homology i)).toNat +
          (∑ j ∈ s, ε i * b j i) + ∑ j ∈ s, ε i * b i j := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hIn i, hOut i,
      hPointLength i hi, mul_add, mul_add]
  have hAll := Finset.sum_congr rfl hPoint
  simp only [Finset.sum_add_distrib] at hAll
  have hCancel : (∑ i ∈ s, ∑ j ∈ s, ε i * b j i) =
      -(∑ i ∈ s, ∑ j ∈ s, ε i * b i j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : c.Rel i j
    · have he : ε j = -ε i := by
        apply eq_neg_iff_add_eq_zero.mpr
        rw [add_comm]
        exact hε i j hij
      rw [he, neg_mul]
    · rw [hbshape i j hij]
      simp
  rw [hAll, hCancel]
  simp only [add_assoc, neg_add_cancel, add_zero]

end HomologicalComplex
