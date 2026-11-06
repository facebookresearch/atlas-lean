/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOrthogonality
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Field.ZMod

/-! Self-duality and small coordinate projections of the actual binary Golay code.
The projection argument uses the genuine minimum weight eight, rather than a
transitivity or group-order assumption. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The coordinate dot product used for the binary code. -/
def golayCoordinateForm : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)

theorem golayCoordinateForm_nondegenerate : golayCoordinateForm.Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i (1 : ZMod 2))
    change dotProduct x (Pi.single i (1 : ZMod 2)) = 0 at h
    simpa only [dotProduct_single, mul_one, Pi.zero_apply] using h
  · intro x hx
    funext i
    have h := hx (Pi.single i (1 : ZMod 2))
    change dotProduct (Pi.single i (1 : ZMod 2)) x = 0 at h
    simpa only [single_dotProduct, one_mul, Pi.zero_apply] using h

theorem golayCode_finrank : Module.finrank (ZMod 2) golayCode = 12 := by
  change Module.finrank (ZMod 2) golayEncoder.range = 12
  rw [← (LinearEquiv.ofInjective golayEncoder golayEncoder_injective).finrank_eq]
  exact Module.finrank_fin_fun (ZMod 2)

/-- The published encoder range equals its dot-product orthogonal complement. -/
theorem golayCode_self_dual : golayCoordinateForm.orthogonal golayCode = golayCode := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (K := ZMod 2) (S₁ := golayCode)
    (S₂ := golayCoordinateForm.orthogonal golayCode)
  · intro c hc d hd
    exact golayCode_self_orthogonal d c hd hc
  · rw [LinearMap.BilinForm.finrank_orthogonal golayCoordinateForm_nondegenerate,
      golayCode_finrank, Module.finrank_fin_fun]

/-- Restriction of a codeword to a list of coordinates. -/
def golayCoordinateProjection {k : ℕ} (f : Fin k → Fin 24) :
    golayCode →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun c j := c.val (f j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem functional_coordinate_expansion {k : ℕ}
    (φ : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (y : Fin k → ZMod 2) :
    φ y = ∑ j, φ (Pi.single j 1) * y j := by
  conv_lhs => rw [← LinearMap.sum_single_apply (fun _ : Fin k => ZMod 2) y, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : Pi.single j (y j) = y j • Pi.single j (1 : ZMod 2) := by
    simp [← Pi.single_smul]
  rw [h, map_smul]
  change y j * φ (Pi.single j 1) = φ (Pi.single j 1) * y j
  exact mul_comm _ _

/-- No nonzero actual Golay word is supported on fewer than eight coordinates. -/
theorem golayCode_eq_zero_of_small_support {k : ℕ} (hk : k < 8)
    (f : Fin k → Fin 24) (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hs : ∀ i, i ∉ Finset.univ.image f → c i = 0) : c = 0 := by
  classical
  by_contra hn
  have hlo := golayCode_weight_ge_eight c hc hn
  have hbound : (∑ i, (c i).val) ≤ (Finset.univ.image f).card := by
    calc
      (∑ i, (c i).val) ≤ ∑ i : Fin 24,
          (if i ∈ Finset.univ.image f then 1 else 0 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ Finset.univ.image f
        · simp only [hi, ite_true]
          have hv := ZMod.val_lt (c i)
          omega
        · simp [hi, hs i hi]
      _ = (Finset.univ.image f).card := by simp
  have hcard : (Finset.univ.image f).card ≤ k := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := f)
  omega

/-- Every prescription on at most seven distinct coordinates extends to a Golay word. -/
theorem golayCoordinateProjection_surjective {k : ℕ} (hk : k < 8)
    (f : Fin k → Fin 24) (hf : Function.Injective f) :
    Function.Surjective (golayCoordinateProjection f) := by
  classical
  by_contra hn
  have hproper : (golayCoordinateProjection f).range < ⊤ :=
    lt_top_iff_ne_top.mpr (fun h => hn (LinearMap.range_eq_top.mp h))
  obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top (K := ZMod 2)
    (golayCoordinateProjection f).range hproper
  let w : Fin 24 → ZMod 2 := ∑ j, Pi.single (f j) (φ (Pi.single j 1))
  have hwcode : w ∈ golayCode := by
    rw [← golayCode_self_dual]
    intro c hc
    change (∑ i, c i * w i) = 0
    have hzero : φ (fun j => c (f j)) = 0 :=
      hker ⟨⟨c, hc⟩, rfl⟩
    rw [functional_coordinate_expansion] at hzero
    simp only [w, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have heq : (∑ j : Fin k, ∑ i : Fin 24,
        c i * (Pi.single (f j) (φ (Pi.single j 1)) : Fin 24 → ZMod 2) i) =
        ∑ j, φ (Pi.single j 1) * c (f j) := by
      apply Finset.sum_congr rfl
      intro j _
      change dotProduct c (Pi.single (f j) (φ (Pi.single j 1))) = _
      rw [dotProduct_single, mul_comm]
    rw [heq]
    exact hzero
  have hwzero : w = 0 := by
    apply golayCode_eq_zero_of_small_support hk f w hwcode
    intro i hi
    simp only [w, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply Pi.single_eq_of_ne
    intro h
    exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
  apply hφ
  apply LinearMap.ext
  intro y
  change φ y = 0
  rw [functional_coordinate_expansion]
  change (∑ j, φ (Pi.single j 1) * y j) = 0
  apply Finset.sum_eq_zero
  intro j _
  have hj := congrFun hwzero (f j)
  have hval : w (f j) = φ (Pi.single j 1) := by
    simp only [w, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      exact Pi.single_eq_of_ne (fun h => hbj (hf h.symm)) _
    · simp
  rw [hval] at hj
  simp [hj]

/-- In particular, any four independently specified bits extend to the actual code. -/
theorem golayCode_four_coordinate_surjective (f : Fin 4 → Fin 24)
    (hf : Function.Injective f) :
    Function.Surjective (fun c : golayCode => fun j => c.val (f j)) :=
  golayCoordinateProjection_surjective (by decide) f hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
