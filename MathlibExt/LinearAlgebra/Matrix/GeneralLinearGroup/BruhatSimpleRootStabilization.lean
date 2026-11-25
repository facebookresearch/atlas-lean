/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRoot
public import MathlibExt.GroupTheory.PermutationBilinearTitsStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialSLStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization
import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialMatrixStabilizationCompatibility

/-!
# Simple-root Weyl and torus stabilization via successor embedding

Field-independent successor API for simple-root Weyl and torus elements.
This packet is matrix/root-data infrastructure, not K-theory.

For `{n : ℕ}`, `{i j : Fin n}`, `hij : i ≠ j`, and `u : Rˣ` over an
arbitrary `CommRing R`:

* `Fin.castSucc` preserves `CovBy` / adjacency;
* `permSuccHom (swap i j) = swap (castSucc i) (castSucc j)`;
* `tupleSuccHom` sends `weylWeightUnit` / `torusWeightUnit` to the
  `castSucc`-embedded weight;
* the induced identities for `weylMonomialBaseUnit` /
  `torusMonomialBaseUnit` under `monomialSuccHom` and for
  `weylMonomialSLUnit` / `torusMonomialSLUnit` under `monomialSLSuccHom`;
* the matrix endpoints
  `stabilization (weylSLUnit i j hij u) = weylSLUnit (castSucc i) (castSucc j) _ u`
  and the torus analogue, via
  `weylSLUnit_eq_monomialSLHom` / `torusSLUnit_eq_monomialSLHom` and
  `monomialSLHom_monomialSLSuccHom`.

Tuple and permutation identities are proved pointwise with
`Fin.lastCases`, `tupleSuccHom_apply_castSucc/last`, and
`permSuccHom_apply_castSucc/last`; the parameter `u` is preserved
exactly.
-/

@[expose] public section

open PermutationBilinearTitsStabilization

namespace Fin

/-- `Fin.castSucc` preserves `CovBy` / adjacency.

For `Fin n` the order is `i < j ↔ i.val < j.val`; `i ⋖ j` means
`j.val = i.val + 1`. The map `castSucc : Fin n → Fin (n+1)` has
`(castSucc i).val = i.val` and is strictly monotone, so it preserves
covers. This is the small order lemma needed for simple-root
stabilization. -/
theorem castSucc_covBy {n : ℕ} {i j : Fin n} (hij : i ⋖ j) :
    (Fin.castSucc i : Fin (n + 1)) ⋖ Fin.castSucc j := by
  have h_lt : Fin.castSucc (n := n) i < Fin.castSucc (n := n) j := by
    rw [Fin.castSucc_lt_castSucc_iff]
    exact hij.lt
  constructor
  · exact h_lt
  · intro k hk1 hk2
    have hk1_val : i.val < k.val := by
      have h1 : (Fin.castSucc (n := n) i).val < k.val := by
        have hk1' : Fin.castSucc (n := n) i < k := hk1
        rw [Fin.lt_def] at hk1'
        exact hk1'
      simpa using h1
    have hk2_val : k.val < j.val := by
      have h2 : k.val < (Fin.castSucc (n := n) j).val := by
        have hk2' : k < Fin.castSucc (n := n) j := hk2
        rw [Fin.lt_def] at hk2'
        exact hk2'
      simpa using h2
    have hk_val_lt_n : k.val < n := by
      have hj_lt : j.val < n := j.isLt
      omega
    let k' : Fin n := ⟨k.val, hk_val_lt_n⟩
    have hi_lt_k' : i < k' := by
      rw [Fin.lt_def]
      exact hk1_val
    have hk'_lt_j : k' < j := by
      rw [Fin.lt_def]
      exact hk2_val
    exact hij.2 hi_lt_k' hk'_lt_j

end Fin

namespace Matrix.GeneralLinearGroup

section PermSucc

/-- Successor of a transposition is the transposition of successors. -/
theorem permSuccHom_swap {n : ℕ} {i j : Fin n} :
    permSuccHom (n := n) (Equiv.swap i j) =
      Equiv.swap (Fin.castSucc i) (Fin.castSucc j) := by
  apply Equiv.ext
  intro k
  refine Fin.lastCases (motive := fun k =>
      (permSuccHom (n := n) (Equiv.swap i j) : Fin (n + 1) → Fin (n + 1)) k =
        Equiv.swap (Fin.castSucc i) (Fin.castSucc j) k) ?_ (fun k' => ?_) k
  · simp only [permSuccHom_apply_last]
    have h1 : Fin.last (n := n) ≠ Fin.castSucc i :=
      Ne.symm (ne_of_lt (Fin.castSucc_lt_last i))
    have h2 : Fin.last (n := n) ≠ Fin.castSucc j :=
      Ne.symm (ne_of_lt (Fin.castSucc_lt_last j))
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · by_cases hk_i : k' = i
    · subst hk_i
      simp only [permSuccHom_apply_castSucc, Equiv.swap_apply_left]
    · by_cases hk_j : k' = j
      · subst hk_j
        simp only [permSuccHom_apply_castSucc, Equiv.swap_apply_right]
      · have h_swap_left : Equiv.swap i j k' = k' :=
          Equiv.swap_apply_of_ne_of_ne hk_i hk_j
        have h_ne_ci : Fin.castSucc k' ≠ Fin.castSucc i := by
          intro h
          exact hk_i (Fin.castSucc_injective n h)
        have h_ne_cj : Fin.castSucc k' ≠ Fin.castSucc j := by
          intro h
          exact hk_j (Fin.castSucc_injective n h)
        have h_swap_right :
            Equiv.swap (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc k') =
              Fin.castSucc k' :=
          Equiv.swap_apply_of_ne_of_ne h_ne_ci h_ne_cj
        simp only [permSuccHom_apply_castSucc, h_swap_left, h_swap_right]

end PermSucc

section WeightSucc

variable {n : ℕ} {i j : Fin n} {R : Type*} [CommRing R]

/-- `tupleSuccHom` sends the Weyl weight at `(i,j)` to the weight at
` (castSucc i, castSucc j)`. Proved pointwise with `Fin.lastCases`. -/
theorem tupleSuccHom_weylWeightUnit (hij : i ≠ j) (u : Rˣ) :
    tupleSuccHom (n := n) (A := Rˣ) (weylWeightUnit (R := R) i j hij u) =
      weylWeightUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  apply funext
  intro k
  refine Fin.lastCases (motive := fun k =>
      tupleSuccHom (n := n) (A := Rˣ) (weylWeightUnit (R := R) i j hij u) k =
        weylWeightUnit (R := R) (Fin.castSucc i) (Fin.castSucc j) _ u k) ?_
      (fun k' => ?_) k
  · simp only [tupleSuccHom_apply_last, weylWeightUnit]
    have h1 : Fin.last (n := n) ≠ Fin.castSucc i :=
      Ne.symm (ne_of_lt (Fin.castSucc_lt_last i))
    have h2 : Fin.last (n := n) ≠ Fin.castSucc j :=
      Ne.symm (ne_of_lt (Fin.castSucc_lt_last j))
    simp [h1, h2]
  · by_cases hk_i : k' = i
    · simp [tupleSuccHom_apply_castSucc, weylWeightUnit]
    · by_cases hk_j : k' = j
      · have h_ne_ci : Fin.castSucc k' ≠ Fin.castSucc i := by
          intro h
          exact hk_i (Fin.castSucc_injective n h)
        simp [tupleSuccHom_apply_castSucc, weylWeightUnit]
      · have h_ne_ci : Fin.castSucc k' ≠ Fin.castSucc i := by
          intro h
          exact hk_i (Fin.castSucc_injective n h)
        have h_ne_cj : Fin.castSucc k' ≠ Fin.castSucc j := by
          intro h
          exact hk_j (Fin.castSucc_injective n h)
        simp [tupleSuccHom_apply_castSucc, weylWeightUnit]

/-- `tupleSuccHom` sends the torus weight at `(i,j)` to the weight at
` (castSucc i, castSucc j)`. -/
theorem tupleSuccHom_torusWeightUnit (hij : i ≠ j) (u : Rˣ) :
    tupleSuccHom (n := n) (A := Rˣ) (torusWeightUnit (R := R) i j hij u) =
      torusWeightUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  apply funext
  intro k
  refine Fin.lastCases (motive := fun k =>
      tupleSuccHom (n := n) (A := Rˣ) (torusWeightUnit (R := R) i j hij u) k =
        torusWeightUnit (R := R) (Fin.castSucc i) (Fin.castSucc j) _ u k) ?_
      (fun k' => ?_) k
  · simp only [tupleSuccHom_apply_last, torusWeightUnit]
    have h1 : Fin.last (n := n) ≠ Fin.castSucc i :=
      Ne.symm (ne_of_lt (Fin.castSucc_lt_last i))
    have h2 : Fin.last (n := n) ≠ Fin.castSucc j :=
      Ne.symm (ne_of_lt (Fin.castSucc_lt_last j))
    simp [h1, h2]
  · by_cases hk_i : k' = i
    · simp [tupleSuccHom_apply_castSucc, torusWeightUnit]
    · by_cases hk_j : k' = j
      · have h_ne_ci : Fin.castSucc k' ≠ Fin.castSucc i := by
          intro h
          exact hk_i (Fin.castSucc_injective n h)
        simp [tupleSuccHom_apply_castSucc, torusWeightUnit]
      · have h_ne_ci : Fin.castSucc k' ≠ Fin.castSucc i := by
          intro h
          exact hk_i (Fin.castSucc_injective n h)
        have h_ne_cj : Fin.castSucc k' ≠ Fin.castSucc j := by
          intro h
          exact hk_j (Fin.castSucc_injective n h)
        simp [tupleSuccHom_apply_castSucc, torusWeightUnit]

end WeightSucc

section MonomialBaseSucc

variable {n : ℕ} {i j : Fin n} {R : Type*} [CommRing R]

theorem monomialSuccHom_weylMonomialBaseUnit (hij : i ≠ j) (u : Rˣ) :
    monomialSuccHom (n := n) (A := Rˣ) (weylMonomialBaseUnit (R := R) i j hij u) =
      weylMonomialBaseUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  apply SemidirectProduct.ext
  · simp only [monomialSuccHom_left]
    exact tupleSuccHom_weylWeightUnit hij u
  · simp only [monomialSuccHom_right, weylMonomialBaseUnit, weylPerm]
    exact permSuccHom_swap

theorem monomialSuccHom_torusMonomialBaseUnit (hij : i ≠ j) (u : Rˣ) :
    monomialSuccHom (n := n) (A := Rˣ) (torusMonomialBaseUnit (R := R) i j hij u) =
      torusMonomialBaseUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  apply SemidirectProduct.ext
  · simp only [monomialSuccHom_left]
    exact tupleSuccHom_torusWeightUnit hij u
  · simp only [monomialSuccHom_right, torusMonomialBaseUnit, torusPerm, permSuccHom_one]

end MonomialBaseSucc

section MonomialSLSucc

variable {n : ℕ} {i j : Fin n} {R : Type*} [CommRing R]

theorem monomialSLSuccHom_weylMonomialSLUnit (hij : i ≠ j) (u : Rˣ) :
    monomialSLSuccHom (R := R) (n := n) (weylMonomialSLUnit (R := R) i j hij u) =
      weylMonomialSLUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  apply Subtype.ext
  simp only [coe_monomialSLSuccHom]
  exact monomialSuccHom_weylMonomialBaseUnit hij u

theorem monomialSLSuccHom_torusMonomialSLUnit (hij : i ≠ j) (u : Rˣ) :
    monomialSLSuccHom (R := R) (n := n) (torusMonomialSLUnit (R := R) i j hij u) =
      torusMonomialSLUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  apply Subtype.ext
  simp only [coe_monomialSLSuccHom]
  exact monomialSuccHom_torusMonomialBaseUnit hij u

end MonomialSLSucc

section Stabilization

variable {n : ℕ} {i j : Fin n} {R : Type*} [CommRing R]

/-- Matrix endpoint: `SL` stabilization sends the simple-root Weyl element
at `(i,j)` to the Weyl element at `(castSucc i, castSucc j)`, preserving
`u` exactly. Uses `weylSLUnit_eq_monomialSLHom` and
`monomialSLHom_monomialSLSuccHom`; no matrix entry computation. -/
theorem stabilization_weylSLUnit (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup.stabilization R (weylSLUnit (R := R) i j hij u) =
      weylSLUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  have hij' : Fin.castSucc (n := n) i ≠ Fin.castSucc (n := n) j :=
    fun h => hij (Fin.castSucc_injective n h)
  calc Matrix.SpecialLinearGroup.stabilization R (weylSLUnit i j hij u)
      = Matrix.SpecialLinearGroup.stabilization R
          (monomialSLHom R (Fin n) (weylMonomialSLUnit i j hij u)) := by
        rw [← weylSLUnit_eq_monomialSLHom]
    _ = monomialSLHom R (Fin (n + 1))
          (monomialSLSuccHom (R := R) (weylMonomialSLUnit i j hij u)) := by
        rw [← monomialSLHom_monomialSLSuccHom]
    _ = monomialSLHom R (Fin (n + 1))
          (weylMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j) hij' u) := by
        rw [monomialSLSuccHom_weylMonomialSLUnit hij u]
    _ = weylSLUnit (Fin.castSucc i) (Fin.castSucc j) hij' u := by
        rw [weylSLUnit_eq_monomialSLHom]

/-- Matrix endpoint: `SL` stabilization sends the simple-root torus element
at `(i,j)` to the torus element at `(castSucc i, castSucc j)`. -/
theorem stabilization_torusSLUnit (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup.stabilization R (torusSLUnit (R := R) i j hij u) =
      torusSLUnit (R := R) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  have hij' : Fin.castSucc (n := n) i ≠ Fin.castSucc (n := n) j :=
    fun h => hij (Fin.castSucc_injective n h)
  calc Matrix.SpecialLinearGroup.stabilization R (torusSLUnit i j hij u)
      = Matrix.SpecialLinearGroup.stabilization R
          (monomialSLHom R (Fin n) (torusMonomialSLUnit i j hij u)) := by
        rw [← torusSLUnit_eq_monomialSLHom]
    _ = monomialSLHom R (Fin (n + 1))
          (monomialSLSuccHom (R := R) (torusMonomialSLUnit i j hij u)) := by
        rw [← monomialSLHom_monomialSLSuccHom]
    _ = monomialSLHom R (Fin (n + 1))
          (torusMonomialSLUnit (Fin.castSucc i) (Fin.castSucc j) hij' u) := by
        rw [monomialSLSuccHom_torusMonomialSLUnit hij u]
    _ = torusSLUnit (Fin.castSucc i) (Fin.castSucc j) hij' u := by
        rw [torusSLUnit_eq_monomialSLHom]

end Stabilization

end Matrix.GeneralLinearGroup
