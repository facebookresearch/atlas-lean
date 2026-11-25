/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat.lean`
and
`P2M/Sol/S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat.lean`,
together with the source proofs of its dependencies
`NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat`,
`NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat`,
`NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat`
and `Int.exists_modEq_and_modEq_and_isCoprime`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.ProductionPinsCompact
public import MathlibExt.NumberTheory.NumberField.AdelicGL2LocalFiniteness

@[expose] public section

/-!
# Strong approximation for `GL₂` over `ℚ`

Every adelic matrix `g` in `GL₂(𝔸_ℚ)` factors as `g = γ h u` with `γ` rational, `h` with
identity finite part and positive-determinant real part, and `u` in the compact level of
`AutomorphicForm.productionPinsCompact ℚ D` at a nonzero ideal `N`, for every fundamental set `D`.

The proof first shows that `GL₂` over the finite adeles of a principal ideal domain `R` with
fraction field `K` is `GL₂(K) · GL₂(Ô)`, by a Gauss decomposition into unipotent and diagonal
factors whose rational parts are absorbed one at a time. Over `ℚ`, a Bezout matrix in `SL₂(ℤ)`
then moves an integral matrix into the level `finiteLevelOne (𝓞 ℚ) ℚ N`, and the matrix
`diag(-1, 1)` fixes the sign of the real determinant.

## Main statements

* `NumberField.AdelicLevel.archComponent`: the component at an infinite place of a `GL₂` matrix
  over the infinite adeles.
* `NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat`: every matrix
  over the finite adeles of `ℚ` is moved into `finiteLevelOne (𝓞 ℚ) ℚ N` by a rational matrix.
* `NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat`: the same for adelic
  matrices, with positive real determinant.
* `AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat`: the factorization
  `g = γ h u` above.
-/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Matrix

namespace NumberField.AdelicLevel

section Arch

variable (K : Type*) [Field K]

/-- The component at the infinite place `w` of a `GL₂` matrix over the infinite adeles. -/
def archComponent (w : InfinitePlace K) :
    GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  GeneralLinearGroup.map (archEval K w)

theorem archComponent_apply (w : InfinitePlace K) (g : GL (Fin 2) (InfiniteAdeleRing K))
    (i j : Fin 2) :
    (archComponent K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w :=
  rfl

end Arch

section ElementaryMatrices

variable {S : Type*} [CommRing S]

private def upperUnip (x : S) : GL (Fin 2) S where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperUnip_coe (x : S) :
    (upperUnip x : Matrix (Fin 2) (Fin 2) S) = !![1, x; 0, 1] := rfl

private def lowerUnip (x : S) : GL (Fin 2) S where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem lowerUnip_coe (x : S) :
    (lowerUnip x : Matrix (Fin 2) (Fin 2) S) = !![1, 0; x, 1] := rfl

private theorem upperUnip_inv (x : S) : (upperUnip x)⁻¹ = upperUnip (-x) :=
  Units.ext (by simp [upperUnip])

private theorem lowerUnip_inv (x : S) : (lowerUnip x)⁻¹ = lowerUnip (-x) :=
  Units.ext (by simp [lowerUnip])

private theorem upperUnip_add (x y : S) : upperUnip (x + y) = upperUnip x * upperUnip y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnip, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem lowerUnip_add (x y : S) : lowerUnip (x + y) = lowerUnip x * lowerUnip y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnip, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem map_upperUnip {T : Type*} [CommRing T] (f : S →+* T) (x : S) :
    GeneralLinearGroup.map f (upperUnip x) = upperUnip (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnip]

private theorem map_lowerUnip {T : Type*} [CommRing T] (f : S →+* T) (x : S) :
    GeneralLinearGroup.map f (lowerUnip x) = lowerUnip (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnip]

private def diagTorus (u : Sˣ) : GL (Fin 2) S where
  val := !![1, 0; 0, (u : S)]
  inv := !![1, 0; 0, ((u⁻¹ : Sˣ) : S)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagTorus_coe (u : Sˣ) :
    (diagTorus u : Matrix (Fin 2) (Fin 2) S) = !![1, 0; 0, (u : S)] := rfl

private theorem diagTorus_mul (u w : Sˣ) : diagTorus (u * w) = diagTorus u * diagTorus w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTorus, Matrix.mul_apply, Fin.sum_univ_two]

private theorem map_diagTorus {T : Type*} [CommRing T] (f : S →+* T) (u : Sˣ) :
    GeneralLinearGroup.map f (diagTorus u) = diagTorus (Units.map (f : S →* T) u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagTorus]

private theorem conj_upperUnip_entry {u w : Matrix (Fin 2) (Fin 2) S} (h : u * w = 1) (b : S)
    (i j : Fin 2) :
    (u * !![1, b; 0, 1] * w) i j = (1 : Matrix (Fin 2) (Fin 2) S) i j + b * (u i 0 * w 1 j) := by
  have hcalc : (u * !![1, b; 0, 1] * w) i j = (u * w) i j + b * (u i 0 * w 1 j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hcalc, h]

private theorem conj_lowerUnip_entry {u w : Matrix (Fin 2) (Fin 2) S} (h : u * w = 1) (b : S)
    (i j : Fin 2) :
    (u * !![1, 0; b, 1] * w) i j = (1 : Matrix (Fin 2) (Fin 2) S) i j + b * (u i 1 * w 0 j) := by
  have hcalc : (u * !![1, 0; b, 1] * w) i j = (u * w) i j + b * (u i 1 * w 0 j) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hcalc, h]

private theorem gauss_factorization (M : Matrix (Fin 2) (Fin 2) S) (c ci δ δi : S)
    (hc : M 1 0 = c) (hci : c * ci = 1) (hδ : M.det = δ) (hδi : δ * δi = 1) :
    !![1, (M 0 0 - 1) * ci; 0, 1] * !![1, 0; c, 1] * !![1, (M 1 1 * δi - 1) * ci; 0, 1] *
      !![1, 0; 0, δ] = M := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = δ := by
    rw [← Matrix.det_fin_two]; exact hδ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (M 0 0 - 1) * hci
  · linear_combination
      (M 0 1 + (M 0 0 - 1) * (M 1 1 * δi - 1) * ci * δ) * hci
        + (ci * M 0 1) * hc + ci * hdet + (ci * M 0 0 * M 1 1) * hδi
  · linear_combination - hc
  · linear_combination ((M 1 1 * δi - 1) * δ) * hci + M 1 1 * hδi

end ElementaryMatrices

section General

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The matrices over the finite adeles that are integral together with their inverses. -/
private def intGL2 : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈
      AdelicBox.integralFiniteAdeles R K) ∧
    ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) _) i j ∈
      AdelicBox.integralFiniteAdeles R K}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈
        AdelicBox.integralFiniteAdeles R K := fun i j => by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem_integralFiniteAdeles
      · exact zero_mem_integralFiniteAdeles
    exact ⟨by rw [Units.val_one]; exact h, by rw [inv_one, Units.val_one]; exact h⟩
  mul_mem' {a b} ha hb := by
    have hmul : ∀ {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)},
        (∀ i j, m i j ∈ AdelicBox.integralFiniteAdeles R K) →
        (∀ i j, m' i j ∈ AdelicBox.integralFiniteAdeles R K) →
        ∀ i j, (m * m') i j ∈ AdelicBox.integralFiniteAdeles R K := fun hm hm' i j => by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hm i 0) (hm' 0 j))
        (mul_mem_integralFiniteAdeles (hm i 1) (hm' 1 j))
    exact ⟨by rw [Units.val_mul]; exact hmul ha.1 hb.1,
      by rw [_root_.mul_inv_rev, Units.val_mul]; exact hmul hb.2 ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {R K} in
private theorem mem_intGL2_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ intGL2 R K ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j ∈
        AdelicBox.integralFiniteAdeles R K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) _) i j ∈
        AdelicBox.integralFiniteAdeles R K :=
  Iff.rfl

private theorem algebraMap_finiteAdeleRing_apply (x : K) (v : HeightOneSpectrum R) :
    (algebraMap K (FiniteAdeleRing R K) x) v = algebraMap K (v.adicCompletion K) x := rfl

private theorem valued_algebraMap_finiteAdeleRing_apply (k : K) (v : HeightOneSpectrum R) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k := by
  rw [show (algebraMap K (FiniteAdeleRing R K) k) v = ((k : K) : v.adicCompletion K) from rfl]
  exact valuedAdicCompletion_eq_valuation' v k

private theorem one_matrix_apply_mem (i j : Fin 2) (v : HeightOneSpectrum R) :
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v ∈ v.adicCompletionIntegers K := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    exact one_mem _
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem lowerUnip_mem {a : FiniteAdeleRing R K}
    (ha : ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K) :
    lowerUnip a ∈ intGL2 R K := by
  rw [mem_intGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact ha v
    · exact one_mem _
  · intro i j v
    rw [lowerUnip_inv]
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact neg_mem (ha v)
    · exact one_mem _

private theorem diagTorus_mem {u : (FiniteAdeleRing R K)ˣ}
    (hu : ∀ v : HeightOneSpectrum R, (u : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K)
    (hu' : ∀ v : HeightOneSpectrum R,
      ((u⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) :
    diagTorus u ∈ intGL2 R K := by
  rw [mem_intGL2_iff]
  constructor
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact zero_mem _
    · exact hu v
  · intro i j v
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact zero_mem _
    · exact hu' v

private theorem exists_sub_algebraMap_eq_mul_integral (a : FiniteAdeleRing R K) (d : K)
    (hd : d ≠ 0) :
    ∃ q : K, ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      a v - algebraMap K (v.adicCompletion K) q = algebraMap K (v.adicCompletion K) d * c := by
  have hdu : IsUnit (algebraMap K (FiniteAdeleRing R K) d) :=
    (Ne.isUnit hd).map (algebraMap K (FiniteAdeleRing R K))
  set a' : FiniteAdeleRing R K := ↑hdu.unit⁻¹ * a with ha'
  obtain ⟨k, hk⟩ := AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles R K a'
  refine ⟨d * (-k), fun v ↦ ⟨a' v - algebraMap K (v.adicCompletion K) (-k), ?_, ?_⟩⟩
  · have hkv : algebraMap K (v.adicCompletion K) k + a' v ∈ v.adicCompletionIntegers K := hk v
    rw [map_neg, sub_neg_eq_add, add_comm]
    exact hkv
  have hda' : algebraMap K (FiniteAdeleRing R K) d * a' = a := by
    rw [ha', ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  calc a v - algebraMap K (v.adicCompletion K) (d * -k)
      = (algebraMap K (FiniteAdeleRing R K) d * a') v
          - algebraMap K (v.adicCompletion K) d * algebraMap K (v.adicCompletion K) (-k) := by
        rw [hda', map_mul]
    _ = algebraMap K (v.adicCompletion K) d
          * (a' v - algebraMap K (v.adicCompletion K) (-k)) := by
        rw [show (algebraMap K (FiniteAdeleRing R K) d * a') v =
          algebraMap K (v.adicCompletion K) d * a' v from rfl]
        ring

private theorem exists_common_denominator (γ : GL (Fin 2) K) :
    ∃ d : R, d ≠ 0 ∧ ∀ i j k l : Fin 2,
      ∃ n : R, algebraMap R K d
          * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            * ((γ : Matrix (Fin 2) (Fin 2) K) k l))
        = algebraMap R K n := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset (Fin 2 × Fin 2 × Bool))
    (fun p ↦ if p.2.2 then ((γ : Matrix (Fin 2) (Fin 2) K) p.1 p.2.1)
      else (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) p.1 p.2.1))
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  refine ⟨b * b, mul_ne_zero hb0 hb0, fun i j k l ↦ ?_⟩
  obtain ⟨n₁, hn₁⟩ := hb (i, j, false) (Finset.mem_univ _)
  obtain ⟨n₂, hn₂⟩ := hb (k, l, true) (Finset.mem_univ _)
  refine ⟨n₁ * n₂, ?_⟩
  have h₁ : algebraMap R K n₁
      = algebraMap R K b * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
    simpa [Algebra.smul_def] using hn₁
  have h₂ : algebraMap R K n₂ = algebraMap R K b * ((γ : Matrix (Fin 2) (Fin 2) K) k l) := by
    simpa [Algebra.smul_def] using hn₂
  rw [map_mul, map_mul, h₁, h₂]
  ring

/-- A rational matrix as a matrix over the finite adeles. -/
private abbrev ratGL (γ : GL (Fin 2) K) : GL (Fin 2) (FiniteAdeleRing R K) :=
  GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ

private theorem ratGL_inv_mul_val (γ : GL (Fin 2) K) :
    (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem ratGL_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = algebraMap K (FiniteAdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  rfl

private theorem ratGL_inv_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = algebraMap K (FiniteAdeleRing R K)
          (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := by
  rw [show (ratGL R K γ)⁻¹ = ratGL R K γ⁻¹ from
    (map_inv (GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K))) γ).symm]
  rfl

private theorem conj_entry_mem (γ : GL (Fin 2) K) (d : R)
    (hd : ∀ i j k l : Fin 2, ∃ n : R, algebraMap R K d
          * (((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            * ((γ : Matrix (Fin 2) (Fin 2) K) k l)) = algebraMap R K n)
    (b : FiniteAdeleRing R K)
    (hb : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
        b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c)
    (x : FiniteAdeleRing R K) (hx : x = b ∨ x = -b) (i p q j : Fin 2)
    (v : HeightOneSpectrum R) :
    ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      + x * ((((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i p
             * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
                Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) q j)) v
      ∈ v.adicCompletionIntegers K := by
  rw [ratGL_inv_val_apply, ratGL_val_apply, ← map_mul]
  change (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v
      + x v * algebraMap K (v.adicCompletion K)
        ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
          * ((γ : Matrix (Fin 2) (Fin 2) K) q j))) ∈ v.adicCompletionIntegers K
  refine add_mem (one_matrix_apply_mem R K i j v) ?_
  obtain ⟨c, hcmem, hc⟩ := hb v
  obtain ⟨n, hn⟩ := hd i p q j
  set e := ((((γ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i p
      * ((γ : Matrix (Fin 2) (Fin 2) K) q j)))
  have hkey : algebraMap K (v.adicCompletion K) (algebraMap R K d)
      * algebraMap K (v.adicCompletion K) e
      = algebraMap K (v.adicCompletion K) (algebraMap R K n) := by
    rw [← map_mul, hn]
  have hint : c * algebraMap K (v.adicCompletion K) (algebraMap R K n)
      ∈ v.adicCompletionIntegers K :=
    mul_mem hcmem (AdelicBox.algebraMap_mem_adicCompletionIntegers R K v n)
  rcases hx with hx | hx
  · rw [hx, hc, show algebraMap K (v.adicCompletion K) (algebraMap R K d) * c
        * algebraMap K (v.adicCompletion K) e
        = c * (algebraMap K (v.adicCompletion K) (algebraMap R K d)
          * algebraMap K (v.adicCompletion K) e) by ring, hkey]
    exact hint
  · rw [hx, show (-b) v = -(b v) from rfl, hc,
      show -(algebraMap K (v.adicCompletion K) (algebraMap R K d) * c)
        * algebraMap K (v.adicCompletion K) e
        = -(c * (algebraMap K (v.adicCompletion K) (algebraMap R K d)
          * algebraMap K (v.adicCompletion K) e)) by ring, hkey]
    exact neg_mem hint

private theorem exists_conj_upperUnip_mem (γ : GL (Fin 2) K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K γ)⁻¹ * upperUnip (a - algebraMap K (FiniteAdeleRing R K) q) *
      ratGL R K γ ∈ intGL2 R K := by
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator R K γ
  have hdK : algebraMap R K d ≠ 0 := fun hcontra ↦
    hd0 (IsFractionRing.injective R K (by rw [hcontra, map_zero]))
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_eq_mul_integral R K a (algebraMap R K d) hdK
  refine ⟨q, ?_⟩
  set b : FiniteAdeleRing R K := a - algebraMap K (FiniteAdeleRing R K) q with hb
  have hbv : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c := hq
  have hAB := ratGL_inv_mul_val R K γ
  have hval : ((((ratGL R K γ)⁻¹ * upperUnip b * ratGL R K γ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, b; 0, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [Units.val_mul, Units.val_mul, upperUnip_coe]
  have hinvval : ((((ratGL R K γ)⁻¹ * upperUnip b * ratGL R K γ)⁻¹ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, -b; 0, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, upperUnip_inv, ← mul_assoc,
      Units.val_mul, Units.val_mul, upperUnip_coe]
  rw [mem_intGL2_iff]
  constructor
  · intro i j v
    rw [hval, conj_upperUnip_entry hAB b i j]
    exact conj_entry_mem R K γ d hd b hbv b (Or.inl rfl) i 0 1 j v
  · intro i j v
    rw [hinvval, conj_upperUnip_entry hAB (-b) i j]
    exact conj_entry_mem R K γ d hd b hbv (-b) (Or.inr rfl) i 0 1 j v

private theorem exists_conj_lowerUnip_mem (γ : GL (Fin 2) K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K γ)⁻¹ * lowerUnip (a - algebraMap K (FiniteAdeleRing R K) q) *
      ratGL R K γ ∈ intGL2 R K := by
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator R K γ
  have hdK : algebraMap R K d ≠ 0 := fun hcontra ↦
    hd0 (IsFractionRing.injective R K (by rw [hcontra, map_zero]))
  obtain ⟨q, hq⟩ := exists_sub_algebraMap_eq_mul_integral R K a (algebraMap R K d) hdK
  refine ⟨q, ?_⟩
  set b : FiniteAdeleRing R K := a - algebraMap K (FiniteAdeleRing R K) q with hb
  have hbv : ∀ v : HeightOneSpectrum R, ∃ c ∈ v.adicCompletionIntegers K,
      b v = algebraMap K (v.adicCompletion K) (algebraMap R K d) * c := hq
  have hAB := ratGL_inv_mul_val R K γ
  have hval : ((((ratGL R K γ)⁻¹ * lowerUnip b * ratGL R K γ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, 0; b, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [Units.val_mul, Units.val_mul, lowerUnip_coe]
  have hinvval : ((((ratGL R K γ)⁻¹ * lowerUnip b * ratGL R K γ)⁻¹ :
      GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
      = (((ratGL R K γ)⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) * !![1, 0; -b, 1]
          * ((ratGL R K γ : GL (Fin 2) (FiniteAdeleRing R K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, lowerUnip_inv, ← mul_assoc,
      Units.val_mul, Units.val_mul, lowerUnip_coe]
  rw [mem_intGL2_iff]
  constructor
  · intro i j v
    rw [hval, conj_lowerUnip_entry hAB b i j]
    exact conj_entry_mem R K γ d hd b hbv b (Or.inl rfl) i 1 0 j v
  · intro i j v
    rw [hinvval, conj_lowerUnip_entry hAB (-b) i j]
    exact conj_entry_mem R K γ d hd b hbv (-b) (Or.inr rfl) i 1 0 j v

private theorem absorb_upperUnip_left {X : GL (Fin 2) (FiniteAdeleRing R K)} {γ : GL (Fin 2) K}
    (hX : (ratGL R K γ)⁻¹ * X ∈ intGL2 R K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K (upperUnip q * γ))⁻¹ * (upperUnip a * X) ∈ intGL2 R K := by
  obtain ⟨q, hq⟩ := exists_conj_upperUnip_mem R K γ a
  refine ⟨q, ?_⟩
  have hsplit : upperUnip (a - algebraMap K (FiniteAdeleRing R K) q)
      = (upperUnip (algebraMap K (FiniteAdeleRing R K) q))⁻¹ * upperUnip a := by
    rw [eq_inv_mul_iff_mul_eq, ← upperUnip_add]
    congr 1
    ring
  have key : (ratGL R K (upperUnip q * γ))⁻¹ * (upperUnip a * X)
      = ((ratGL R K γ)⁻¹ * upperUnip (a - algebraMap K (FiniteAdeleRing R K) q)
          * ratGL R K γ) * ((ratGL R K γ)⁻¹ * X) := by
    rw [ratGL, map_mul, map_upperUnip, hsplit]
    group
  rw [key]
  exact mul_mem hq hX

private theorem absorb_lowerUnip_left {X : GL (Fin 2) (FiniteAdeleRing R K)} {γ : GL (Fin 2) K}
    (hX : (ratGL R K γ)⁻¹ * X ∈ intGL2 R K) (a : FiniteAdeleRing R K) :
    ∃ q : K, (ratGL R K (lowerUnip q * γ))⁻¹ * (lowerUnip a * X) ∈ intGL2 R K := by
  obtain ⟨q, hq⟩ := exists_conj_lowerUnip_mem R K γ a
  refine ⟨q, ?_⟩
  have hsplit : lowerUnip (a - algebraMap K (FiniteAdeleRing R K) q)
      = (lowerUnip (algebraMap K (FiniteAdeleRing R K) q))⁻¹ * lowerUnip a := by
    rw [eq_inv_mul_iff_mul_eq, ← lowerUnip_add]
    congr 1
    ring
  have key : (ratGL R K (lowerUnip q * γ))⁻¹ * (lowerUnip a * X)
      = ((ratGL R K γ)⁻¹ * lowerUnip (a - algebraMap K (FiniteAdeleRing R K) q)
          * ratGL R K γ) * ((ratGL R K γ)⁻¹ * X) := by
    rw [ratGL, map_mul, map_lowerUnip, hsplit]
    group
  rw [key]
  exact mul_mem hq hX

private theorem det_apply (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
    (v : HeightOneSpectrum R) : M.det v = M 0 0 v * M 1 1 v - M 0 1 v * M 1 0 v := by
  rw [Matrix.det_fin_two]; rfl

private theorem exists_lowerUnip_translate_isUnit (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ t : FiniteAdeleRing R K, (∀ v : HeightOneSpectrum R, t v ∈ v.adicCompletionIntegers K) ∧
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
        + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t) := by
  classical
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hM
  set N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K))
    with hN
  have hMN : M.det * N.det = 1 := by
    rw [← Matrix.det_mul, hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one]
  have hdetprod : ∀ v : HeightOneSpectrum R, M.det v * N.det v = 1 := by
    intro v
    rw [show M.det v * N.det v = (M.det * N.det) v from rfl, hMN]; rfl
  have hdet_ne : ∀ v : HeightOneSpectrum R, M.det v ≠ 0 := by
    intro v hzero
    have h1 := hdetprod v
    rw [hzero, zero_mul] at h1
    exact zero_ne_one h1
  have hrow : ∀ v : HeightOneSpectrum R, ¬(M 1 0 v = 0 ∧ M 1 1 v = 0) := by
    intro v ⟨h0, h1⟩
    apply hdet_ne v
    rw [det_apply R K M v, h0, h1, mul_zero, mul_zero, sub_zero]
  set tfun : (v : HeightOneSpectrum R) → v.adicCompletion K := fun v ↦
    if Valued.v (M 1 0 v) < Valued.v (M 1 1 v) then 1 else 0 with htfun
  have htfun_eval : ∀ v : HeightOneSpectrum R, tfun v
      = if Valued.v (M 1 0 v) < Valued.v (M 1 1 v) then (1 : v.adicCompletion K) else 0 :=
    fun v ↦ rfl
  have htint : ∀ v, tfun v ∈ v.adicCompletionIntegers K := by
    intro v
    rw [htfun_eval v]
    split
    · exact one_mem _
    · exact zero_mem _
  set t : FiniteAdeleRing R K := ⟨tfun, Filter.Eventually.of_forall fun v ↦ htint v⟩ with ht
  have htv : ∀ v, t v = tfun v := fun v ↦ rfl
  refine ⟨t, fun v ↦ by rw [htv v]; exact htint v, ?_⟩
  set c : FiniteAdeleRing R K := M 1 0 + M 1 1 * t with hc
  have hcv : ∀ v, c v = M 1 0 v + M 1 1 v * tfun v := fun v ↦ rfl
  have hcne : ∀ v, c v ≠ 0 := by
    intro v
    rw [hcv v, htfun_eval v]
    split
    · rename_i hlt
      intro hzero
      have hne : Valued.v (M 1 0 v) ≠ Valued.v (M 1 1 v) := ne_of_lt hlt
      have hval : Valued.v (M 1 0 v + M 1 1 v) =
          max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) :=
        Valuation.map_add_of_distinct_val _ hne
      rw [mul_one] at hzero
      rw [hzero, Valuation.map_zero, max_eq_right (le_of_lt hlt)] at hval
      have hd0 : M 1 1 v = 0 := by
        have := hval.symm
        rwa [Valuation.zero_iff] at this
      have hc0 : M 1 0 v = 0 := by
        have := hzero
        rwa [hd0, add_zero] at this
      exact hrow v ⟨hc0, hd0⟩
    · rename_i hge
      rw [mul_zero, add_zero]
      intro hzero
      have hc0 : Valued.v (M 1 0 v) = 0 := by rw [hzero, Valuation.map_zero]
      have hd0 : Valued.v (M 1 1 v) = 0 := by
        have hle : Valued.v (M 1 1 v) ≤ Valued.v (M 1 0 v) := not_lt.mp hge
        rw [hc0] at hle
        exact le_zero_iff.mp hle
      rw [Valuation.zero_iff] at hd0
      exact hrow v ⟨hzero, hd0⟩
  have hcunit : ∀ᶠ v in Filter.cofinite, Valued.v (c v) = 1 := by
    have h00 : ∀ᶠ v in Filter.cofinite, M 0 0 v ∈ v.adicCompletionIntegers K := (M 0 0).2
    have h01 : ∀ᶠ v in Filter.cofinite, M 0 1 v ∈ v.adicCompletionIntegers K := (M 0 1).2
    have h10 : ∀ᶠ v in Filter.cofinite, M 1 0 v ∈ v.adicCompletionIntegers K := (M 1 0).2
    have h11 : ∀ᶠ v in Filter.cofinite, M 1 1 v ∈ v.adicCompletionIntegers K := (M 1 1).2
    have k00 : ∀ᶠ v in Filter.cofinite, N 0 0 v ∈ v.adicCompletionIntegers K := (N 0 0).2
    have k01 : ∀ᶠ v in Filter.cofinite, N 0 1 v ∈ v.adicCompletionIntegers K := (N 0 1).2
    have k10 : ∀ᶠ v in Filter.cofinite, N 1 0 v ∈ v.adicCompletionIntegers K := (N 1 0).2
    have k11 : ∀ᶠ v in Filter.cofinite, N 1 1 v ∈ v.adicCompletionIntegers K := (N 1 1).2
    filter_upwards [h00, h01, h10, h11, k00, k01, k10, k11] with v
      h00 h01 h10 h11 k00 k01 k10 k11
    have hNdetint : N.det v ∈ v.adicCompletionIntegers K := by
      rw [det_apply R K N v]
      exact sub_mem (mul_mem k00 k11) (mul_mem k01 k10)
    have hMdetint : M.det v ∈ v.adicCompletionIntegers K := by
      rw [det_apply R K M v]
      exact sub_mem (mul_mem h00 h11) (mul_mem h01 h10)
    have hdetone : Valued.v (M.det v) = 1 := by
      have hprodval : Valued.v (M.det v) * Valued.v (N.det v) = 1 := by
        rw [← Valuation.map_mul, hdetprod v, Valuation.map_one]
      have hMle : Valued.v (M.det v) ≤ 1 := hMdetint
      have hNle : Valued.v (N.det v) ≤ 1 := hNdetint
      have hge : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v (M.det v) := by
        calc (1 : WithZero (Multiplicative ℤ))
            = Valued.v (M.det v) * Valued.v (N.det v) := hprodval.symm
          _ ≤ Valued.v (M.det v) * 1 := mul_le_mul' le_rfl hNle
          _ = Valued.v (M.det v) := mul_one _
      exact le_antisymm hMle hge
    have hmax : (1 : WithZero (Multiplicative ℤ))
        ≤ max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) := by
      have hsub : Valued.v (M.det v)
          ≤ max (Valued.v (M 0 0 v * M 1 1 v)) (Valued.v (M 0 1 v * M 1 0 v)) := by
        rw [det_apply R K M v]
        exact Valuation.map_sub _ _ _
      have h1 : Valued.v (M 0 0 v * M 1 1 v) ≤ Valued.v (M 1 1 v) := by
        rw [Valuation.map_mul]
        calc Valued.v (M 0 0 v) * Valued.v (M 1 1 v) ≤ 1 * Valued.v (M 1 1 v) :=
              mul_le_mul' h00 le_rfl
          _ = Valued.v (M 1 1 v) := one_mul _
      have h2 : Valued.v (M 0 1 v * M 1 0 v) ≤ Valued.v (M 1 0 v) := by
        rw [Valuation.map_mul]
        calc Valued.v (M 0 1 v) * Valued.v (M 1 0 v) ≤ 1 * Valued.v (M 1 0 v) :=
              mul_le_mul' h01 le_rfl
          _ = Valued.v (M 1 0 v) := one_mul _
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (M.det v) := hdetone.symm
        _ ≤ max (Valued.v (M 0 0 v * M 1 1 v)) (Valued.v (M 0 1 v * M 1 0 v)) := hsub
        _ ≤ max (Valued.v (M 1 1 v)) (Valued.v (M 1 0 v)) := max_le_max h1 h2
        _ = max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) := max_comm _ _
    rw [hcv v, htfun_eval v]
    split
    · rename_i hlt
      rw [mul_one]
      have hne : Valued.v (M 1 0 v) ≠ Valued.v (M 1 1 v) := ne_of_lt hlt
      rw [Valuation.map_add_of_distinct_val _ hne]
      have hmaxeq : max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) = Valued.v (M 1 1 v) :=
        max_eq_right (le_of_lt hlt)
      rw [hmaxeq]
      refine le_antisymm h11 ?_
      rw [hmaxeq] at hmax
      exact hmax
    · rename_i hge
      rw [mul_zero, add_zero]
      have hmaxeq : max (Valued.v (M 1 0 v)) (Valued.v (M 1 1 v)) = Valued.v (M 1 0 v) :=
        max_eq_left (not_lt.mp hge)
      refine le_antisymm h10 ?_
      rw [hmaxeq] at hmax
      exact hmax
  set cinvfun : (v : HeightOneSpectrum R) → v.adicCompletion K := fun v ↦ (c v)⁻¹
    with hcinvfun
  have hcinv_ev : ∀ᶠ v in Filter.cofinite,
      cinvfun v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    filter_upwards [hcunit] with v hv
    change (c v)⁻¹ ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))
    rw [SetLike.mem_coe, mem_adicCompletionIntegers, Valuation.map_inv, hv]
    exact le_of_eq inv_one
  set cinv : FiniteAdeleRing R K := ⟨cinvfun, hcinv_ev⟩ with hcinv
  have hcinvv : ∀ v, cinv v = (c v)⁻¹ := fun v ↦ rfl
  have hmul : c * cinv = 1 := by
    have hkey : ∀ w : HeightOneSpectrum R, (c * cinv) w = (1 : FiniteAdeleRing R K) w := by
      intro w
      rw [show (c * cinv) w = c w * cinv w from rfl, hcinvv w, mul_inv_cancel₀ (hcne w)]
      rfl
    exact Subtype.ext (funext fun w ↦ hkey w)
  exact ⟨⟨c, cinv, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

/-- The determinant of a matrix over the finite adeles, as a unit. -/
private def detUnit (g : GL (Fin 2) (FiniteAdeleRing R K)) : (FiniteAdeleRing R K)ˣ where
  val := ((g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) _).det
  inv := ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix (Fin 2) (Fin 2) _).det
  val_inv := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  inv_val := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

private theorem detUnit_coe (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    (detUnit R K g : FiniteAdeleRing R K)
      = ((g : GL (Fin 2) (FiniteAdeleRing R K)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)).det := rfl

private theorem exists_gauss_decomposition (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ (t : FiniteAdeleRing R K) (x z : FiniteAdeleRing R K) (cu : (FiniteAdeleRing R K)ˣ),
      (∀ v : HeightOneSpectrum R, t v ∈ v.adicCompletionIntegers K) ∧
      g = upperUnip x * (lowerUnip (cu : FiniteAdeleRing R K)
        * (upperUnip z * (diagTorus (detUnit R K g) * lowerUnip (-t)))) := by
  obtain ⟨t, htint, hunit⟩ := exists_lowerUnip_translate_isUnit R K g
  set h : GL (Fin 2) (FiniteAdeleRing R K) := g * lowerUnip t with hh
  set M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
    (h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) with hM
  have hM10 : M 1 0 = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 0
      + (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) 1 1 * t := by
    rw [hM, hh, Units.val_mul, lowerUnip_coe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  set cu : (FiniteAdeleRing R K)ˣ := hunit.unit with hcu
  have hc : M 1 0 = (cu : FiniteAdeleRing R K) := by rw [hM10, hcu, hunit.unit_spec]
  have hdet : M.det = (detUnit R K g : FiniteAdeleRing R K) := by
    rw [hM, hh, Units.val_mul, Matrix.det_mul, lowerUnip_coe, Matrix.det_fin_two_of,
      detUnit_coe]
    ring
  have hfact := gauss_factorization M (cu : FiniteAdeleRing R K)
    ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
    (detUnit R K g : FiniteAdeleRing R K)
    (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
    hc cu.mul_inv hdet (detUnit R K g).mul_inv
  set x : FiniteAdeleRing R K :=
    (M 0 0 - 1) * ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) with hx
  set z : FiniteAdeleRing R K :=
    (M 1 1 * (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) - 1)
      * ((cu⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) with hz
  have hgroup : upperUnip x * lowerUnip (cu : FiniteAdeleRing R K)
      * upperUnip z * diagTorus (detUnit R K g) = h := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, upperUnip_coe, lowerUnip_coe,
      upperUnip_coe, diagTorus_coe, hx, hz]
    exact hfact
  refine ⟨t, x, z, cu, htint, ?_⟩
  have hgh : g = h * (lowerUnip t)⁻¹ := by
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  have hassoc : upperUnip x * (lowerUnip (cu : FiniteAdeleRing R K)
      * (upperUnip z * (diagTorus (detUnit R K g) * lowerUnip (-t))))
      = h * (lowerUnip t)⁻¹ := by
    rw [← hgroup, lowerUnip_inv]
    group
  rw [hassoc]
  exact hgh

omit [IsFractionRing R K] in
private theorem exists_primeGenerator [IsPrincipalIdealRing R] (v : HeightOneSpectrum R) :
    ∃ π : R, π ≠ 0 ∧ v.intValuation π = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.intValuation π = 1 := by
  classical
  have hspan : Ideal.span {Submodule.IsPrincipal.generator v.asIdeal} = v.asIdeal :=
    Ideal.span_singleton_generator v.asIdeal
  have h0 : Submodule.IsPrincipal.generator v.asIdeal ≠ 0 := fun h ↦
    v.ne_bot (by rw [← hspan, h]; exact Ideal.span_singleton_eq_bot.mpr rfl)
  refine ⟨Submodule.IsPrincipal.generator v.asIdeal, h0,
    intValuation_singleton v h0 hspan.symm, fun w hw ↦ ?_⟩
  rw [intValuation_eq_one_iff]
  intro hmem
  apply hw
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm

private theorem finiteIdele_exists_global_profile [IsPrincipalIdealRing R]
    (δ : (FiniteAdeleRing R K)ˣ) :
    ∃ α : Kˣ,
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
          * (δ : FiniteAdeleRing R K)) v ∈ v.adicCompletionIntegers K) ∧
      (∀ v : HeightOneSpectrum R,
        (algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
          * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v
          ∈ v.adicCompletionIntegers K) := by
  classical
  obtain ⟨hne, hev⟩ := FiniteAdeleRing.isUnit_iff.mp (Units.isUnit δ)
  have hvne : ∀ v : HeightOneSpectrum R, Valued.v ((δ : FiniteAdeleRing R K) v) ≠ 0 :=
    fun v ↦ (Valuation.ne_zero_iff _).mpr (hne v)
  choose π hπ0 hπv hπw using fun v : HeightOneSpectrum R ↦ exists_primeGenerator R v
  obtain ⟨m, hm⟩ : ∃ m : HeightOneSpectrum R → ℤ,
      ∀ v, WithZero.exp (m v) = Valued.v ((δ : FiniteAdeleRing R K) v) :=
    ⟨fun v ↦ WithZero.log (Valued.v ((δ : FiniteAdeleRing R K) v)),
      fun v ↦ WithZero.exp_log (hvne v)⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum R),
      ∀ w, w ∉ S → Valued.v ((δ : FiniteAdeleRing R K) w) = 1 :=
    ⟨(Filter.eventually_cofinite.mp hev).toFinset,
      fun w hw ↦ by_contra fun h ↦ hw ((Set.Finite.mem_toFinset _).mpr h)⟩
  have hπK : ∀ v, algebraMap R K (π v) ≠ 0 := fun v h ↦
    hπ0 v (IsFractionRing.injective R K (by rw [h, map_zero]))
  set a : K := ∏ v ∈ S, (algebraMap R K (π v)) ^ (-(m v)) with ha
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero _ (hπK v)
  have hval : ∀ w : HeightOneSpectrum R,
      w.valuation K a = Valued.v ((δ : FiniteAdeleRing R K) w) := by
    intro w
    rw [ha, map_prod]
    simp_rw [map_zpow₀]
    rw [Finset.prod_eq_single w]
    · rw [valuation_of_algebraMap, hπv w, ← WithZero.exp_zsmul, ← hm w]
      congr 1
      rw [smul_eq_mul, neg_mul_neg, mul_one]
    · intro v _ hvw
      rw [valuation_of_algebraMap, hπw v w (Ne.symm hvw), _root_.one_zpow]
    · intro hw
      have hm0 : m w = 0 := by
        have h1 := hm w
        rw [hS w hw, WithZero.exp_eq_one] at h1
        exact h1
      rw [hm0, neg_zero, zpow_zero]
  refine ⟨Units.mk0 a ha0, fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [show (algebraMap K (FiniteAdeleRing R K) ((Units.mk0 a ha0)⁻¹ : Kˣ) *
        (δ : FiniteAdeleRing R K)) v = algebraMap K (FiniteAdeleRing R K)
          ((Units.mk0 a ha0)⁻¹ : Kˣ) v * (δ : FiniteAdeleRing R K) v from rfl,
      mem_adicCompletionIntegers, Valuation.map_mul,
      valued_algebraMap_finiteAdeleRing_apply, Units.val_inv_eq_inv_val, Units.val_mk0,
      map_inv₀, hval v]
    exact le_of_eq (inv_mul_cancel₀ (hvne v))
  · have hprod : (δ : FiniteAdeleRing R K) v
        * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
      rw [show (δ : FiniteAdeleRing R K) v
          * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v
          = ((δ : FiniteAdeleRing R K) * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) :
            FiniteAdeleRing R K)) v from rfl, Units.mul_inv]
      rfl
    rw [show (algebraMap K (FiniteAdeleRing R K) ((Units.mk0 a ha0 : Kˣ) : K) *
        ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v =
        algebraMap K (FiniteAdeleRing R K) ((Units.mk0 a ha0 : Kˣ) : K) v *
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v from rfl,
      mem_adicCompletionIntegers, Valuation.map_mul,
      valued_algebraMap_finiteAdeleRing_apply, Units.val_mk0, hval v]
    exact le_of_eq (by rw [← Valuation.map_mul, hprod, Valuation.map_one])

private theorem exists_ratGL_inv_mul_mem [IsPrincipalIdealRing R]
    (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ∃ γ : GL (Fin 2) K, (ratGL R K γ)⁻¹ * g ∈ intGL2 R K := by
  obtain ⟨t, x, z, cu, htint, hg⟩ := exists_gauss_decomposition R K g
  obtain ⟨α, hα₁, hα₂⟩ := finiteIdele_exists_global_profile R K (detUnit R K g)
  set w : (FiniteAdeleRing R K)ˣ :=
    (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α)⁻¹
      * detUnit R K g with hw
  have hmapinv :
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α)⁻¹
        = Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) α⁻¹ :=
    (map_inv (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K))
      α).symm
  have hwval : (w : FiniteAdeleRing R K)
      = algebraMap K (FiniteAdeleRing R K) ((α⁻¹ : Kˣ) : K)
        * (detUnit R K g : FiniteAdeleRing R K) := by
    rw [hw, hmapinv, Units.val_mul, Units.coe_map]; rfl
  have hwinvval : ((w⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)
      = algebraMap K (FiniteAdeleRing R K) ((α : Kˣ) : K)
        * (((detUnit R K g)⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) := by
    rw [hw, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_comm, Units.coe_map]; rfl
  have hwmem : diagTorus w ∈ intGL2 R K :=
    diagTorus_mem R K (fun v ↦ by rw [hwval]; exact hα₁ v)
      (fun v ↦ by rw [hwinvval]; exact hα₂ v)
  have hδsplit : diagTorus (detUnit R K g) = ratGL R K (diagTorus α) * diagTorus w := by
    rw [ratGL, map_diagTorus, ← diagTorus_mul, hw]
    congr 1
    group
  have hbase : (ratGL R K (diagTorus α))⁻¹
      * (diagTorus (detUnit R K g) * lowerUnip (-t)) ∈ intGL2 R K := by
    have heq : (ratGL R K (diagTorus α))⁻¹
        * (diagTorus (detUnit R K g) * lowerUnip (-t)) = diagTorus w * lowerUnip (-t) := by
      rw [hδsplit]; group
    rw [heq]
    exact mul_mem hwmem (lowerUnip_mem R K fun v ↦ neg_mem (htint v))
  obtain ⟨q₁, hq₁⟩ := absorb_upperUnip_left R K hbase z
  obtain ⟨q₂, hq₂⟩ := absorb_lowerUnip_left R K hq₁ (cu : FiniteAdeleRing R K)
  obtain ⟨q₃, hq₃⟩ := absorb_upperUnip_left R K hq₂ x
  refine ⟨upperUnip q₃ * (lowerUnip q₂ * (upperUnip q₁ * diagTorus α)), ?_⟩
  rw [hg]
  exact hq₃

end General

section Level

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

private theorem idealBound_of_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v =
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ)) := by
  rw [idealBound]
  split_ifs with h
  · exact absurd h hN
  · rfl

private theorem sub_mem_integralFiniteAdeles' {x y : FiniteAdeleRing R K}
    (hx : x ∈ AdelicBox.integralFiniteAdeles R K) (hy : y ∈ AdelicBox.integralFiniteAdeles R K) :
    x - y ∈ AdelicBox.integralFiniteAdeles R K :=
  fun v => sub_mem (hx v) (hy v)

private theorem exists_algebraMap_eq_of_mem_integralFiniteAdeles {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ AdelicBox.integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

private theorem pow_count_dvd {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    v.asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk N).factors) ∣ N := by
  classical
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
  exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN)
    (Associates.irreducible_mk.mpr v.irreducible)).mpr le_rfl

private theorem algebraMap_mem_idealBall {N : Ideal R} (hN : N ≠ ⊥) {r : R} (hr : r ∈ N) :
    algebraMap K (FiniteAdeleRing R K) (algebraMap R K r) ∈ idealBall R K N := fun v => by
  rw [show (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) v
      = algebraMap K (v.adicCompletion K) (algebraMap R K r) from rfl,
    AdelicBox.valued_algebraMap, idealBound_of_ne_bot hN, intValuation_le_pow_iff_dvd]
  exact (pow_count_dvd hN v).trans (Ideal.dvd_span_singleton.mpr hr)

private theorem algebraMap_mem_integralFiniteAdeles (r : R) :
    algebraMap K (FiniteAdeleRing R K) (algebraMap R K r) ∈
      AdelicBox.integralFiniteAdeles R K := fun v =>
  AdelicBox.algebraMap_mem_adicCompletionIntegers R K v r

private theorem mem_span_singleton_of_algebraMap_mem_idealBall {n₀ r : R} (hn : n₀ ≠ 0)
    (h : algebraMap K (FiniteAdeleRing R K) (algebraMap R K r) ∈
      idealBall R K (Ideal.span {n₀})) :
    r ∈ Ideal.span {n₀} := by
  have hv : ∀ v : HeightOneSpectrum R, v.intValuation r ≤ v.intValuation n₀ := fun v => by
    have h1 := h v
    rw [show (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) v
        = algebraMap K (v.adicCompletion K) (algebraMap R K r) from rfl,
      AdelicBox.valued_algebraMap,
      idealBound_of_ne_bot (by rwa [Ne, Ideal.span_singleton_eq_bot]),
      ← v.intValuation_if_neg hn] at h1
    exact h1
  have hn' : algebraMap R K n₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hn
  have hle : ∀ v : HeightOneSpectrum R,
      v.valuation K (algebraMap R K r / algebraMap R K n₀) ≤ 1 := fun v => by
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap]
    exact (div_le_one₀ (zero_lt_iff.mpr (intValuation_ne_zero v n₀ hn))).mpr (hv v)
  obtain ⟨m, hm⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hle
  rw [Ideal.mem_span_singleton']
  refine ⟨m, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hm, div_mul_cancel₀ _ hn']

private theorem neg_mem_idealBall {N : Ideal R} {x : FiniteAdeleRing R K}
    (hx : x ∈ idealBall R K N) : -x ∈ idealBall R K N := fun v => by
  rw [show (-x) v = -(x v) from rfl, Valuation.map_neg]; exact hx v

private theorem sub_mem_idealBall {N : Ideal R} {x y : FiniteAdeleRing R K}
    (hx : x ∈ idealBall R K N) (hy : y ∈ idealBall R K N) : x - y ∈ idealBall R K N := by
  rw [sub_eq_add_neg]; exact add_mem_idealBall hx (neg_mem_idealBall hy)

private theorem idealBall_mono {M N : Ideal R} (hM : M ≠ ⊥) (h : M ≤ N) :
    idealBall R K M ⊆ idealBall R K N := fun x hx v => by
  classical
  have hN : N ≠ ⊥ := fun hN => hM (le_bot_iff.mp (hN ▸ h))
  refine (hx v).trans ?_
  rw [idealBound_of_ne_bot hM, idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hM)
    (Associates.irreducible_mk.mpr v.irreducible)
    (Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_iff_le.mpr h))

private theorem exists_sub_algebraMap_mem_idealBall {N : Ideal R} (hN : N ≠ ⊥)
    {x : FiniteAdeleRing R K} (hx : x ∈ AdelicBox.integralFiniteAdeles R K) :
    ∃ a : R, x - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a) ∈ idealBall R K N := by
  obtain ⟨n₀, hnN, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hnK : algebraMap R K n₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hn0
  set nA : FiniteAdeleRing R K := algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀)
    with hnA_def
  have hnA : IsUnit nA := (Ne.isUnit hnK).map (algebraMap K (FiniteAdeleRing R K))
  obtain ⟨k, hk⟩ := AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles R K
    (((hnA.unit⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) * x)
  set y : FiniteAdeleRing R K := ((hnA.unit⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) * x
    - algebraMap K (FiniteAdeleRing R K) (-k) with hy_def
  have hy : y ∈ AdelicBox.integralFiniteAdeles R K := by
    rw [hy_def, map_neg, sub_neg_eq_add, add_comm]
    exact hk
  have hunit : nA * ((hnA.unit⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) = 1 :=
    hnA.mul_val_inv
  have hxy : x - algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀ * -k) = nA * y := by
    rw [hy_def, mul_sub, ← mul_assoc, hunit, one_mul, map_mul]
  have hint : algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀ * -k) ∈
      AdelicBox.integralFiniteAdeles R K := by
    have h1 : algebraMap K (FiniteAdeleRing R K) (algebraMap R K n₀ * -k) = x - nA * y := by
      rw [← hxy, sub_sub_cancel]
    rw [h1]
    exact sub_mem_integralFiniteAdeles' hx
      (mul_mem_integralFiniteAdeles (algebraMap_mem_integralFiniteAdeles n₀) hy)
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_mem_integralFiniteAdeles hint
  refine ⟨a, ?_⟩
  rw [ha, hxy]
  exact mul_mem_idealBall_right (algebraMap_mem_idealBall hN hnN) hy

end Level

section Unimodular

private theorem triple_of_modEq {n c d d' : ℤ} (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1)
    (hd : d' ≡ d [ZMOD n]) : ∃ x y z : ℤ, x * c + y * d' + z * n = 1 := by
  obtain ⟨x, y, z, hxyz⟩ := h
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hd.symm
  exact ⟨x, y, z - y * t, by linear_combination hxyz + y * ht⟩

private theorem not_dvd_of_dvd_of_dvd {n c d p : ℤ} (hp : Prime p)
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) (hpc : p ∣ c) (hpd : p ∣ d) : ¬ p ∣ n := by
  rintro hpn
  obtain ⟨x, y, z, hxyz⟩ := h
  have h1 : p ∣ (1 : ℤ) := by
    rw [← hxyz]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right hpc x) (dvd_mul_of_dvd_right hpd y))
      (dvd_mul_of_dvd_right hpn z)
  exact hp.not_isUnit (isUnit_of_dvd_one h1)

private theorem exists_modEq_isCoprime_of_ne_zero {n c d : ℤ} (hd : d ≠ 0)
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' : ℤ, c' ≡ c [ZMOD n] ∧ IsCoprime c' d := by
  classical
  set S : Finset ℕ := d.natAbs.primeFactors.filter (fun p => ¬ (p : ℤ) ∣ c) with hS
  set m : ℤ := ∏ p ∈ S, (p : ℤ) with hm
  refine ⟨c + n * m, Int.modEq_iff_dvd.mpr ⟨-m, by ring⟩, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  change Nat.Coprime d.natAbs (c + n * m).natAbs
  refine Nat.Coprime.symm (Nat.coprime_of_dvd fun p hp hpc' hpd => ?_)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpd' : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
  have hpc'Z : (p : ℤ) ∣ c + n * m := Int.natCast_dvd.mpr hpc'
  by_cases hpc : (p : ℤ) ∣ c
  · have hpn : ¬ (p : ℤ) ∣ n := not_dvd_of_dvd_of_dvd hpZ h hpc hpd'
    have hpm : ¬ (p : ℤ) ∣ m := by
      rw [hm, hpZ.dvd_finsetProd_iff]
      rintro ⟨q, hq, hpq⟩
      rw [hS, Finset.mem_filter] at hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq.1
      have hpq' : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (Int.natCast_dvd_natCast.mp hpq)
      exact hq.2 (hpq' ▸ hpc)
    have hnm : (p : ℤ) ∣ n * m := by
      have h2 := dvd_sub hpc'Z hpc
      rwa [add_sub_cancel_left] at h2
    exact (hpZ.dvd_or_dvd hnm).elim hpn hpm
  · have hpS : p ∈ S := by
      rw [hS, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, hpd, Int.natAbs_ne_zero.mpr hd⟩, hpc⟩
    have hpm : (p : ℤ) ∣ m := hm ▸ Finset.dvd_prod_of_mem _ hpS
    have h3 := dvd_sub hpc'Z (dvd_mul_of_dvd_right hpm n)
    rw [add_sub_cancel_right] at h3
    exact hpc h3

/-- Residues `c, d` modulo `n` generating the unit ideal together with `n` lift to coprime
integers. -/
private theorem exists_modEq_and_modEq_and_isCoprime {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by
  by_cases hn : n = 0
  · subst hn
    obtain ⟨x, y, z, hxyz⟩ := h
    exact ⟨c, d, Int.ModEq.refl c, Int.ModEq.refl d, x, y, by linear_combination hxyz⟩
  obtain ⟨d', hd'd, hd'0⟩ : ∃ d' : ℤ, d' ≡ d [ZMOD n] ∧ d' ≠ 0 := by
    by_cases hd : d = 0
    · exact ⟨n, by rw [hd]; exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩, hn⟩
    · exact ⟨d, Int.ModEq.refl d, hd⟩
  obtain ⟨c', hc'c, hcop⟩ := exists_modEq_isCoprime_of_ne_zero hd'0 (triple_of_modEq h hd'd)
  exact ⟨c', d', hc'c, hd'd, hcop⟩

private def bezoutGL2 {A : Type*} [CommRing A] (a b s t : A) (h : a * s + b * t = 1) :
    GL (Fin 2) A where
  val := !![b, -a; s, t]
  inv := !![t, a; -s, b]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
      first | linear_combination h | ring
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
      first | linear_combination h | ring

end Unimodular

section Rat

private theorem isPrincipalIdealRing_ringOfIntegers_rat : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
    Rat.ringOfIntegersEquiv.symm.surjective

private theorem glFin_globalPoints (γ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)
      = GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ := by
  ext i j
  rfl

/-- An integer of `ℚ` as a finite adele. -/
private abbrev intAdele (r : 𝓞 ℚ) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r)

private theorem intAdele_mem (r : 𝓞 ℚ) : intAdele r ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  algebraMap_mem_integralFiniteAdeles r

private theorem exists_map_mul_mem_finiteLevelOne {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hk : k ∈ intGL2 (𝓞 ℚ) ℚ) :
    ∃ γ : GL (Fin 2) ℚ,
      GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ * k
        ∈ finiteLevelOne (𝓞 ℚ) ℚ N := by
  rw [mem_intGL2_iff] at hk
  obtain ⟨hkint, hkinvint⟩ := hk
  obtain ⟨n₀, hnN, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  set P : Ideal (𝓞 ℚ) := Ideal.span {n₀} with hP_def
  have hP : P ≠ ⊥ := by rwa [hP_def, Ne, Ideal.span_singleton_eq_bot]
  have hPN : P ≤ N := (Ideal.span_singleton_le_iff_mem _).mpr hnN
  set A : FiniteAdeleRing (𝓞 ℚ) ℚ := ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 0
    with hA
  set B : FiniteAdeleRing (𝓞 ℚ) ℚ := ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 1
    with hB
  have hAint : A ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := hkinvint 1 0
  have hBint : B ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := hkinvint 1 1
  have hinv : ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      * (k : Matrix (Fin 2) (Fin 2) _) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrow0 : A * (k : Matrix (Fin 2) (Fin 2) _) 0 0 + B * (k : Matrix (Fin 2) (Fin 2) _) 1 0
      = 0 := by
    have h := congrFun (congrFun hinv 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide)] at h
    exact h
  have hrow1 : A * (k : Matrix (Fin 2) (Fin 2) _) 0 1 + B * (k : Matrix (Fin 2) (Fin 2) _) 1 1
      = 1 := by
    have h := congrFun (congrFun hinv 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
    exact h
  obtain ⟨c₀, hc₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP hAint
  obtain ⟨d₀, hd₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP hBint
  obtain ⟨p₀, hp₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP (hkint 0 1)
  obtain ⟨q₀, hq₀⟩ := exists_sub_algebraMap_mem_idealBall (K := ℚ) hP (hkint 1 1)
  have hbez : c₀ * p₀ + d₀ * q₀ - 1 ∈ P := by
    refine mem_span_singleton_of_algebraMap_mem_idealBall (K := ℚ) hn0 ?_
    have himage : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
        (algebraMap (𝓞 ℚ) ℚ (c₀ * p₀ + d₀ * q₀ - 1))
        = intAdele c₀ * intAdele p₀ + intAdele d₀ * intAdele q₀ - 1 := by
      simp only [intAdele, map_add, map_sub, map_mul, map_one]
    rw [himage]
    have halg : intAdele c₀ * intAdele p₀ + intAdele d₀ * intAdele q₀ - 1
        = (A * (k : Matrix (Fin 2) (Fin 2) _) 0 1 + B * (k : Matrix (Fin 2) (Fin 2) _) 1 1 - 1)
          - ((A - intAdele c₀) * (k : Matrix (Fin 2) (Fin 2) _) 0 1
              + intAdele c₀ * ((k : Matrix (Fin 2) (Fin 2) _) 0 1 - intAdele p₀)
              + (B - intAdele d₀) * (k : Matrix (Fin 2) (Fin 2) _) 1 1
              + intAdele d₀ * ((k : Matrix (Fin 2) (Fin 2) _) 1 1 - intAdele q₀)) := by ring
    rw [halg, hrow1, sub_self, zero_sub]
    refine neg_mem_idealBall
      (add_mem_idealBall (add_mem_idealBall (add_mem_idealBall ?_ ?_) ?_) ?_)
    · exact mul_mem_idealBall_right hc₀ (hkint 0 1)
    · exact mul_mem_idealBall_left (intAdele_mem c₀) hp₀
    · exact mul_mem_idealBall_right hd₀ (hkint 1 1)
    · exact mul_mem_idealBall_left (intAdele_mem d₀) hq₀
  set e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv with he
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hbez
  have htriple : ∃ x y z : ℤ, x * e c₀ + y * e d₀ + z * e n₀ = 1 := by
    refine ⟨e p₀, e q₀, -e w, ?_⟩
    have h := congrArg e hw
    rw [map_mul, map_sub, map_add, map_mul, map_mul, map_one] at h
    linear_combination -h
  obtain ⟨s, t, hs, ht, hcop⟩ := exists_modEq_and_modEq_and_isCoprime htriple
  obtain ⟨a, b, hab⟩ := hcop
  set s₀ := e.symm s with hs₀
  set t₀ := e.symm t with ht₀
  set a₀ := e.symm a with ha₀
  set b₀ := e.symm b with hb₀
  have hab₀ : a₀ * s₀ + b₀ * t₀ = 1 := by
    apply e.injective
    rw [map_add, map_mul, map_mul, map_one, hs₀, ht₀, ha₀, hb₀, e.apply_symm_apply,
      e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
    exact hab
  have hcong : ∀ {u : ℤ} {r₀ : 𝓞 ℚ}, u ≡ e r₀ [ZMOD e n₀] →
      intAdele (e.symm u) - intAdele r₀ ∈ idealBall (𝓞 ℚ) ℚ P := by
    intro u r₀ hu
    have hdvd : n₀ ∣ e.symm u - r₀ := by
      have h1 : e n₀ ∣ u - e r₀ := Int.modEq_iff_dvd.mp hu.symm
      have h2 := map_dvd e.symm h1
      rwa [map_sub, e.symm_apply_apply, e.symm_apply_apply] at h2
    have hmem : e.symm u - r₀ ∈ P := Ideal.mem_span_singleton.mpr hdvd
    have h3 := algebraMap_mem_idealBall (K := ℚ) hP hmem
    rwa [map_sub, map_sub] at h3
  have hsA : intAdele s₀ - A ∈ idealBall (𝓞 ℚ) ℚ P := by
    have h1 : intAdele s₀ - A = (intAdele s₀ - intAdele c₀) - (A - intAdele c₀) := by ring
    rw [h1]; exact sub_mem_idealBall (hcong hs) hc₀
  have htB : intAdele t₀ - B ∈ idealBall (𝓞 ℚ) ℚ P := by
    have h1 : intAdele t₀ - B = (intAdele t₀ - intAdele d₀) - (B - intAdele d₀) := by ring
    rw [h1]; exact sub_mem_idealBall (hcong ht) hd₀
  have habQ : algebraMap (𝓞 ℚ) ℚ a₀ * algebraMap (𝓞 ℚ) ℚ s₀
      + algebraMap (𝓞 ℚ) ℚ b₀ * algebraMap (𝓞 ℚ) ℚ t₀ = 1 := by
    have h := congrArg (algebraMap (𝓞 ℚ) ℚ) hab₀
    rwa [map_add, map_mul, map_mul, map_one] at h
  refine ⟨bezoutGL2 _ _ _ _ habQ, ?_⟩
  set SA := GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))
    (bezoutGL2 _ _ _ _ habQ) with hSA
  have hSA00 : (SA : Matrix (Fin 2) (Fin 2) _) 0 0 = intAdele b₀ := rfl
  have hSA01 : (SA : Matrix (Fin 2) (Fin 2) _) 0 1 = intAdele (-a₀) := by
    change algebraMap ℚ _ (-(algebraMap (𝓞 ℚ) ℚ a₀)) = _
    rw [← map_neg]
  have hSA10 : (SA : Matrix (Fin 2) (Fin 2) _) 1 0 = intAdele s₀ := rfl
  have hSA11 : (SA : Matrix (Fin 2) (Fin 2) _) 1 1 = intAdele t₀ := rfl
  have hSAinv : SA⁻¹ = GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))
      (bezoutGL2 _ _ _ _ habQ)⁻¹ := (map_inv _ _).symm
  have hSAi00 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 0 0 = intAdele t₀ := by
    rw [hSAinv]; rfl
  have hSAi01 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 0 1 = intAdele a₀ := by
    rw [hSAinv]; rfl
  have hSAi10 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 0 = intAdele (-s₀) := by
    rw [hSAinv]
    change algebraMap ℚ _ (-(algebraMap (𝓞 ℚ) ℚ s₀)) = _
    rw [← map_neg]
  have hSAi11 : ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) 1 1 = intAdele b₀ := by
    rw [hSAinv]; rfl
  have hSAint : ∀ i j, (SA : Matrix (Fin 2) (Fin 2) _) i j ∈
      AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [hSA00]; exact intAdele_mem _
    · rw [hSA01]; exact intAdele_mem _
    · rw [hSA10]; exact intAdele_mem _
    · rw [hSA11]; exact intAdele_mem _
  have hSAiint : ∀ i j, ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
      ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [hSAi00]; exact intAdele_mem _
    · rw [hSAi01]; exact intAdele_mem _
    · rw [hSAi10]; exact intAdele_mem _
    · rw [hSAi11]; exact intAdele_mem _
  have hAs : A - intAdele s₀ ∈ idealBall (𝓞 ℚ) ℚ P := by
    rw [← neg_sub]; exact neg_mem_idealBall hsA
  have hBt : B - intAdele t₀ ∈ idealBall (𝓞 ℚ) ℚ P := by
    rw [← neg_sub]; exact neg_mem_idealBall htB
  have hM : ((SA * k : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (SA : Matrix (Fin 2) (Fin 2) _) * (k : Matrix (Fin 2) (Fin 2) _) := Units.val_mul _ _
  have hMi : (((SA * k)⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = ((k⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _)
        * ((SA⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) := by
    rw [_root_.mul_inv_rev, Units.val_mul]
  rw [mem_finiteLevelOne_iff]
  constructor
  · refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
    · intro i j
      rw [hM, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_integralFiniteAdeles
        (mul_mem_integralFiniteAdeles (hSAint i 0) (hkint 0 j))
        (mul_mem_integralFiniteAdeles (hSAint i 1) (hkint 1 j))
    · rw [hM, Matrix.mul_apply, Fin.sum_univ_two, hSA10, hSA11]
      have h1 : intAdele s₀ * (k : Matrix (Fin 2) (Fin 2) _) 0 0
            + intAdele t₀ * (k : Matrix (Fin 2) (Fin 2) _) 1 0
          = (intAdele s₀ - A) * (k : Matrix (Fin 2) (Fin 2) _) 0 0
            + (intAdele t₀ - B) * (k : Matrix (Fin 2) (Fin 2) _) 1 0
            + (A * (k : Matrix (Fin 2) (Fin 2) _) 0 0
              + B * (k : Matrix (Fin 2) (Fin 2) _) 1 0) := by
        ring
      rw [h1, hrow0, add_zero]
      exact idealBall_mono hP hPN (add_mem_idealBall
        (mul_mem_idealBall_right hsA (hkint 0 0)) (mul_mem_idealBall_right htB (hkint 1 0)))
    · rw [hM, Matrix.mul_apply, Fin.sum_univ_two, hSA10, hSA11]
      have h1 : intAdele s₀ * (k : Matrix (Fin 2) (Fin 2) _) 0 1
            + intAdele t₀ * (k : Matrix (Fin 2) (Fin 2) _) 1 1 - 1
          = (intAdele s₀ - A) * (k : Matrix (Fin 2) (Fin 2) _) 0 1
            + (intAdele t₀ - B) * (k : Matrix (Fin 2) (Fin 2) _) 1 1
            + (A * (k : Matrix (Fin 2) (Fin 2) _) 0 1
              + B * (k : Matrix (Fin 2) (Fin 2) _) 1 1 - 1) := by
        ring
      rw [h1, hrow1, sub_self, add_zero]
      exact idealBall_mono hP hPN (add_mem_idealBall
        (mul_mem_idealBall_right hsA (hkint 0 1)) (mul_mem_idealBall_right htB (hkint 1 1)))
  · refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
    · intro i j
      rw [hMi, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem_integralFiniteAdeles
        (mul_mem_integralFiniteAdeles (hkinvint i 0) (hSAiint 0 j))
        (mul_mem_integralFiniteAdeles (hkinvint i 1) (hSAiint 1 j))
    · rw [hMi, Matrix.mul_apply, Fin.sum_univ_two, hSAi00, hSAi10, ← hA, ← hB]
      have h1 : A * intAdele t₀ + B * intAdele (-s₀)
          = A * (intAdele t₀ - B) - B * (intAdele s₀ - A) := by
        simp only [intAdele, map_neg]; ring
      rw [h1]
      exact idealBall_mono hP hPN (sub_mem_idealBall (mul_mem_idealBall_left hAint htB)
        (mul_mem_idealBall_left hBint hsA))
    · rw [hMi, Matrix.mul_apply, Fin.sum_univ_two, hSAi01, hSAi11, ← hA, ← hB]
      have hone : intAdele a₀ * intAdele s₀ + intAdele b₀ * intAdele t₀ = 1 := by
        simp only [intAdele, ← map_mul, ← map_add, hab₀, map_one]
      have h1 : A * intAdele a₀ + B * intAdele b₀ - 1
          = intAdele a₀ * (A - intAdele s₀) + intAdele b₀ * (B - intAdele t₀)
            + (intAdele a₀ * intAdele s₀ + intAdele b₀ * intAdele t₀ - 1) := by
        ring
      rw [h1, hone, sub_self, add_zero]
      exact idealBall_mono hP hPN (add_mem_idealBall
        (mul_mem_idealBall_left (intAdele_mem _) hAs)
        (mul_mem_idealBall_left (intAdele_mem _) hBt))

/-- Strong approximation for `GL₂` over the finite adeles of `ℚ`: for every nonzero ideal `N`,
every matrix `g` over the finite adeles is moved into the level `finiteLevelOne (𝓞 ℚ) ℚ N` by
left multiplication with a rational matrix. -/
theorem exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * g ∈ finiteLevelOne (𝓞 ℚ) ℚ N := by
  have := isPrincipalIdealRing_ringOfIntegers_rat
  obtain ⟨γ₀, hγ₀⟩ := exists_ratGL_inv_mul_mem (𝓞 ℚ) ℚ g
  obtain ⟨γ₁, hγ₁⟩ := exists_map_mul_mem_finiteLevelOne hN hγ₀
  refine ⟨γ₁ * γ₀⁻¹, ?_⟩
  rw [glFin_globalPoints, map_mul, map_inv, mul_assoc]
  exact hγ₁

open NumberField.InfinitePlace in
private theorem realProj_globalPoints_apply (w : InfinitePlace ℚ) (hw : w.IsReal)
    (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
        (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j : ℝ) := by
  let f : ℚ →+* ℝ := (Completion.ringEquivRealOfIsReal hw).toRingHom.comp
    ((archEval ℚ w).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))))
  change f ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = _
  exact eq_ratCast f _

open NumberField.InfinitePlace in
private theorem det_realProj_globalPoints (w : InfinitePlace ℚ) (hw : w.IsReal)
    (γ : GL (Fin 2) ℚ) :
    ((GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
        (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = ((γ : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, realProj_globalPoints_apply,
    realProj_globalPoints_apply, realProj_globalPoints_apply, realProj_globalPoints_apply]
  push_cast
  ring

/-- The rational matrix `diag(-1, 1)`. -/
private def negOneDiag : GL (Fin 2) ℚ where
  val := !![-1, 0; 0, 1]
  inv := !![-1, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem negOneDiag_inv : negOneDiag⁻¹ = negOneDiag := Units.ext rfl

private theorem det_negOneDiag :
    ((negOneDiag : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = -1 := by
  rw [show ((negOneDiag : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, 1] from rfl,
    Matrix.det_fin_two]
  simp

private theorem isLevelOneMatrix_negOneDiag (N : Ideal (𝓞 ℚ)) :
    IsLevelOneMatrix (𝓞 ℚ) ℚ N
      ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ negOneDiag) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  have hentry : ∀ i j, ((glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ negOneDiag) :
      GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
          ((!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j) :=
    fun _ _ => rfl
  have hneg1 : (-1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ :=
    fun v => neg_mem (one_mem _)
  refine { integral := ?_, lowerLeft := ?_, lowerRight := ?_ }
  · refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;> rw [hentry]
    · change algebraMap ℚ _ (-1) ∈ _
      rw [map_neg, map_one]
      exact hneg1
    · change algebraMap ℚ _ 0 ∈ _
      rw [map_zero]
      exact zero_mem_integralFiniteAdeles
    · change algebraMap ℚ _ 0 ∈ _
      rw [map_zero]
      exact zero_mem_integralFiniteAdeles
    · change algebraMap ℚ _ 1 ∈ _
      rw [map_one]
      exact one_mem_integralFiniteAdeles
  · rw [hentry]; simpa using zero_mem_idealBall N
  · rw [hentry]; simpa using zero_mem_idealBall N

private theorem globalPoints_negOneDiag_mem_levelOne (N : Ideal (𝓞 ℚ)) :
    globalPoints (𝓞 ℚ) ℚ negOneDiag ∈ levelOne (𝓞 ℚ) ℚ N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_negOneDiag N, ?_⟩
  rw [← map_inv, ← map_inv, negOneDiag_inv]
  exact isLevelOneMatrix_negOneDiag N

open NumberField.InfinitePlace in
/-- Strong approximation for adelic `GL₂` over `ℚ`: for every nonzero ideal `N`, every adelic
matrix `g` is moved by left multiplication with a rational matrix into the level
`levelOne (𝓞 ℚ) ℚ N`, with positive determinant at the real place. -/
theorem exists_globalPoints_mul_mem_levelOne_rat {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      globalPoints (𝓞 ℚ) ℚ γ * g ∈ levelOne (𝓞 ℚ) ℚ N ∧
        ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * g)))
            ∈ GLPos (Fin 2) ℝ := by
  obtain ⟨γ₁, hγ₁⟩ := exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat hN (glFin (𝓞 ℚ) ℚ g)
  have hg₁ : globalPoints (𝓞 ℚ) ℚ γ₁ * g ∈ levelOne (𝓞 ℚ) ℚ N := by
    rw [mem_levelOne_iff, map_mul]; exact hγ₁
  set w₀ : InfinitePlace ℚ := Rat.infinitePlace
  have hw₀ : w₀.IsReal := Rat.isReal_infinitePlace
  set proj : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
    (GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw₀).toRingHom).comp
      ((archComponent ℚ w₀).comp (glArch (𝓞 ℚ) ℚ)) with hproj
  have key : ∀ γ : GL (Fin 2) ℚ,
      0 < ((proj (globalPoints (𝓞 ℚ) ℚ γ * g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det →
      ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
            (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * g)))
          ∈ GLPos (Fin 2) ℝ := by
    intro γ hγ w hw
    obtain rfl : w = w₀ := Subsingleton.elim _ _
    rw [Matrix.mem_glpos, GeneralLinearGroup.val_det_apply]
    exact hγ
  by_cases hsign :
      0 < ((proj (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
  · exact ⟨γ₁, hg₁, key γ₁ hsign⟩
  · refine ⟨negOneDiag * γ₁, ?_, key (negOneDiag * γ₁) ?_⟩
    · rw [map_mul, mul_assoc]
      exact mul_mem (globalPoints_negOneDiag_mem_levelOne N) hg₁
    · have hne : ((proj (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
        rw [← GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
      have hlt : ((proj (globalPoints (𝓞 ℚ) ℚ γ₁ * g) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ).det < 0 := lt_of_le_of_ne (not_lt.mp hsign) hne
      rw [map_mul (globalPoints (𝓞 ℚ) ℚ) negOneDiag γ₁, mul_assoc, map_mul proj,
        Units.val_mul, Matrix.det_mul, hproj, MonoidHom.comp_apply, MonoidHom.comp_apply,
        det_realProj_globalPoints, det_negOneDiag]
      rw [hproj] at hlt
      push_cast
      linarith

end Rat

end NumberField.AdelicLevel

namespace AutomorphicForm

open NumberField.AdelicLevel

/-- Matrices over the adeles of `ℚ` as pairs of matrices over the infinite and finite adeles. -/
private def matrixProdEquiv :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) ≃+*
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) ×
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) where
  toFun M := ((RingHom.fst _ _).mapMatrix M, (RingHom.snd _ _).mapMatrix M)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j; rfl
  right_inv p := by ext i j <;> rfl
  map_mul' M N := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; exact map_mul _ M N
    · simp only [Prod.snd_mul]; exact map_mul _ M N
  map_add' _ _ := rfl

/-- The matrix over the adeles of `ℚ` with identity infinite part and a given finite part. -/
private def finEmbed : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) →* AdelicGL2 (𝓞 ℚ) ℚ :=
  (Units.mapEquiv matrixProdEquiv.symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) _) (MonoidHom.id _)

private theorem glFin_finEmbed (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    glFin (𝓞 ℚ) ℚ (finEmbed k) = k := by
  ext i j
  rfl

private theorem glArch_finEmbed (k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    glArch (𝓞 ℚ) ℚ (finEmbed k) = 1 := by
  ext i j
  rfl

open NumberField.InfinitePlace in
/-- Strong approximation for `GL₂` over `ℚ` at the compact production pins: for every
fundamental set `D` and nonzero ideal `N`, every adelic matrix `g` factors as `g = γ h u` with
`γ` rational, `h` with identity finite part and positive determinant at the real place, and `u`
in the level `(productionPinsCompact ℚ D).U N`. -/
theorem exists_mem_productionPinsCompact_U_mul_eq_rat (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : AdelicGL2 (𝓞 ℚ) ℚ),
      u ∈ (productionPinsCompact ℚ D).U N ∧ glFin (𝓞 ℚ) ℚ h = 1 ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h)) ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = globalPoints (𝓞 ℚ) ℚ γ * h * u := by
  obtain ⟨γ, hmem, hpos⟩ := exists_globalPoints_mul_mem_levelOne_rat hN g
  set g' : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ * g with hg'
  set u : AdelicGL2 (𝓞 ℚ) ℚ := finEmbed (glFin (𝓞 ℚ) ℚ g') with hu
  refine ⟨γ⁻¹, g' * u⁻¹, u, ?_, ?_, ?_, ?_⟩
  · rw [mem_productionPinsCompact_U_iff, hu, glFin_finEmbed, glArch_finEmbed]
    exact ⟨mem_levelOne_iff.mp hmem, rfl⟩
  · rw [map_mul, map_inv, hu, glFin_finEmbed, mul_inv_cancel]
  · intro w hw
    rw [map_mul, map_inv, hu, glArch_finEmbed, inv_one, mul_one]
    exact hpos w hw
  · rw [mul_assoc, inv_mul_cancel_right, map_inv, hg', inv_mul_cancel_left]

end AutomorphicForm
