/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AdelicDock_LocalEmbedding.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
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

public import MathlibExt.NumberTheory.NumberField.AdelicLevel

/-!
# The local level-one subgroup of `GL₂` at a finite place

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a finite place. This file
defines

* `NumberField.AdelicLevel.localMat R K v g`, the `2 × 2` matrix over the finite adeles equal to
  `g` at `v` and to the identity at every other place;
* `NumberField.AdelicLevel.localEmbed R K v`, the resulting embedding of `GL₂(K_v)` into `GL₂` of
  the finite adeles;
* `NumberField.AdelicLevel.localLevelOne R K v N`, the preimage of `finiteLevelOne R K N` under
  `localEmbed`, characterized in `mem_localLevelOne_iff` through `IsLocalLevelOne`.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

open scoped Classical in
/-- The `2 × 2` matrix over the finite adeles equal to `g` at the place `v` and to the identity
at every other place. -/
def localMat (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.of fun i j =>
    ⟨Function.update (fun w : HeightOneSpectrum R =>
        (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) v (g i j),
      Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
        by_contra hwv
        refine hw ?_
        rw [Function.update_of_ne hwv, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _)⟩

theorem localMat_apply_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2) :
    localMat R K v g i j v = g i j := by
  classical
  change Function.update (fun w : HeightOneSpectrum R =>
    (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) v (g i j) v = g i j
  exact Function.update_self _ _ _

theorem localMat_apply_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMat R K v g i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  classical
  change Function.update (fun w : HeightOneSpectrum R =>
    (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) v (g i j) w = _
  rw [Function.update_of_ne hw]

private theorem matrix_ext_finiteAdele {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (finAdeleEval R K w).mapMatrix M = (finAdeleEval R K w).mapMatrix N) : M = N := by
  refine Matrix.ext fun i j => ?_
  apply RestrictedProduct.ext
  intro w
  exact congrFun (congrFun (h w) i) j

private theorem mapMatrix_localMat_self (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (finAdeleEval R K v).mapMatrix (localMat R K v g) = g := by
  refine Matrix.ext fun i j => ?_
  exact localMat_apply_self R K v g i j

private theorem mapMatrix_localMat_of_ne (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (finAdeleEval R K w).mapMatrix (localMat R K v g) = 1 := by
  refine Matrix.ext fun i j => ?_
  exact localMat_apply_of_ne R K v g i j hw

private theorem localMat_one : localMat R K v 1 = 1 := by
  refine matrix_ext_finiteAdele R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat_self, map_one]
  · rw [mapMatrix_localMat_of_ne R K v _ hw, map_one]

private theorem localMat_mul (g h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    localMat R K v (g * h) = localMat R K v g * localMat R K v h := by
  refine matrix_ext_finiteAdele R K fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, mapMatrix_localMat_self, mapMatrix_localMat_self, mapMatrix_localMat_self]
  · rw [map_mul, mapMatrix_localMat_of_ne R K v _ hw, mapMatrix_localMat_of_ne R K v _ hw,
      mapMatrix_localMat_of_ne R K v _ hw, mul_one]

/-- The embedding of `GL₂(K_v)` into `GL₂` of the finite adeles: `g` at the place `v` and the
identity at every other place. -/
def localEmbed : GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMat R K v g
      inv := localMat R K v ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMat_mul, Units.mul_inv, localMat_one]
      inv_val := by rw [← localMat_mul, Units.inv_mul, localMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMat_one R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMat_mul R K v _ _)

@[simp] theorem coe_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
    ((localEmbed R K v g : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) =
      localMat R K v g :=
  rfl

/-- The local level-one subgroup of `GL₂(K_v)` at an ideal `N`: the elements whose image under
`localEmbed` lies in `finiteLevelOne R K N`. -/
def localLevelOne (N : Ideal R) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  (finiteLevelOne R K N).comap (localEmbed R K v)

/-- A `2 × 2` matrix over `K_v` has local level one at `N` when its entries are integral, its
lower-left entry has valuation at most `idealBound R N v`, and its lower-right entry is congruent
to `1` to the same bound. -/
structure IsLocalLevelOne (N : Ideal R) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    Prop where
  /-- Every entry is integral. -/
  integral : ∀ i j, m i j ∈ v.adicCompletionIntegers K
  /-- The lower-left entry lies in `N` locally at `v`. -/
  lowerLeft : Valued.v (m 1 0) ≤ idealBound R N v
  /-- The lower-right entry is congruent to `1` modulo `N` locally at `v`. -/
  lowerRight : Valued.v (m 1 1 - 1) ≤ idealBound R N v

variable {R K v} in
private theorem isLevelOneMatrix_localMat_iff {N : Ideal R}
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    IsLevelOneMatrix R K N (localMat R K v m) ↔ IsLocalLevelOne R K v N m := by
  constructor
  · rintro ⟨⟨hint, hll⟩, hlr⟩
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := hint i j v
      rwa [localMat_apply_self] at this
    · have := hll v
      rwa [localMat_apply_self] at this
    · have := hlr v
      rwa [show (localMat R K v m 1 1 - 1) v = localMat R K v m 1 1 v - 1 from rfl,
        localMat_apply_self] at this
  · rintro ⟨hint, hll, hlr⟩
    refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hint i j
      · rw [localMat_apply_of_ne R K v m i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hll
      · rw [localMat_apply_of_ne R K v m 1 0 hw, Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le
    · rw [show (localMat R K v m 1 1 - 1) w = localMat R K v m 1 1 w - 1 from rfl]
      by_cases hw : w = v
      · subst hw; rw [localMat_apply_self]; exact hlr
      · rw [localMat_apply_of_ne R K v m 1 1 hw, Matrix.one_apply_eq, sub_self, map_zero]
        exact zero_le

variable {R K v} in
theorem mem_localLevelOne_iff {N : Ideal R} {k : GL (Fin 2) (v.adicCompletion K)} :
    k ∈ localLevelOne R K v N ↔ IsLocalLevelOne R K v N k ∧
      IsLocalLevelOne R K v N ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix _ _ _) := by
  rw [localLevelOne, Subgroup.mem_comap, mem_finiteLevelOne_iff, ← map_inv, coe_localEmbed,
    coe_localEmbed, isLevelOneMatrix_localMat_iff, isLevelOneMatrix_localMat_iff]

end NumberField.AdelicLevel

end
