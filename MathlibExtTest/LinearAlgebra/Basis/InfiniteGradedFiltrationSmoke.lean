/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Determinant.FiltrationUnipotent
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
namespace InfiniteGradedFiltrationSmoke

private abbrev P := ℕ →₀ ℚ
private abbrev V := P × P
private abbrev GradeIndex (_ : ℕ) := ℕ

private def flag : ℕ → Submodule ℚ V
  | 0 => ⊥
  | 1 => LinearMap.ker (LinearMap.snd ℚ P P)
  | _ + 2 => ⊤
private theorem flag_zero : flag 0 = ⊥ := rfl
private theorem flag_top : flag 2 = ⊤ := rfl
private theorem flag_le (i : Fin 2) : flag i.val ≤ flag (i.val + 1) := by
  fin_cases i <;> simp [flag]

private abbrev Graded (i : Fin 2) :=
  flag (i.val + 1) ⧸ (flag i.val).comap (flag (i.val + 1)).subtype
private def coordinate (i : Fin 2) : flag (i.val + 1) →ₗ[ℚ] P :=
  (if i.val = 0 then LinearMap.fst ℚ P P else LinearMap.snd ℚ P P).comp
    (flag (i.val + 1)).subtype
private def liftVector (i : Fin 2) (p : P) : flag (i.val + 1) :=
  ⟨if i.val = 0 then (p, 0) else (0, p), by fin_cases i <;> simp [flag]⟩

private theorem coordinate_surjective (i : Fin 2) : Function.Surjective (coordinate i) := by
  intro p
  refine ⟨liftVector i p, ?_⟩
  fin_cases i <;> simp [coordinate, liftVector]

private theorem coordinate_ker (i : Fin 2) :
    (coordinate i).ker = (flag i.val).comap (flag (i.val + 1)).subtype := by
  ext x
  change coordinate i x = 0 ↔ (x : V) ∈ flag i.val
  fin_cases i
  · change (x : V).1 = 0 ↔ (x : V) = 0
    constructor
    · intro hp
      have hq : (x : V).2 = 0 := x.property
      exact Prod.ext hp hq
    · intro h
      exact congrArg Prod.fst h
  · change (x : V).2 = 0 ↔ (x : V).2 = 0
    exact Iff.rfl

private def gradedEquiv (i : Fin 2) : Graded i ≃ₗ[ℚ] P :=
  (Submodule.quotEquivOfEq _ _ (coordinate_ker i).symm).trans
    ((coordinate i).quotKerEquivOfSurjective (coordinate_surjective i))
private def gradedBasis (i : Fin 2) : Module.Basis (GradeIndex i.val) ℚ (Graded i) :=
  (Finsupp.basisSingleOne (ι := ℕ) (R := ℚ)).map (gradedEquiv i).symm
private def assembled : Module.Basis (Module.Basis.FiltrationIndex GradeIndex 2) ℚ V :=
  Module.Basis.ofFiltration flag flag_zero GradeIndex 2 flag_le gradedBasis flag_top

private def shear : V →ₗ[ℚ] V :=
  (LinearMap.fst ℚ P P + LinearMap.snd ℚ P P).prod (LinearMap.snd ℚ P P)
private theorem shear_error (i : Fin 2) (x : V) (hx : x ∈ flag (i.val + 1)) :
    shear x - x ∈ flag i.val := by
  fin_cases i
  · change x.2 = 0 at hx
    change shear x - x = 0
    apply Prod.ext
    · change x.1 + x.2 - x.1 = 0
      simp [hx]
    · change x.2 - x.2 = 0
      exact sub_self _
  · change (shear x - x).2 = 0
    change x.2 - x.2 = 0
    exact sub_self _

private theorem assembled_error (i : Fin 2) (k : ℕ) :
    shear (assembled ⟨i, k⟩) - assembled ⟨i, k⟩ ∈ flag i.val := by
  apply shear_error
  rw [assembled, Module.Basis.ofFiltration_apply]
  exact Module.Basis.ofFiltrationStage_mem flag flag_zero GradeIndex 2
    flag_le gradedBasis i k

-- The two actual graded quotient bases have genuinely infinite natural-number indices.
example (i : Fin 2) (k : ℕ) :
    gradedEquiv i
      (Submodule.Quotient.mk
        (Module.Basis.ofFiltrationStageVector flag flag_zero GradeIndex 2
          flag_le gradedBasis i k) : Graded i) = Finsupp.single k (1 : ℚ) := by
  rw [Module.Basis.ofFiltrationStageVector_mk]
  simp [gradedBasis]

-- This public application cannot synthesize a finite certificate for GradeIndex = ℕ.
example (j : ℕ) (hj : j ≤ 2) : flag j ≤ (flag j).comap shear :=
  Module.Basis.ofFiltration_stable (κ := GradeIndex)
    flag flag_zero 2 flag_le gradedBasis flag_top shear assembled_error j hj

example :
    flag 1 ≠ ⊥ ∧ flag 1 ≠ ⊤ ∧ shear ≠ LinearMap.id := by
  let e : P := Finsupp.single 0 (1 : ℚ)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hm : (e, 0) ∈ flag 1 := by
      change (0 : P) = 0
      rfl
    rw [h, Submodule.mem_bot] at hm
    have hc := congrArg (fun x : V => x.1 0) hm
    norm_num [e] at hc
  · intro h
    have hm : (0, e) ∈ flag 1 := by
      rw [h]
      trivial
    change e = 0 at hm
    have hc := congrArg (fun p : P => p 0) hm
    norm_num [e] at hc
  · intro h
    have hv := LinearMap.congr_fun h (0, e)
    have hc := congrArg (fun x : V => x.1 0) hv
    norm_num [shear, e] at hc

end InfiniteGradedFiltrationSmoke
