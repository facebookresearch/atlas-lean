/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact rational sparse certificates for actual linear actions. -/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A finite rational linear combination of numbered actual vectors. -/
abbrev monsterNortonSparseState := List (ℕ × ℚ)

/-- Interpret a finite certificate in any real vector space using its actual basis vectors. -/
noncomputable def monsterNortonSparseEvaluate {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : ℕ → E) (l : monsterNortonSparseState) : E :=
  (l.map (fun p => (p.2 : ℝ) • b p.1)).sum

/-- Insert one rational coefficient in an ordered sparse certificate, combining equal labels. -/
def monsterNortonSparseInsert (k : ℕ) (c : ℚ) : monsterNortonSparseState →
    monsterNortonSparseState
  | [] => if c = 0 then [] else [(k,c)]
  | (j,d) :: l => if c = 0 then (j,d) :: l else
      if k < j then (k,c) :: (j,d) :: l else
        if k = j then if c + d = 0 then l else (k,c+d) :: l
        else (j,d) :: monsterNortonSparseInsert k c l

/-- Combine duplicate labels and remove zero coefficients by finite rational arithmetic. -/
def monsterNortonSparseNormalize : monsterNortonSparseState → monsterNortonSparseState
  | [] => []
  | (k,c) :: l => monsterNortonSparseInsert k c (monsterNortonSparseNormalize l)

/-- Multiply every exact rational coefficient by a given scalar. -/
def monsterNortonSparseScale (c : ℚ) (l : monsterNortonSparseState) : monsterNortonSparseState :=
  l.map (fun p => (p.1, c * p.2))

/-- Expand finitely many certified basis images and normalize their exact rational coefficients. -/
def monsterNortonSparseStep (image : ℕ → monsterNortonSparseState)
    (l : monsterNortonSparseState) : monsterNortonSparseState :=
  monsterNortonSparseNormalize (l.flatMap (fun p => monsterNortonSparseScale p.2 (image p.1)))

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem evaluate_cons (b : ℕ → E) (k : ℕ) (c : ℚ) (l : monsterNortonSparseState) :
    monsterNortonSparseEvaluate b ((k,c) :: l) =
      (c : ℝ) • b k + monsterNortonSparseEvaluate b l := rfl

/-- Combining rational coefficients preserves their actual real vector exactly. -/
theorem monsterNortonSparseInsert_evaluate (b : ℕ → E) (k : ℕ) (c : ℚ)
    (l : monsterNortonSparseState) :
    monsterNortonSparseEvaluate b (monsterNortonSparseInsert k c l) =
      (c : ℝ) • b k + monsterNortonSparseEvaluate b l := by
  induction l with
  | nil =>
    by_cases hc : c = 0 <;>
      simp [monsterNortonSparseInsert, monsterNortonSparseEvaluate, hc]
  | cons p l ih =>
    rcases p with ⟨j,d⟩
    by_cases hc : c = 0
    · simp [monsterNortonSparseInsert, hc]
    · by_cases hk : k < j
      · simp only [monsterNortonSparseInsert, hc, hk, ite_false, ite_true, evaluate_cons]
      · by_cases hkj : k = j
        · subst j
          by_cases hd : c + d = 0
          · have hz : (c : ℝ) • b k + (d : ℝ) • b k = 0 := by
              rw [← add_smul, ← Rat.cast_add, hd, Rat.cast_zero, zero_smul]
            simp only [monsterNortonSparseInsert, hc, hk, hd, ite_false, ite_true,
              evaluate_cons]
            rw [← add_assoc, hz, zero_add]
          · simp only [monsterNortonSparseInsert, hc, hk, hd, ite_false, ite_true,
              evaluate_cons, Rat.cast_add, add_smul]
            exact add_assoc _ _ _
        · simp only [monsterNortonSparseInsert, hc, hk, hkj, ite_false, evaluate_cons, ih]
          abel

/-- The computable sparse normal form represents the same actual vector. -/
theorem monsterNortonSparseNormalize_evaluate (b : ℕ → E) (l : monsterNortonSparseState) :
    monsterNortonSparseEvaluate b (monsterNortonSparseNormalize l) =
      monsterNortonSparseEvaluate b l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨k,c⟩
    rw [monsterNortonSparseNormalize, monsterNortonSparseInsert_evaluate, ih, evaluate_cons]

/-- Exact rational scaling agrees with scalar multiplication in the actual real space. -/
theorem monsterNortonSparseScale_evaluate (b : ℕ → E) (c : ℚ) (l : monsterNortonSparseState) :
    monsterNortonSparseEvaluate b (monsterNortonSparseScale c l) =
      (c : ℝ) • monsterNortonSparseEvaluate b l := by
  induction l with
  | nil => simp [monsterNortonSparseScale, monsterNortonSparseEvaluate]
  | cons p l ih =>
    rcases p with ⟨k,d⟩
    simp only [monsterNortonSparseScale, List.map_cons, evaluate_cons] at *
    rw [ih, Rat.cast_mul, mul_smul, smul_add]

private theorem evaluate_append (b : ℕ → E) (l m : monsterNortonSparseState) :
    monsterNortonSparseEvaluate b (l ++ m) =
      monsterNortonSparseEvaluate b l + monsterNortonSparseEvaluate b m := by
  simp only [monsterNortonSparseEvaluate, List.map_append, List.sum_append]

/-- Checked actual basis images and a finite rational computation determine the actual full step. -/
theorem monsterNortonSparseStep_actual (b : ℕ → E) (f : E →ₗ[ℝ] E)
    (image : ℕ → monsterNortonSparseState) (l : monsterNortonSparseState)
    (h : ∀ p ∈ l, f (b p.1) = monsterNortonSparseEvaluate b (image p.1)) :
    f (monsterNortonSparseEvaluate b l) =
      monsterNortonSparseEvaluate b (monsterNortonSparseStep image l) := by
  rw [monsterNortonSparseStep, monsterNortonSparseNormalize_evaluate]
  induction l with
  | nil => simp [monsterNortonSparseEvaluate]
  | cons p l ih =>
    rcases p with ⟨k,c⟩
    rw [evaluate_cons, map_add, map_smul, h (k,c) (by simp)]
    rw [List.flatMap_cons, evaluate_append, monsterNortonSparseScale_evaluate]
    rw [ih (by intro p hp; exact h p (List.mem_cons_of_mem _ hp))]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
