/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Privacy.DifferentialPrivacy

/-!
# Discrete differential privacy regression tests

These kernel-checked examples exercise normalized PMFs, deterministic maps,
and bounded adjacency. They are analytic proofs, not sampler executions.
-/

open CSLibExt.Privacy.DifferentialPrivacy
open scoped NNReal ENNReal

namespace CSLibExtTest.Privacy.DifferentialPrivacy

-- Empty databases are adjacent, without choosing an element of `Fin 0`.
example (d d' : Fin 0 → ℕ) : ReplaceOne d d' := by
  intro i
  exact Fin.elim0 i

-- Every pair of singleton databases is adjacent.
example (d d' : Fin 1 → ℕ) : ReplaceOne d d' := by
  intro i _ j _
  exact Subsingleton.elim i j

example (d : Fin 3 → ℕ) : ReplaceOne d d := ReplaceOne.refl d

example {d d' : Fin 3 → ℕ} (h : ReplaceOne d d') :
    ReplaceOne d' d := h.symm

-- One genuine change is accepted; two distinct changes are rejected.
example : ReplaceOne (fun _ : Fin 2 => false) (fun i => i == 0) := by
  intro i hi j hj
  have hi0 : i = 0 := by simpa using hi
  have hj0 : j = 0 := by simpa using hj
  exact hi0.trans hj0.symm

example : ¬ReplaceOne (fun _ : Fin 2 => false) (fun _ => true) := by
  intro h
  have bad : (0 : Fin 2) = 1 := h (by decide) (by decide)
  exact (by decide : (0 : Fin 2) ≠ 1) bad

-- PMF carries normalization before and after every deterministic map.
example {D O : Type*} (M : D → PMF O) (d : D) :
    ∑' o, M d o = 1 := (M d).tsum_coe

example {D O O' : Type*} (M : D → PMF O) (g : O → O') (d : D) :
    ∑' o', postProcess g M d o' = 1 := (postProcess g M d).tsum_coe

example {D O : Type*} (M : D → PMF O) : postProcess id M = M := by
  funext d
  exact PMF.map_id (M d)

example {D O O' : Type*} (M : D → PMF O) (o' : O') :
    postProcess (fun _ => o') M = fun _ => PMF.pure o' := by
  funext d
  exact PMF.map_const (M d) o'

-- A permutation followed by its inverse recovers the original distribution.
example {D O : Type*} (M : D → PMF O) (e : O ≃ O) :
    postProcess e.symm (postProcess e M) = M := by
  funext d
  simp only [postProcess, PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]

-- Any input-independent distribution has zero privacy budget.
example {D O : Type*} (p : PMF O) (adj : D → D → Prop) :
    IsDP (fun _ => p) adj 0 := isDP_const p adj

-- Nonuniform mass distinguishes merging from simply retaining one preimage.
private noncomputable def threePoint : PMF (Fin 3) :=
  PMF.ofFintype (fun i =>
    ((if i = 0 then 1 / 2 else 1 / 4 : ℝ≥0) : ℝ≥0∞)) (by
      norm_cast
      norm_num [Fin.sum_univ_succ])

example : ∑' i, threePoint i = 1 := threePoint.tsum_coe

example : threePoint 0 = 1 / 2 ∧ threePoint 1 = 1 / 4 ∧
    threePoint 2 = 1 / 4 := by
  norm_num [threePoint]

-- Indices 1 and 2 merge; both of their masses must contribute.
example : postProcess (fun i : Fin 3 => i == 0)
    (fun _ : Unit => threePoint) () false = 1 / 2 := by
  change (threePoint.map (fun i : Fin 3 => i == 0)) false = 1 / 2
  rw [PMF.map_apply, tsum_fintype]
  norm_num [Fin.sum_univ_succ, threePoint]
  simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    (by norm_num : (2 : ℝ≥0) * 4⁻¹ = 2⁻¹)

example : postProcess (fun i : Fin 3 => i == 0)
    (fun _ : Unit => threePoint) () true = 1 / 2 := by
  change (threePoint.map (fun i : Fin 3 => i == 0)) true = 1 / 2
  rw [PMF.map_apply, tsum_fintype]
  norm_num [Fin.sum_univ_succ, threePoint]

example : postProcess (fun _ : Fin 3 => ())
    (fun _ : Bool => threePoint) false () = 1 := by
  change (threePoint.map (Function.const (Fin 3) ())) () = 1
  rw [PMF.map_const, PMF.pure_apply_self]

example : IsDP (fun _ : Fin 2 → Bool => threePoint) ReplaceOne 0 :=
  isDP_const threePoint ReplaceOne

-- The preservation theorem also applies to a many-to-one map.
example : IsDP (postProcess (fun i : Fin 3 => i == 0)
    (fun _ : Fin 2 → Bool => threePoint)) ReplaceOne 0 :=
  isDP_postProcess (isDP_const threePoint ReplaceOne) _

-- Exercise both directions of the event equivalence through the public API.
example : IsDPEvent (fun _ : Bool => threePoint) (fun _ _ => True) 0 :=
  isDP_iff_isDPEvent.mp (isDP_const threePoint _)

example {D O : Type*} {M : D → PMF O} {adj : D → D → Prop} {ε : ℝ}
    (h : IsDPEvent M adj ε) : IsDP M adj ε :=
  isDP_iff_isDPEvent.mpr h

-- Releasing the sole row exactly is not private for any finite real budget.
private theorem identity_not_private (ε : ℝ) :
    ¬IsDP (fun d : Fin 1 → Bool => PMF.pure (d 0)) ReplaceOne ε := by
  intro h
  have hadj : ReplaceOne (fun _ : Fin 1 => false) (fun _ => true) := by
    intro i _ j _
    exact Subsingleton.elim i j
  have bad := h.2 (fun _ => false) (fun _ => true) hadj false
  simp only [PMF.pure_apply, ite_true, Bool.false_eq_true, ite_false,
    mul_zero, nonpos_iff_eq_zero, one_ne_zero] at bad

example (ε : ℝ) :
    ¬IsDPEvent (fun d : Fin 1 → Bool => PMF.pure (d 0)) ReplaceOne ε := by
  intro h
  exact identity_not_private ε (isDP_iff_isDPEvent.mpr h)

-- Constant postprocessing can make even that nonprivate mechanism private.
example : IsDP (postProcess (fun _ : Bool => ())
    (fun d : Fin 1 → Bool => PMF.pure (d 0))) ReplaceOne 0 := by
  change IsDP (fun d : Fin 1 → Bool =>
    (PMF.pure (d 0)).map (fun _ => ())) ReplaceOne 0
  simpa only [PMF.pure_map] using isDP_const (PMF.pure ()) ReplaceOne

-- Negative budgets are excluded even for an empty adjacency relation.
example : ¬IsDP (fun _ : Bool => threePoint) (fun _ _ => False) (-1) := by
  intro h
  exact (by norm_num : ¬(0 : ℝ) ≤ -1) h.1

-- A database-dependent randomized response needs a positive budget.
private noncomputable def randomizedResponse (d : Bool) : PMF Bool :=
  PMF.ofFintype (fun o =>
    ((if o = d then 3 / 4 else 1 / 4 : ℝ≥0) : ℝ≥0∞)) (by
      norm_cast
      cases d <;> norm_num)

private theorem randomizedResponse_private :
    IsDP randomizedResponse (fun _ _ => True) (Real.log 3) := by
  refine ⟨Real.log_nonneg (by norm_num), fun d d' _ o => ?_⟩
  rw [Real.exp_log (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  have h : (if o = d then 3 / 4 else 1 / 4 : ℝ≥0) ≤
      3 * (if o = d' then 3 / 4 else 1 / 4 : ℝ≥0) := by
    cases d <;> cases d' <;> cases o <;>
      norm_num [← NNReal.coe_le_coe]
  simpa only [randomizedResponse, PMF.ofFintype_apply, ENNReal.coe_mul,
    ENNReal.coe_ofNat] using ENNReal.coe_le_coe.mpr h

example : ¬IsDP randomizedResponse (fun _ _ => True) 0 := by
  intro h
  have bad := h.2 false true trivial false
  have hmass : ((3 / 4 : ℝ≥0) : ℝ≥0∞) ≤ (1 / 4 : ℝ≥0) := by
    simpa only [randomizedResponse, PMF.ofFintype_apply, Real.exp_zero,
      ENNReal.ofReal_one, one_mul, ite_true, Bool.false_eq_true,
      ite_false] using bad
  have hreal := ENNReal.coe_le_coe.mp hmass
  norm_num [← NNReal.coe_le_coe] at hreal

example : IsDPEvent randomizedResponse (fun _ _ => True) (Real.log 3) :=
  isDP_iff_isDPEvent.mp randomizedResponse_private

example : IsDP (postProcess Bool.not randomizedResponse)
    (fun _ _ => True) (Real.log 3) :=
  isDP_postProcess randomizedResponse_private Bool.not

end CSLibExtTest.Privacy.DifferentialPrivacy
