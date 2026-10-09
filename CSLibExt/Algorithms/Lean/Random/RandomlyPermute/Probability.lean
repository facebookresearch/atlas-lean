/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Random.RandomlyPermute.Basic
public import Cslib.Probability.PMF
import all CSLibExt.Algorithms.Lean.Random.RandomlyPermute.Correctness
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact ideal-oracle law for the Fisher–Yates executor

Uniform sampling of the complete dependent legal draw history is mapped through
the same saved-vector executor. This definition is not an executable PRNG and
does not assume that output permutations are uniform.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

namespace Cslib.Algorithms.Lean.TimeM

universe u

open scoped BigOperators

private theorem history_card (n : Nat) :
    Fintype.card ((i : Fin n) → Fin (n - i.val)) = n.factorial := by
  have hprod : (∏ i : Fin n, (n - i.val)) = n.factorial := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.prod_univ_succ]
      simpa only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_add_right,
        Nat.factorial_succ] using congrArg (fun x => (n + 1) * x) ih
  simpa only [Fintype.card_pi, Fintype.card_fin] using hprod

private theorem positionPerm_bijective (n : Nat) :
    Function.Bijective (positionPerm (n := n)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨positionPerm_injective n, ?_⟩
  rw [history_card, Fintype.card_perm, Fintype.card_fin]

noncomputable section

@[no_expose] private def historyEquiv (n : Nat) :
    ((i : Fin n) → Fin (n - i.val)) ≃ Equiv.Perm (Fin n) :=
  Equiv.ofBijective positionPerm (positionPerm_bijective n)

private theorem historyEquiv_left_inv (n : Nat) (draws : (i : Fin n) → Fin (n - i.val)) :
    (historyEquiv n).symm (historyEquiv n draws) = draws :=
  (historyEquiv n).symm_apply_apply draws

private theorem historyEquiv_right_inv (n : Nat) (σ : Equiv.Perm (Fin n)) :
    historyEquiv n ((historyEquiv n).symm σ) = σ :=
  (historyEquiv n).apply_symm_apply σ

private theorem output_reindex {α : Type u} {n : Nat} (xs : Vector α n)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    randomlyPermute xs draws =
      ⟨Vector.ofFn (fun p => xs[(positionPerm draws p).val]), (n, n)⟩ := by
  apply TimeM.ext
  · have hinput : (Vector.ofFn fun p : Fin n => p).map (fun p => xs[p.val]) = xs := by
      ext p
      simp
    have h := scan_map (fun p : Fin n => xs[p.val]) draws 0 (Vector.ofFn fun p : Fin n => p)
    rw [hinput] at h
    change (randomlyPermute xs draws).ret =
      (randomlyPermute (Vector.ofFn fun p : Fin n => p) draws).ret.map (fun p => xs[p.val]) at h
    rw [positionPerm_eq] at h
    rw [h]
    ext p
    simp
  · exact randomlyPermute_time xs draws

private theorem uniform_output {α : Type u} {n : Nat}
    [Nonempty ((i : Fin n) → Fin (n - i.val))] (xs : Vector α n) :
    (PMF.uniformOfFintype ((i : Fin n) → Fin (n - i.val))).map (randomlyPermute xs) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
        (fun σ => (⟨Vector.ofFn (fun p => xs[(σ p).val]), (n, n)⟩ :
          Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n))) := by
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv (historyEquiv n)]
  rw [PMF.map_comp]
  congr 1
  funext draws
  exact output_reindex xs draws

private theorem uniform_pair {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    ((PMF.uniformOfFintype α).bind fun a =>
      (PMF.uniformOfFintype β).bind fun b => PMF.pure (a, b)) =
      PMF.uniformOfFintype (α × β) := by
  ext x
  rw [Cslib.Probability.PMF.bind_pair_apply]
  simp [Fintype.card_prod, ENNReal.mul_inv]

@[no_expose] private def historyConsEquiv (n : Nat) :
    (Fin (n + 1) × ((i : Fin n) → Fin (n - i.val))) ≃
      ((i : Fin (n + 1)) → Fin (n + 1 - i.val)) :=
  (Equiv.prodCongr (Fin.castOrderIso (by simp)).toEquiv
    (Equiv.piCongrRight fun i : Fin n =>
      (Fin.castOrderIso (show n - i.val = n + 1 - i.succ.val by
        rw [Fin.val_succ]
        omega)).toEquiv)).trans
    (Fin.consEquiv (fun i : Fin (n + 1) => Fin (n + 1 - i.val)))

/- The tail distribution is independent of the head draw. These are PMF proof data,
not a second saved-vector executor or a public sampler API. -/
@[no_expose] private def sequentialHistory :
    (n : Nat) → PMF ((i : Fin n) → Fin (n - i.val))
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | n + 1 => (PMF.uniformOfFintype (Fin (n + 1))).bind fun head =>
      (sequentialHistory n).map fun tail => historyConsEquiv n (head, tail)

private theorem sequentialHistory_eq_uniform (n : Nat)
    [h : Nonempty ((i : Fin n) → Fin (n - i.val))] :
    sequentialHistory n = PMF.uniformOfFintype ((i : Fin n) → Fin (n - i.val)) := by
  induction n generalizing h with
  | zero =>
    ext draws
    simp [sequentialHistory, PMF.pure_apply,
      Subsingleton.elim draws (fun i => Fin.elim0 i)]
  | succ n ih =>
    let : Nonempty ((i : Fin n) → Fin (n - i.val)) := ⟨fun i => ⟨0, by omega⟩⟩
    rw [sequentialHistory, ih]
    calc
      _ = ((PMF.uniformOfFintype (Fin (n + 1))).bind fun head =>
          (PMF.uniformOfFintype ((i : Fin n) → Fin (n - i.val))).bind
            fun tail => PMF.pure (head, tail)).map (historyConsEquiv n) := by
        simp only [PMF.map_bind, PMF.pure_map]
        rfl
      _ = (PMF.uniformOfFintype
          (Fin (n + 1) × ((i : Fin n) → Fin (n - i.val)))).map (historyConsEquiv n) := by
        rw [uniform_pair]
      _ = _ := Cslib.Probability.PMF.uniformOfFintype_map_equiv (historyConsEquiv n)

private theorem history_weight (n : Nat) :
    (∏ i : Fin n, ((n - i.val : Nat) : ENNReal)⁻¹) = (n.factorial : ENNReal)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have ht : (∏ i : Fin n, ((n + 1 - i.succ.val : Nat) : ENNReal)⁻¹) =
        (n.factorial : ENNReal)⁻¹ := by
      simpa only [Fin.val_succ, Nat.add_sub_add_right] using ih
    rw [ht]
    simp [Nat.factorial_succ, ENNReal.mul_inv]

private theorem sequentialHistory_weight (n : Nat)
    (draws : (i : Fin n) → Fin (n - i.val)) :
    sequentialHistory n draws = ∏ i : Fin n, ((n - i.val : Nat) : ENNReal)⁻¹ := by
  let : Nonempty ((i : Fin n) → Fin (n - i.val)) := ⟨fun i => ⟨0, by omega⟩⟩
  rw [sequentialHistory_eq_uniform, PMF.uniformOfFintype_apply, history_card, history_weight]

open scoped Classical in
private theorem independent_output_apply {α : Type u} {n : Nat} (xs : Vector α n)
    (out : Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n)) :
    ((sequentialHistory n).map (randomlyPermute xs)) out =
      ∑ draws : (i : Fin n) → Fin (n - i.val),
        if out = randomlyPermute xs draws
        then ∏ i : Fin n, ((n - i.val : Nat) : ENNReal)⁻¹ else 0 := by
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [sequentialHistory_weight]

private theorem fixed_prefix_card {n k : Nat} (hkn : k ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ p : Fin k, σ (Fin.castLE hkn p) = Fin.castLE hkn p} = (n - k).factorial := by
  classical
  have hc : Fintype.card {p : Fin n // k ≤ p.val} = n - k := by
    have h := Fintype.card_subtype_compl (fun p : Fin n => p.val < k)
    simpa only [not_lt, Fintype.card_fin, Fintype.card_subtype,
      Fin.card_filter_val_lt, min_eq_right hkn] using h
  let e : Equiv.Perm {p : Fin n // k ≤ p.val} ≃
      {σ : Equiv.Perm (Fin n) // ∀ p : Fin k, σ (Fin.castLE hkn p) = Fin.castLE hkn p} :=
    (Equiv.Perm.subtypeEquivSubtypePerm (fun p : Fin n => k ≤ p.val)).trans
    (Equiv.subtypeEquivRight fun σ => by
      constructor
      · intro h p
        exact h (Fin.castLE hkn p) (by simpa only [Fin.val_castLE] using p.isLt.not_ge)
      · intro h p hp
        have hpk : p.val < k := Nat.lt_of_not_ge hp
        have heq : Fin.castLE hkn (⟨p.val, hpk⟩ : Fin k) = p := Fin.ext rfl
        simpa only [heq] using h ⟨p.val, hpk⟩)
  rw [← Fintype.card_congr e, Fintype.card_perm, hc]

private theorem arbitrary_prefix_card {n k : Nat} (hkn : k ≤ n)
    (a : Fin k → Fin n) (hinj : Function.Injective a) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ p : Fin k, σ (Fin.castLE hkn p) = a p} = (n - k).factorial := by
  classical
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hkn) a
    (fun _ _ h => Fin.ext (congrArg (fun p : Fin n => p.val) h)) hinj
  let e : {σ : Equiv.Perm (Fin n) //
      ∀ p : Fin k, σ (Fin.castLE hkn p) = Fin.castLE hkn p} ≃
      {σ : Equiv.Perm (Fin n) // ∀ p : Fin k, σ (Fin.castLE hkn p) = a p} :=
    (Equiv.mulLeft ρ).subtypeEquiv fun σ => by
      constructor
      · intro h p
        change ρ (σ (Fin.castLE hkn p)) = a p
        rw [h p, hρ p]
      · intro h p
        apply ρ.injective
        rw [hρ p]
        exact h p
  rw [← Fintype.card_congr e, fixed_prefix_card hkn]

private theorem uniform_prefix_mass {n k : Nat} (hkn : k ≤ n)
    (a : Fin k → Fin n) (hinj : Function.Injective a) :
    (∑ σ : Equiv.Perm (Fin n),
      if ∀ p : Fin k, σ (Fin.castLE hkn p) = a p
      then (n.factorial : ENNReal)⁻¹ else 0) =
        ((n - k).factorial : ENNReal) / n.factorial := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype, arbitrary_prefix_card hkn a hinj]
  rfl

/-- The ideal-oracle distribution of the actual Fisher–Yates computation,
obtained from uniform complete legal suffix-draw histories. -/
public def randomlyPermuteDistribution {α : Type u} {n : Nat}
    (xs : Vector α n) : PMF (Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n)) := by
  letI : Nonempty ((i : Fin n) → Fin (n - i.val)) := ⟨fun i => ⟨0, by omega⟩⟩
  exact (PMF.uniformOfFintype ((i : Fin n) → Fin (n - i.val))).map (randomlyPermute xs)

private theorem distribution_eq_sequential {α : Type u} {n : Nat} (xs : Vector α n) :
    randomlyPermuteDistribution xs = (sequentialHistory n).map (randomlyPermute xs) := by
  let : Nonempty ((i : Fin n) → Fin (n - i.val)) := ⟨fun i => ⟨0, by omega⟩⟩
  rw [sequentialHistory_eq_uniform]
  rfl

open scoped Classical in
/-- The mass of a full actual output is the sum of its independent suffix-draw
history weights. Repeated values coalesce, and impossible event counts receive no mass. -/
public theorem randomlyPermuteDistribution_apply {α : Type u} {n : Nat} (xs : Vector α n)
    (out : Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n)) :
    randomlyPermuteDistribution xs out =
      ∑ draws : (i : Fin n) → Fin (n - i.val),
        if out = randomlyPermute xs draws
        then ∏ i : Fin n, ((n - i.val : Nat) : ENNReal)⁻¹ else 0 := by
  rw [distribution_eq_sequential]
  exact independent_output_apply xs out

/-- The actual ideal-oracle computation is the pushforward of the canonical uniform
position permutation. This equation retains the saved vector and the exact same-run cost. -/
public theorem randomlyPermuteDistribution_eq_map_uniform {α : Type u} {n : Nat}
    (xs : Vector α n) :
    randomlyPermuteDistribution xs =
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
        (fun σ => (⟨Vector.ofFn (fun p => xs[(σ p).val]), (n, n)⟩ :
          Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector α n))) := by
  let : Nonempty ((i : Fin n) → Fin (n - i.val)) := ⟨fun i => ⟨0, by omega⟩⟩
  rw [distribution_eq_sequential, sequentialHistory_eq_uniform]
  exact uniform_output xs

/-- Every injective labelled prefix has mass `(n - k)! / n!` in the actual run.
The finite sum uses the proved complete independent-history mass `1 / n!`;
empty and full prefixes are included, with no new probability-event wrapper. -/
public theorem randomlyPermute_prefix_probability {n k : Nat} (hkn : k ≤ n)
    (a : Fin k → Fin n) (hinj : Function.Injective a) :
    (∑ draws : (i : Fin n) → Fin (n - i.val),
      if ∀ p : Fin k,
        (randomlyPermute (Vector.ofFn fun q : Fin n => q) draws).ret[(Fin.castLE hkn p).val] = a p
      then (n.factorial : ENNReal)⁻¹ else 0) =
        ((n - k).factorial : ENNReal) / n.factorial := by
  classical
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        if ∀ p : Fin k, σ (Fin.castLE hkn p) = a p
        then (n.factorial : ENNReal)⁻¹ else 0 := by
      apply Fintype.sum_equiv (historyEquiv n)
      intro draws
      rw [output_reindex]
      simp only [Vector.getElem_ofFn]
      rfl
    _ = _ := uniform_prefix_mass hkn a hinj

end

end Cslib.Algorithms.Lean.TimeM
