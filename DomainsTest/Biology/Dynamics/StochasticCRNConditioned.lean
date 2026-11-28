/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.StochasticCRNConditioned

/-! Tests for the product-form law conditioned on a stoichiometric compatibility class.

* The isomerization `A ⇌ B` with rate constants `κ = (2, 1)`: `c = (1, 2)` and `d = (2, 4)` are
  complex balanced (checked from the definition). Its compatibility class through `(n, 0)` is
  the set of states with total count `n`, membership and non-membership being checked from the
  definition of the stoichiometric subspace.
* The conditioned law at `(1, 1)` on the class of total count `2`, computed by hand from the
  three Poisson weights, is `2 c₀ c₁ / (c₀ + c₁)²`, which is `4 / 9` for both `c` and `d`. The
  multinomial formula `conditionedLaw_totalClass` and the equality of laws
  `conditionedLaw_totalClass_eq_multinomialReal` give the same `4 / 9`, and
  `conditionedLaw_compatClass_eq` applies with its hypotheses discharged.
* Boundaries: conditioned on the empty set the law is `0` and does not sum to `1`, so the
  nonemptiness hypothesis of `hasSum_conditionedLaw` is needed; conditioned on the single state
  `(1, 1)`, which is not reaction-closed, the law violates the master equation at `(1, 1)`, so
  the closure hypothesis of `isStationaryMasterSolution_conditionedLaw` is needed. -/

namespace MathlibExtTest.Biology.Dynamics.StochasticCRNConditioned

open MathlibExt.Biology.Dynamics.ComplexBalanced MathlibExt.Biology.Dynamics.SystemsBiology
  MathlibExt.Biology.Dynamics.StochasticCRNErgodicity
  MathlibExt.Biology.Dynamics.StochasticCRNConditioned

/-- The isomerization `A ⇌ B`: reaction `0` is `A → B`, reaction `1` is `B → A`. -/
def iso : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

/-- Rate constants `κ = (2, 1)`. -/
noncomputable def κIso : Fin 2 → ℝ := ![2, 1]

/-- Concentrations `c = (1, 2)`. -/
noncomputable def cIso : Fin 2 → ℝ := ![1, 2]

/-- Concentrations `d = (2, 4)`. -/
noncomputable def dIso : Fin 2 → ℝ := ![2, 4]

theorem cIso_pos : ∀ s, 0 < cIso s := fun s => by fin_cases s <;> norm_num [cIso]

theorem dIso_pos : ∀ s, 0 < dIso s := fun s => by fin_cases s <;> norm_num [dIso]

theorem κIso_pos : ∀ r, 0 < κIso r := fun r => by fin_cases r <;> norm_num [κIso]

/-! ### Complex balance from the definition -/

theorem rate_iso (c : Fin 2 → ℝ) : iso.rate κIso c 0 = 2 * c 0 ∧ iso.rate κIso c 1 = c 1 := by
  simp [ReactionNetwork.rate, iso, κIso, Fin.prod_univ_two]

/-- `c` is complex balanced for `κ = (2, 1)` exactly when the flux `2 c₀` of `A → B` equals the
flux `c₁` of `B → A`; checked at every complex from the definition. -/
theorem isComplexBalanced_iso {c : Fin 2 → ℝ} (h : 2 * c 0 = c 1) :
    iso.IsComplexBalanced κIso c := by
  intro z
  obtain ⟨h0, h1⟩ := rate_iso c
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two, h0, h1]
  have e0 : iso.src 0 = iso.prod 1 := rfl
  have e1 : iso.src 1 = iso.prod 0 := rfl
  rw [e0, e1]
  by_cases ha : iso.prod 1 = z <;> by_cases hb : iso.prod 0 = z <;> simp [ha, hb, h]

theorem isComplexBalanced_cIso : iso.IsComplexBalanced κIso cIso :=
  isComplexBalanced_iso (by norm_num [cIso])

theorem isComplexBalanced_dIso : iso.IsComplexBalanced κIso dIso :=
  isComplexBalanced_iso (by norm_num [dIso])

/-! ### The compatibility class through `(n, 0)` -/

/-- Every vector of the stoichiometric subspace of `A ⇌ B` has coordinate sum `0`. -/
theorem sum_eq_zero_of_mem {v : Fin 2 → ℝ} (hv : v ∈ iso.stoichiometricSubspace) :
    v 0 + v 1 = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨r, rfl⟩ := hv
    fin_cases r <;> norm_num [iso]
  | zero => simp
  | add u w _ _ hu hw => simp only [Pi.add_apply]; linarith
  | smul a u _ hu => simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, hu, mul_zero]

/-- `(1, 1)` is in the class of `(2, 0)`: the difference `(-1, 1)` is the reaction vector of
`A → B`. -/
theorem mem_compatClass_one_one : ![1, 1] ∈ compatClass iso ![2, 0] := by
  change (fun s => ((![1, 1] : Fin 2 → ℕ) s : ℝ) - (![2, 0] : Fin 2 → ℕ) s) ∈
    iso.stoichiometricSubspace
  refine Submodule.subset_span ⟨0, ?_⟩
  funext s
  fin_cases s <;> norm_num [iso]

/-- `(2, 1)` is not in the class of `(2, 0)`: the difference `(0, 1)` has coordinate sum `1`. -/
theorem notMem_compatClass_two_one : ![2, 1] ∉ compatClass iso ![2, 0] := by
  intro h
  have := sum_eq_zero_of_mem
    (v := fun s => ((![2, 1] : Fin 2 → ℕ) s : ℝ) - (![2, 0] : Fin 2 → ℕ) s) h
  norm_num at this

/-- The class of `(n, 0)` is the set of states with total count `n`. -/
theorem compatClass_iso_eq (n : ℕ) : compatClass iso ![n, 0] = totalClass n := by
  ext x
  constructor
  · intro hx
    have h := sum_eq_zero_of_mem (v := fun s => (x s : ℝ) - (![n, 0] : Fin 2 → ℕ) s) hx
    change ∑ s, x s = n
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_zero, sub_zero] at h
    exact_mod_cast (by linarith : (x 0 : ℝ) + x 1 = n)
  · intro hx
    change ∑ s, x s = n at hx
    rw [Fin.sum_univ_two] at hx
    have hx' : (x 0 : ℝ) + x 1 = n := by exact_mod_cast hx
    change (fun s => (x s : ℝ) - (![n, 0] : Fin 2 → ℕ) s) ∈ iso.stoichiometricSubspace
    have hv := iso.stoichiometricSubspace.smul_mem (x 1 : ℝ)
      (Submodule.subset_span ⟨0, rfl⟩ :
        (fun s => (iso.prod 0 s : ℝ) - iso.src 0 s) ∈ iso.stoichiometricSubspace)
    convert hv using 1
    funext s
    fin_cases s
    · simp [iso]
      linarith
    · simp [iso]

/-! ### The conditioned law on total count `2`, by hand -/

theorem poissonWeight_pair (c : Fin 2 → ℝ) (a b : ℕ) :
    poissonWeight c ![a, b] = (Real.exp (-c 0) * Real.exp (-c 1)) *
      (c 0 ^ a * c 1 ^ b / ((a.factorial : ℝ) * b.factorial)) := by
  simp only [poissonWeight, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- A state with total count `2` is `(2, 0)`, `(1, 1)` or `(0, 2)`. -/
theorem mem_three_of_sum {y : Fin 2 → ℕ} (hy : y 0 + y 1 = 2) :
    y ∈ ({![2, 0], ![1, 1], ![0, 2]} : Finset (Fin 2 → ℕ)) := by
  have hy' : y = ![y 0, y 1] := by funext s; fin_cases s <;> rfl
  rw [hy']
  rcases (by omega : (y 0 = 2 ∧ y 1 = 0) ∨ (y 0 = 1 ∧ y 1 = 1) ∨ (y 0 = 0 ∧ y 1 = 2)) with
    ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]

/-- The mass of total count `2`, summed over the three states directly. -/
theorem classMass_totalClass_two (c : Fin 2 → ℝ) :
    classMass c (totalClass 2) =
      poissonWeight c ![2, 0] + poissonWeight c ![1, 1] + poissonWeight c ![0, 2] := by
  rw [classMass, tsum_eq_sum (s := {![2, 0], ![1, 1], ![0, 2]}) fun y hy =>
    Set.indicator_of_notMem (fun h => hy (mem_three_of_sum
      (by simpa [totalClass, Fin.sum_univ_two] using h))) _]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [totalClass, Fin.sum_univ_two, add_assoc]

/-- By hand: the conditioned law of `(1, 1)` given total count `2` is `2 c₀ c₁ / (c₀ + c₁)²`. -/
theorem conditionedLaw_one_one {c : Fin 2 → ℝ} (hc : ∀ s, 0 < c s) :
    conditionedLaw c (totalClass 2) ![1, 1] * (c 0 + c 1) ^ 2 = 2 * c 0 * c 1 := by
  have hZ : poissonWeight c ![2, 0] + poissonWeight c ![1, 1] + poissonWeight c ![0, 2] ≠ 0 :=
    (add_pos (add_pos (poissonWeight_pos hc _) (poissonWeight_pos hc _))
      (poissonWeight_pos hc _)).ne'
  rw [conditionedLaw, Set.indicator_of_mem (show (![1, 1] : Fin 2 → ℕ) ∈ totalClass 2 by
    simp [totalClass, Fin.sum_univ_two]), classMass_totalClass_two, div_mul_eq_mul_div,
    div_eq_iff hZ]
  simp only [poissonWeight_pair, Nat.factorial_two, Nat.factorial_one, Nat.factorial_zero,
    Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_one]
  ring

theorem conditionedLaw_cIso_one_one : conditionedLaw cIso (totalClass 2) ![1, 1] = 4 / 9 := by
  have h := conditionedLaw_one_one cIso_pos
  rw [show cIso 0 = 1 from rfl, show cIso 1 = 2 from rfl] at h
  norm_num at h
  linarith

theorem conditionedLaw_dIso_one_one : conditionedLaw dIso (totalClass 2) ![1, 1] = 4 / 9 := by
  have h := conditionedLaw_one_one dIso_pos
  rw [show dIso 0 = 2 from rfl, show dIso 1 = 4 from rfl] at h
  norm_num at h
  linarith

/-! ### The theorems agree with the hand computation -/

/-- The multinomial formula gives the hand value `4 / 9`: `2! / (1! 1!) · (1/3) · (2/3)`. -/
theorem multinomial_cIso_one_one :
    conditionedLaw cIso (totalClass 2) ![1, 1] = 4 / 9 := by
  have h := conditionedLaw_totalClass cIso_pos ![1, 1]
  have hs : ∑ s, (![1, 1] : Fin 2 → ℕ) s = 2 := by simp [Fin.sum_univ_two]
  have hm : Nat.multinomial Finset.univ (![1, 1] : Fin 2 → ℕ) = 2 := by
    simp [Nat.multinomial, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [hs, hm] at h
  rw [h]
  norm_num [Fin.prod_univ_two, Fin.sum_univ_two, cIso]

/-- The equality with `ProbabilityTheory.multinomialReal` gives the same `4 / 9` on the support,
and `0` off it, where `conditionedLaw_totalClass` does not apply. -/
theorem multinomialReal_cIso_one_one :
    conditionedLaw cIso (totalClass 2) ![1, 1] = 4 / 9 ∧
      conditionedLaw cIso (totalClass 3) ![1, 1] = 0 := by
  have hm : Nat.multinomial Finset.univ (![1, 1] : Fin 2 → ℕ) = 2 := by
    simp [Nat.multinomial, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [conditionedLaw_totalClass_eq_multinomialReal cIso_pos,
    conditionedLaw_totalClass_eq_multinomialReal cIso_pos]
  refine ⟨?_, ProbabilityTheory.multinomialReal_of_sum_ne (by simp [Fin.sum_univ_two])⟩
  rw [ProbabilityTheory.multinomialReal, ite_eq_left (by simp [Fin.sum_univ_two]), hm]
  norm_num [Fin.prod_univ_two, Fin.sum_univ_two, cIso]

/-- `A ⇌ B` conserves the total count, so total count `n` is reaction-closed. -/
theorem iso_conserves (r : Fin 2) : ∑ s, iso.src r s = ∑ s, iso.prod r s := by
  fin_cases r <;> simp [iso, Fin.sum_univ_two]

/-- The equilibrium-independence theorem applies to `c` and `d` (its hypotheses are discharged),
and its conclusion matches the two hand computations. -/
theorem conditionedLaw_dIso_eq_cIso (n : ℕ) :
    conditionedLaw dIso (totalClass n) = conditionedLaw cIso (totalClass n) := by
  rw [← compatClass_iso_eq n]
  exact conditionedLaw_compatClass_eq κIso_pos cIso_pos dIso_pos isComplexBalanced_cIso
    isComplexBalanced_dIso _

example : conditionedLaw dIso (totalClass 2) ![1, 1] =
    conditionedLaw cIso (totalClass 2) ![1, 1] := by
  rw [conditionedLaw_dIso_one_one, conditionedLaw_cIso_one_one]

/-- The conditioned-product-form theorem applies to `A ⇌ B` on the class of `(2, 0)`. -/
example : HasSum (conditionedLaw cIso (compatClass iso ![2, 0])) 1 ∧
    IsStationaryMasterSolution iso κIso (conditionedLaw cIso (compatClass iso ![2, 0])) :=
  let h := conditionedLaw_spec cIso_pos isComplexBalanced_cIso ![2, 0]
  ⟨h.2.2.1, h.2.2.2⟩

example (n : ℕ) : IsReactionClosed iso (totalClass n) :=
  isReactionClosed_totalClass iso iso_conserves n

/-! ### Boundaries -/

/-- Conditioned on the empty set the law is `0`, which does not sum to `1`. -/
theorem not_hasSum_conditionedLaw_empty (c : Fin 2 → ℝ) :
    ¬ HasSum (conditionedLaw c ∅) 1 := by
  have h0 : conditionedLaw c ∅ = 0 := funext fun x => by simp [conditionedLaw]
  rw [h0]
  intro h
  have := h.unique hasSum_zero
  norm_num at this

/-- Conditioned on the single state `(1, 1)`, which is not reaction-closed, the law puts mass
`1` on `(1, 1)` and violates the master equation there: the outflow is `1 · (2 + 1)` and both
predecessors `(2, 0)` and `(0, 2)` carry mass `0`. -/
theorem not_master_singleton :
    ¬ IsStationaryMasterSolution iso κIso (conditionedLaw cIso {![1, 1]}) := by
  intro h
  have h11 := h ![1, 1]
  have hp : conditionedLaw cIso {![1, 1]} ![1, 1] = 1 := by
    rw [conditionedLaw, Set.indicator_of_mem (Set.mem_singleton _), classMass,
      tsum_eq_single (f := ({![1, 1]} : Set (Fin 2 → ℕ)).indicator (poissonWeight cIso)) ![1, 1]
        fun y hy => Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hy) _,
      Set.indicator_of_mem (Set.mem_singleton _), div_self (poissonWeight_pos cIso_pos _).ne']
  have hq : ∀ y, y ≠ ![1, 1] → conditionedLaw cIso {![1, 1]} y = 0 := fun y hy => by
    simp [conditionedLaw, hy]
  rw [hp, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_two,
    hq (unfire iso 0 ![1, 1]) (by decide), hq (unfire iso 1 ![1, 1]) (by decide)] at h11
  norm_num [propensity, iso, κIso, Fin.prod_univ_two, ReactionNetwork.propensity] at h11

end MathlibExtTest.Biology.Dynamics.StochasticCRNConditioned
