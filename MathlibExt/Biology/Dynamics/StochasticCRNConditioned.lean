/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.StochasticCRNErgodicity
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import MathlibExt.Probability.Distributions.Multinomial

/-!
# The product-form law conditioned on a stoichiometric compatibility class

Under stochastic mass-action kinetics a reaction network `N` moves molecule counts
`x ∈ ℕ^S` only along reaction vectors `prod r - src r`, so the chain never leaves the
**stoichiometric compatibility class** `{x ∈ ℕ^S | x - x₀ ∈ 𝒮}` of its initial state `x₀`
(`compatClass`), where `𝒮` is the stoichiometric subspace. When `c` is complex balanced, the
product-form Poisson weights `π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!` solve the stationary
master equation on all of `ℕ^S` (`StochasticCRNErgodicity.isStationaryMasterSolution_poissonWeight`)
and sum to `1` there (`StochasticCRNErgodicity.hasSum_poissonWeight`). A chain started in a
class sees only that class, and its stationary law there is `π_c` conditioned on the class,
`π_c(x) / π_c(Γ)` on `Γ` and `0` off it (Anderson, Craciun & Kurtz 2010, Theorems 4.1–4.2). This
file builds that conditioned law (`conditionedLaw`) and proves its properties.

## Main results

* `isReactionClosed_compatClass`, `mem_compatClass_self`: a compatibility class contains its
  base point and is closed under firing and unfiring reactions (`IsReactionClosed`).
* `hasSum_classMass`, `classMass_pos`: for `c ≥ 0` the mass `π_c(Γ)` of any set of states is a
  convergent sum; for `c > 0` it is positive on a nonempty set.
* `isStationaryMasterSolution_indicator`: restricting a solution of the stationary master
  equation to a reaction-closed set gives a solution.
* `conditionedLaw_spec`: **conditioned product form.** For `c > 0` complex balanced, the law
  `π_c(· | Γ)` on the compatibility class `Γ` of any `x₀` is positive on `Γ`, zero off `Γ`,
  sums to `1`, and solves the stationary master equation on `ℕ^S`.
  `isStationaryMasterSolution_conditionedLaw` holds for every reaction-closed `Γ`;
  `hasSum_conditionedLaw` (sum `1`) additionally needs `c > 0` and `Γ` nonempty, since the law
  conditioned on `∅` is `0`.
* `cond_poissonPMF_singleton`: `conditionedLaw c Γ x` is the probability of `{x}` under the
  measure-theoretic conditioning `μ[· | Γ]` of the product-form law `μ` (`poissonPMF`).
* `conditionedLaw_compatClass_eq`: for positive rate constants, any two positive complex-balanced
  equilibria give the same conditioned law on every compatibility class, so the law depends only
  on the class (`conditionedLaw_compatClass_eq_of_orthogonal` states the orthogonality form).
* `conditionedLaw_coe_finset`: on a finite set the conditioned law is
  `SystemsBiology.classStationaryLaw`, the normalized weights of the finite-class theorem.
* `conditionedLaw_totalClass_eq_multinomialReal`, `isReactionClosed_totalClass`: when every
  reaction conserves the total molecule count, the states with total count `n` form a
  reaction-closed set, and for every `n` the conditioned law there is the multinomial law
  `ProbabilityTheory.multinomialReal n (c / ∑ c)`; on its support
  (`conditionedLaw_totalClass`) this is `n! / ∏_s x_s! · ∏_s (c_s / ∑ c)^{x_s}`.

## Not covered

A compatibility class can split into several irreducible classes of the chain; the conditioned
law on the whole class is stationary but is unique only on an irreducible class, and uniqueness
is not proved here. As in `MathlibExt.Biology.Dynamics.StochasticCRNErgodicity`, stationarity is
the stationary master equation `π Q = 0`; the passage to `π P(t) = π` for the countable-state
chain needs non-explosion and is not treated.

## References

* D. F. Anderson, G. Craciun, T. G. Kurtz, *Product-form stationary distributions for
  deficiency zero chemical reaction networks*, Bull. Math. Biol. 72 (2010) 1947–1970,
  Theorems 4.1–4.2.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Dynamics.StochasticCRNConditioned

open MathlibExt.Biology.Dynamics.ComplexBalanced MathlibExt.Biology.Dynamics.SystemsBiology
  MathlibExt.Biology.Dynamics.StochasticCRNErgodicity

variable {S ρ : Type*}

/-! ### Reaction-closed sets and compatibility classes -/

section Classes

variable (N : ReactionNetwork S ρ)

/-- The stoichiometric compatibility class of `x₀` in `ℕ^S`: the states `x` with
`x - x₀ ∈ 𝒮`, the stoichiometric subspace. -/
def compatClass (x₀ : S → ℕ) : Set (S → ℕ) :=
  {x | (fun s => (x s : ℝ) - x₀ s) ∈ N.stoichiometricSubspace}

/-- A set of states closed under the reactions in both directions: firing a reaction from a
state of `Γ` stays in `Γ`, and so does the unique predecessor along any reaction. -/
structure IsReactionClosed (Γ : Set (S → ℕ)) : Prop where
  /-- Firing a reaction whose source complex fits stays in `Γ`. -/
  fire_mem : ∀ x ∈ Γ, ∀ r, N.src r ≤ x → fire N r x ∈ Γ
  /-- The predecessor along a reaction whose product complex fits lies in `Γ`. -/
  unfire_mem : ∀ x ∈ Γ, ∀ r, N.prod r ≤ x → unfire N r x ∈ Γ

/-- Every reaction vector lies in the stoichiometric subspace. -/
theorem reactionVector_mem (r : ρ) :
    (fun s => (N.prod r s : ℝ) - N.src r s) ∈ N.stoichiometricSubspace :=
  Submodule.subset_span ⟨r, rfl⟩

theorem mem_compatClass_self (x₀ : S → ℕ) : x₀ ∈ compatClass N x₀ := by
  have h : (fun s => (x₀ s : ℝ) - x₀ s) = 0 := funext fun s => sub_self _
  change (fun s => (x₀ s : ℝ) - x₀ s) ∈ N.stoichiometricSubspace
  rw [h]
  exact N.stoichiometricSubspace.zero_mem

/-- A stoichiometric compatibility class is closed under the reactions in both directions. -/
theorem isReactionClosed_compatClass (x₀ : S → ℕ) : IsReactionClosed N (compatClass N x₀) where
  fire_mem x hx r hr := by
    have hx' : (fun s => (x s : ℝ) - x₀ s) ∈ N.stoichiometricSubspace := hx
    have hv := N.stoichiometricSubspace.add_mem hx' (reactionVector_mem N r)
    change (fun s => (fire N r x s : ℝ) - x₀ s) ∈ N.stoichiometricSubspace
    convert hv using 1
    funext s
    simp only [fire, Pi.add_apply]
    rw [Nat.cast_add, Nat.cast_sub (hr s)]
    ring
  unfire_mem x hx r hr := by
    have hx' : (fun s => (x s : ℝ) - x₀ s) ∈ N.stoichiometricSubspace := hx
    have hv := N.stoichiometricSubspace.sub_mem hx' (reactionVector_mem N r)
    change (fun s => (unfire N r x s : ℝ) - x₀ s) ∈ N.stoichiometricSubspace
    convert hv using 1
    funext s
    simp only [unfire, Pi.sub_apply]
    rw [Nat.cast_add, Nat.cast_sub (hr s)]
    ring

/-- The source complex of `r` fits into the predecessor `unfire N r x`. -/
theorem src_le_unfire (r : ρ) (x : S → ℕ) : N.src r ≤ unfire N r x :=
  fun s => by simp [unfire]

/-- The states with total molecule count `n`. -/
def totalClass [Fintype S] (n : ℕ) : Set (S → ℕ) :=
  {x | ∑ s, x s = n}

/-- If every reaction conserves the total molecule count, the states with total count `n`
form a reaction-closed set. -/
theorem isReactionClosed_totalClass [Fintype S]
    (hN : ∀ r, ∑ s, N.src r s = ∑ s, N.prod r s) (n : ℕ) :
    IsReactionClosed N (totalClass (S := S) n) where
  fire_mem x hx r hr := by
    have h1 : ∑ s, (fire N r x s + N.src r s) = ∑ s, (x s + N.prod r s) :=
      Finset.sum_congr rfl fun s _ => by
        have h : N.src r s ≤ x s := hr s
        simp only [fire]
        omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
    have h2 := hN r
    have hx' : ∑ s, x s = n := hx
    change ∑ s, fire N r x s = n
    omega
  unfire_mem x hx r hr := by
    have h1 : ∑ s, (unfire N r x s + N.prod r s) = ∑ s, (x s + N.src r s) :=
      Finset.sum_congr rfl fun s _ => by
        have h : N.prod r s ≤ x s := hr s
        simp only [unfire]
        omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
    have h2 := hN r
    have hx' : ∑ s, x s = n := hx
    change ∑ s, unfire N r x s = n
    omega

end Classes

/-! ### Restricting solutions of the master equation -/

section Master

variable (N : ReactionNetwork S ρ) [Fintype S] [Fintype ρ]

/-- Restricting a solution of the stationary master equation to a reaction-closed set `Γ`
(zero off `Γ`) gives a solution: inside `Γ` every predecessor lies in `Γ`, and outside `Γ` no
predecessor does, since firing from it would enter the complement. -/
theorem isStationaryMasterSolution_indicator {κ : ρ → ℝ} {p : (S → ℕ) → ℝ}
    (hp : IsStationaryMasterSolution N κ p) {Γ : Set (S → ℕ)} (hΓ : IsReactionClosed N Γ) :
    IsStationaryMasterSolution N κ (Γ.indicator p) := by
  intro x
  by_cases hx : x ∈ Γ
  · rw [Set.indicator_of_mem hx, hp x]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Set.indicator_of_mem (hΓ.unfire_mem x hx r (Finset.mem_filter.1 hr).2)]
  · rw [Set.indicator_of_notMem hx, zero_mul]
    refine (Finset.sum_eq_zero fun r hr => ?_).symm
    have hw : unfire N r x ∉ Γ := fun hw => hx <| by
      have h := hΓ.fire_mem _ hw r (src_le_unfire N r x)
      rwa [(fire_eq_iff N (src_le_unfire N r x)).2 ⟨(Finset.mem_filter.1 hr).2, rfl⟩] at h
    rw [Set.indicator_of_notMem hw, zero_mul]

/-- The stationary master equation is linear: dividing a solution by a constant gives a
solution. -/
theorem isStationaryMasterSolution_div_const {κ : ρ → ℝ} {p : (S → ℕ) → ℝ}
    (hp : IsStationaryMasterSolution N κ p) (a : ℝ) :
    IsStationaryMasterSolution N κ (fun x => p x / a) := by
  intro x
  beta_reduce
  rw [div_mul_eq_mul_div, hp x, Finset.sum_div]
  exact Finset.sum_congr rfl fun r _ => by ring

end Master

/-! ### The conditioned law -/

section Conditioned

variable [Fintype S]

/-- The mass `π_c(Γ) = ∑_{x ∈ Γ} π_c(x)` of a set of states under the product-form weights. -/
noncomputable def classMass (c : S → ℝ) (Γ : Set (S → ℕ)) : ℝ :=
  ∑' x, Γ.indicator (poissonWeight c) x

/-- The product-form law conditioned on `Γ`: `π_c(x) / π_c(Γ)` for `x ∈ Γ` and `0` otherwise.
It is a probability law when `c > 0` and `Γ` is nonempty (`hasSum_conditionedLaw`). -/
noncomputable def conditionedLaw (c : S → ℝ) (Γ : Set (S → ℕ)) (x : S → ℕ) : ℝ :=
  Γ.indicator (poissonWeight c) x / classMass c Γ

theorem hasSum_classMass {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) (Γ : Set (S → ℕ)) :
    HasSum (Γ.indicator (poissonWeight c)) (classMass c Γ) :=
  ((hasSum_poissonWeight hc).summable.indicator Γ).hasSum

theorem classMass_nonneg {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) (Γ : Set (S → ℕ)) :
    0 ≤ classMass c Γ :=
  tsum_nonneg fun x => Set.indicator_nonneg (fun y _ => poissonWeight_nonneg hc y) x

/-- For `c > 0` a set containing some state has positive product-form mass. -/
theorem classMass_pos {c : S → ℝ} (hc : ∀ s, 0 < c s) {Γ : Set (S → ℕ)} {x₀ : S → ℕ}
    (hx₀ : x₀ ∈ Γ) : 0 < classMass c Γ := by
  have hc' : ∀ s, 0 ≤ c s := fun s => (hc s).le
  have h := le_hasSum (hasSum_classMass hc' Γ) x₀ fun y _ =>
    Set.indicator_nonneg (fun y _ => poissonWeight_nonneg hc' y) y
  rw [Set.indicator_of_mem hx₀] at h
  exact (poissonWeight_pos hc x₀).trans_le h

theorem conditionedLaw_of_mem (c : S → ℝ) {Γ : Set (S → ℕ)} {x : S → ℕ} (hx : x ∈ Γ) :
    conditionedLaw c Γ x = poissonWeight c x / classMass c Γ := by
  rw [conditionedLaw, Set.indicator_of_mem hx]

theorem conditionedLaw_of_notMem (c : S → ℝ) {Γ : Set (S → ℕ)} {x : S → ℕ} (hx : x ∉ Γ) :
    conditionedLaw c Γ x = 0 := by
  rw [conditionedLaw, Set.indicator_of_notMem hx, zero_div]

theorem conditionedLaw_pos {c : S → ℝ} (hc : ∀ s, 0 < c s) {Γ : Set (S → ℕ)} {x : S → ℕ}
    (hx : x ∈ Γ) : 0 < conditionedLaw c Γ x := by
  rw [conditionedLaw_of_mem c hx]
  exact div_pos (poissonWeight_pos hc x) (classMass_pos hc hx)

/-- For `c > 0` and nonempty `Γ`, the conditioned law sums to `1` over `ℕ^S`. -/
theorem hasSum_conditionedLaw {c : S → ℝ} (hc : ∀ s, 0 < c s) {Γ : Set (S → ℕ)}
    {x₀ : S → ℕ} (hx₀ : x₀ ∈ Γ) : HasSum (conditionedLaw c Γ) 1 := by
  have h := (hasSum_classMass (fun s => (hc s).le) Γ).div_const (classMass c Γ)
  rwa [div_self (classMass_pos hc hx₀).ne'] at h

/-- **Conditioned product form solves the master equation.** If `c` is complex balanced and
`Γ` is reaction-closed, `π_c(· | Γ)` solves the stationary master equation at every state of
`ℕ^S` (for all real `κ` and `c`). -/
theorem isStationaryMasterSolution_conditionedLaw {N : ReactionNetwork S ρ} [Fintype ρ]
    {κ : ρ → ℝ} {c : S → ℝ} (hcb : N.IsComplexBalanced κ c) {Γ : Set (S → ℕ)}
    (hΓ : IsReactionClosed N Γ) : IsStationaryMasterSolution N κ (conditionedLaw c Γ) :=
  isStationaryMasterSolution_div_const N
    (isStationaryMasterSolution_indicator N (isStationaryMasterSolution_poissonWeight N hcb) hΓ)
    (classMass c Γ)

/-- **Stationary law on a compatibility class** (Anderson, Craciun & Kurtz 2010,
Theorems 4.1–4.2). For a complex-balanced `c > 0`, the product-form law conditioned on the
stoichiometric compatibility class `Γ` of any state `x₀` is positive on `Γ`, zero off `Γ`, a
probability law on `ℕ^S`, and a solution of the stationary master equation. -/
theorem conditionedLaw_spec {N : ReactionNetwork S ρ} [Fintype ρ] {κ : ρ → ℝ} {c : S → ℝ}
    (hc : ∀ s, 0 < c s) (hcb : N.IsComplexBalanced κ c) (x₀ : S → ℕ) :
    (∀ x ∈ compatClass N x₀, 0 < conditionedLaw c (compatClass N x₀) x) ∧
      (∀ x ∉ compatClass N x₀, conditionedLaw c (compatClass N x₀) x = 0) ∧
      HasSum (conditionedLaw c (compatClass N x₀)) 1 ∧
      IsStationaryMasterSolution N κ (conditionedLaw c (compatClass N x₀)) :=
  ⟨fun _ hx => conditionedLaw_pos hc hx, fun _ hx => conditionedLaw_of_notMem c hx,
    hasSum_conditionedLaw hc (mem_compatClass_self N x₀),
    isStationaryMasterSolution_conditionedLaw hcb (isReactionClosed_compatClass N x₀)⟩

/-- On a finite set `Ω` the conditioned law is the normalized weight
`SystemsBiology.classStationaryLaw c Ω` of the finite-class theorem. -/
theorem conditionedLaw_coe_finset (c : S → ℝ) (Ω : Finset (S → ℕ)) (x : Ω) :
    conditionedLaw c (Ω : Set (S → ℕ)) x = classStationaryLaw c Ω x := by
  have hZ : classMass c Ω = ∑ y ∈ Ω, poissonWeight c y := by
    rw [classMass, tsum_eq_sum (s := Ω) fun y hy =>
      Set.indicator_of_notMem (mt Finset.mem_coe.1 hy) _]
    exact Finset.sum_congr rfl fun y hy => Set.indicator_of_mem (Finset.mem_coe.2 hy) _
  rw [conditionedLaw_of_mem c (Finset.mem_coe.2 x.2), hZ, classStationaryLaw]

/-! ### The law does not depend on the complex-balanced equilibrium -/

/-- If `π_d = a π_c` on `Γ` for a nonzero constant `a`, the two conditioned laws agree. -/
theorem conditionedLaw_eq_of_forall_mem {Γ : Set (S → ℕ)} {c d : S → ℝ} {a : ℝ} (ha : a ≠ 0)
    (h : ∀ x ∈ Γ, poissonWeight d x = a * poissonWeight c x) :
    conditionedLaw d Γ = conditionedLaw c Γ := by
  have hind : ∀ x, Γ.indicator (poissonWeight d) x = a * Γ.indicator (poissonWeight c) x := by
    intro x
    by_cases hx : x ∈ Γ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h x hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  funext x
  simp only [conditionedLaw, classMass, hind, tsum_mul_left]
  exact mul_div_mul_left _ _ ha

/-- For `c > 0`, `π_c(x) = exp (∑_s (x_s log c_s - c_s)) / ∏_s x_s!`. -/
theorem poissonWeight_eq_exp {c : S → ℝ} (hc : ∀ s, 0 < c s) (x : S → ℕ) :
    poissonWeight c x =
      Real.exp (∑ s, ((x s : ℝ) * Real.log (c s) - c s)) / ∏ s, ((x s).factorial : ℝ) := by
  rw [poissonWeight, Real.exp_sum, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (hc s), Real.exp_neg]
  ring

/-- If `log d - log c` is orthogonal to the stoichiometric subspace, `c, d > 0` give the same
conditioned law on every compatibility class: `π_d / π_c` is constant on the class. -/
theorem conditionedLaw_compatClass_eq_of_orthogonal (N : ReactionNetwork S ρ) {c d : S → ℝ}
    (hc : ∀ s, 0 < c s) (hd : ∀ s, 0 < d s)
    (horth : ∀ v ∈ N.stoichiometricSubspace,
      (fun s => Real.log (d s) - Real.log (c s)) ⬝ᵥ v = 0) (x₀ : S → ℕ) :
    conditionedLaw d (compatClass N x₀) = conditionedLaw c (compatClass N x₀) := by
  have hcx₀ := (poissonWeight_pos hc x₀).ne'
  refine conditionedLaw_eq_of_forall_mem (a := poissonWeight d x₀ / poissonWeight c x₀)
    (div_ne_zero (poissonWeight_pos hd x₀).ne' hcx₀) fun x hx => ?_
  have hv := horth (fun s => (x s : ℝ) - x₀ s) hx
  simp only [dotProduct] at hv
  have key : (∑ s, ((x s : ℝ) * Real.log (d s) - d s)) +
      ∑ s, ((x₀ s : ℝ) * Real.log (c s) - c s) =
      (∑ s, ((x₀ s : ℝ) * Real.log (d s) - d s)) + ∑ s, ((x s : ℝ) * Real.log (c s) - c s) := by
    have h2 : ∑ s, (Real.log (d s) - Real.log (c s)) * ((x s : ℝ) - x₀ s) =
        (∑ s, ((x s : ℝ) * Real.log (d s) - d s)) + ∑ s, ((x₀ s : ℝ) * Real.log (c s) - c s) -
        ((∑ s, ((x₀ s : ℝ) * Real.log (d s) - d s)) +
          ∑ s, ((x s : ℝ) * Real.log (c s) - c s)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    linarith
  rw [div_mul_eq_mul_div, eq_div_iff hcx₀]
  simp only [poissonWeight_eq_exp hd, poissonWeight_eq_exp hc]
  rw [div_mul_div_comm, div_mul_div_comm, ← Real.exp_add, ← Real.exp_add, key]
  ring

/-- **The conditioned law depends only on the class.** For positive rate constants, two
positive complex-balanced equilibria `c` and `d` give the same law on every stoichiometric
compatibility class (Horn–Jackson: `log d - log c ⊥ 𝒮`, `ComplexBalanced.positiveEquilibria_eq`). -/
theorem conditionedLaw_compatClass_eq {N : ReactionNetwork S ρ} [Fintype ρ] {κ : ρ → ℝ}
    (hκ : ∀ r, 0 < κ r) {c d : S → ℝ} (hc : ∀ s, 0 < c s) (hd : ∀ s, 0 < d s)
    (hcb : N.IsComplexBalanced κ c) (hdb : N.IsComplexBalanced κ d) (x₀ : S → ℕ) :
    conditionedLaw d (compatClass N x₀) = conditionedLaw c (compatClass N x₀) := by
  have hmem : d ∈ {c : S → ℝ | (∀ s, 0 < c s) ∧ N.massActionField κ c = 0} :=
    ⟨hd, N.massActionField_eq_zero_of_isComplexBalanced hdb⟩
  rw [N.positiveEquilibria_eq hκ hc hcb] at hmem
  exact conditionedLaw_compatClass_eq_of_orthogonal N hc hd hmem.2 x₀

/-! ### Conservation of the total count: the multinomial law -/

/-- `π_c(x) = (∏_s e^{-c_s}) · ∏_s c_s^{x_s} / ∏_s x_s!`. -/
theorem poissonWeight_eq_mul (c : S → ℝ) (x : S → ℕ) :
    poissonWeight c x =
      (∏ s, Real.exp (-c s)) * ((∏ s, c s ^ x s) / ∏ s, ((x s).factorial : ℝ)) := by
  rw [poissonWeight, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => by ring

/-- `∏_s c_s^{x_s} / ∏_s x_s! = multinomial(x) ∏_s c_s^{x_s} / (∑_s x_s)!`. -/
theorem prod_div_prod_factorial (c : S → ℝ) (x : S → ℕ) :
    (∏ s, c s ^ x s) / ∏ s, ((x s).factorial : ℝ) =
      (Nat.multinomial univ x : ℝ) * (∏ s, c s ^ x s) / ((∑ s, x s).factorial : ℝ) := by
  have hspec : (∏ s, ((x s).factorial : ℝ)) * Nat.multinomial univ x =
      ((∑ s, x s).factorial : ℝ) := by
    exact_mod_cast Nat.multinomial_spec univ x
  have hF : (∏ s, ((x s).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => by positivity
  have hm : (Nat.multinomial univ x : ℝ) ≠ 0 := by exact_mod_cast (Nat.multinomial_pos _ _).ne'
  rw [← hspec, div_eq_div_iff hF (mul_ne_zero hF hm)]
  ring

theorem totalClass_eq_coe [DecidableEq S] (n : ℕ) :
    totalClass (S := S) n = ((piAntidiag univ n : Finset (S → ℕ)) : Set (S → ℕ)) := by
  ext x
  simp [totalClass]

/-- The product-form mass of the states with total count `n` is
`(∏_s e^{-c_s}) (∑_s c_s)^n / n!` (the multinomial theorem). -/
theorem classMass_totalClass (c : S → ℝ) (n : ℕ) :
    classMass c (totalClass n) = (∏ s, Real.exp (-c s)) * (∑ s, c s) ^ n / (n.factorial : ℝ) := by
  classical
  have hpow := Finset.sum_pow_eq_sum_piAntidiag univ c n
  rw [classMass, totalClass_eq_coe, tsum_eq_sum (s := piAntidiag univ n) fun y hy =>
    Set.indicator_of_notMem (mt Finset.mem_coe.1 hy) _]
  have hterm : ∀ y ∈ piAntidiag univ n,
      ((piAntidiag univ n : Finset (S → ℕ)) : Set (S → ℕ)).indicator (poissonWeight c) y =
        (∏ s, Real.exp (-c s)) *
          ((Nat.multinomial univ y : ℝ) * (∏ s, c s ^ y s) / (n.factorial : ℝ)) :=
    fun y hy => by
      rw [Set.indicator_of_mem (Finset.mem_coe.2 hy), poissonWeight_eq_mul,
        prod_div_prod_factorial, (mem_piAntidiag.1 hy).1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_div, ← hpow, mul_div_assoc]

/-- **Multinomial law on its support.** Conditioned on the total molecule count
`n = ∑_s x_s`, the product-form law with means `c > 0` is multinomial:
`π_c(x | ∑ x = n) = n! / ∏_s x_s! · ∏_s (c_s / ∑_s c_s)^{x_s}`. The equality of laws for a
fixed `n` is `conditionedLaw_totalClass_eq_multinomialReal`. With
`isReactionClosed_totalClass` this is the stationary law of a network that conserves the total
count, such as a network of unimolecular conversions `A_i ⇌ A_j`. -/
theorem conditionedLaw_totalClass {c : S → ℝ} (hc : ∀ s, 0 < c s) (x : S → ℕ) :
    conditionedLaw c (totalClass (∑ s, x s)) x =
      (Nat.multinomial univ x : ℝ) * ∏ s, (c s / ∑ s', c s') ^ x s := by
  have hE : (∏ s, Real.exp (-c s)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (Real.exp_pos _).ne'
  have hF : ((∑ s, x s).factorial : ℝ) ≠ 0 := by positivity
  have hC : (∑ s, c s) ^ (∑ s, x s) ≠ 0 := by
    rcases isEmpty_or_nonempty S with hS | hS
    · simp [Finset.univ_eq_empty]
    · exact pow_ne_zero _ (Finset.sum_pos (fun s _ => hc s) Finset.univ_nonempty).ne'
  have hx : x ∈ totalClass (∑ s, x s) := rfl
  rw [conditionedLaw_of_mem c hx, classMass_totalClass, poissonWeight_eq_mul,
    prod_div_prod_factorial, Finset.prod_congr rfl fun s _ => div_pow (c s) (∑ s', c s') (x s),
    Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  field_simp

/-- **Multinomial law, as a law.** For every total `n`, the product-form law with means `c > 0`
conditioned on the states with total count `n` is the multinomial law
`ProbabilityTheory.multinomialReal n (c / ∑ c)`: both vanish off `∑ x = n`, and on it they agree
by `conditionedLaw_totalClass`. -/
theorem conditionedLaw_totalClass_eq_multinomialReal {c : S → ℝ} (hc : ∀ s, 0 < c s) (n : ℕ) :
    conditionedLaw c (totalClass n) =
      ProbabilityTheory.multinomialReal n (fun s => c s / ∑ s', c s') := by
  funext x
  by_cases hx : ∑ s, x s = n
  · subst hx
    rw [conditionedLaw_totalClass hc x, ProbabilityTheory.multinomialReal, ite_eq_left rfl]
  · rw [conditionedLaw_of_notMem c hx, ProbabilityTheory.multinomialReal_of_sum_ne hx]

end Conditioned

/-! ### The conditioned law as a conditional probability -/

section Measure

open MeasureTheory ProbabilityTheory

variable [Fintype S]

/-- The product-form Poisson law on `ℕ^S` with means `c ≥ 0`, as a probability mass
function. -/
noncomputable def poissonPMF {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) : PMF (S → ℕ) :=
  ⟨fun x => ENNReal.ofReal (poissonWeight c x), by
    have h := hasSum_poissonWeight hc
    have h1 := ENNReal.ofReal_tsum_of_nonneg (poissonWeight_nonneg hc) h.summable
    rw [h.tsum_eq, ENNReal.ofReal_one] at h1
    rw [h1]
    exact ENNReal.summable.hasSum⟩

theorem poissonPMF_apply {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) (x : S → ℕ) :
    poissonPMF hc x = ENNReal.ofReal (poissonWeight c x) :=
  rfl

/-- **The conditioned law is a conditional probability.** Under the product-form law
`μ = poissonPMF hc` on `ℕ^S`, the conditional probability `μ[{x} | Γ]` of a state given a set
`Γ` of states is `conditionedLaw c Γ x`. -/
theorem cond_poissonPMF_singleton {c : S → ℝ} (hc : ∀ s, 0 ≤ c s) (Γ : Set (S → ℕ))
    (x : S → ℕ) : ((poissonPMF hc).toMeasure[{x} | Γ]).toReal = conditionedLaw c Γ x := by
  have hΓ : MeasurableSet Γ := Γ.to_countable.measurableSet
  have hmass : (poissonPMF hc).toMeasure Γ = ENNReal.ofReal (classMass c Γ) := by
    rw [PMF.toMeasure_apply _ hΓ, classMass, ENNReal.ofReal_tsum_of_nonneg
      (fun y => Set.indicator_nonneg (fun y _ => poissonWeight_nonneg hc y) y)
      ((hasSum_poissonWeight hc).summable.indicator Γ)]
    refine tsum_congr fun y => ?_
    by_cases hy : y ∈ Γ <;> simp [hy, poissonPMF_apply]
  rw [cond_apply hΓ, hmass, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (classMass_nonneg hc Γ)]
  by_cases hx : x ∈ Γ
  · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hx),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), poissonPMF_apply,
      ENNReal.toReal_ofReal (poissonWeight_nonneg hc x), conditionedLaw_of_mem c hx,
      div_eq_inv_mul]
  · rw [Set.inter_singleton_eq_empty.2 hx, measure_empty, ENNReal.toReal_zero, mul_zero,
      conditionedLaw_of_notMem c hx]

end Measure

end MathlibExt.Biology.Dynamics.StochasticCRNConditioned
