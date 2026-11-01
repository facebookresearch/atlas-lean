/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# The Bayesian–Dirichlet (BD, BDe) network score and covered-edge reversals

Discrete variables `v : V` take values in finite types `σ v`; a complete case is an assignment
`x : (v : V) → σ v` and the data are a list `D` of cases. A network structure is a parent-set
map `Pa : V → Finset V`; the family of `v` is `insert v (Pa v)`. For a set `S` of variables,
`Config σ S` are the joint values of `S` and `count D S c` counts the cases that agree with
`c` on `S`.

**BD score.** With Dirichlet hyperparameters `α c > 0` for every configuration `c` of a family
`F ⊇ P` (`F` = child and parents, `P` = parents), the Bayesian–Dirichlet family score is
`∏_c rising(α c, N c) / ∏_j rising(α_j, N_j)`, where `j` runs over parent configurations,
`α_j = ∑_{c ↦ j} α c` and `N_j = ∑_{c ↦ j} N c` (`sum_count_restrict₂`). Here
`rising a n = a (a + 1) ⋯ (a + n - 1) = Γ(a + n) / Γ(a)` is the rising factorial, so this is
the closed form `∏_j Γ(α_j)/Γ(α_j + N_j) ∏_k Γ(α_jk + N_jk)/Γ(α_jk)` of Cooper and Herskovits
and of Heckerman, Geiger and Chickering. The network score `bdScore` is the product of the
family scores (decomposability).

**BDe.** Heckerman, Geiger and Chickering take `α c = ess · p(c)`, where `p` is a weight
function on complete cases — a prior joint distribution when `∑ x, p x = 1` — and `ess > 0`
an equivalent sample size (`bdeHyper`).

## Main results

* `seqProb_eq_bdScore`: the BD score equals `seqProb`, the probability of the data under
  sequential Pólya–Dirichlet prediction (case `t` has probability
  `∏_v (α_{v,c} + n_{v,c}) / (α_{v,j} + n_{v,j})` with counts `n` over the earlier cases),
  so it does not depend on the order of the cases. Each factor is the Dirichlet posterior
  predictive probability (see `posterior_predictive_dirichletMeasure` in
  `CSLibExt/MachineLearning/Bayesian/DirichletMultinomial.lean`); the measure-theoretic
  integral over the parameters is not restated here.
* `bdFamily_bdeHyper`: with BDe hyperparameters the family score is a ratio
  `margLik D F / margLik D P` of set marginal likelihoods.
* `bdeScore_coveredReversal`: **reversing a covered edge** (`x → y` with
  `Pa y = insert x (Pa x)`) leaves the BDe score unchanged; `bdeScore_eq_of_reflTransGen`:
  so does any sequence of covered-edge reversals.

Chickering's theorem that any two Markov-equivalent DAGs are connected by covered-edge
reversals is stated in `WantedExt/ComputerScience/BayesianNetworkEquivalenceWanted.lean`;
together with `bdeScore_eq_of_reflTransGen` it gives the score equivalence of BDe.
Acyclicity of `Pa` is not needed for the identities proved here.

## References

* G. F. Cooper and E. Herskovits, "A Bayesian method for the induction of probabilistic
  networks from data", *Machine Learning* 9 (1992), 309–347.
* D. Heckerman, D. Geiger and D. M. Chickering, "Learning Bayesian networks: the combination
  of knowledge and statistical data", *Machine Learning* 20 (1995), 197–243.
* D. M. Chickering, "A transformational characterization of equivalent Bayesian network
  structures", *Proc. 11th Conference on Uncertainty in Artificial Intelligence* (1995);
  arXiv:1302.4938.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.BayesianDirichlet

open Finset

variable {V : Type*} [DecidableEq V] {σ : V → Type*} [∀ v, Fintype (σ v)]
  [∀ v, DecidableEq (σ v)]

/-- The joint values of the variables in `S`. -/
abbrev Config (σ : V → Type*) (S : Finset V) := (u : S) → σ u

/-- The rising factorial `a (a + 1) ⋯ (a + n - 1)`, equal to `Γ(a + n) / Γ(a)` for `a > 0`. -/
noncomputable def rising (a : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval a

/-- The number of cases in `D` that take the values `c` on the variables `S`. -/
def count (D : List ((v : V) → σ v)) (S : Finset V) (c : Config σ S) : ℕ :=
  D.countP fun x => S.restrict x = c

/-- The Bayesian–Dirichlet score of a family `F` with parent set `P ⊆ F` and hyperparameters
`α` on the configurations of `F`. -/
noncomputable def bdFamily (D : List ((v : V) → σ v)) {P F : Finset V} (hPF : P ⊆ F)
    (α : Config σ F → ℝ) : ℝ :=
  (∏ c : Config σ F, rising (α c) (count D F c)) /
    ∏ j : Config σ P, rising (∑ c with Finset.restrict₂ hPF c = j, α c) (count D P j)

/-- The BD score of the structure `Pa` with family hyperparameters `α`: the product of the
family scores. -/
noncomputable def bdScore [Fintype V] (D : List ((v : V) → σ v)) (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) : ℝ :=
  ∏ v, bdFamily D (subset_insert v (Pa v)) (α v)

/-- The sequential Pólya–Dirichlet prediction probability of the case `x` after the cases `D`:
`∏_v (α_{v,c} + n_{v,c}) / (α_{v,j} + n_{v,j})`, with `c`, `j` the family and parent values of
`x` and `n` the counts in `D`. -/
noncomputable def predictive [Fintype V] (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) (D : List ((v : V) → σ v))
    (x : (v : V) → σ v) : ℝ :=
  ∏ v, (α v ((insert v (Pa v)).restrict x) + count D _ ((insert v (Pa v)).restrict x)) /
    ((∑ c with Finset.restrict₂ (subset_insert v (Pa v)) c = (Pa v).restrict x, α v c) +
      count D (Pa v) ((Pa v).restrict x))

/-- The probability of the cases `D`, in order, under sequential Pólya–Dirichlet prediction
after the cases `E`: each case is predicted from all cases before it. -/
noncomputable def seqProbAfter [Fintype V] (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) :
    List ((v : V) → σ v) → List ((v : V) → σ v) → ℝ
  | _, [] => 1
  | E, x :: D => predictive Pa α E x * seqProbAfter Pa α (E ++ [x]) D

/-- The probability of the cases of `D`, in order, under sequential Pólya–Dirichlet prediction. -/
noncomputable def seqProb [Fintype V] (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) (D : List ((v : V) → σ v)) : ℝ :=
  seqProbAfter Pa α [] D

/-- The number of cases matching a parent configuration is the sum over the family
configurations extending it (`N_j = ∑_k N_jk`). -/
theorem sum_count_restrict₂ (D : List ((v : V) → σ v)) {P F : Finset V} (hPF : P ⊆ F)
    (j : Config σ P) :
    ∑ c with Finset.restrict₂ hPF c = j, count D F c = count D P j := by
  induction D with
  | nil => simp [count]
  | cons x D ih =>
    simp only [count, List.countP_cons] at ih ⊢
    rw [Finset.sum_add_distrib, ih]
    congr 1
    simp only [decide_eq_true_eq, Finset.sum_boole, Nat.cast_id]
    have : (Finset.univ.filter fun c : Config σ F =>
        Finset.restrict₂ hPF c = j ∧ F.restrict x = c) =
        if P.restrict x = j then {F.restrict x} else ∅ := by
      ext c
      split_ifs with h
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h' => h'.2.symm, fun h' => ⟨h' ▸ h, h'.symm⟩⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        rintro hc rfl
        exact h hc
    rw [Finset.filter_filter, this]
    split_ifs <;> simp

/-- Adding a case multiplies a product of rising factorials by one factor `a + n` at the
configuration of the new case. -/
private theorem prod_rising_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (N : ι → ℕ) (c₀ : ι) :
    ∏ c, rising (a c) (N c + if c₀ = c then 1 else 0) =
      (∏ c, rising (a c) (N c)) * (a c₀ + N c₀) := by
  have : ∀ c, rising (a c) (N c + if c₀ = c then 1 else 0) =
      rising (a c) (N c) * (if c₀ = c then a c + N c else 1) := by
    intro c
    split_ifs
    · simp [rising, ascPochhammer_succ_eval]
    · simp
  simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, ite_true]

omit [DecidableEq V] [∀ v, Fintype (σ v)] in
private theorem count_append_singleton (D : List ((v : V) → σ v)) (x : (v : V) → σ v)
    (S : Finset V) (c : Config σ S) :
    count (D ++ [x]) S c = count D S c + if S.restrict x = c then 1 else 0 := by
  simp [count, List.countP_append]

/-- Adding a case multiplies the BD score by the sequential prediction probability of the case. -/
private theorem bdScore_append_singleton [Fintype V] (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) (D : List ((v : V) → σ v))
    (x : (v : V) → σ v) :
    bdScore (D ++ [x]) Pa α = bdScore D Pa α * predictive Pa α D x := by
  simp only [bdScore, predictive, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [bdFamily, count_append_singleton]
  rw [prod_rising_succ, prod_rising_succ (fun j => ∑ c with Finset.restrict₂
    (subset_insert v (Pa v)) c = j, α v c), mul_div_mul_comm]

private theorem seqProbAfter_mul_bdScore [Fintype V] (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) (E D : List ((v : V) → σ v)) :
    seqProbAfter Pa α E D * bdScore E Pa α = bdScore (E ++ D) Pa α := by
  induction D generalizing E with
  | nil => simp [seqProbAfter]
  | cons x D ih =>
    rw [seqProbAfter, mul_comm (predictive Pa α E x), mul_assoc, mul_comm (predictive Pa α E x),
      ← bdScore_append_singleton, ih, List.append_assoc, List.singleton_append]

/-- **The BD score is the sequential prediction probability** of the data (hence it does not
depend on the order of the cases). This is an identity for all real hyperparameters; it is a
probability statement when they are positive (then every predictive denominator is positive). -/
theorem seqProb_eq_bdScore [Fintype V] (Pa : V → Finset V)
    (α : (v : V) → Config σ (insert v (Pa v)) → ℝ) (D : List ((v : V) → σ v)) :
    seqProb Pa α D = bdScore D Pa α := by
  have h0 : bdScore [] Pa α = 1 := by simp [bdScore, bdFamily, count, rising]
  rw [seqProb, ← mul_one (seqProbAfter Pa α [] D), ← h0, seqProbAfter_mul_bdScore,
    List.nil_append]

/-- BDe hyperparameters (Heckerman, Geiger and Chickering): `ess` times the weight
`∑_{x ↦ c} p x` of the configuration `c` of `S`. When `∑ x, p x = 1`, `p` is a prior joint
distribution and this is the prior probability of `c`. -/
noncomputable def bdeHyper [Fintype V] (p : ((v : V) → σ v) → ℝ) (ess : ℝ) (S : Finset V)
    (c : Config σ S) : ℝ :=
  ess * ∑ x with S.restrict x = c, p x

/-- The (unnormalized) marginal likelihood of the data restricted to the variables `S` under
the BDe Dirichlet prior on the joint values of `S`. `p` is treated as generalized weights
here: the total Dirichlet mass over configurations is `ess * ∑ x, p x`, so the omitted
normalizing factor is `1 / rising (ess * ∑ x, p x) D.length`, the same for every `S`. When
`p` is normalized (`∑ x, p x = 1`) this is `1 / rising ess D.length`, and `p` is a prior
joint distribution. -/
noncomputable def margLik [Fintype V] (p : ((v : V) → σ v) → ℝ) (ess : ℝ)
    (D : List ((v : V) → σ v)) (S : Finset V) : ℝ :=
  ∏ c : Config σ S, rising (bdeHyper p ess S c) (count D S c)

/-- With BDe hyperparameters, a family score is a ratio of set marginal likelihoods. -/
theorem bdFamily_bdeHyper [Fintype V] (p : ((v : V) → σ v) → ℝ) (ess : ℝ)
    (D : List ((v : V) → σ v)) {P F : Finset V} (hPF : P ⊆ F) :
    bdFamily D hPF (bdeHyper p ess F) = margLik p ess D F / margLik p ess D P := by
  have hfib : ∀ j : Config σ P,
      ∑ c with Finset.restrict₂ hPF c = j, bdeHyper p ess F c = bdeHyper p ess P j := by
    intro j
    simp only [bdeHyper, ← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun x => P.restrict x = j)
      (t := Finset.univ.filter fun c : Config σ F => Finset.restrict₂ hPF c = j)
      (g := F.restrict) ?_]
    · refine Finset.sum_congr rfl fun c hc => ?_
      rw [Finset.filter_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨fun h => ⟨by rw [← hc, ← h]; rfl, h⟩, fun h => h.2⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
  simp only [bdFamily, margLik, hfib]

/-- The BDe score of the structure `Pa`. -/
noncomputable def bdeScore [Fintype V] (p : ((v : V) → σ v) → ℝ) (ess : ℝ)
    (D : List ((v : V) → σ v)) (Pa : V → Finset V) : ℝ :=
  bdScore D Pa fun v => bdeHyper p ess (insert v (Pa v))

/-- `Pa'` is obtained from `Pa` by reversing a covered edge `x → y` (Chickering 1995): `x` is a
parent of `y` and `y`'s other parents are exactly `x`'s parents (`Pa y = insert x (Pa x)`);
after the reversal `y` has parents `Pa x` and `x` has parents `insert y (Pa x)`. Acyclicity
is not required: the score identity holds for any parent-set maps (on a DAG, `x ∉ Pa x` and
`y ∉ Pa x` hold automatically). -/
def CoveredReversal (Pa Pa' : V → Finset V) : Prop :=
  ∃ x y, x ≠ y ∧ Pa y = insert x (Pa x) ∧
    Pa' = Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))

/-- **Covered-edge reversal preserves the BDe score** (for a positive weight function `p` —
a prior when `∑ x, p x = 1` — and positive equivalent sample size). -/
theorem bdeScore_coveredReversal [Fintype V] [∀ v, Nonempty (σ v)]
    (p : ((v : V) → σ v) → ℝ) (hp : ∀ x, 0 < p x) {ess : ℝ} (hess : 0 < ess)
    (D : List ((v : V) → σ v)) {Pa Pa' : V → Finset V} (h : CoveredReversal Pa Pa') :
    bdeScore p ess D Pa' = bdeScore p ess D Pa := by
  classical
  obtain ⟨x, y, hxy, hPay, rfl⟩ := h
  have hpos : ∀ S : Finset V, 0 < margLik p ess D S := by
    intro S
    refine Finset.prod_pos fun c _ => ascPochhammer_pos _ _ ?_
    refine mul_pos hess (Finset.sum_pos (fun _ _ => hp _) ?_)
    refine ⟨fun v => if hv : v ∈ S then c ⟨v, hv⟩ else Classical.arbitrary _, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext u
    simp [Finset.restrict, u.2]
  have hscore : ∀ Q : V → Finset V, bdeScore p ess D Q =
      ∏ v, margLik p ess D (insert v (Q v)) / margLik p ess D (Q v) := fun Q => by
    simp only [bdeScore, bdScore, bdFamily_bdeHyper]
  rw [hscore, hscore]
  have hy : y ∈ Finset.univ.erase x := Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), ← Finset.mul_prod_erase _ _ hy,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ x), ← Finset.mul_prod_erase _ _ hy,
    ← mul_assoc, ← mul_assoc]
  congr 1
  · simp only [Function.update_self, Function.update_of_ne hxy.symm, hPay]
    have h1 := (hpos (insert y (Pa x))).ne'
    have h2 := (hpos (insert x (Pa x))).ne'
    rw [Finset.insert_comm x y]
    field_simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvy : v ≠ y := (Finset.mem_erase.1 hv).1
    have hvx : v ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 hv).2).1
    simp only [Function.update_of_ne hvx, Function.update_of_ne hvy]

/-- Structures connected by a sequence of covered-edge reversals have the same BDe score. -/
theorem bdeScore_eq_of_reflTransGen [Fintype V] [∀ v, Nonempty (σ v)]
    (p : ((v : V) → σ v) → ℝ) (hp : ∀ x, 0 < p x) {ess : ℝ} (hess : 0 < ess)
    (D : List ((v : V) → σ v)) {Pa Pa' : V → Finset V}
    (h : Relation.ReflTransGen CoveredReversal Pa Pa') :
    bdeScore p ess D Pa' = bdeScore p ess D Pa := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (bdeScore_coveredReversal p hp hess D hstep).trans ih

end Cslib.MachineLearning.GraphicalModels.BayesianDirichlet
