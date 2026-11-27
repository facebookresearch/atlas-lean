/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModels
public import CSLibExt.MachineLearning.GraphicalModels.Identifiability

/-!
# Natural direct and indirect effects and the mediation formula in finite SCMs

For a treatment node `t` (`X`), a mediator node `m` (`Z`) and an outcome node `y` (`Y`, read
through a real readout `g`) of a finite recursive structural causal model (`FiniteSCM`) with
independent noise laws `μ`, this file defines the nested counterfactual `Y_{x, Z_{x*}}(u)`, the
average natural direct, natural indirect and total effects, and states their identification by
the mediation formula, a counterexample to identification when a mediator-outcome confounder is
affected by the treatment, and Pearl's decomposition of the total effect.

Source locators (J. Pearl, *Direct and Indirect Effects*, UAI 2001, R-273-U, cited as P01, PDF
page `k` is proceedings page `410 + k`; J. Pearl, *Interpretation and Identification of Causal
Mediation*, Psychological Methods 2014, R-389, cited as P14):

* nested counterfactual: P01 §3.1 and eqs. (4)-(5), PDF pp. 4-5;
* `nde`: P01 Definition 5, eq. (6), PDF p. 5; `nie`, `te`: P01 Definition 7, eqs. (20)-(21),
  PDF pp. 7-8 (P14 eqs. (9)-(10), pp. 10-11);
* `te_eq_nie_sub_nde`, `te_eq_nde_sub_nie`: P01 Theorem 3, eqs. (22)-(23), PDF p. 8;
* `noiseExpect_nested_eq_sum`, `nde_eq_sum_counterfactual`: P01 Theorem 1, eqs. (7)-(10),
  PDF p. 6;
* `nde_eq_doFormula`: P14 Theorem 1, eq. (13), p. 17 (P01 Theorem 1, "experimentally
  identifiable");
* `nde_eq_mediationFormulaNDE`: P01 Theorem 2 with (ii)-(iii) realized by adjustment, PDF p. 6;
  P14 Corollary 1, eq. (14a), p. 17; `nie_eq_mediationFormulaNIE`: P01 Theorem 4, eqs.
  (25)-(26), PDF p. 8; P14 eq. (14b), p. 17. Both are proved under the counterfactual H1-H4
  hypotheses below, which dispense with the A-1 nondescendant premise of the published
  statements; the `_of_notAffected` corollaries give the published hypothesis sets;
* `nde_eq_mediationFormula_unadjusted`, `nie_eq_mediationFormula_unadjusted` (`W = ∅`): P01
  eqs. (17) and (27), PDF pp. 7-8; P14 eqs. (16)-(17), p. 19 ("the mediation formula");
* `MediationKite`: P14 §5, Fig. 10, pp. 27-28; C. Avin, I. Shpitser and J. Pearl,
  *Identifiability of Path-Specific Effects*, IJCAI 2005, Definition 10 and Theorem 4, p. 362,
  Lemma 2, p. 361.

## The four no-confounding conditions and positivity

`nde_eq_mediationFormulaNDE` assumes four conditional independences of functions of the noise
(`NoiseCondIndep`, counterfactual form, factual covariates `W`), for `x' ∈ {x, x*}` and all `z`:
(H1) `Y_{x'z} ⫫ X | W` (no X-Y confounding); (H2) `Y_{x'z} ⫫ Z | X, W` (no Z-Y confounding);
(H3) `Z_{x*} ⫫ X | W` (no X-Z confounding); (H4) `Y_{x'z} ⫫ Z_{x*} | W`, the cross-world
condition of P01 eq. (7) (no Z-Y confounder affected by X; P14 A-2).

**Positivity is in neither paper.** P01 and P14 divide by `P(x*, w)` and `P(x, z, w)` without
stating that they are positive. With Lean's total division (`a / 0 = 0`) the formula is false
without positivity: `MediationFormulaTests` pins a deterministic three-node model satisfying
H1-H4 and `hposW` whose natural direct effect is `1` while the formula is `0`. The theorems
therefore add explicit support positivity (`hposW`, `hposZ`): `P(W = w) > 0` implies
`P(X = x*, W = w) > 0`, and `P(X = x*, Z = z, W = w) > 0` implies `P(X = x, Z = z, W = w) > 0`.

**"W is not affected by X"** (P14 A-1; P01 "nondescendants of X or Z") is part of the published
hypothesis sets for the observational formulas: P14 Corollary 1 states eqs. (14a)-(14b) under
A-1 and A-2, and P01 likewise takes the adjustment covariates to be nondescendants. The
counterfactual H1-H4 form proved here does not need it: with factual covariates, H1-H4 and
positivity give the observational formula without any nondescendant premise.
Two forms of the premise appear below. P14's A-1 itself is treatment-only (`W` unaffected by
`X`); `nde_eq_mediationFormulaNDE_a1` and `nie_eq_mediationFormulaNIE_a1` state it in that
form and follow immediately. The parent-closed form `W ⊆ S` for a parent-closed node set `S`
avoiding `t` and `m` ("no member of `W` is a descendant of `t` or of `m`") is stronger than
A-1, since it also excludes mediator descendants; it is the working hypothesis of
`nde_eq_doFormula`, whose mediator surgery needs that too (P14 fn. 18, p. 17, and p. 18),
and the `_of_notAffected` corollaries record the formulas under it.

## Natural indirect effect convention

`nie` is P01 Definition 7: `nie ... x x*` is `NIE(x, x*; Y) = E(Y_{x*, Z_x}) - E(Y_{x*})`.
Atlas `LinearMediation.MediationModel.naturalIndirectEffect x₀ x₁ = Y_{x₁} - Y_{x₁, M_{x₀}}`
is the `TE - NDE` convention (P14 fn. 13): by P01 eq. (23) it equals `-nie ... x₀ x₁` in every
model (note the sign and argument order). It equals the reversed call `nie ... x₁ x₀` (both
`a b (x₁ - x₀)`, while `nie ... x₀ x₁` is `a b (x₀ - x₁)`) only in additive models, not with
treatment-mediator interaction. The agreement with `LinearMediation` is a sanity check in
`MediationFormulaTests` (`nie_toFiniteSCM`, the reversed call `nie ... x₁ x₀`), in the
additive case only, with an interaction model as negative control.

## Scope

Single treatment and single mediator node (P01 allows a set `Z`); identification by adjustment
only (P01 Theorem 2 (ii)-(iii) by other routes, estimation, path-specific effects and
exposure-induced confounding beyond the counterexample are out of scope).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

namespace FiniteSCM

variable {α : Type*} {n : ℕ} {U : Fin n → Type*}

/-! ### Nested counterfactuals and natural effects -/

/-- `X_{t ← a, m ← b}(u)`: surgery on the two nodes `t` and `m` at the noise value `u`
(the controlled counterfactual `Y_{xz}(u)` of P01, eq. (2)). -/
def counterfactual₂ (M : FiniteSCM α n U) (t : Fin n) (a : α) (m : Fin n) (b : α)
    (u : (k : Fin n) → U k) : Fin n → α :=
  ((M.doNode t a).doNode m b).solve u

/-- **Nested counterfactual** `X_{t ← x, m ← Z_{x'}(u)}(u)` (P01, §3.1 and eqs. (4)-(6)): the
treatment is set to `x` and the mediator to the value `Z_{x'}(u)` it takes under
`do(X_t = x')` at the same noise value. -/
def nestedCounterfactual (M : FiniteSCM α n U) (t m : Fin n) (x x' : α)
    (u : (k : Fin n) → U k) : Fin n → α :=
  M.counterfactual₂ t x m (M.counterfactual t x' u m) u

/-- On the event `Z_{x'}(u) = z` the nested counterfactual is the controlled one (the step
from (6) to (9) in P01). -/
theorem nestedCounterfactual_of_eq (M : FiniteSCM α n U) (t m : Fin n) (x x' : α)
    (u : (k : Fin n) → U k) {z : α} (h : M.counterfactual t x' u m = z) :
    M.nestedCounterfactual t m x x' u = M.counterfactual₂ t x m z u := by
  rw [nestedCounterfactual, h]

/-- **Composition** `Y_{x, Z_x} = Y_x` (Pearl 2000, p. 229, used in P01's proof of Theorem 1),
from `FiniteSCM.solve_doNode_doNode_of_counterfactual`. -/
theorem nestedCounterfactual_self (M : FiniteSCM α n U) (t m : Fin n) (x : α)
    (u : (k : Fin n) → U k) : M.nestedCounterfactual t m x x u = M.counterfactual t x u :=
  M.solve_doNode_doNode_of_counterfactual rfl

/-- **Consistency** for two-node surgery: where `X_t = x` and `X_m = z` already hold, the
surgery changes nothing. -/
theorem counterfactual₂_eq_solve (M : FiniteSCM α n U) {t m : Fin n} {x z : α}
    {u : (k : Fin n) → U k} (ht : M.solve u t = x) (hm : M.solve u m = z) :
    M.counterfactual₂ t x m z u = M.solve u := by
  have h1 : (M.doNode t x).solve u = M.solve u := M.counterfactual_eq_solve ht
  have h2 : (M.doNode t x).solve u m = z := by rw [h1]; exact hm
  change ((M.doNode t x).doNode m z).solve u = M.solve u
  rw [← h1]
  exact (M.doNode t x).counterfactual_eq_solve h2

/-- Expectation of a real function of the noise under independent noise laws `μ`; the sum
runs over the product of the supports, as in `FiniteSCM.inducedLaw`. -/
noncomputable def noiseExpect (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (F : ((k : Fin n) → U k) → ℝ) : ℝ :=
  ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support), noiseWeight μ u * F u

/-- Probability of an event of the noise under independent noise laws `μ`. -/
noncomputable def noiseProb (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : ((k : Fin n) → U k) → Prop) [DecidablePred E] : ℝ :=
  ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support) with E u, noiseWeight μ u

/-- `E(F | E)` under the noise law (`0` when `P(E) = 0`, Lean's total division). -/
noncomputable def noiseCondExpect (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (F : ((k : Fin n) → U k) → ℝ) (E : ((k : Fin n) → U k) → Prop) [DecidablePred E] : ℝ :=
  noiseExpect μ (fun u => if E u then F u else 0) / noiseProb μ E

/-- Conditional independence `A ⫫ B | C` of finite-valued functions of the noise, in the
product form of `MathlibExt.Probability.FiniteWeight.CondIndep`:
`P(A = a, B = b, C = c) P(C = c) = P(A = a, C = c) P(B = b, C = c)`. -/
def NoiseCondIndep (μ : (k : Fin n) → StdSimplex ℝ (U k)) {A B C : Type*} [DecidableEq A]
    [DecidableEq B] [DecidableEq C] (fA : ((k : Fin n) → U k) → A)
    (fB : ((k : Fin n) → U k) → B) (fC : ((k : Fin n) → U k) → C) : Prop :=
  ∀ a b c, noiseProb μ (fun u => fA u = a ∧ fB u = b ∧ fC u = c) *
      noiseProb μ (fun u => fC u = c) =
    noiseProb μ (fun u => fA u = a ∧ fC u = c) * noiseProb μ (fun u => fB u = b ∧ fC u = c)

/-- The expectation of a constant is that constant (from `sum_noiseWeight_eq_one`). -/
theorem noiseExpect_const (μ : (k : Fin n) → StdSimplex ℝ (U k)) (c : ℝ) :
    noiseExpect μ (fun _ => c) = c := by
  unfold noiseExpect
  rw [← Finset.sum_mul, sum_noiseWeight_eq_one, one_mul]

/-- **Average natural direct effect** `NDE(x, x*; Y) = E(Y_{x, Z_{x*}}) - E(Y_{x*})` (P01,
Definition 5, eq. (6)), for treatment `t`, mediator `m`, outcome `y` read by `g`. -/
noncomputable def nde (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t m y : Fin n) (g : α → ℝ) (x xstar : α) : ℝ :=
  noiseExpect μ (fun u => g (M.nestedCounterfactual t m x xstar u y)) -
    noiseExpect μ (fun u => g (M.counterfactual t xstar u y))

/-- **Average natural indirect effect** `NIE(x, x*; Y) = E(Y_{x*, Z_x}) - E(Y_{x*})` (P01,
Definition 7, eq. (20)). This is not the `TE - NDE` convention of
`LinearMediation.MediationModel.naturalIndirectEffect x₀ x₁`, which equals `-nie ... x₀ x₁`
in every model and agrees with the reversed call `nie ... x₁ x₀` only in additive models
(module docstring). -/
noncomputable def nie (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t m y : Fin n) (g : α → ℝ) (x xstar : α) : ℝ :=
  noiseExpect μ (fun u => g (M.nestedCounterfactual t m xstar x u y)) -
    noiseExpect μ (fun u => g (M.counterfactual t xstar u y))

/-- **Total effect** `TE(x, x*; Y) = E(Y_x) - E(Y_{x*})` (P01, eq. (21)). -/
noncomputable def te (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t y : Fin n) (g : α → ℝ) (x xstar : α) : ℝ :=
  noiseExpect μ (fun u => g (M.counterfactual t x u y)) -
    noiseExpect μ (fun u => g (M.counterfactual t xstar u y))

/-- P01, Theorem 3, eq. (22): `TE(x, x*; Y) = NIE(x, x*; Y) - NDE(x*, x; Y)`. -/
theorem te_eq_nie_sub_nde (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t m y : Fin n) (g : α → ℝ) (x xstar : α) :
    M.te μ t y g x xstar = M.nie μ t m y g x xstar - M.nde μ t m y g xstar x := by
  unfold te nie nde
  ring

/-- P01, Theorem 3, eq. (23): `TE(x, x*; Y) = NDE(x, x*; Y) - NIE(x*, x; Y)`. -/
theorem te_eq_nde_sub_nie (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t m y : Fin n) (g : α → ℝ) (x xstar : α) :
    M.te μ t y g x xstar = M.nde μ t m y g x xstar - M.nie μ t m y g xstar x := by
  unfold te nie nde
  ring

/-! ### Identification -/

section Identification

variable [Fintype α] [DecidableEq α]

/-- `P(E) = ∑_{v ∈ E} P(v)` for a weight `P` on full assignments. -/
noncomputable def lawProb (P : (Fin n → α) → ℝ) (E : (Fin n → α) → Prop)
    [DecidablePred E] : ℝ :=
  ∑ v with E v, P v

/-- `E(g(X_y) | E)` for a weight `P` on full assignments (`0` when `P(E) = 0`). -/
noncomputable def lawMean (P : (Fin n → α) → ℝ) (g : α → ℝ) (y : Fin n)
    (E : (Fin n → α) → Prop) [DecidablePred E] : ℝ :=
  (∑ v with E v, P v * g (v y)) / lawProb P E

/-- **The mediation formula for the NDE**, a functional of the law `P` alone: P14, eq. (14a)
(`∑_{w,z} [E(Y | x, z, w) - E(Y | x*, z, w)] P(z | x*, w) P(w)`); with `W = ∅` it is P01,
eq. (17), and P14, eq. (16). -/
noncomputable def mediationFormulaNDE (P : (Fin n → α) → ℝ) (t m y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α) : ℝ :=
  ∑ w : W → α, ∑ z : α,
    (lawMean P g y (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) -
      lawMean P g y (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)) *
    (lawProb P (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) /
      lawProb P (fun v => v t = xstar ∧ (fun i : W => v i) = w)) *
    lawProb P (fun v => (fun i : W => v i) = w)

/-- **The mediation formula for the NIE**: P14, eq. (14b)
(`∑_{w,z} E(Y | x*, z, w) [P(z | x, w) - P(z | x*, w)] P(w)`); with `W = ∅` it is P01,
eq. (27), and P14, eq. (17). -/
noncomputable def mediationFormulaNIE (P : (Fin n → α) → ℝ) (t m y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α) : ℝ :=
  ∑ w : W → α, ∑ z : α,
    lawMean P g y (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) *
    (lawProb P (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) /
        lawProb P (fun v => v t = x ∧ (fun i : W => v i) = w) -
      lawProb P (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) /
        lawProb P (fun v => v t = xstar ∧ (fun i : W => v i) = w)) *
    lawProb P (fun v => (fun i : W => v i) = w)

omit [DecidableEq α] in
/-- Bridge: events of the induced law are events of the noise. -/
theorem lawProb_inducedLaw (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : (Fin n → α) → Prop) [DecidablePred E] :
    lawProb (M.inducedLaw μ) E = noiseProb μ (fun u => E (M.solve u)) := by
  classical
  unfold lawProb inducedLaw noiseProb
  calc ∑ v with E v, ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
          (if M.solve u = v then noiseWeight μ u else 0)
      = ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
          ∑ v with E v, (if M.solve u = v then noiseWeight μ u else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
          (if E (M.solve u) then noiseWeight μ u else 0) := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hE : E (M.solve u)
        · have hmem : M.solve u ∈ Finset.univ.filter (fun v => E v) := by
            simp [hE]
          have h0 : ∀ b ∈ Finset.univ.filter (fun v => E v), b ≠ M.solve u →
              (if M.solve u = b then noiseWeight μ u else 0) = 0 := by
            intro b _ hb
            exact if_neg (Ne.symm hb)
          have hsum := Finset.sum_eq_single_of_mem (M.solve u) hmem h0
          have hf : (if M.solve u = M.solve u then noiseWeight μ u else 0) =
              noiseWeight μ u := if_pos rfl
          rw [hsum, hf, if_pos hE]
        · have h0 : ∀ b ∈ Finset.univ.filter (fun v => E v),
              (if M.solve u = b then noiseWeight μ u else 0) = 0 := by
            intro b hb
            simp at hb
            apply if_neg
            intro hcontra
            apply hE
            rw [hcontra]
            exact hb
          have hsum : (∑ v ∈ Finset.univ.filter (fun v => E v),
              (if M.solve u = v then noiseWeight μ u else 0)) = 0 :=
            Finset.sum_eq_zero h0
          rw [hsum, if_neg hE]
    _ = ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support) with E (M.solve u),
          noiseWeight μ u := by
        rw [Finset.sum_filter]

/-- **P01, Theorem 1, eqs. (9)-(10)**: under the cross-world independence (7) the nested term
decomposes over the factual covariates `W`. No positivity is needed. -/
theorem noiseExpect_nested_eq_sum (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t m y : Fin n) (W : Finset (Fin n))
    (g : α → ℝ) (x x' : α)
    (hcross : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t x m z u y)
      (fun u => M.counterfactual t x' u m) (fun u (i : W) => M.solve u i)) :
    noiseExpect μ (fun u => g (M.nestedCounterfactual t m x x' u y)) =
      ∑ w : W → α, ∑ z : α,
        noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
            (fun u => (fun i : W => M.solve u i) = w) *
          (noiseProb μ (fun u => M.counterfactual t x' u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
  have hrhs_gen : ∀ A B C : ℝ, A / B * (C / B) * B = A * C / B := by
    intro A B C
    by_cases hB : B = 0
    · simp [hB, div_zero]
    · calc A / B * (C / B) * B = (A / B) * ((C / B) * B) := by ring
        _ = (A / B) * C := by rw [div_mul_cancel₀ _ hB]
        _ = A * C / B := div_mul_eq_mul_div _ _ _
  have hdecomp : noiseExpect μ (fun u => g (M.nestedCounterfactual t m x x' u y)) =
      ∑ w : W → α, ∑ z : α, ∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y) := by
    have hW : noiseExpect μ (fun u => g (M.nestedCounterfactual t m x x' u y)) =
        ∑ w : W → α, ∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.nestedCounterfactual t m x x' u y) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := Fintype.piFinset (fun k => (μ k).weights.support)) (t := Finset.univ)
        (g := fun u => (fun i : W => M.solve u i)) (fun u _ => Finset.mem_univ _) _).symm
    rw [hW]
    apply Finset.sum_congr rfl
    intro w _
    have hZ : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.nestedCounterfactual t m x x' u y)) =
        ∑ z : α, ∑ u ∈ ((Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w)).filter
          (fun u => M.counterfactual t x' u m = z),
          noiseWeight μ u * g (M.nestedCounterfactual t m x x' u y) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w)) (t := Finset.univ)
        (g := fun u => M.counterfactual t x' u m) (fun u _ => Finset.mem_univ _) _).symm
    rw [hZ]
    apply Finset.sum_congr rfl
    intro z _
    have hF : ((Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w)).filter
          (fun u => M.counterfactual t x' u m = z) =
        (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro u _
      show ((fun i : W => M.solve u i) = w ∧ M.counterfactual t x' u m = z) ↔
        (M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w)
      tauto
    rw [hF]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨_, hz, _⟩ := hu
    have heq := M.nestedCounterfactual_of_eq t m x x' u hz
    rw [heq]
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  have hE2 : noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
        (fun u => (fun i : W => M.solve u i) = w) =
      (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) /
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
    simp only [noiseCondExpect, noiseExpect, mul_ite, mul_zero]
    congr 1
    exact (Finset.sum_filter _ _).symm
  have hFib_yv : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) =
      ∑ yv : α, g yv * noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
        M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) := by
    have hagg : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) =
        ∑ yv : α, ∑ u ∈ ((Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w))
        (t := Finset.univ) (g := fun u => M.counterfactual₂ t x m z u y)
        (fun u _ => Finset.mem_univ _) _).symm
    rw [hagg]
    apply Finset.sum_congr rfl
    intro yv _
    have hP : ((Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv) =
        (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv ∧
            M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro u _
      show ((M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) ∧
          M.counterfactual₂ t x m z u y = yv) ↔
        (M.counterfactual₂ t x m z u y = yv ∧
          M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w)
      tauto
    rw [hP]
    have e : noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
        M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) =
        ∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv ∧
            M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
          noiseWeight μ u := rfl
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨_, hy, _, _⟩ := hu
    rw [hy]
    ring
  have hA_yv : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) =
      ∑ yv : α, g yv * noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
        (fun i : W => M.solve u i) = w) := by
    have hagg : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) =
        ∑ yv : α, ∑ u ∈ ((Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w))
        (t := Finset.univ) (g := fun u => M.counterfactual₂ t x m z u y)
        (fun u _ => Finset.mem_univ _) _).symm
    rw [hagg]
    apply Finset.sum_congr rfl
    intro yv _
    have hP : ((Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv) =
        (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv ∧ (fun i : W => M.solve u i) = w) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro u _
      show ((fun i : W => M.solve u i) = w ∧ M.counterfactual₂ t x m z u y = yv) ↔
        (M.counterfactual₂ t x m z u y = yv ∧ (fun i : W => M.solve u i) = w)
      tauto
    rw [hP]
    have e : noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
        (fun i : W => M.solve u i) = w) =
        ∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual₂ t x m z u y = yv ∧ (fun i : W => M.solve u i) = w),
          noiseWeight μ u := rfl
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨_, hy, _⟩ := hu
    rw [hy]
    ring
  have hclean : ∀ yv : α, noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
      M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) *
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) =
      noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧ (fun i : W => M.solve u i) = w) *
      noiseProb μ (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) :=
    fun yv => hcross z yv z w
  rw [hE2, hrhs_gen]
  by_cases hB : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0
  · have hweight_nonneg : ∀ u : (k : Fin n) → U k, 0 ≤ noiseWeight μ u := by
      intro u
      unfold noiseWeight
      apply Finset.prod_nonneg
      intro k _
      exact StdSimplex.weights_nonneg _
    have hB' : ∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => (fun i : W => M.solve u i) = w), noiseWeight μ u = 0 := hB
    have hvanish : ∀ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => (fun i : W => M.solve u i) = w), noiseWeight μ u = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hweight_nonneg u)).mp hB'
    have hFib0 : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huS, _, hw⟩ := hu
      have huw : u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => (fun i : W => M.solve u i) = w) := Finset.mem_filter.mpr ⟨huS, hw⟩
      have hw0 := hvanish u huw
      simp [hw0]
    have hA0 : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hw0 := hvanish u hu
      simp [hw0]
    rw [hFib0, hA0]
    simp [hB, div_zero]
  · have hmul : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
        (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
        noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) =
        (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) *
        noiseProb μ (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) := by
      have e1 : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) *
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) =
          ∑ yv : α, g yv * noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
            M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) *
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
        rw [hFib_yv, Finset.sum_mul]
      have e2 : (∑ u ∈ (Fintype.piFinset (fun k => (μ k).weights.support)).filter
          (fun u => (fun i : W => M.solve u i) = w),
          noiseWeight μ u * g (M.counterfactual₂ t x m z u y)) *
          noiseProb μ (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) =
          ∑ yv : α, g yv * noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
            (fun i : W => M.solve u i) = w) *
            noiseProb μ (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) := by
        rw [hA_yv, Finset.sum_mul]
      rw [e1, e2]
      apply Finset.sum_congr rfl
      intro yv _
      calc g yv * noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
            M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) *
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w)
          = g yv * (noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
            M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) *
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) := by ring
        _ = g yv * (noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
            (fun i : W => M.solve u i) = w) *
            noiseProb μ (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w)) := by
          rw [hclean yv]
        _ = g yv * noiseProb μ (fun u => M.counterfactual₂ t x m z u y = yv ∧
            (fun i : W => M.solve u i) = w) *
            noiseProb μ (fun u => M.counterfactual t x' u m = z ∧ (fun i : W => M.solve u i) = w) := by ring
    exact (eq_div_iff hB).mpr hmul

/-- **P01, Theorem 1, eq. (8)** (counterfactual form): under (7) for `x` and `x*`,
`NDE = ∑_{w,z} [E(Y_{xz} | w) - E(Y_{x*z} | w)] P(Z_{x*} = z | w) P(w)`. -/
theorem nde_eq_sum_counterfactual (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t m y : Fin n) (W : Finset (Fin n))
    (g : α → ℝ) (x xstar : α)
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun u (i : W) => M.solve u i)) :
    M.nde μ t m y g x xstar =
      ∑ w : W → α, ∑ z : α,
        (noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
            (fun u => (fun i : W => M.solve u i) = w) -
          noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
            (fun u => (fun i : W => M.solve u i) = w)) *
        (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
            (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
  unfold nde
  have hself : (fun u => g (M.counterfactual t xstar u y)) =
      (fun u => g (M.nestedCounterfactual t m xstar xstar u y)) := by
    funext u
    have h := M.nestedCounterfactual_self t m xstar u
    rw [h]
  rw [hself,
    noiseExpect_nested_eq_sum M μ t m y W g x xstar (fun z => hcross x (by simp) z),
    noiseExpect_nested_eq_sum M μ t m y W g xstar xstar (fun z => hcross xstar (by simp) z),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  show (∑ z : α, noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
        (fun u => (fun i : W => M.solve u i) = w) *
        (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧ (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) -
      (∑ z : α, noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
        (fun u => (fun i : W => M.solve u i) = w) *
        (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧ (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) =
      ∑ z : α, (noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
        (fun u => (fun i : W => M.solve u i) = w) -
        noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
          (fun u => (fun i : W => M.solve u i) = w)) *
      (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧ (fun i : W => M.solve u i) = w) /
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  show noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
      (fun u => (fun i : W => M.solve u i) = w) *
      (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧ (fun i : W => M.solve u i) = w) /
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) -
      noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
        (fun u => (fun i : W => M.solve u i) = w) *
        (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧ (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) =
      (noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
        (fun u => (fun i : W => M.solve u i) = w) -
        noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
          (fun u => (fun i : W => M.solve u i) = w)) *
      (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧ (fun i : W => M.solve u i) = w) /
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w)
  ring

omit [Fintype α] [DecidableEq α] in
private theorem med_aux_doNode_f_eq (M : FiniteSCM α n U) (t : Fin n) (a : α) (k : Fin n)
    (hne : k ≠ t) (z : (M.doNode t a).pa k → α) (w : U k) :
    (M.doNode t a).f k z w =
      M.f k (fun i => z ⟨i, by
        have hpa : (M.doNode t a).pa k = M.pa k := ite_eq_right hne
        rw [hpa]
        exact i.2⟩) w := by
  show (if h : k = t then a else M.f k (fun i => z ⟨i, by
    have hpa : (M.doNode t a).pa k = M.pa k := ite_eq_right h
    rw [hpa]
    exact i.2⟩) w)
    = M.f k (fun i => z ⟨i, by
      have hpa : (M.doNode t a).pa k = M.pa k := ite_eq_right hne
      rw [hpa]
      exact i.2⟩) w
  rw [dite_eq_right hne]

omit [Fintype α] [DecidableEq α] in
private theorem med_aux_solvePrefix_doNode_mem (M : FiniteSCM α n U) (u : (k : Fin n) → U k)
    {t : Fin n} {a : α} {S : Set (Fin n)}
    (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S) (htS : t ∉ S)
    (m : ℕ) (hm : m ≤ n) (i : Fin m)
    (hi : (⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩ : Fin n) ∈ S) :
    (M.doNode t a).solvePrefix u m hm i = M.solvePrefix u m hm i := by
  revert hm i hi
  induction m with
  | zero =>
      intro hm i hi
      exact Fin.elim0 i
  | succ m ih =>
      intro hm i hi
      refine Fin.lastCases
        (motive := fun i' => (⟨i'.val, Nat.lt_of_lt_of_le i'.isLt hm⟩ : Fin n) ∈ S →
          (M.doNode t a).solvePrefix u (m + 1) hm i' = M.solvePrefix u (m + 1) hm i')
        ?_ ?_ i hi
      · intro hmem
        have hL : (M.doNode t a).solvePrefix u (m + 1) hm
            = Fin.snoc ((M.doNode t a).solvePrefix u m (Nat.le_of_succ_le hm))
              ((M.doNode t a).f ⟨m, hm⟩
                (fun j => (M.doNode t a).solvePrefix u m (Nat.le_of_succ_le hm) ↑j)
                (u ⟨m, hm⟩)) := rfl
        have hR : M.solvePrefix u (m + 1) hm
            = Fin.snoc (M.solvePrefix u m (Nat.le_of_succ_le hm))
              (M.f ⟨m, hm⟩ (fun j => M.solvePrefix u m (Nat.le_of_succ_le hm) ↑j)
                (u ⟨m, hm⟩)) := rfl
        have hmemK : (⟨m, hm⟩ : Fin n) ∈ S := hmem
        have hneK : ∀ K : Fin n, K.val = m → K ≠ t := by
          intro K hval heq
          apply htS
          rw [← heq]
          have hKeq :
              K = (⟨(Fin.last m).val, Nat.lt_of_lt_of_le (Fin.last m).isLt hm⟩ : Fin n) :=
            Fin.ext (by rw [hval]; exact (Fin.val_last m).symm)
          rw [hKeq]
          exact hmem
        have hne : (⟨m, hm⟩ : Fin n) ≠ t := hneK (⟨m, hm⟩ : Fin n) rfl
        simp only [hL, hR, Fin.snoc_last]
        rw [med_aux_doNode_f_eq M t a _ hne _ _]
        congr 1
        funext i
        exact ih _ _ (hS _ hmemK _ i.2)
      · intro j hmem
        have hL : (M.doNode t a).solvePrefix u (m + 1) hm
            = Fin.snoc ((M.doNode t a).solvePrefix u m (Nat.le_of_succ_le hm))
              ((M.doNode t a).f ⟨m, hm⟩
                (fun j => (M.doNode t a).solvePrefix u m (Nat.le_of_succ_le hm) ↑j)
                (u ⟨m, hm⟩)) := rfl
        have hR : M.solvePrefix u (m + 1) hm
            = Fin.snoc (M.solvePrefix u m (Nat.le_of_succ_le hm))
              (M.f ⟨m, hm⟩ (fun j => M.solvePrefix u m (Nat.le_of_succ_le hm) ↑j)
                (u ⟨m, hm⟩)) := rfl
        simp only [hL, hR, Fin.snoc_castSucc]
        exact ih _ _ hmem

omit [Fintype α] [DecidableEq α] in
private theorem med_aux_solve_doNode_mem (M : FiniteSCM α n U) (u : (k : Fin n) → U k)
    {t : Fin n} {a : α} {S : Set (Fin n)}
    (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S) (htS : t ∉ S)
    {i : Fin n} (hi : i ∈ S) :
    (M.doNode t a).solve u i = M.solve u i :=
  med_aux_solvePrefix_doNode_mem M u hS htS n le_rfl i hi

omit [Fintype α] [DecidableEq α] in
private theorem med_aux_solve_doNode_doNode_mem (M : FiniteSCM α n U) (u : (k : Fin n) → U k)
    {t m : Fin n} {a b : α} {S : Set (Fin n)}
    (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S) (htS : t ∉ S) (hmS : m ∉ S)
    {i : Fin n} (hi : i ∈ S) :
    ((M.doNode t a).doNode m b).solve u i = M.solve u i := by
  have hS' : ∀ j ∈ S, ∀ k ∈ (M.doNode t a).pa j, Fin.castLE j.2.le k ∈ S := by
    intro j hj k hk
    have hpa : (M.doNode t a).pa j = M.pa j := by
      by_cases hjt : j = t
      · rw [hjt] at hj
        exact absurd hj htS
      · exact ite_eq_right hjt
    rw [hpa] at hk
    exact hS j hj k hk
  calc ((M.doNode t a).doNode m b).solve u i
      = (M.doNode t a).solve u i :=
        med_aux_solve_doNode_mem (M.doNode t a) u hS' hmS hi
    _ = M.solve u i := med_aux_solve_doNode_mem M u hS htS hi

omit [DecidableEq α] in
private theorem med_aux_lawMean_inducedLaw (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (g : α → ℝ) (y : Fin n)
    (E : (Fin n → α) → Prop) [DecidablePred E] :
    lawMean (M.inducedLaw μ) g y E =
      noiseCondExpect μ (fun u => g (M.solve u y)) (fun u => E (M.solve u)) := by
  unfold lawMean noiseCondExpect
  rw [lawProb_inducedLaw]
  have hnum : (∑ v with E v, (M.inducedLaw μ) v * g (v y))
      = noiseExpect μ (fun u => if E (M.solve u) then g (M.solve u y) else 0) := by
    unfold noiseExpect inducedLaw
    simp only []
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hE : E (M.solve u)
    · rw [ite_eq_left hE]
      rw [Finset.sum_eq_single (M.solve u)]
      · rw [ite_eq_left rfl]
      · intro v _ hne
        rw [ite_eq_right (fun h => hne h.symm), zero_mul]
      · intro hcon
        exfalso
        apply hcon
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hE⟩
    · rw [ite_eq_right hE, mul_zero]
      apply Finset.sum_eq_zero
      intro v hv
      rw [Finset.mem_filter] at hv
      have hne : M.solve u ≠ v := by
        intro h
        rw [← h] at hv
        exact hE hv.2
      rw [ite_eq_right hne, zero_mul]
  rw [hnum]

private theorem med_aux_lawMean_doNode_doNode (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (a b : α) (w : W → α)
    {S : Set (Fin n)} (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S)
    (htS : t ∉ S) (hmS : m ∉ S) (hWS : ∀ i ∈ W, i ∈ S) :
    lawMean (((M.doNode t a).doNode m b).inducedLaw μ) g y
        (fun v => (fun i : W => v i) = w) =
      noiseCondExpect μ (fun u => g (M.counterfactual₂ t a m b u y))
        (fun u => (fun i : W => M.solve u i) = w) := by
  have hW : ∀ u, (fun i : W => ((M.doNode t a).doNode m b).solve u i)
      = (fun i : W => M.solve u i) :=
    fun u => funext fun i => med_aux_solve_doNode_doNode_mem M u hS htS hmS (hWS i i.2)
  have hY : ∀ u, g (((M.doNode t a).doNode m b).solve u y)
      = g (M.counterfactual₂ t a m b u y) := fun u => rfl
  have hstep : lawMean (((M.doNode t a).doNode m b).inducedLaw μ) g y
        (fun v => (fun i : W => v i) = w)
      = noiseCondExpect μ (fun u => g (((M.doNode t a).doNode m b).solve u y))
        (fun u => (fun i : W => ((M.doNode t a).doNode m b).solve u i) = w) :=
    med_aux_lawMean_inducedLaw (((M.doNode t a).doNode m b)) μ g y
      (fun v => (fun i : W => v i) = w)
  rw [hstep]
  simp only [hW, hY]

private theorem med_aux_lawProb_doNode (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n}
    (W : Finset (Fin n)) (a : α) (z : α) (w : W → α)
    {S : Set (Fin n)} (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S)
    (htS : t ∉ S) (hWS : ∀ i ∈ W, i ∈ S) :
    lawProb ((M.doNode t a).inducedLaw μ)
        (fun v => v m = z ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.counterfactual t a u m = z ∧ (fun i : W => M.solve u i) = w) := by
  have hW : ∀ u, (fun i : W => (M.doNode t a).solve u i) = (fun i : W => M.solve u i) :=
    fun u => funext fun i => med_aux_solve_doNode_mem M u hS htS (hWS i i.2)
  have hM : ∀ u, (M.doNode t a).solve u m = M.counterfactual t a u m := fun u => rfl
  have hstep : lawProb ((M.doNode t a).inducedLaw μ)
        (fun v => v m = z ∧ (fun i : W => v i) = w)
      = noiseProb μ (fun u => (M.doNode t a).solve u m = z ∧
        (fun i : W => (M.doNode t a).solve u i) = w) :=
    lawProb_inducedLaw (M.doNode t a) μ (fun v => v m = z ∧ (fun i : W => v i) = w)
  rw [hstep]
  simp only [hW, hM]

private theorem med_aux_lawProb_doNode_W (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t : Fin n}
    (W : Finset (Fin n)) (a : α) (w : W → α)
    {S : Set (Fin n)} (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S)
    (htS : t ∉ S) (hWS : ∀ i ∈ W, i ∈ S) :
    lawProb ((M.doNode t a).inducedLaw μ) (fun v => (fun i : W => v i) = w) =
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
  have hW : ∀ u, (fun i : W => (M.doNode t a).solve u i) = (fun i : W => M.solve u i) :=
    fun u => funext fun i => med_aux_solve_doNode_mem M u hS htS (hWS i i.2)
  have hstep : lawProb ((M.doNode t a).inducedLaw μ) (fun v => (fun i : W => v i) = w)
      = noiseProb μ (fun u => (fun i : W => (M.doNode t a).solve u i) = w) :=
    lawProb_inducedLaw (M.doNode t a) μ (fun v => (fun i : W => v i) = w)
  rw [hstep]
  simp only [hW]

/-- **P14, Theorem 1, eq. (13)** (experimental identification, P01 Theorem 1): with `W` inside
a parent-closed set `S` avoiding `t` and `m` (A-1: no member of `W` is a descendant of the
treatment or the mediator; the only place this assumption appears), the factors are
interventional laws. -/
theorem nde_eq_doFormula (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    {t m : Fin n} (y : Fin n) (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    {S : Set (Fin n)} (hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S)
    (htS : t ∉ S) (hmS : m ∉ S) (hWS : ∀ i ∈ W, i ∈ S)
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun u (i : W) => M.solve u i)) :
    M.nde μ t m y g x xstar =
      ∑ w : W → α, ∑ z : α,
        (lawMean (((M.doNode t x).doNode m z).inducedLaw μ) g y
            (fun v => (fun i : W => v i) = w) -
          lawMean (((M.doNode t xstar).doNode m z).inducedLaw μ) g y
            (fun v => (fun i : W => v i) = w)) *
        (lawProb ((M.doNode t xstar).inducedLaw μ) (fun v => v m = z ∧ (fun i : W => v i) = w) /
          lawProb ((M.doNode t xstar).inducedLaw μ) (fun v => (fun i : W => v i) = w)) *
        lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) := by
  rw [nde_eq_sum_counterfactual M μ t m y W g x xstar hcross]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  rw [med_aux_lawMean_doNode_doNode M μ y W g x z w hS htS hmS hWS,
    med_aux_lawMean_doNode_doNode M μ y W g xstar z w hS htS hmS hWS,
    med_aux_lawProb_doNode M μ W xstar z w hS htS hWS,
    med_aux_lawProb_doNode_W M μ W xstar w hS htS hWS,
    show lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w)
      = noiseProb μ (fun u => (fun i : W => M.solve u i) = w) from
      lawProb_inducedLaw M μ (fun v => (fun i : W => v i) = w)]

private theorem med_aux_noiseWeight_nonneg (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (u : (k : Fin n) → U k) : 0 ≤ noiseWeight μ u := by
  unfold noiseWeight
  positivity

private theorem med_aux_noiseProb_nonneg (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (E : ((k : Fin n) → U k) → Prop) [DecidablePred E] : 0 ≤ noiseProb μ E := by
  unfold noiseProb
  apply Finset.sum_nonneg
  intro u _
  exact med_aux_noiseWeight_nonneg μ u

private theorem med_aux_noiseProb_congr (μ : (k : Fin n) → StdSimplex ℝ (U k))
    {p q : ((k : Fin n) → U k) → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ u, p u ↔ q u) : noiseProb μ p = noiseProb μ q := by
  unfold noiseProb
  have hfilter : (Fintype.piFinset (fun k => (μ k).weights.support)).filter p =
      (Fintype.piFinset (fun k => (μ k).weights.support)).filter q := by
    apply Finset.filter_congr
    intro u _
    exact h u
  rw [hfilter]

private theorem med_aux_noiseProb_mono (μ : (k : Fin n) → StdSimplex ℝ (U k))
    {p q : ((k : Fin n) → U k) → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ u, p u → q u) : noiseProb μ p ≤ noiseProb μ q := by
  unfold noiseProb
  have hsub : (Fintype.piFinset (fun k => (μ k).weights.support)).filter p ⊆
      (Fintype.piFinset (fun k => (μ k).weights.support)).filter q := by
    apply Finset.monotone_filter_right
    intro u _ hpu
    exact h u hpu
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro u _ _
  exact med_aux_noiseWeight_nonneg μ u

private theorem med_aux_noiseProb_eq_zero_of_subset (μ : (k : Fin n) → StdSimplex ℝ (U k))
    {p q : ((k : Fin n) → U k) → Prop} [DecidablePred p] [DecidablePred q]
    (hsub : ∀ u, p u → q u) (hq0 : noiseProb μ q = 0) : noiseProb μ p = 0 := by
  have hle : noiseProb μ p ≤ noiseProb μ q := med_aux_noiseProb_mono μ hsub
  have hnonneg : 0 ≤ noiseProb μ p := med_aux_noiseProb_nonneg μ _
  rw [hq0] at hle
  exact le_antisymm hle hnonneg

private theorem med_aux_noiseExpect_if_eq_sum (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (Y : ((k : Fin n) → U k) → α) (E : ((k : Fin n) → U k) → Prop)
    [DecidablePred E] (g : α → ℝ) :
    noiseExpect μ (fun u => if E u then g (Y u) else 0) =
      ∑ y0 : α, g y0 * noiseProb μ (fun u => Y u = y0 ∧ E u) := by
  classical
  unfold noiseExpect noiseProb
  calc ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
        noiseWeight μ u * (if E u then g (Y u) else 0)
      = ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
          ∑ y0 : α, (if Y u = y0 ∧ E u then noiseWeight μ u * g y0 else 0) := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hE : E u
        · have hY : (if E u then g (Y u) else 0) =
              ∑ y0 : α, (if Y u = y0 then g y0 else 0) := by
            rw [if_pos hE]
            symm
            have h := Finset.sum_ite_eq Finset.univ (Y u) g
            simp only [Finset.mem_univ, if_true] at h
            exact h
          have hmul : noiseWeight μ u * (if E u then g (Y u) else 0) =
              ∑ y0 : α, noiseWeight μ u * (if Y u = y0 then g y0 else 0) := by
            rw [hY, Finset.mul_sum]
          rw [hmul]
          apply Finset.sum_congr rfl
          intro y0 _
          by_cases hy : Y u = y0
          · have htrue : (Y u = y0 ∧ E u) := ⟨hy, hE⟩
            simp [htrue, hy]
          · have hfalse : ¬ (Y u = y0 ∧ E u) := fun h => hy h.1
            simp [hfalse, hy]
        · have hL : noiseWeight μ u * (if E u then g (Y u) else 0) = 0 := by
            simp [hE]
          have hR : (∑ y0 : α, (if Y u = y0 ∧ E u then noiseWeight μ u * g y0 else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro y0 _
            have hfalse : ¬ (Y u = y0 ∧ E u) := fun h => hE h.2
            simp [hfalse]
          rw [hL, hR]
    _ = ∑ y0 : α, ∑ u ∈ Fintype.piFinset (fun k => (μ k).weights.support),
          (if Y u = y0 ∧ E u then noiseWeight μ u * g y0 else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ y0 : α, g y0 * noiseProb μ (fun u => Y u = y0 ∧ E u) := by
        apply Finset.sum_congr rfl
        intro y0 _
        unfold noiseProb
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u _
        by_cases h : Y u = y0 ∧ E u <;> simp [h, mul_comm]

private theorem med_aux_mediator_NDE_eq (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t m : Fin n) (W : Finset (Fin n))
    (xstar : α) (w : W → α) (z : α)
    (hXZ : NoiseCondIndep μ (fun u => M.counterfactual t xstar u m)
      (fun u => M.solve u t) (fun u (i : W) => M.solve u i))
    (hpos : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0 →
      noiseProb μ (fun u => M.solve u t = xstar ∧ (fun i : W => M.solve u i) = w) ≠ 0) :
    noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
        (fun i : W => M.solve u i) = w) /
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) =
    noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) /
      noiseProb μ (fun u => M.solve u t = xstar ∧
        (fun i : W => M.solve u i) = w) := by
  have hBeq : noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
      M.solve u t = xstar ∧ (fun i : W => M.solve u i) = w) =
      noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    constructor
    · intro h
      have hXt : M.solve u t = xstar := h.2.1
      have hcm : M.counterfactual t xstar u m = M.solve u m := by
        rw [M.counterfactual_eq_solve hXt]
      have hZ : M.solve u m = z := hcm.symm.trans h.1
      exact ⟨hXt, hZ, h.2.2⟩
    · intro h
      have hXt : M.solve u t = xstar := h.1
      have hcm : M.counterfactual t xstar u m = M.solve u m := by
        rw [M.counterfactual_eq_solve hXt]
      have hZc : M.counterfactual t xstar u m = z := hcm.trans h.2.1
      exact ⟨hZc, hXt, h.2.2⟩
  have hXZeq := hXZ z xstar w
  rw [hBeq] at hXZeq
  by_cases hC : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0
  · have hL : noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
        (fun i : W => M.solve u i) = w) /
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      simp [hC]
    have hB0 : noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) = 0 := by
      exact med_aux_noiseProb_eq_zero_of_subset μ (fun u h => h.2.2) hC
    have hR : noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) /
        noiseProb μ (fun u => M.solve u t = xstar ∧
          (fun i : W => M.solve u i) = w) = 0 := by
      simp [hB0]
    rw [hL, hR]
  · have hD : noiseProb μ (fun u => M.solve u t = xstar ∧
      (fun i : W => M.solve u i) = w) ≠ 0 := hpos hC
    rw [div_eq_div_iff hC hD]
    exact hXZeq.symm

private theorem med_aux_algebra_indep_eqs (A C D E G H : ℝ) (hDNe : D ≠ 0)
    (h1 : E * C = A * D) (h2 : G * D = E * H) : A * H = G * C := by
  have h1H : (E * C) * H = (A * D) * H := congrArg (· * H) h1
  have h2C : (G * D) * C = (E * H) * C := congrArg (· * C) h2
  have heq1 : E * C * H = E * H * C := by ring
  have heq2 : G * D * C = G * C * D := by ring
  have heq3 : A * D * H = A * H * D := by ring
  rw [heq1] at h1H
  rw [heq3] at h1H
  rw [heq2] at h2C
  have hCD : G * C * D = A * H * D := h2C.trans h1H
  have hGC : G * C = A * H := mul_right_cancel₀ hDNe hCD
  exact hGC.symm

private theorem med_aux_outcome_prob_NDE_eq (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t m y : Fin n) (W : Finset (Fin n))
    (x' : α) (w : W → α) (z y0 : α)
    (hXY : NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
      (fun u => M.solve u t) (fun u (i : W) => M.solve u i))
    (hZY : NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
      (fun u => M.solve u m) (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hCNe : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0)
    (hDNe : noiseProb μ (fun u => M.solve u t = x' ∧
      (fun i : W => M.solve u i) = w) ≠ 0)
    (hHNe : noiseProb μ (fun u => M.solve u t = x' ∧ M.solve u m = z ∧
      (fun i : W => M.solve u i) = w) ≠ 0) :
    noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = y0 ∧
        (fun i : W => M.solve u i) = w) /
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) =
    noiseProb μ (fun u => M.solve u y = y0 ∧ M.solve u t = x' ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) /
      noiseProb μ (fun u => M.solve u t = x' ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
  have hXYeq := hXY y0 x' w
  have hZYeq0 := hZY y0 z (x', w)
  have hP2 : noiseProb μ (fun u => (M.solve u t, fun i : W => M.solve u i) = (x', w)) =
      noiseProb μ (fun u => M.solve u t = x' ∧ (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    simp [Prod.mk.injEq]
  have hP3 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = y0 ∧
      (M.solve u t, fun i : W => M.solve u i) = (x', w)) =
      noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = y0 ∧ M.solve u t = x' ∧
        (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    simp [Prod.mk.injEq]
  have hP4 : noiseProb μ (fun u => M.solve u m = z ∧
      (M.solve u t, fun i : W => M.solve u i) = (x', w)) =
      noiseProb μ (fun u => M.solve u m = z ∧ M.solve u t = x' ∧
        (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    simp [Prod.mk.injEq]
  have hP1 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = y0 ∧ M.solve u m = z ∧
      (M.solve u t, fun i : W => M.solve u i) = (x', w)) =
      noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = y0 ∧ M.solve u m = z ∧
        M.solve u t = x' ∧ (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    simp [Prod.mk.injEq]
  rw [hP1, hP2, hP3, hP4] at hZYeq0
  have hP1_obs : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = y0 ∧
      M.solve u m = z ∧ M.solve u t = x' ∧ (fun i : W => M.solve u i) = w) =
      noiseProb μ (fun u => M.solve u y = y0 ∧ M.solve u t = x' ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    constructor
    · intro h
      have hXt : M.solve u t = x' := h.2.2.1
      have hZm : M.solve u m = z := h.2.1
      have hcf : M.counterfactual₂ t x' m z u = M.solve u :=
        M.counterfactual₂_eq_solve hXt hZm
      have hYc : M.counterfactual₂ t x' m z u y = M.solve u y := by
        rw [hcf]
      have hY : M.solve u y = y0 := hYc.symm.trans h.1
      exact ⟨hY, hXt, hZm, h.2.2.2⟩
    · intro h
      have hXt : M.solve u t = x' := h.2.1
      have hZm : M.solve u m = z := h.2.2.1
      have hcf : M.counterfactual₂ t x' m z u = M.solve u :=
        M.counterfactual₂_eq_solve hXt hZm
      have hYc : M.counterfactual₂ t x' m z u y = M.solve u y := by
        rw [hcf]
      have hYc0 : M.counterfactual₂ t x' m z u y = y0 := hYc.trans h.1
      exact ⟨hYc0, hZm, hXt, h.2.2.2⟩
  have hFH : noiseProb μ (fun u => M.solve u m = z ∧ M.solve u t = x' ∧
      (fun i : W => M.solve u i) = w) =
      noiseProb μ (fun u => M.solve u t = x' ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
    apply med_aux_noiseProb_congr
    intro u
    constructor
    · intro h
      exact ⟨h.2.1, h.1, h.2.2⟩
    · intro h
      exact ⟨h.2.1, h.1, h.2.2⟩
  rw [hP1_obs, hFH] at hZYeq0
  rw [div_eq_div_iff hCNe hHNe]
  exact med_aux_algebra_indep_eqs _ _ _ _ _ _ hDNe hXYeq hZYeq0

private theorem med_aux_sum_div (f : α → ℝ) (C : ℝ) :
    (∑ y0 : α, f y0) / C = ∑ y0 : α, f y0 / C := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private theorem med_aux_outcome_expect_NDE_eq (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t m y : Fin n) (W : Finset (Fin n))
    (x' : α) (w : W → α) (z : α) (g : α → ℝ)
    (hXY : NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
      (fun u => M.solve u t) (fun u (i : W) => M.solve u i))
    (hZY : NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
      (fun u => M.solve u m) (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hCNe : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0)
    (hDNe : noiseProb μ (fun u => M.solve u t = x' ∧
      (fun i : W => M.solve u i) = w) ≠ 0)
    (hHNe : noiseProb μ (fun u => M.solve u t = x' ∧ M.solve u m = z ∧
      (fun i : W => M.solve u i) = w) ≠ 0) :
    noiseCondExpect μ (fun u => g (M.counterfactual₂ t x' m z u y))
        (fun u => (fun i : W => M.solve u i) = w) =
      noiseCondExpect μ (fun u => g (M.solve u y))
        (fun u => M.solve u t = x' ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
  unfold noiseCondExpect
  have hNumC := med_aux_noiseExpect_if_eq_sum μ
    (fun u => M.counterfactual₂ t x' m z u y)
    (fun u => (fun i : W => M.solve u i) = w) g
  have hNumO := med_aux_noiseExpect_if_eq_sum μ
    (fun u => M.solve u y)
    (fun u => M.solve u t = x' ∧ M.solve u m = z ∧
      (fun i : W => M.solve u i) = w) g
  rw [hNumC, hNumO, med_aux_sum_div, med_aux_sum_div]
  apply Finset.sum_congr rfl
  intro y0 _
  have hProb := med_aux_outcome_prob_NDE_eq M μ t m y W x' w z y0
    hXY hZY hCNe hDNe hHNe
  rw [mul_div_assoc, mul_div_assoc, hProb]

/-- **The mediation formula** (P01, Theorem 2 with eq. (17); P14, Corollary 1, eq. (14a)) under
the four no-confounding conditions H1-H4 and support positivity. Positivity (`hposW`, `hposZ`)
is stated in neither source; the formula is false without it (module docstring). -/
theorem nde_eq_mediationFormulaNDE (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    -- (H1) no X-Y confounding given W
    (hXY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u t)
        (fun u (i : W) => M.solve u i))
    -- (H2) no Z-Y confounding given X and W
    (hZY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u m)
        (fun u => (M.solve u t, fun i : W => M.solve u i)))
    -- (H3) no X-Z confounding given W
    (hXZ : NoiseCondIndep μ (fun u => M.counterfactual t xstar u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i))
    -- (H4) cross-world: no Z-Y confounder affected by X (P01, eq. (7))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun u (i : W) => M.solve u i))
    -- (P) positivity on the support (in neither source)
    (hposW : ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ (fun i : W => v i) = w) ≠ 0)
    (hposZ : ∀ (w : W → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0) :
    M.nde μ t m y g x xstar = mediationFormulaNDE (M.inducedLaw μ) t m y W g x xstar := by
  have hNDE := nde_eq_sum_counterfactual M μ t m y W g x xstar hcross
  have hposW_noise : ∀ w : W → α,
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0 →
      noiseProb μ (fun u => M.solve u t = xstar ∧ (fun i : W => M.solve u i) = w) ≠ 0 := by
    intro w hWPNe
    have hWbridge : lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) =
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ (fun v => (fun i : W => v i) = w)
    have hWlawNe : lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 := by
      rw [hWbridge]
      exact hWPNe
    have hXWlawNe := hposW w hWlawNe
    have hXWbridge : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ (fun i : W => v i) = w) =
        noiseProb μ (fun u => M.solve u t = xstar ∧ (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ (fun v => v t = xstar ∧ (fun i : W => v i) = w)
    rw [← hXWbridge]
    exact hXWlawNe
  have hposZ_noise : ∀ (w : W → α) (z : α),
      noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 →
      noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 := by
    intro w z hOP1Ne
    have hOP1bridge : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) =
        noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ
        (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)
    have hOP1lawNe : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 := by
      rw [hOP1bridge]
      exact hOP1Ne
    have hHxLawNe := hposZ w z hOP1lawNe
    have hHxbridge : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) =
        noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ
        (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w)
    rw [← hHxbridge]
    exact hHxLawNe
  rw [hNDE]
  unfold mediationFormulaNDE
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  have hLMx : lawMean (M.inducedLaw μ) g y
      (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) =
      noiseCondExpect μ (fun u => g (M.solve u y))
        (fun u => M.solve u t = x ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
    have h := med_aux_lawMean_inducedLaw M μ g y
      (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w)
    simpa using h
  have hLMxstar : lawMean (M.inducedLaw μ) g y
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) =
      noiseCondExpect μ (fun u => g (M.solve u y))
        (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
    have h := med_aux_lawMean_inducedLaw M μ g y
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)
    simpa using h
  have hLP1 : lawProb (M.inducedLaw μ)
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)
  have hLP2 : lawProb (M.inducedLaw μ)
      (fun v => v t = xstar ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.solve u t = xstar ∧
        (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ
      (fun v => v t = xstar ∧ (fun i : W => v i) = w)
  have hLP3 : lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) =
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ (fun v => (fun i : W => v i) = w)
  rw [hLMx, hLMxstar, hLP1, hLP2, hLP3]
  have hMed := med_aux_mediator_NDE_eq M μ t m W xstar w z hXZ (hposW_noise w)
  by_cases hOP1 : noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
      (fun i : W => M.solve u i) = w) = 0
  · have hR0 : (noiseCondExpect μ (fun u => g (M.solve u y))
          (fun u => M.solve u t = x ∧ M.solve u m = z ∧ (fun i : W => M.solve u i) = w) -
          noiseCondExpect μ (fun u => g (M.solve u y))
          (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧ (fun i : W => M.solve u i) = w)) *
        (noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
            (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => M.solve u t = xstar ∧ (fun i : W => M.solve u i) = w)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      simp [hOP1]
    have hMP0 : noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
          (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      rw [hMed]
      simp [hOP1]
    have hL0 : (noiseCondExpect μ (fun u => g (M.counterfactual₂ t x m z u y))
          (fun u => (fun i : W => M.solve u i) = w) -
          noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
          (fun u => (fun i : W => M.solve u i) = w)) *
        (noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
            (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      simp [hMP0]
    rw [hL0, hR0]
  · have hx_mem : x ∈ ({x, xstar} : Finset α) := by simp
    have hxstar_mem : xstar ∈ ({x, xstar} : Finset α) := by simp
    have hCNe : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0 := by
      intro hC0
      apply hOP1
      exact med_aux_noiseProb_eq_zero_of_subset μ (fun u h => h.2.2) hC0
    have hDNe_xstar : noiseProb μ (fun u => M.solve u t = xstar ∧
        (fun i : W => M.solve u i) = w) ≠ 0 :=
      hposW_noise w hCNe
    have hHNe_xstar : noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 := hOP1
    have hHNe_x : noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 :=
      hposZ_noise w z hOP1
    have hDNe_x : noiseProb μ (fun u => M.solve u t = x ∧
        (fun i : W => M.solve u i) = w) ≠ 0 := by
      intro hD0
      apply hHNe_x
      exact med_aux_noiseProb_eq_zero_of_subset μ (fun u h => ⟨h.1, h.2.2⟩) hD0
    have hCE_x := med_aux_outcome_expect_NDE_eq M μ t m y W x w z g
      (hXY x hx_mem z) (hZY x hx_mem z) hCNe hDNe_x hHNe_x
    have hCE_xstar := med_aux_outcome_expect_NDE_eq M μ t m y W xstar w z g
      (hXY xstar hxstar_mem z) (hZY xstar hxstar_mem z) hCNe hDNe_xstar hHNe_xstar
    rw [hCE_x, hCE_xstar, hMed]

/-- The NIE twin (P01, Theorem 4, eqs. (25)-(26); P14, eq. (14b)): H1 and H2 at `x*`, H3 at
`x` and `x*`, the cross-world condition (25), and positivity in both directions. -/
theorem nie_eq_mediationFormulaNIE (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    (hXY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u t) (fun u (i : W) => M.solve u i))
    (hZY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u m) (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hXZ : ∀ x' ∈ ({x, xstar} : Finset α), NoiseCondIndep μ
      (fun u => M.counterfactual t x' u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
        (fun u => M.counterfactual t x' u m) (fun u (i : W) => M.solve u i))
    (hposW : ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
      ∀ x' ∈ ({x, xstar} : Finset α),
        lawProb (M.inducedLaw μ) (fun v => v t = x' ∧ (fun i : W => v i) = w) ≠ 0)
    (hposZ : ∀ (w : W → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0) :
    M.nie μ t m y g x xstar = mediationFormulaNIE (M.inducedLaw μ) t m y W g x xstar := by
  have hx_mem : x ∈ ({x, xstar} : Finset α) := by simp
  have hxstar_mem : xstar ∈ ({x, xstar} : Finset α) := by simp
  have hposW_noise : ∀ (w : W → α) (x' : α), x' ∈ ({x, xstar} : Finset α) →
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0 →
      noiseProb μ (fun u => M.solve u t = x' ∧ (fun i : W => M.solve u i) = w) ≠ 0 := by
    intro w x' hx' hWPNe
    have hWbridge : lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) =
        noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ (fun v => (fun i : W => v i) = w)
    have hWlawNe : lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 := by
      rw [hWbridge]
      exact hWPNe
    have hXWlawNe := hposW w hWlawNe x' hx'
    have hXWbridge : lawProb (M.inducedLaw μ)
        (fun v => v t = x' ∧ (fun i : W => v i) = w) =
        noiseProb μ (fun u => M.solve u t = x' ∧ (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ (fun v => v t = x' ∧ (fun i : W => v i) = w)
    rw [← hXWbridge]
    exact hXWlawNe
  have hposZ_noise : ∀ (w : W → α) (z : α),
      noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 →
      noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 := by
    intro w z hOPxNe
    have hOPxbridge : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) =
        noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ
        (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w)
    have hOPxlawNe : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 := by
      rw [hOPxbridge]
      exact hOPxNe
    have hOPxstarLawNe := hposZ w z hOPxlawNe
    have hOPxstarbridge : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) =
        noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
      simpa using lawProb_inducedLaw M μ
        (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)
    rw [← hOPxstarbridge]
    exact hOPxstarLawNe
  have hNest1 := noiseExpect_nested_eq_sum M μ t m y W g xstar x
    (fun z => hcross x hx_mem z)
  have hNest2 := noiseExpect_nested_eq_sum M μ t m y W g xstar xstar
    (fun z => hcross xstar hxstar_mem z)
  have hEq : (fun u : (k : Fin n) → U k => g (M.counterfactual t xstar u y)) =
      (fun u => g (M.nestedCounterfactual t m xstar xstar u y)) := by
    funext u
    have h := M.nestedCounterfactual_self t m xstar u
    rw [← h]
  have hNIE_sum : M.nie μ t m y g x xstar =
      ∑ w : W → α, ∑ z : α,
        noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
            (fun u => (fun i : W => M.solve u i) = w) *
          (noiseProb μ (fun u => M.counterfactual t x u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w) -
            noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
    unfold nie
    rw [hEq, hNest1, hNest2]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hNIE_sum]
  unfold mediationFormulaNIE
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro z _
  have hLM : lawMean (M.inducedLaw μ) g y
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) =
      noiseCondExpect μ (fun u => g (M.solve u y))
        (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
          (fun i : W => M.solve u i) = w) := by
    have h := med_aux_lawMean_inducedLaw M μ g y
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)
    simpa using h
  have hLPx : lawProb (M.inducedLaw μ)
      (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ
      (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w)
  have hLPxstar : lawProb (M.inducedLaw μ)
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ
      (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w)
  have hLP2x : lawProb (M.inducedLaw μ)
      (fun v => v t = x ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.solve u t = x ∧
        (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ
      (fun v => v t = x ∧ (fun i : W => v i) = w)
  have hLP2xstar : lawProb (M.inducedLaw μ)
      (fun v => v t = xstar ∧ (fun i : W => v i) = w) =
      noiseProb μ (fun u => M.solve u t = xstar ∧
        (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ
      (fun v => v t = xstar ∧ (fun i : W => v i) = w)
  have hLP3 : lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) =
      noiseProb μ (fun u => (fun i : W => M.solve u i) = w) := by
    simpa using lawProb_inducedLaw M μ (fun v => (fun i : W => v i) = w)
  rw [hLM, hLPx, hLPxstar, hLP2x, hLP2xstar, hLP3]
  have hMed_x := med_aux_mediator_NDE_eq M μ t m W x w z
    (hXZ x hx_mem) (hposW_noise w x hx_mem)
  have hMed_xstar := med_aux_mediator_NDE_eq M μ t m W xstar w z
    (hXZ xstar hxstar_mem) (hposW_noise w xstar hxstar_mem)
  by_cases hOP : noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
      (fun i : W => M.solve u i) = w) = 0
  · have hOPx0 : noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) = 0 := by
      by_contra hNe
      exact (hposZ_noise w z hNe) hOP
    have hMPx0 : noiseProb μ (fun u => M.counterfactual t x u m = z ∧
          (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      rw [hMed_x]
      simp [hOPx0]
    have hMPxstar0 : noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
          (fun i : W => M.solve u i) = w) /
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      rw [hMed_xstar]
      simp [hOP]
    have hL0 : noiseCondExpect μ (fun u => g (M.counterfactual₂ t xstar m z u y))
          (fun u => (fun i : W => M.solve u i) = w) *
          (noiseProb μ (fun u => M.counterfactual t x u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w) -
            noiseProb μ (fun u => M.counterfactual t xstar u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => (fun i : W => M.solve u i) = w)) *
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      simp [hMPx0, hMPxstar0]
    have hR0 : noiseCondExpect μ (fun u => g (M.solve u y))
          (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
            (fun i : W => M.solve u i) = w) *
          (noiseProb μ (fun u => M.solve u t = x ∧ M.solve u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => M.solve u t = x ∧
              (fun i : W => M.solve u i) = w) -
            noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
              (fun i : W => M.solve u i) = w) /
            noiseProb μ (fun u => M.solve u t = xstar ∧
              (fun i : W => M.solve u i) = w)) *
          noiseProb μ (fun u => (fun i : W => M.solve u i) = w) = 0 := by
      simp [hOPx0, hOP]
    rw [hL0, hR0]
  · have hCNe : noiseProb μ (fun u => (fun i : W => M.solve u i) = w) ≠ 0 := by
      intro hC0
      apply hOP
      exact med_aux_noiseProb_eq_zero_of_subset μ (fun u h => h.2.2) hC0
    have hDNe : noiseProb μ (fun u => M.solve u t = xstar ∧
        (fun i : W => M.solve u i) = w) ≠ 0 :=
      hposW_noise w xstar hxstar_mem hCNe
    have hHNe : noiseProb μ (fun u => M.solve u t = xstar ∧ M.solve u m = z ∧
        (fun i : W => M.solve u i) = w) ≠ 0 := hOP
    have hCE := med_aux_outcome_expect_NDE_eq M μ t m y W xstar w z g
      (hXY z) (hZY z) hCNe hDNe hHNe
    rw [hCE, hMed_x, hMed_xstar]

private theorem med_aux_noiseProb_eq_one_of_forall (μ : (k : Fin n) → StdSimplex ℝ (U k))
    {p : ((k : Fin n) → U k) → Prop} [DecidablePred p] (h : ∀ u, p u) :
    noiseProb μ p = 1 := by
  unfold noiseProb
  have hfilter : (Fintype.piFinset (fun k => (μ k).weights.support)).filter p =
      Fintype.piFinset (fun k => (μ k).weights.support) :=
    Finset.filter_true_of_mem (fun u _ => h u)
  rw [hfilter]
  exact sum_noiseWeight_eq_one μ

private theorem med_aux_lawProb_congr (P : (Fin n → α) → ℝ)
    {E1 E2 : (Fin n → α) → Prop} [DecidablePred E1] [DecidablePred E2]
    (h : ∀ v, E1 v ↔ E2 v) : lawProb P E1 = lawProb P E2 := by
  unfold lawProb
  have hfilter : Finset.univ.filter E1 = Finset.univ.filter E2 := by
    apply Finset.filter_congr
    intro v _
    exact h v
  rw [hfilter]

private theorem med_aux_lawMean_congr (P : (Fin n → α) → ℝ) (g : α → ℝ) (y : Fin n)
    {E1 E2 : (Fin n → α) → Prop} [DecidablePred E1] [DecidablePred E2]
    (h : ∀ v, E1 v ↔ E2 v) : lawMean P g y E1 = lawMean P g y E2 := by
  unfold lawMean
  have hfilter : Finset.univ.filter E1 = Finset.univ.filter E2 := by
    apply Finset.filter_congr
    intro v _
    exact h v
  have hNum : (∑ v with E1 v, P v * g (v y)) = ∑ v with E2 v, P v * g (v y) := by
    rw [hfilter]
  have hDen := med_aux_lawProb_congr P h
  rw [hNum, hDen]

private theorem med_aux_empty_fun_eq {n : ℕ} {β : (∅ : Finset (Fin n)) → Type*} (f g : ∀ i, β i) :
    f = g :=
  funext fun i => (Finset.notMem_empty _ i.2).elim

/-- **The mediation formula without covariates** (P01, eq. (17); P14, eq. (16); the card's
formula): `NDE = ∑_z [E(Y | x, z) - E(Y | x*, z)] P(z | x*)`, under H1-H4 with `W = ∅`
(unconditional independences, written with the trivial covariate `fun _ => ()`) and
positivity. The positivity of the planned roadmap node (`P(X = x) > 0` for both values and
`P(Z = z, X = x) > 0` for both values whenever `P(z | x) > 0` for one) implies `hposX` and
`hposZ`. -/
theorem nde_eq_mediationFormula_unadjusted (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (g : α → ℝ) (x xstar : α)
    (hXY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u t)
        (fun _ => ()))
    (hZY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u m)
        (fun u => M.solve u t))
    (hXZ : NoiseCondIndep μ (fun u => M.counterfactual t xstar u m) (fun u => M.solve u t)
      (fun _ => ()))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun _ => ()))
    (hposX : lawProb (M.inducedLaw μ) (fun v => v t = xstar) ≠ 0)
    (hposZ : ∀ z : α, lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) ≠ 0) :
    M.nde μ t m y g x xstar =
      ∑ z : α,
        (lawMean (M.inducedLaw μ) g y (fun v => v t = x ∧ v m = z) -
          lawMean (M.inducedLaw μ) g y (fun v => v t = xstar ∧ v m = z)) *
        (lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) /
          lawProb (M.inducedLaw μ) (fun v => v t = xstar)) := by
  have hXY_gen : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u t)
        (fun u (i : ↥(∅ : Finset (Fin n))) => M.solve u i) := by
    intro x' hx' z a b c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c :=
      fun u => med_aux_empty_fun_eq _ _
    have h1 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        M.solve u t = b ∧ (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue u⟩
    have h2 : noiseProb μ (fun u => (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        exact hWtrue u
    have h3 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have h4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have hU1 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        M.solve u t = b ∧ (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, rfl⟩
    have hU2 : noiseProb μ (fun u => (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        rfl
    have hU3 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hU4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hUnit := hXY x' hx' z a b ()
    rw [h1, h2, h3, h4]
    rw [hU1, hU2, hU3, hU4] at hUnit
    exact hUnit
  have hZY_gen : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u m)
        (fun u => (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i)) := by
    intro x' hx' z a b c
    obtain ⟨x0, w⟩ := c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = w :=
      fun u => med_aux_empty_fun_eq _ _
    have hP1 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        M.solve u m = b ∧ (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧ M.solve u m = b ∧
          M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        have hX : M.solve u t = x0 := congrArg Prod.fst h.2.2
        exact ⟨h.1, h.2.1, hX⟩
      · intro h
        have hPair : (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w) := by
          rw [h.2.2, hWtrue u]
        exact ⟨h.1, h.2.1, hPair⟩
    have hP2 : noiseProb μ (fun u => (M.solve u t,
        fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact congrArg Prod.fst h
      · intro h
        rw [h, hWtrue u]
    have hP3 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧ M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, congrArg Prod.fst h.2⟩
      · intro h
        have hPair : (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w) := by
          rw [h.2, hWtrue u]
        exact ⟨h.1, hPair⟩
    have hP4 : noiseProb μ (fun u => M.solve u m = b ∧
        (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.solve u m = b ∧ M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, congrArg Prod.fst h.2⟩
      · intro h
        have hPair : (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w) := by
          rw [h.2, hWtrue u]
        exact ⟨h.1, hPair⟩
    have hUnit := hZY x' hx' z a b x0
    rw [hP1, hP2, hP3, hP4]
    exact hUnit
  have hXZ_gen : NoiseCondIndep μ (fun u => M.counterfactual t xstar u m)
      (fun u => M.solve u t) (fun u (i : ↥(∅ : Finset (Fin n))) => M.solve u i) := by
    intro a b c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c :=
      fun u => med_aux_empty_fun_eq _ _
    have h1 : noiseProb μ (fun u => M.counterfactual t xstar u m = a ∧
        M.solve u t = b ∧ (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual t xstar u m = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue u⟩
    have h2 : noiseProb μ (fun u => (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        exact hWtrue u
    have h3 : noiseProb μ (fun u => M.counterfactual t xstar u m = a ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual t xstar u m = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have h4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have hU1 : noiseProb μ (fun u => M.counterfactual t xstar u m = a ∧
        M.solve u t = b ∧ (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual t xstar u m = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, rfl⟩
    have hU2 : noiseProb μ (fun u => (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        rfl
    have hU3 : noiseProb μ (fun u => M.counterfactual t xstar u m = a ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual t xstar u m = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hU4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hUnit := hXZ a b ()
    rw [h1, h2, h3, h4]
    rw [hU1, hU2, hU3, hU4] at hUnit
    exact hUnit
  have hcross_gen : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m)
        (fun u (i : ↥(∅ : Finset (Fin n))) => M.solve u i) := by
    intro x' hx' z a b c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c :=
      fun u => med_aux_empty_fun_eq _ _
    have h1 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        M.counterfactual t xstar u m = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
          M.counterfactual t xstar u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue u⟩
    have h2 : noiseProb μ (fun u => (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        exact hWtrue u
    have h3 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have h4 : noiseProb μ (fun u => M.counterfactual t xstar u m = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual t xstar u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have hU1 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        M.counterfactual t xstar u m = b ∧ (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
          M.counterfactual t xstar u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, rfl⟩
    have hU2 : noiseProb μ (fun u => (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        rfl
    have hU3 : noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t x' m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hU4 : noiseProb μ (fun u => M.counterfactual t xstar u m = b ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual t xstar u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hUnit := hcross x' hx' z a b ()
    rw [h1, h2, h3, h4]
    rw [hU1, hU2, hU3, hU4] at hUnit
    exact hUnit
  have hposW_gen : ∀ w : ↥(∅ : Finset (Fin n)) → α,
      lawProb (M.inducedLaw μ) (fun v => (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 := by
    intro w hNe
    have hWtrue : ∀ v : Fin n → α,
        (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w :=
      fun v => med_aux_empty_fun_eq _ _
    have hEq : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue v⟩
    rw [hEq]
    exact hposX
  have hposZ_gen : ∀ (w : ↥(∅ : Finset (Fin n)) → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧
        (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧
        (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 := by
    intro w z hNe
    have hWtrue : ∀ v : Fin n → α,
        (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w :=
      fun v => med_aux_empty_fun_eq _ _
    have hEq1 : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v⟩
    have hNe' : lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) ≠ 0 := by
      rw [← hEq1]
      exact hNe
    have hConseq := hposZ z hNe'
    have hEq2 : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ v m = z ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
        lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v⟩
    rw [hEq2]
    exact hConseq
  have hGen := nde_eq_mediationFormulaNDE M μ htm y ∅ g x xstar
    hXY_gen hZY_gen hXZ_gen hcross_gen hposW_gen hposZ_gen
  have hEq : mediationFormulaNDE (M.inducedLaw μ) t m y ∅ g x xstar =
      ∑ z : α,
        (lawMean (M.inducedLaw μ) g y (fun v => v t = x ∧ v m = z) -
          lawMean (M.inducedLaw μ) g y (fun v => v t = xstar ∧ v m = z)) *
        (lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) /
          lawProb (M.inducedLaw μ) (fun v => v t = xstar)) := by
    haveI : IsEmpty ↥(∅ : Finset (Fin n)) :=
      ⟨fun ⟨j, hj⟩ => (Finset.notMem_empty j) hj⟩
    have hWtrue : ∀ (v : Fin n → α) (w : ↥(∅ : Finset (Fin n)) → α),
        (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w :=
      fun v w => med_aux_empty_fun_eq _ _
    have hLP3_one : ∀ w : ↥(∅ : Finset (Fin n)) → α,
        lawProb (M.inducedLaw μ)
          (fun v => (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) = 1 := by
      intro w
      have hEqTrue : lawProb (M.inducedLaw μ)
          (fun v => (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
          lawProb (M.inducedLaw μ) (fun _ : Fin n → α => True) := by
        apply med_aux_lawProb_congr
        intro v
        constructor
        · intro _
          trivial
        · intro _
          exact hWtrue v w
      have hTrue1 : lawProb (M.inducedLaw μ) (fun _ : Fin n → α => True) = 1 := by
        have hbridge : lawProb (M.inducedLaw μ) (fun _ : Fin n → α => True) =
            noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
          simpa using lawProb_inducedLaw M μ (fun _ : Fin n → α => True)
        have hN1 : noiseProb μ (fun _ : (k : Fin n) → U k => True) = 1 :=
          med_aux_noiseProb_eq_one_of_forall μ (fun _ => trivial)
        rw [hbridge]
        exact hN1
      rw [hEqTrue]
      exact hTrue1
    unfold mediationFormulaNDE
    rw [Fintype.sum_unique]
    apply Finset.sum_congr rfl
    intro z _
    have hLMx : lawMean (M.inducedLaw μ) g y
        (fun v => v t = x ∧ v m = z ∧
          (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawMean (M.inducedLaw μ) g y (fun v => v t = x ∧ v m = z) := by
      apply med_aux_lawMean_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v default⟩
    have hLMxstar : lawMean (M.inducedLaw μ) g y
        (fun v => v t = xstar ∧ v m = z ∧
          (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawMean (M.inducedLaw μ) g y (fun v => v t = xstar ∧ v m = z) := by
      apply med_aux_lawMean_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v default⟩
    have hLP1 : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧
          (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v default⟩
    have hLP2 : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue v default⟩
    rw [hLMx, hLMxstar, hLP1, hLP2, hLP3_one default, mul_one]
  rw [hGen]
  exact hEq

/-- **The NIE mediation formula without covariates** (P01, eq. (27); P14, eq. (17)):
`NIE = ∑_z E(Y | x*, z) [P(z | x) - P(z | x*)]`, under the hypotheses of
`nie_eq_mediationFormulaNIE` with `W = ∅`. -/
theorem nie_eq_mediationFormula_unadjusted (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (g : α → ℝ) (x xstar : α)
    (hXY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u t) (fun _ => ()))
    (hZY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u m) (fun u => M.solve u t))
    (hXZ : ∀ x' ∈ ({x, xstar} : Finset α), NoiseCondIndep μ
      (fun u => M.counterfactual t x' u m) (fun u => M.solve u t) (fun _ => ()))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
        (fun u => M.counterfactual t x' u m) (fun _ => ()))
    (hposX : ∀ x' ∈ ({x, xstar} : Finset α), lawProb (M.inducedLaw μ) (fun v => v t = x') ≠ 0)
    (hposZ : ∀ z : α, lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) ≠ 0) :
    M.nie μ t m y g x xstar =
      ∑ z : α, lawMean (M.inducedLaw μ) g y (fun v => v t = xstar ∧ v m = z) *
        (lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) /
            lawProb (M.inducedLaw μ) (fun v => v t = x) -
          lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) /
            lawProb (M.inducedLaw μ) (fun v => v t = xstar)) := by
  have hXY_gen : ∀ z : α, NoiseCondIndep μ
      (fun u => M.counterfactual₂ t xstar m z u y) (fun u => M.solve u t)
        (fun u (i : ↥(∅ : Finset (Fin n))) => M.solve u i) := by
    intro z a b c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c :=
      fun u => med_aux_empty_fun_eq _ _
    have h1 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        M.solve u t = b ∧ (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue u⟩
    have h2 : noiseProb μ (fun u => (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        exact hWtrue u
    have h3 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have h4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have hU1 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        M.solve u t = b ∧ (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, rfl⟩
    have hU2 : noiseProb μ (fun u => (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        rfl
    have hU3 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hU4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hUnit := hXY z a b ()
    rw [h1, h2, h3, h4]
    rw [hU1, hU2, hU3, hU4] at hUnit
    exact hUnit
  have hZY_gen : ∀ z : α, NoiseCondIndep μ
      (fun u => M.counterfactual₂ t xstar m z u y) (fun u => M.solve u m)
        (fun u => (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i)) := by
    intro z a b c
    obtain ⟨x0, w⟩ := c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = w :=
      fun u => med_aux_empty_fun_eq _ _
    have hP1 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        M.solve u m = b ∧ (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧ M.solve u m = b ∧
          M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        have hX : M.solve u t = x0 := congrArg Prod.fst h.2.2
        exact ⟨h.1, h.2.1, hX⟩
      · intro h
        have hPair : (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w) := by
          rw [h.2.2, hWtrue u]
        exact ⟨h.1, h.2.1, hPair⟩
    have hP2 : noiseProb μ (fun u => (M.solve u t,
        fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact congrArg Prod.fst h
      · intro h
        rw [h, hWtrue u]
    have hP3 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧ M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, congrArg Prod.fst h.2⟩
      · intro h
        have hPair : (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w) := by
          rw [h.2, hWtrue u]
        exact ⟨h.1, hPair⟩
    have hP4 : noiseProb μ (fun u => M.solve u m = b ∧
        (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w)) =
        noiseProb μ (fun u => M.solve u m = b ∧ M.solve u t = x0) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, congrArg Prod.fst h.2⟩
      · intro h
        have hPair : (M.solve u t, fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = (x0, w) := by
          rw [h.2, hWtrue u]
        exact ⟨h.1, hPair⟩
    have hUnit := hZY z a b x0
    rw [hP1, hP2, hP3, hP4]
    exact hUnit
  have hXZ_gen : ∀ x' ∈ ({x, xstar} : Finset α), NoiseCondIndep μ
      (fun u => M.counterfactual t x' u m) (fun u => M.solve u t)
      (fun u (i : ↥(∅ : Finset (Fin n))) => M.solve u i) := by
    intro x' hx' a b c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c :=
      fun u => med_aux_empty_fun_eq _ _
    have h1 : noiseProb μ (fun u => M.counterfactual t x' u m = a ∧
        M.solve u t = b ∧ (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual t x' u m = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue u⟩
    have h2 : noiseProb μ (fun u => (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        exact hWtrue u
    have h3 : noiseProb μ (fun u => M.counterfactual t x' u m = a ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual t x' u m = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have h4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have hU1 : noiseProb μ (fun u => M.counterfactual t x' u m = a ∧
        M.solve u t = b ∧ (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual t x' u m = a ∧ M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, rfl⟩
    have hU2 : noiseProb μ (fun u => (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        rfl
    have hU3 : noiseProb μ (fun u => M.counterfactual t x' u m = a ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual t x' u m = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hU4 : noiseProb μ (fun u => M.solve u t = b ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.solve u t = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hUnit := hXZ x' hx' a b ()
    rw [h1, h2, h3, h4]
    rw [hU1, hU2, hU3, hU4] at hUnit
    exact hUnit
  have hcross_gen : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
        (fun u => M.counterfactual t x' u m)
        (fun u (i : ↥(∅ : Finset (Fin n))) => M.solve u i) := by
    intro x' hx' z a b c
    have hWtrue : ∀ u : (k : Fin n) → U k,
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c :=
      fun u => med_aux_empty_fun_eq _ _
    have h1 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        M.counterfactual t x' u m = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
          M.counterfactual t x' u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue u⟩
    have h2 : noiseProb μ (fun u => (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        exact hWtrue u
    have h3 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have h4 : noiseProb μ (fun u => M.counterfactual t x' u m = b ∧
        (fun (i : ↥(∅ : Finset (Fin n))) => M.solve u i) = c) =
        noiseProb μ (fun u => M.counterfactual t x' u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue u⟩
    have hU1 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        M.counterfactual t x' u m = b ∧ (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
          M.counterfactual t x' u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, rfl⟩
    have hU2 : noiseProb μ (fun u => (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro _
        trivial
      · intro _
        rfl
    have hU3 : noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual₂ t xstar m z u y = a) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hU4 : noiseProb μ (fun u => M.counterfactual t x' u m = b ∧
        (fun _ : (k : Fin n) → U k => ()) u = ()) =
        noiseProb μ (fun u => M.counterfactual t x' u m = b) := by
      apply med_aux_noiseProb_congr
      intro u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, rfl⟩
    have hUnit := hcross x' hx' z a b ()
    rw [h1, h2, h3, h4]
    rw [hU1, hU2, hU3, hU4] at hUnit
    exact hUnit
  have hposW_gen : ∀ w : ↥(∅ : Finset (Fin n)) → α,
      lawProb (M.inducedLaw μ) (fun v => (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 →
      ∀ x' ∈ ({x, xstar} : Finset α),
        lawProb (M.inducedLaw μ)
          (fun v => v t = x' ∧ (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 := by
    intro w hNe x' hx'
    have hWtrue : ∀ v : Fin n → α,
        (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w :=
      fun v => med_aux_empty_fun_eq _ _
    have hEq : lawProb (M.inducedLaw μ)
        (fun v => v t = x' ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
        lawProb (M.inducedLaw μ) (fun v => v t = x') := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue v⟩
    rw [hEq]
    exact hposX x' hx'
  have hposZ_gen : ∀ (w : ↥(∅ : Finset (Fin n)) → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧
        (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧
        (fun i : ↥(∅ : Finset (Fin n)) => v i) = w) ≠ 0 := by
    intro w z hNe
    have hWtrue : ∀ v : Fin n → α,
        (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w :=
      fun v => med_aux_empty_fun_eq _ _
    have hEq1 : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ v m = z ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
        lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v⟩
    have hNe' : lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) ≠ 0 := by
      rw [← hEq1]
      exact hNe
    have hConseq := hposZ z hNe'
    have hEq2 : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v⟩
    rw [hEq2]
    exact hConseq
  have hGen := nie_eq_mediationFormulaNIE M μ htm y ∅ g x xstar
    hXY_gen hZY_gen hXZ_gen hcross_gen hposW_gen hposZ_gen
  have hEq : mediationFormulaNIE (M.inducedLaw μ) t m y ∅ g x xstar =
      ∑ z : α, lawMean (M.inducedLaw μ) g y (fun v => v t = xstar ∧ v m = z) *
        (lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) /
            lawProb (M.inducedLaw μ) (fun v => v t = x) -
          lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) /
            lawProb (M.inducedLaw μ) (fun v => v t = xstar)) := by
    haveI : IsEmpty ↥(∅ : Finset (Fin n)) :=
      ⟨fun ⟨j, hj⟩ => (Finset.notMem_empty j) hj⟩
    have hWtrue : ∀ (v : Fin n → α) (w : ↥(∅ : Finset (Fin n)) → α),
        (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w :=
      fun v w => med_aux_empty_fun_eq _ _
    have hLP3_one : ∀ w : ↥(∅ : Finset (Fin n)) → α,
        lawProb (M.inducedLaw μ)
          (fun v => (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) = 1 := by
      intro w
      have hEqTrue : lawProb (M.inducedLaw μ)
          (fun v => (fun (i : ↥(∅ : Finset (Fin n))) => v i) = w) =
          lawProb (M.inducedLaw μ) (fun _ : Fin n → α => True) := by
        apply med_aux_lawProb_congr
        intro v
        constructor
        · intro _
          trivial
        · intro _
          exact hWtrue v w
      have hTrue1 : lawProb (M.inducedLaw μ) (fun _ : Fin n → α => True) = 1 := by
        have hbridge : lawProb (M.inducedLaw μ) (fun _ : Fin n → α => True) =
            noiseProb μ (fun _ : (k : Fin n) → U k => True) := by
          simpa using lawProb_inducedLaw M μ (fun _ : Fin n → α => True)
        have hN1 : noiseProb μ (fun _ : (k : Fin n) → U k => True) = 1 :=
          med_aux_noiseProb_eq_one_of_forall μ (fun _ => trivial)
        rw [hbridge]
        exact hN1
      rw [hEqTrue]
      exact hTrue1
    unfold mediationFormulaNIE
    rw [Fintype.sum_unique]
    apply Finset.sum_congr rfl
    intro z _
    have hLM : lawMean (M.inducedLaw μ) g y
        (fun v => v t = xstar ∧ v m = z ∧
          (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawMean (M.inducedLaw μ) g y (fun v => v t = xstar ∧ v m = z) := by
      apply med_aux_lawMean_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v default⟩
    have hLPx : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ v m = z ∧
          (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v default⟩
    have hLPxstar : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ v m = z ∧
          (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact ⟨h.1, h.2.1⟩
      · intro h
        exact ⟨h.1, h.2, hWtrue v default⟩
    have hLP2x : lawProb (M.inducedLaw μ)
        (fun v => v t = x ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawProb (M.inducedLaw μ) (fun v => v t = x) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue v default⟩
    have hLP2xstar : lawProb (M.inducedLaw μ)
        (fun v => v t = xstar ∧ (fun (i : ↥(∅ : Finset (Fin n))) => v i) = default) =
        lawProb (M.inducedLaw μ) (fun v => v t = xstar) := by
      apply med_aux_lawProb_congr
      intro v
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hWtrue v default⟩
    rw [hLM, hLPx, hLPxstar, hLP2x, hLP2xstar, hLP3_one default, mul_one]
  rw [hGen]
  exact hEq

/-- The mediation formula for the natural direct effect with the nondescendant premise in
parent-closed form (`W ⊆ S` for a parent-closed `S` avoiding `t` and `m`): stronger than
P14's A-1, which excludes only treatment descendants, and the form `nde_eq_doFormula`
needs. Immediate from `nde_eq_mediationFormulaNDE`, whose counterfactual hypotheses do
not need any nondescendant premise; `nde_eq_mediationFormulaNDE_a1` is the published
(treatment-only) form. -/
theorem nde_eq_mediationFormulaNDE_of_notAffected (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    {S : Set (Fin n)} (_hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S)
    (_htS : t ∉ S) (_hmS : m ∉ S) (_hWS : ∀ i ∈ W, i ∈ S)
    (hXY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u t)
        (fun u (i : W) => M.solve u i))
    (hZY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u m)
        (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hXZ : NoiseCondIndep μ (fun u => M.counterfactual t xstar u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun u (i : W) => M.solve u i))
    (hposW : ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ (fun i : W => v i) = w) ≠ 0)
    (hposZ : ∀ (w : W → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0) :
    M.nde μ t m y g x xstar = mediationFormulaNDE (M.inducedLaw μ) t m y W g x xstar := by
  exact nde_eq_mediationFormulaNDE M μ htm y W g x xstar hXY hZY hXZ hcross hposW hposZ

/-- The mediation formula for the natural indirect effect with the nondescendant premise in
the parent-closed (stronger than A-1) form of `nde_eq_mediationFormulaNDE_of_notAffected`.
Immediate from `nie_eq_mediationFormulaNIE`; `nie_eq_mediationFormulaNIE_a1` is the
published (treatment-only) form. -/
theorem nie_eq_mediationFormulaNIE_of_notAffected (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    {S : Set (Fin n)} (_hS : ∀ j ∈ S, ∀ i ∈ M.pa j, Fin.castLE j.2.le i ∈ S)
    (_htS : t ∉ S) (_hmS : m ∉ S) (_hWS : ∀ i ∈ W, i ∈ S)
    (hXY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u t) (fun u (i : W) => M.solve u i))
    (hZY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u m) (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hXZ : ∀ x' ∈ ({x, xstar} : Finset α), NoiseCondIndep μ
      (fun u => M.counterfactual t x' u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
        (fun u => M.counterfactual t x' u m) (fun u (i : W) => M.solve u i))
    (hposW : ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
      ∀ x' ∈ ({x, xstar} : Finset α),
        lawProb (M.inducedLaw μ) (fun v => v t = x' ∧ (fun i : W => v i) = w) ≠ 0)
    (hposZ : ∀ (w : W → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0) :
    M.nie μ t m y g x xstar = mediationFormulaNIE (M.inducedLaw μ) t m y W g x xstar := by
  exact nie_eq_mediationFormulaNIE M μ htm y W g x xstar hXY hZY hXZ hcross hposW hposZ

/-- The mediation formula for the natural direct effect under P14's **A-1** as published:
`W` is not affected by the treatment (for every `i ∈ W`, the value at `i` is the same
under `do(t = a)` as factually, for every `a`), with no condition about the mediator.
P01 Theorem 2, PDF p. 6; P14 Corollary 1, eq. (14a), p. 17. Immediate from
`nde_eq_mediationFormulaNDE`, whose counterfactual hypotheses need no nondescendant
premise at all. -/
theorem nde_eq_mediationFormulaNDE_a1 (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    (_hA1 : ∀ i ∈ W, ∀ (a : α) (u : (k : Fin n) → U k), M.counterfactual t a u i = M.solve u i)
    (hXY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u t)
        (fun u (i : W) => M.solve u i))
    (hZY : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u m)
        (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hXZ : NoiseCondIndep μ (fun u => M.counterfactual t xstar u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun u (i : W) => M.solve u i))
    (hposW : ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ (fun i : W => v i) = w) ≠ 0)
    (hposZ : ∀ (w : W → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0) :
    M.nde μ t m y g x xstar = mediationFormulaNDE (M.inducedLaw μ) t m y W g x xstar := by
  exact nde_eq_mediationFormulaNDE M μ htm y W g x xstar hXY hZY hXZ hcross hposW hposZ

/-- The mediation formula for the natural indirect effect under P14's **A-1** as published
(`W` not affected by the treatment): P01 Theorem 4, eqs. (25)-(26), PDF p. 8; P14
eq. (14b), p. 17. Immediate from `nie_eq_mediationFormulaNIE`. -/
theorem nie_eq_mediationFormulaNIE_a1 (M : FiniteSCM α n U)
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m) (y : Fin n)
    (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    (_hA1 : ∀ i ∈ W, ∀ (a : α) (u : (k : Fin n) → U k), M.counterfactual t a u i = M.solve u i)
    (hXY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u t) (fun u (i : W) => M.solve u i))
    (hZY : ∀ z : α, NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
      (fun u => M.solve u m) (fun u => (M.solve u t, fun i : W => M.solve u i)))
    (hXZ : ∀ x' ∈ ({x, xstar} : Finset α), NoiseCondIndep μ
      (fun u => M.counterfactual t x' u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i))
    (hcross : ∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t xstar m z u y)
        (fun u => M.counterfactual t x' u m) (fun u (i : W) => M.solve u i))
    (hposW : ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
      ∀ x' ∈ ({x, xstar} : Finset α),
        lawProb (M.inducedLaw μ) (fun v => v t = x' ∧ (fun i : W => v i) = w) ≠ 0)
    (hposZ : ∀ (w : W → α) (z : α),
      lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
      lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0) :
    M.nie μ t m y g x xstar = mediationFormulaNIE (M.inducedLaw μ) t m y W g x xstar := by
  exact nie_eq_mediationFormulaNIE M μ htm y W g x xstar hXY hZY hXZ hcross hposW hposZ

end Identification

end FiniteSCM

/-! ### The kite counterexample (P14, Fig. 10) -/

namespace MediationKite

open FiniteSCM

/-- A fair coin. -/
noncomputable def fair : StdSimplex ℝ Bool :=
  StdSimplex.duple true false (s := (1 / 2 : ℝ)) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

/-- Two independent fair coins. -/
noncomputable def unif : StdSimplex ℝ (Bool × Bool) :=
  (fair.map fun a => fair.map fun b => (a, b)).join

/-- Every node has noise `(a, b)` uniform on `Bool × Bool`. -/
noncomputable def noise : (k : Fin 4) → StdSimplex ℝ ((fun _ : Fin 4 => Bool × Bool) k) :=
  fun _ => unif

/-- The kite on `T = 0`, `W = 1`, `M = 2`, `Y = 3`, every earlier node a parent (the complete
DAG of P14, Fig. 10, with `T = X` and `M = Z`): `T = a`, `W = wMech T (a, b)`,
`M = W xor (a ∧ b)`, `Y = (M xor W) xor (a ∧ b)`, with each node's own noise `(a, b)`. -/
def kite (wMech : Bool → Bool × Bool → Bool) : FiniteSCM Bool 4 (fun _ => Bool × Bool) where
  pa _ := univ
  f k z u :=
    if h0 : (k : ℕ) = 0 then u.1
    else if h1 : (k : ℕ) = 1 then wMech (z ⟨⟨0, by omega⟩, mem_univ _⟩) u
    else if h2 : (k : ℕ) = 2 then xor (z ⟨⟨1, by omega⟩, mem_univ _⟩) (u.1 && u.2)
    else xor (xor (z ⟨⟨2, by omega⟩, mem_univ _⟩) (z ⟨⟨1, by omega⟩, mem_univ _⟩)) (u.1 && u.2)

/-- Monotone coupling: `W_0 = a ∧ b ≤ W_1 = a ∨ b`. -/
def wMono (x : Bool) (u : Bool × Bool) : Bool := if x then u.1 || u.2 else u.1 && u.2

/-- Anti-monotone coupling: `W_1 = ¬ W_0`, same marginals `1/4` and `3/4`. -/
def wAnti (x : Bool) (u : Bool × Bool) : Bool := if x then !(u.1 && u.2) else u.1 && u.2

/-- The numeric readout of a Boolean outcome. -/
def boolVal (b : Bool) : ℝ := if b then 1 else 0

private theorem med_aux_duple_weights (x y p : Bool × Bool) (hs : (0:ℝ) ≤ 1 / 2)
    (ht : (0:ℝ) ≤ 1 / 2) (h : (1/2:ℝ) + 1 / 2 = 1) :
    (StdSimplex.duple x y (s := (1/2:ℝ)) (t := 1/2) hs ht h).weights p
      = (if x = p then (1/2:ℝ) else 0) + (if y = p then 1/2 else 0) := by
  show (((Finsupp.single x (1/2:ℝ) + Finsupp.single y (1/2:ℝ))) p : ℝ) = _
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]

private theorem med_aux_join_duple (x y : StdSimplex ℝ (Bool × Bool)) (p : Bool × Bool)
    (hs : (0:ℝ) ≤ 1 / 2) (ht : (0:ℝ) ≤ 1 / 2) (h : (1/2:ℝ) + 1 / 2 = 1) :
    (StdSimplex.duple x y (s := (1/2:ℝ)) (t := 1/2) hs ht h).join.weights p
      = 1 / 2 * x.weights p + 1 / 2 * y.weights p := by
  show (((Finsupp.single x (1/2:ℝ) + Finsupp.single y (1/2:ℝ)).sum
    fun d r => r • d.weights) p : ℝ) = _
  rw [Finsupp.sum_add_index' (fun a => zero_smul ℝ a.weights) (fun a b₁ b₂ => add_smul _ _ _),
    Finsupp.sum_single_index (zero_smul ℝ x.weights),
    Finsupp.sum_single_index (zero_smul ℝ y.weights),
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]

private theorem med_aux_unif_weights (p : Bool × Bool) : unif.weights p = 1 / 4 := by
  have hfair : fair = StdSimplex.duple true false (s := (1/2:ℝ)) (t := 1/2) (by norm_num)
    (by norm_num) (by norm_num) := rfl
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;>
    simp only [unif, hfair, StdSimplex.map_duple, med_aux_join_duple,
      med_aux_duple_weights] <;> norm_num

private theorem med_aux_map_or_eq :
    unif.map (fun u : Bool × Bool => u.1 || u.2) =
      unif.map (fun u : Bool × Bool => !(u.1 && u.2)) := by
  classical
  apply StdSimplex.ext
  ext b
  cases b with
  | false =>
    simp only [StdSimplex.weights_map, Finsupp.mapDomain_apply]
    simp [Finsupp.sum_fintype, med_aux_unif_weights]
    simp [Fintype.sum_prod_type]
  | true =>
    simp only [StdSimplex.weights_map, Finsupp.mapDomain_apply]
    simp [Finsupp.sum_fintype, med_aux_unif_weights]
    simp [Fintype.sum_prod_type]
    norm_num

/-- Same parents and same node laws: the two kites induce the same Bayesian network. -/
theorem kite_inducedBayesNet_eq :
    (kite wMono).inducedBayesNet noise = (kite wAnti).inducedBayesNet noise := by
  classical
  unfold FiniteSCM.inducedBayesNet kite noise
  congr 1
  funext k z
  fin_cases k
  · simp
  · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, reduceCtorEq, ↓reduceDIte]
    cases (z ⟨0, Finset.mem_univ _⟩)
    · simp [wMono, wAnti]
    · simp [wMono, wAnti, med_aux_map_or_eq]
  · simp
  · simp

/-- Hence the same law under every surgery, including none (`FiniteSCM.inducedLaw_doSet`): the
observational law and all 81 regimes of the prep packet's exact check agree. -/
theorem kite_doSet_inducedLaw_eq (S : Finset (Fin 4)) (w : Fin 4 → Bool) :
    ((kite wMono).doSet S w).inducedLaw noise = ((kite wAnti).doSet S w).inducedLaw noise := by
  funext v
  rw [inducedLaw_doSet, inducedLaw_doSet, kite_inducedBayesNet_eq]

private def med_aux_tupleToFun (p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool)) :
    Fin 4 → Bool × Bool :=
  fun i => if i = 0 then p.1 else if i = 1 then p.2.1 else if i = 2 then p.2.2.1 else p.2.2.2

private def med_aux_funToTuple (u : Fin 4 → Bool × Bool) :
    (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) :=
  (u 0, u 1, u 2, u 3)

private def med_aux_tupleEquiv : (Fin 4 → Bool × Bool) ≃
    (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) where
  toFun := med_aux_funToTuple
  invFun := med_aux_tupleToFun
  left_inv := by
    intro u
    funext i
    fin_cases i <;> simp [med_aux_funToTuple, med_aux_tupleToFun]
  right_inv := by
    intro p
    cases p with
    | mk a bcd =>
      cases bcd with
      | mk b cd =>
        cases cd with
        | mk c d => simp [med_aux_funToTuple, med_aux_tupleToFun]

private theorem med_aux_noise_support (k : Fin 4) : (noise k).support = Finset.univ := by
  simp [noise]
  ext p
  simp [Finsupp.mem_support_iff, med_aux_unif_weights]

private theorem med_aux_piFinset_eq :
    Fintype.piFinset (fun k => (noise k).support) = Finset.univ := by
  simp [med_aux_noise_support, Fintype.piFinset_univ]

private theorem med_aux_weight_eq (u : (k : Fin 4) → Bool × Bool) :
    FiniteSCM.noiseWeight noise u = 1 / 256 := by
  simp [FiniteSCM.noiseWeight, noise, med_aux_unif_weights, Finset.prod_const, Finset.card_univ]
  norm_num

private theorem med_aux_base_mono (u : (k : Fin 4) → Bool × Bool) :
    (kite wMono).counterfactual 0 false u 3 =
      xor (xor (xor ((u 1).1 && (u 1).2) ((u 2).1 && (u 2).2)) ((u 1).1 && (u 1).2))
        ((u 3).1 && (u 3).2) := by
  rfl

private theorem med_aux_nested_mono (u : (k : Fin 4) → Bool × Bool) :
    (kite wMono).nestedCounterfactual 0 2 true false u 3 =
      xor (xor (xor ((u 1).1 && (u 1).2) ((u 2).1 && (u 2).2)) ((u 1).1 || (u 1).2))
        ((u 3).1 && (u 3).2) := by
  rfl

/-- `NDE(1, 0) = P(W_0 ≠ W_1) / 4 = 1/8` in the monotone kite. -/
theorem nde_kite_mono : (kite wMono).nde noise 0 2 3 boolVal true false = 1 / 8 := by
  classical
  unfold FiniteSCM.nde FiniteSCM.noiseExpect
  simp only [med_aux_piFinset_eq, med_aux_weight_eq]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : (∑ x : Fin 4 → Bool × Bool,
      boolVal ((kite wMono).nestedCounterfactual 0 2 true false x 3)) = 128 := by
    have heq : (∑ x : Fin 4 → Bool × Bool,
        boolVal ((kite wMono).nestedCounterfactual 0 2 true false x 3)) =
        ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
          boolVal ((kite wMono).nestedCounterfactual 0 2 true false (med_aux_tupleEquiv.symm p) 3) :=
      (Equiv.sum_comp _ _).symm
    rw [heq]
    simp [med_aux_nested_mono, boolVal, Fintype.sum_prod_type, med_aux_tupleEquiv,
      med_aux_tupleToFun]
    norm_num
  have h2 : (∑ x : Fin 4 → Bool × Bool, boolVal ((kite wMono).counterfactual 0 false x 3)) = 96 := by
    have heq : (∑ x : Fin 4 → Bool × Bool, boolVal ((kite wMono).counterfactual 0 false x 3)) =
        ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
          boolVal ((kite wMono).counterfactual 0 false (med_aux_tupleEquiv.symm p) 3) :=
      (Equiv.sum_comp _ _).symm
    rw [heq]
    simp [med_aux_base_mono, boolVal, Fintype.sum_prod_type, med_aux_tupleEquiv,
      med_aux_tupleToFun]
    norm_num
  rw [h1, h2]
  norm_num

private theorem med_aux_base_anti (u : (k : Fin 4) → Bool × Bool) :
    (kite wAnti).counterfactual 0 false u 3 =
      xor (xor (xor ((u 1).1 && (u 1).2) ((u 2).1 && (u 2).2)) ((u 1).1 && (u 1).2))
        ((u 3).1 && (u 3).2) := by
  rfl

private theorem med_aux_nested_anti (u : (k : Fin 4) → Bool × Bool) :
    (kite wAnti).nestedCounterfactual 0 2 true false u 3 =
      xor (xor (xor ((u 1).1 && (u 1).2) ((u 2).1 && (u 2).2)) (!( (u 1).1 && (u 1).2)))
        ((u 3).1 && (u 3).2) := by
  rfl

/-- `NDE(1, 0) = P(W_0 ≠ W_1) / 4 = 1/4` in the anti-monotone kite. -/
theorem nde_kite_anti : (kite wAnti).nde noise 0 2 3 boolVal true false = 1 / 4 := by
  classical
  unfold FiniteSCM.nde FiniteSCM.noiseExpect
  simp only [med_aux_piFinset_eq, med_aux_weight_eq]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : (∑ x : Fin 4 → Bool × Bool,
      boolVal ((kite wAnti).nestedCounterfactual 0 2 true false x 3)) = 160 := by
    have heq : (∑ x : Fin 4 → Bool × Bool,
        boolVal ((kite wAnti).nestedCounterfactual 0 2 true false x 3)) =
        ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
          boolVal ((kite wAnti).nestedCounterfactual 0 2 true false (med_aux_tupleEquiv.symm p) 3) :=
      (Equiv.sum_comp _ _).symm
    rw [heq]
    simp [med_aux_nested_anti, boolVal, Fintype.sum_prod_type, med_aux_tupleEquiv,
      med_aux_tupleToFun]
    norm_num
  have h2 : (∑ x : Fin 4 → Bool × Bool, boolVal ((kite wAnti).counterfactual 0 false x 3)) = 96 := by
    have heq : (∑ x : Fin 4 → Bool × Bool, boolVal ((kite wAnti).counterfactual 0 false x 3)) =
        ∑ p : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool),
          boolVal ((kite wAnti).counterfactual 0 false (med_aux_tupleEquiv.symm p) 3) :=
      (Equiv.sum_comp _ _).symm
    rw [heq]
    simp [med_aux_base_anti, boolVal, Fintype.sum_prod_type, med_aux_tupleEquiv,
      med_aux_tupleToFun]
    norm_num
  rw [h1, h2]
  norm_num

/-- **The NDE is not identified** from the observational and all interventional laws when a
mediator-outcome confounder (`W`) is affected by the treatment (P14, Fig. 10; Avin, Shpitser
and Pearl 2005, Theorem 4): the two kites have the same law under every surgery and different
natural direct effects. -/
theorem not_identifiedOn_nde_kite :
    ¬ IdentifiedOn ({kite wMono, kite wAnti} : Set (FiniteSCM Bool 4 fun _ => Bool × Bool))
      (fun M => fun (S : Finset (Fin 4)) (w : Fin 4 → Bool) => (M.doSet S w).inducedLaw noise)
      (fun M => M.nde noise 0 2 3 boolVal true false) := by
  intro h
  have := h _ (Or.inl rfl) _ (Or.inr rfl)
    (funext fun S => funext fun w => kite_doSet_inducedLaw_eq S w)
  dsimp only at this
  rw [nde_kite_mono, nde_kite_anti] at this
  norm_num at this

private theorem med_aux_unif_support : unif.weights.support = Finset.univ := by
  ext p
  simp [Finsupp.mem_support_iff, med_aux_unif_weights]

private theorem med_aux_solve0 (wMech : Bool → Bool × Bool → Bool)
    (u : (k : Fin 4) → Bool × Bool) : (kite wMech).solve u 0 = (u 0).1 := rfl

private theorem med_aux_solve1 (wMech : Bool → Bool × Bool → Bool)
    (u : (k : Fin 4) → Bool × Bool) : (kite wMech).solve u 1 = wMech ((u 0).1) (u 1) := rfl

private theorem med_aux_solve2 (wMech : Bool → Bool × Bool → Bool)
    (u : (k : Fin 4) → Bool × Bool) :
    (kite wMech).solve u 2 = xor ((kite wMech).solve u 1) ((u 2).1 && (u 2).2) := rfl

private theorem med_aux_solve3 (wMech : Bool → Bool × Bool → Bool)
    (u : (k : Fin 4) → Bool × Bool) : (kite wMech).solve u 3
      = xor (xor ((kite wMech).solve u 2) ((kite wMech).solve u 1))
        ((u 3).1 && (u 3).2) := rfl

private theorem med_aux_conj (wMech : Bool → Bool × Bool → Bool) (u : (k : Fin 4) → Bool × Bool)
    (v : Fin 4 → Bool) :
    (kite wMech).solve u = v ↔
      ((u 0).1 = v 0 ∧ wMech (v 0) (u 1) = v 1 ∧
        (xor (v 1) ((u 2).1 && (u 2).2) = v 2) ∧
        (xor (xor (v 2) (v 1)) ((u 3).1 && (u 3).2) = v 3)) := by
  constructor
  · intro h
    have h0 : (kite wMech).solve u 0 = v 0 := congrFun h 0
    have h1 : (kite wMech).solve u 1 = v 1 := congrFun h 1
    have h2 : (kite wMech).solve u 2 = v 2 := congrFun h 2
    have h3 : (kite wMech).solve u 3 = v 3 := congrFun h 3
    rw [med_aux_solve0] at h0
    rw [med_aux_solve1] at h1
    rw [h0] at h1
    rw [med_aux_solve2] at h2
    have e1 : (kite wMech).solve u 1 = v 1 := by rw [med_aux_solve1, h0]; exact h1
    rw [e1] at h2
    rw [med_aux_solve3] at h3
    have e2 : (kite wMech).solve u 2 = v 2 := by rw [med_aux_solve2, e1]; exact h2
    rw [e2, e1] at h3
    exact ⟨h0, h1, h2, h3⟩
  · intro h
    have g0 : (kite wMech).solve u 0 = v 0 := by
      rw [med_aux_solve0]; exact h.1
    have g1 : (kite wMech).solve u 1 = v 1 := by
      rw [med_aux_solve1, h.1]; exact h.2.1
    have g2 : (kite wMech).solve u 2 = v 2 := by
      rw [med_aux_solve2, g1]; exact h.2.2.1
    have g3 : (kite wMech).solve u 3 = v 3 := by
      rw [med_aux_solve3, g2, g1]; exact h.2.2.2
    funext k
    fin_cases k
    · exact g0
    · exact g1
    · exact g2
    · exact g3

private theorem med_aux_if_conj (c0 c1 c2 c3 : Prop) [Decidable (c0 ∧ c1 ∧ c2 ∧ c3)]
    [Decidable c0] [Decidable c1] [Decidable c2] [Decidable c3]
    (a b c d : ℝ) :
    (if c0 ∧ c1 ∧ c2 ∧ c3 then a * b * c * d else 0)
      = (if c0 then a else 0) * (if c1 then b else 0) * (if c2 then c else 0) *
        (if c3 then d else 0) := by
  by_cases h0 : c0 <;> by_cases h1 : c1 <;> by_cases h2 : c2 <;> by_cases h3 : c3 <;>
    simp [h0, h1, h2, h3]

private theorem med_aux_sum_cons (n : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (f : (Fin (n + 1) → β) → ℝ) :
    ∑ v, f v = ∑ b : β, ∑ w : Fin n → β, f (Fin.cons b w) := by
  let e : β × (Fin n → β) ≃ (Fin (n + 1) → β) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun v => (v 0, Fin.tail v)
      left_inv := fun p => by simp [Fin.tail_cons, Fin.cons_zero]
      right_inv := fun v => Fin.cons_self_tail v }
  rw [Fintype.sum_equiv e.symm f (fun p => f (Fin.cons p.1 p.2))
    (fun v => (congrArg f (Fin.cons_self_tail v)).symm),
    Fintype.sum_prod_type]

private theorem med_aux_sum_base (β : Type) [Fintype β] [DecidableEq β] (g : (Fin 0 → β) → ℝ) :
    ∑ w, g w = g Fin.elim0 := by
  haveI : Unique (Fin 0 → β) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique]
  congr 1
  funext i
  exact Fin.elim0 i

private theorem med_aux_cproj0 (β : Type) (p0 p1 p2 p3 : β) (w : Fin 0 → β) :
    ((Fin.cons p0 (Fin.cons p1 (Fin.cons p2 (Fin.cons p3 w)))) : Fin 4 → β) 0 = p0 := rfl

private theorem med_aux_cproj1 (β : Type) (p0 p1 p2 p3 : β) (w : Fin 0 → β) :
    ((Fin.cons p0 (Fin.cons p1 (Fin.cons p2 (Fin.cons p3 w)))) : Fin 4 → β) 1 = p1 := rfl

private theorem med_aux_cproj2 (β : Type) (p0 p1 p2 p3 : β) (w : Fin 0 → β) :
    ((Fin.cons p0 (Fin.cons p1 (Fin.cons p2 (Fin.cons p3 w)))) : Fin 4 → β) 2 = p2 := rfl

private theorem med_aux_cproj3 (β : Type) (p0 p1 p2 p3 : β) (w : Fin 0 → β) :
    ((Fin.cons p0 (Fin.cons p1 (Fin.cons p2 (Fin.cons p3 w)))) : Fin 4 → β) 3 = p3 := rfl

private theorem med_aux_factor4 (s0 s1 s2 s3 : Finset (Bool × Bool)) (A0 A1 A2 A3 : (Bool × Bool) → ℝ) :
    (∑ p0 ∈ s0, ∑ p1 ∈ s1, ∑ p2 ∈ s2, ∑ p3 ∈ s3, A0 p0 * A1 p1 * A2 p2 * A3 p3)
      = (∑ p0 ∈ s0, A0 p0) * (∑ p1 ∈ s1, A1 p1) * (∑ p2 ∈ s2, A2 p2) *
        (∑ p3 ∈ s3, A3 p3) := by
  have h23 : ∀ (a b : ℝ), (∑ p2 ∈ s2, ∑ p3 ∈ s3, a * b * A2 p2 * A3 p3)
      = (∑ p2 ∈ s2, a * b * A2 p2) * (∑ p3 ∈ s3, A3 p3) := by
    intro a b
    rw [← Finset.sum_mul_sum]
  simp only [h23]
  have h2 : ∀ (a b : ℝ), (∑ p2 ∈ s2, a * b * A2 p2) = a * b * (∑ p2 ∈ s2, A2 p2) := by
    intro a b
    rw [← Finset.mul_sum]
  simp only [h2]
  simp only [mul_assoc]
  have h01 : ∀ (c : ℝ), (∑ p0 ∈ s0, ∑ p1 ∈ s1, A0 p0 * (A1 p1 * c))
      = (∑ p0 ∈ s0, A0 p0) * (∑ p1 ∈ s1, A1 p1 * c) := by
    intro c
    rw [← Finset.sum_mul_sum]
  simp only [h01]
  have h1 : ∀ (c : ℝ), (∑ p1 ∈ s1, A1 p1 * c) = (∑ p1 ∈ s1, A1 p1) * c := by
    intro c
    rw [← Finset.sum_mul]
  simp only [h1]

private noncomputable def med_aux_T1 (x w : Bool) : ℝ :=
  if x then (if w then 3 / 4 else 1 / 4) else (if w then 1 / 4 else 3 / 4)

private noncomputable def med_aux_Txor (a b : Bool) : ℝ := if b = a then 3 / 4 else 1 / 4

private noncomputable def med_aux_J (v : Fin 4 → Bool) : ℝ :=
  1 / 2 * med_aux_T1 (v 0) (v 1) * med_aux_Txor (v 1) (v 2) *
    med_aux_Txor (xor (v 2) (v 1)) (v 3)

private theorem med_aux_S0 (x : Bool) :
    (∑ p : Bool × Bool, if p.1 = x then unif.weights p else 0) = 1 / 2 := by
  simp only [med_aux_unif_weights]
  cases x <;> simp only [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

private theorem med_aux_Sxor (a b : Bool) :
    (∑ p : Bool × Bool, if xor a (p.1 && p.2) = b then unif.weights p else 0)
      = med_aux_Txor a b := by
  simp only [med_aux_unif_weights, med_aux_Txor]
  cases a <;> cases b <;> simp only [Fintype.sum_prod_type, Fintype.sum_bool] <;> norm_num

private theorem med_aux_W1_mono (x b : Bool) :
    (∑ p : Bool × Bool, if wMono x p = b then unif.weights p else 0) = med_aux_T1 x b := by
  have mT : ∀ p : Bool × Bool, wMono true p = (p.1 || p.2) := fun p => rfl
  have mF : ∀ p : Bool × Bool, wMono false p = (p.1 && p.2) := fun p => rfl
  cases x <;> cases b <;>
    simp only [med_aux_unif_weights, med_aux_T1, mT, mF, Fintype.sum_prod_type,
      Fintype.sum_bool] <;> norm_num

private theorem med_aux_W1_anti (x b : Bool) :
    (∑ p : Bool × Bool, if wAnti x p = b then unif.weights p else 0) = med_aux_T1 x b := by
  have mT : ∀ p : Bool × Bool, wAnti true p = (!(p.1 && p.2)) := fun p => rfl
  have mF : ∀ p : Bool × Bool, wAnti false p = (p.1 && p.2) := fun p => rfl
  cases x <;> cases b <;>
    simp only [med_aux_unif_weights, med_aux_T1, mT, mF, Fintype.sum_prod_type,
      Fintype.sum_bool] <;> norm_num

private theorem med_aux_pi_univ :
    Fintype.piFinset (fun k : Fin 4 => (noise k).weights.support) = Finset.univ := by
  simp only [noise, med_aux_unif_support]
  ext u
  simp [Fintype.mem_piFinset]

private theorem med_aux_inducedLaw (wMech : Bool → Bool × Bool → Bool)
    (hW1 : ∀ (x b : Bool),
      (∑ p : Bool × Bool, if wMech x p = b then unif.weights p else 0) = med_aux_T1 x b)
    (v : Fin 4 → Bool) :
    (kite wMech).inducedLaw noise v = med_aux_J v := by
  unfold inducedLaw noiseWeight
  rw [med_aux_pi_univ]
  simp only [med_aux_sum_cons, med_aux_sum_base]
  simp only [med_aux_conj, Fin.prod_univ_four, noise, med_aux_if_conj, med_aux_cproj0,
    med_aux_cproj1, med_aux_cproj2, med_aux_cproj3, med_aux_factor4, med_aux_S0, hW1,
    med_aux_Sxor, med_aux_J]

private theorem med_aux_Pmono (v : Fin 4 → Bool) :
    (kite wMono).inducedLaw noise v = med_aux_J v :=
  med_aux_inducedLaw wMono (fun x b => med_aux_W1_mono x b) v

private theorem med_aux_Panti (v : Fin 4 → Bool) :
    (kite wAnti).inducedLaw noise v = med_aux_J v :=
  med_aux_inducedLaw wAnti (fun x b => med_aux_W1_anti x b) v

private theorem med_aux_eval16 (f : (Fin 4 → Bool) → ℝ) :
    ∑ v, f v = ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
      f (Fin.cons b0 (Fin.cons b1 (Fin.cons b2 (Fin.cons b3 Fin.elim0)))) := by
  simp only [med_aux_sum_cons, med_aux_sum_base]

private theorem med_aux_wcond0 (v : Fin 4 → Bool) (w : ↥(∅ : Finset (Fin 4)) → Bool) :
    ((fun i : ↥(∅ : Finset (Fin 4)) => v ↑i) = w) ↔ True := by
  haveI : Subsingleton (↥(∅ : Finset (Fin 4)) → Bool) :=
    ⟨fun a b => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
  exact iff_true_intro (Subsingleton.elim _ _)

private theorem med_aux_wcond1 (v : Fin 4 → Bool) (w : ↥({1} : Finset (Fin 4)) → Bool) :
    ((fun i : ↥({1} : Finset (Fin 4)) => v ↑i) = w)
      ↔ v 1 = w ⟨1, Finset.mem_singleton_self 1⟩ := by
  constructor
  · intro h
    exact congrFun h ⟨1, Finset.mem_singleton_self 1⟩
  · intro h
    funext i
    have hii : i = ⟨1, Finset.mem_singleton_self 1⟩ :=
      Subtype.ext (Finset.mem_singleton.mp i.2)
    rw [hii]
    exact h

private theorem med_aux_sum_W0 (T : (↥(∅ : Finset (Fin 4)) → Bool) → ℝ) :
    ∑ w, T w = T default := by
  haveI : IsEmpty ↥(∅ : Finset (Fin 4)) :=
    ⟨fun i => absurd i.2 (Finset.notMem_empty _)⟩
  haveI : Unique (↥(∅ : Finset (Fin 4)) → Bool) := Pi.uniqueOfIsEmpty (fun _ => Bool)
  haveI : Subsingleton (↥(∅ : Finset (Fin 4)) → Bool) :=
    ⟨fun a b => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
  rw [Fintype.sum_unique T]
  congr 1
  exact Subsingleton.elim _ _

private theorem med_aux_sum_W1 (T : (↥({1} : Finset (Fin 4)) → Bool) → ℝ) :
    ∑ w, T w = ∑ b : Bool, T (fun _ => b) := by
  let e : (↥({1} : Finset (Fin 4)) → Bool) ≃ Bool :=
    { toFun := fun w => w ⟨1, Finset.mem_singleton_self 1⟩
      invFun := fun b _ => b
      left_inv := fun w => by
        funext i
        have hii : i = ⟨1, Finset.mem_singleton_self 1⟩ :=
          Subtype.ext (Finset.mem_singleton.mp i.2)
        simp [hii]
      right_inv := fun b => rfl }
  rw [Fintype.sum_equiv e T (fun b => T (e.symm b))
    (fun w => by rw [Equiv.symm_apply_apply])]
  apply Finset.sum_congr rfl
  intro b _
  rfl

private theorem med_aux_Wempty (P : (Fin 4 → Bool) → ℝ) (t m y : Fin 4) (g : Bool → ℝ)
    (x xstar : Bool) :
    mediationFormulaNDE P t m y ∅ g x xstar
      = ∑ z : Bool, (lawMean P g y (fun v => v t = x ∧ v m = z)
        - lawMean P g y (fun v => v t = xstar ∧ v m = z))
        * (lawProb P (fun v => v t = xstar ∧ v m = z)
          / lawProb P (fun v => v t = xstar))
        * lawProb P (fun v => True) := by
  unfold mediationFormulaNDE
  simp only [med_aux_sum_W0]
  apply Finset.sum_congr rfl
  intro z _
  simp only [med_aux_wcond0, and_true]

private theorem med_aux_Wsingle (P : (Fin 4 → Bool) → ℝ) (t m y : Fin 4) (g : Bool → ℝ)
    (x xstar : Bool) :
    mediationFormulaNDE P t m y {1} g x xstar
      = ∑ b : Bool, ∑ z : Bool, (lawMean P g y (fun v => v t = x ∧ v m = z ∧ v 1 = b)
        - lawMean P g y (fun v => v t = xstar ∧ v m = z ∧ v 1 = b))
        * (lawProb P (fun v => v t = xstar ∧ v m = z ∧ v 1 = b)
          / lawProb P (fun v => v t = xstar ∧ v 1 = b))
        * lawProb P (fun v => v 1 = b) := by
  unfold mediationFormulaNDE
  simp only [med_aux_sum_W1]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro z _
  simp only [med_aux_wcond1]

private theorem med_aux_probs (P : (Fin 4 → Bool) → ℝ)
    (hP : ∀ v, P v = med_aux_J v) :
    lawProb P (fun v => v 0 = true ∧ v 2 = true) = 5 / 16 ∧
    lawProb P (fun v => v 0 = true ∧ v 2 = false) = 3 / 16 ∧
    lawProb P (fun v => v 0 = false ∧ v 2 = true) = 3 / 16 ∧
    lawProb P (fun v => v 0 = false ∧ v 2 = false) = 5 / 16 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = true ∧ v 2 = true),
      P v * boolVal (v 3)) = 3 / 32 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = true ∧ v 2 = false),
      P v * boolVal (v 3)) = 3 / 32 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = false ∧ v 2 = true),
      P v * boolVal (v 3)) = 3 / 32 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = false ∧ v 2 = false),
      P v * boolVal (v 3)) = 3 / 32 ∧
    lawProb P (fun v => v 0 = false) = 1 / 2 ∧
    lawProb P (fun v => True) = 1 ∧
    lawProb P (fun v => v 0 = true ∧ v 2 = true ∧ v 1 = true) = 9 / 32 ∧
    lawProb P (fun v => v 0 = true ∧ v 2 = true ∧ v 1 = false) = 1 / 32 ∧
    lawProb P (fun v => v 0 = true ∧ v 2 = false ∧ v 1 = true) = 3 / 32 ∧
    lawProb P (fun v => v 0 = true ∧ v 2 = false ∧ v 1 = false) = 3 / 32 ∧
    lawProb P (fun v => v 0 = false ∧ v 2 = true ∧ v 1 = true) = 3 / 32 ∧
    lawProb P (fun v => v 0 = false ∧ v 2 = true ∧ v 1 = false) = 3 / 32 ∧
    lawProb P (fun v => v 0 = false ∧ v 2 = false ∧ v 1 = true) = 1 / 32 ∧
    lawProb P (fun v => v 0 = false ∧ v 2 = false ∧ v 1 = false) = 9 / 32 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = true ∧ v 2 = true ∧ v 1 = true),
      P v * boolVal (v 3)) = 9 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = true ∧ v 2 = true ∧ v 1 = false),
      P v * boolVal (v 3)) = 3 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = true ∧ v 2 = false ∧ v 1 = true),
      P v * boolVal (v 3)) = 9 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = true ∧ v 2 = false ∧ v 1 = false),
      P v * boolVal (v 3)) = 3 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = false ∧ v 2 = true ∧ v 1 = true),
      P v * boolVal (v 3)) = 3 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = false ∧ v 2 = true ∧ v 1 = false),
      P v * boolVal (v 3)) = 9 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = false ∧ v 2 = false ∧ v 1 = true),
      P v * boolVal (v 3)) = 3 / 128 ∧
    (∑ v ∈ Finset.univ.filter (fun v => v 0 = false ∧ v 2 = false ∧ v 1 = false),
      P v * boolVal (v 3)) = 9 / 128 ∧
    lawProb P (fun v => v 0 = false ∧ v 1 = true) = 1 / 8 ∧
    lawProb P (fun v => v 0 = false ∧ v 1 = false) = 3 / 8 ∧
    lawProb P (fun v => v 1 = true) = 1 / 2 ∧
    lawProb P (fun v => v 1 = false) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [lawProb, hP, Finset.sum_filter, med_aux_eval16, med_aux_cproj0,
      med_aux_cproj1, med_aux_cproj2, med_aux_cproj3, Fintype.sum_bool, med_aux_J,
      med_aux_T1, med_aux_Txor, boolVal, and_true, true_and, and_false, false_and,
      ite_true, ite_false] <;>
    norm_num

/-- In both kites the unadjusted formula (P01, eq. (17)) is `1/20` and the `W`-adjusted formula
(P14, eq. (14a), `W = {1}`) is `0`: both miss both NDE values (`1/8`, `1/4`). -/
theorem mediationFormulaNDE_kite :
    mediationFormulaNDE ((kite wMono).inducedLaw noise) 0 2 3 ∅ boolVal true false = 1 / 20 ∧
      mediationFormulaNDE ((kite wMono).inducedLaw noise) 0 2 3 {1} boolVal true false = 0 ∧
      mediationFormulaNDE ((kite wAnti).inducedLaw noise) 0 2 3 ∅ boolVal true false = 1 / 20 ∧
      mediationFormulaNDE ((kite wAnti).inducedLaw noise) 0 2 3 {1} boolVal true false = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hPs := med_aux_probs _ med_aux_Pmono
    rw [med_aux_Wempty, Fintype.sum_bool]
    simp only [lawMean, hPs]
    norm_num
  · have hPs := med_aux_probs _ med_aux_Pmono
    rw [med_aux_Wsingle]
    simp only [Fintype.sum_bool, lawMean, hPs]
    norm_num
  · have hPs := med_aux_probs _ med_aux_Panti
    rw [med_aux_Wempty, Fintype.sum_bool]
    simp only [lawMean, hPs]
    norm_num
  · have hPs := med_aux_probs _ med_aux_Panti
    rw [med_aux_Wsingle]
    simp only [Fintype.sum_bool, lawMean, hPs]
    norm_num

end MediationKite

end Cslib.MachineLearning.GraphicalModels
