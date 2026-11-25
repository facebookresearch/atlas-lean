/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MediationFormula
public import CSLibExt.MachineLearning.GraphicalModels.LinearMediation

/-!
# Tests for natural effects and the mediation formula

* Pearl 2001, Theorem 3 and composition on a three-node Boolean model.
* A shape check: `med_aux_FourConditions`, `med_aux_PosW` and `med_aux_PosZ` bundle exactly the
  hypotheses of `FiniteSCM.nde_eq_mediationFormulaNDE` (the check elaborates them against it).
* **Positive control** (prep packet §6): `W` a root (not affected by `X`), `Z = (W xor X) xor U_Z`,
  `Y = ((Z ∧ X) xor W) xor U_Y`, noise laws fair, fair, `1/4`, `1/3`: H1-H4 and positivity hold
  with `W = {W}`; `NDE(1, 0) = -1/12` equals the `W`-adjusted formula, while the unadjusted formula
  gives `1/12`.
* **Positivity witness** (freeze ruling 1): the deterministic model `X = 0`, `Z = 0`, `Y = X`
  satisfies H1-H4 and `hposW` with `W = ∅`, fails `hposZ` (`P(X = 1, Z = 0) = 0`), and has
  `NDE(1, 0) = 1` while the formula is `0` (Lean's `0 / 0 = 0`): positivity, stated in neither
  source, cannot be dropped.
* **Agreement with `LinearMediation`** (card acceptance 3, a sanity check in the additive case
  only): the additive model as a `FiniteSCM` on `ℝ`; NDE and TE agree with `LinearMediation`, and
  Pearl's NIE (Definition 7) agrees with `LinearMediation.MediationModel.naturalIndirectEffect`
  (the `TE - NDE` convention) in this additive model; the values at `a = 3`, `b = -2`, `c' = 1/2`,
  contrast `2 → 5`, are those of `LinearMediationTests`.
* **Interaction negative control**: `M = x + U_M`, `Y = x + m + x m + U_Y`, contrast `0 → 1`:
  Pearl's NIE is `1` while `TE - NDE` is `2`, so the additive agreement is not a tautology.

Values were checked exactly (Python `fractions`) on these encodings before freezing.
-/

@[expose] public section

namespace Cslib.MachineLearning.MediationFormulaTests

open Cslib.MachineLearning.GraphicalModels
open Cslib.MachineLearning.GraphicalModels.FiniteSCM
open Cslib.MachineLearning.GraphicalModels.MediationKite
open Cslib.MachineLearning.GraphicalModels.LinearMediation
open Finset Convexity

private theorem med_aux_empty_fun_eq {n : ℕ} {β : (∅ : Finset (Fin n)) → Type*} (f g : ∀ i, β i) :
    f = g :=
  funext fun i => (Finset.notMem_empty _ i.2).elim

/-! ### Hypothesis bundles and the shape check -/

/-- H1-H4 of `nde_eq_mediationFormulaNDE` for the treatment `t`, mediator `m`, outcome `y`,
covariates `W` and contrast `x` versus `xstar`. -/
abbrev med_aux_FourConditions {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    {U : Fin n → Type*} (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k))
    (t m y : Fin n) (W : Finset (Fin n)) (x xstar : α) : Prop :=
  (∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u t)
        (fun u (i : W) => M.solve u i)) ∧
    (∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y) (fun u => M.solve u m)
        (fun u => (M.solve u t, fun i : W => M.solve u i))) ∧
    NoiseCondIndep μ (fun u => M.counterfactual t xstar u m) (fun u => M.solve u t)
      (fun u (i : W) => M.solve u i) ∧
    (∀ x' ∈ ({x, xstar} : Finset α), ∀ z : α,
      NoiseCondIndep μ (fun u => M.counterfactual₂ t x' m z u y)
        (fun u => M.counterfactual t xstar u m) (fun u (i : W) => M.solve u i))

/-- The positivity hypothesis `hposW` of `nde_eq_mediationFormulaNDE`. -/
abbrev med_aux_PosW {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t : Fin n)
    (W : Finset (Fin n)) (xstar : α) : Prop :=
  ∀ w : W → α, lawProb (M.inducedLaw μ) (fun v => (fun i : W => v i) = w) ≠ 0 →
    lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ (fun i : W => v i) = w) ≠ 0

/-- The positivity hypothesis `hposZ` of `nde_eq_mediationFormulaNDE`. -/
abbrev med_aux_PosZ {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) (t m : Fin n)
    (W : Finset (Fin n)) (x xstar : α) : Prop :=
  ∀ (w : W → α) (z : α),
    lawProb (M.inducedLaw μ) (fun v => v t = xstar ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0 →
    lawProb (M.inducedLaw μ) (fun v => v t = x ∧ v m = z ∧ (fun i : W => v i) = w) ≠ 0

/-- Shape check: the bundles are exactly the hypotheses of the mediation-formula theorem. -/
example {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} {U : Fin n → Type*}
    (M : FiniteSCM α n U) (μ : (k : Fin n) → StdSimplex ℝ (U k)) {t m : Fin n} (htm : t ≠ m)
    (y : Fin n) (W : Finset (Fin n)) (g : α → ℝ) (x xstar : α)
    (h : med_aux_FourConditions M μ t m y W x xstar) (hW : med_aux_PosW M μ t W xstar)
    (hZ : med_aux_PosZ M μ t m W x xstar) :
    M.nde μ t m y g x xstar = mediationFormulaNDE (M.inducedLaw μ) t m y W g x xstar :=
  nde_eq_mediationFormulaNDE M μ htm y W g x xstar h.1 h.2.1 h.2.2.1 h.2.2.2 hW hZ

/-! ### Positivity witness and Theorem 3 on a three-node Boolean model -/

/-- `X = 0`, `Z = 0`, `Y = X` on the nodes `0`, `1`, `2`, with trivial noise. -/
def med_aux_constSCM : FiniteSCM Bool 3 (fun _ => Unit) where
  pa _ := univ
  f k z _ :=
    if h0 : (k : ℕ) = 0 then false
    else if (k : ℕ) = 1 then false
    else z ⟨⟨0, by omega⟩, mem_univ _⟩

/-- The point mass on the trivial noise value. -/
noncomputable def med_aux_unitNoise : (k : Fin 3) → StdSimplex ℝ ((fun _ : Fin 3 => Unit) k) :=
  fun _ => StdSimplex.single ()

private theorem med_aux_unit_support :
    Fintype.piFinset (fun k => (med_aux_unitNoise k).weights.support) = {(fun _ => ())} := by
  have hsupp : ∀ k : Fin 3, (med_aux_unitNoise k).weights.support = {()} := by
    intro k
    simp only [med_aux_unitNoise, StdSimplex.weights_single]
    exact Finsupp.support_single _ (by norm_num)
  simp only [hsupp]
  ext u
  rw [Fintype.mem_piFinset]
  constructor
  · intro _
    exact Finset.mem_singleton.mpr (funext fun k => Subsingleton.elim _ _)
  · intro _ k
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)

private theorem med_aux_unit_weight (u : (k : Fin 3) → Unit) :
    noiseWeight med_aux_unitNoise u = 1 := by
  have hu : ∀ k : Fin 3, u k = () := fun k => Subsingleton.elim _ _
  unfold noiseWeight
  exact Finset.prod_eq_one fun k _ => by
    simp only [med_aux_unitNoise, StdSimplex.weights_single, hu, Finsupp.single_eq_same]

private theorem med_aux_unit_prob (E : ((k : Fin 3) → Unit) → Prop) [DecidablePred E] :
    noiseProb med_aux_unitNoise E = (if E (fun _ => ()) then 1 else 0) := by
  unfold noiseProb
  rw [med_aux_unit_support, Finset.filter_singleton]
  by_cases h : E (fun _ => ())
  · simp only [if_pos h, Finset.sum_singleton, med_aux_unit_weight]
  · simp only [if_neg h, Finset.sum_empty]

private theorem med_aux_unit_indep {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (fA : ((k : Fin 3) → Unit) → A) (fB : ((k : Fin 3) → Unit) → B)
    (fC : ((k : Fin 3) → Unit) → C) :
    NoiseCondIndep med_aux_unitNoise fA fB fC := by
  unfold NoiseCondIndep
  intro a b c
  rw [med_aux_unit_prob, med_aux_unit_prob, med_aux_unit_prob, med_aux_unit_prob]
  by_cases ha : fA (fun _ => ()) = a <;> by_cases hb : fB (fun _ => ()) = b <;>
    by_cases hc : fC (fun _ => ()) = c <;> simp [ha, hb, hc]

private theorem med_aux_const_solve (u : (k : Fin 3) → Unit) :
    med_aux_constSCM.solve u = fun _ => false := by
  apply funext
  intro i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, h⟩ => exact absurd h (by omega)

private theorem med_aux_const_induced (x : Fin 3 → Bool) :
    med_aux_constSCM.inducedLaw med_aux_unitNoise x =
      (if (fun _ => false) = x then 1 else 0) := by
  unfold FiniteSCM.inducedLaw
  rw [med_aux_unit_support, Finset.sum_singleton, med_aux_const_solve, med_aux_unit_weight]
  by_cases h : (fun _ => false) = x <;> simp [h]

private theorem med_aux_const_law (E : (Fin 3 → Bool) → Prop) [DecidablePred E] :
    lawProb (med_aux_constSCM.inducedLaw med_aux_unitNoise) E =
      (if E (fun _ => false) then 1 else 0) := by
  unfold lawProb
  simp only [med_aux_const_induced]
  by_cases h : E (fun _ => false)
  · rw [if_pos h, Finset.sum_eq_single (fun _ => false)]
    · simp
    · intro v _ hne
      exact if_neg (fun he => hne he.symm)
    · intro hcon
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcon
      exact (hcon h).elim
  · rw [if_neg h, Finset.sum_eq_zero]
    intro v hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    apply if_neg
    intro he
    apply h
    rw [he]
    exact hmem

private theorem med_aux_const_lawmean (E : (Fin 3 → Bool) → Prop) [DecidablePred E] :
    lawMean (med_aux_constSCM.inducedLaw med_aux_unitNoise) boolVal 2 E = 0 := by
  unfold lawMean
  have hnum : (∑ v with E v, med_aux_constSCM.inducedLaw med_aux_unitNoise v * boolVal (v 2)) =
      0 := by
    rw [Finset.sum_eq_zero]
    intro v hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [med_aux_const_induced]
    by_cases he : (fun _ => false) = v
    · rw [if_pos he, ← he]
      simp [boolVal]
    · rw [if_neg he]
      simp
  rw [hnum]
  simp

private theorem med_aux_const_cf (u : (k : Fin 3) → Unit) :
    med_aux_constSCM.counterfactual 0 false u 2 = false :=
  rfl

private theorem med_aux_const_nested (u : (k : Fin 3) → Unit) :
    med_aux_constSCM.nestedCounterfactual 0 1 true false u 2 = true :=
  rfl

/-- **Positivity cannot be dropped** (ruling 1): H1-H4 and `hposW` hold, `hposZ` fails, and
`NDE(1, 0) = 1` while the formula is `0`. -/
example :
    med_aux_FourConditions med_aux_constSCM med_aux_unitNoise 0 1 2 ∅ true false ∧
      med_aux_PosW med_aux_constSCM med_aux_unitNoise 0 ∅ false ∧
      ¬ med_aux_PosZ med_aux_constSCM med_aux_unitNoise 0 1 ∅ true false ∧
      med_aux_constSCM.nde med_aux_unitNoise 0 1 2 boolVal true false = 1 ∧
      mediationFormulaNDE (med_aux_constSCM.inducedLaw med_aux_unitNoise) 0 1 2 ∅ boolVal true
        false = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun x' _ z => med_aux_unit_indep _ _ _, fun x' _ z => med_aux_unit_indep _ _ _,
      med_aux_unit_indep _ _ _, fun x' _ z => med_aux_unit_indep _ _ _⟩
  · intro w hw
    simp only [med_aux_const_law] at hw ⊢
    have hC1 : (fun _ : (∅ : Finset (Fin 3)) => false) = w := med_aux_empty_fun_eq _ _
    have hC2 : True ∧ (fun _ : (∅ : Finset (Fin 3)) => false) = w :=
      ⟨trivial, med_aux_empty_fun_eq _ _⟩
    rw [if_pos hC1] at hw
    rw [if_pos hC2]
    exact hw
  · intro hcon
    have h1 := hcon (fun i : (∅ : Finset (Fin 3)) => (fun _ => false) (i : Fin 3)) false
    simp only [med_aux_const_law] at h1
    have hC1 : True ∧ True ∧ True := ⟨trivial, trivial, trivial⟩
    have hC2 : ¬ (false = true ∧ True ∧ True) := by simp
    rw [if_pos hC1, if_neg hC2] at h1
    exact h1 (by norm_num) rfl
  · unfold nde noiseExpect
    simp only [med_aux_unit_support, Finset.sum_singleton, med_aux_const_nested, med_aux_const_cf,
      med_aux_unit_weight]
    norm_num [boolVal]
  · unfold mediationFormulaNDE
    simp only [med_aux_const_lawmean]
    simp

/-- Pearl 2001, Theorem 3, eq. (22), on the three-node model. -/
example (g : Bool → ℝ) :
    med_aux_constSCM.te med_aux_unitNoise 0 2 g true false =
      med_aux_constSCM.nie med_aux_unitNoise 0 1 2 g true false -
        med_aux_constSCM.nde med_aux_unitNoise 0 1 2 g false true :=
  te_eq_nie_sub_nde _ _ _ _ _ _ _ _

/-- Pearl 2001, Theorem 3, eq. (23), on the three-node model. -/
example (g : Bool → ℝ) :
    med_aux_constSCM.te med_aux_unitNoise 0 2 g true false =
      med_aux_constSCM.nde med_aux_unitNoise 0 1 2 g true false -
        med_aux_constSCM.nie med_aux_unitNoise 0 1 2 g false true :=
  te_eq_nde_sub_nie _ _ _ _ _ _ _ _

/-- Composition `Y_{x, Z_x} = Y_x` on the three-node model. -/
example (u : (k : Fin 3) → Unit) :
    med_aux_constSCM.nestedCounterfactual 0 1 true true u =
      med_aux_constSCM.counterfactual 0 true u :=
  nestedCounterfactual_self _ _ _ _ _

/-! ### Positive control (prep packet §6) -/

/-- `X = U_X`, `W = U_W` (a root), `Z = (W xor X) xor U_Z`, `Y = ((Z ∧ X) xor W) xor U_Y` on
`X = 0`, `W = 1`, `Z = 2`, `Y = 3`. -/
def med_aux_posControl : FiniteSCM Bool 4 (fun _ => Bool) where
  pa _ := univ
  f k z u :=
    if h0 : (k : ℕ) = 0 then u
    else if h1 : (k : ℕ) = 1 then u
    else if h2 : (k : ℕ) = 2 then
      xor (xor (z ⟨⟨1, by omega⟩, mem_univ _⟩) (z ⟨⟨0, by omega⟩, mem_univ _⟩)) u
    else
      xor (xor (z ⟨⟨2, by omega⟩, mem_univ _⟩ && z ⟨⟨0, by omega⟩, mem_univ _⟩)
        (z ⟨⟨1, by omega⟩, mem_univ _⟩)) u

/-- Noise laws `P(U = true)`: `1/2`, `1/2`, `1/4`, `1/3`. -/
noncomputable def med_aux_posNoise : (k : Fin 4) → StdSimplex ℝ ((fun _ : Fin 4 => Bool) k) :=
  ![fair, fair,
    StdSimplex.duple true false (s := (1 / 4 : ℝ)) (t := 3 / 4) (by norm_num) (by norm_num)
      (by norm_num),
    StdSimplex.duple true false (s := (1 / 3 : ℝ)) (t := 2 / 3) (by norm_num) (by norm_num)
      (by norm_num)]

private theorem med_aux_pos_solve0 (u : (k : Fin 4) → Bool) :
    med_aux_posControl.solve u 0 = u 0 :=
  rfl

private theorem med_aux_pos_solve1 (u : (k : Fin 4) → Bool) :
    med_aux_posControl.solve u 1 = u 1 :=
  rfl

private theorem med_aux_pos_solve2 (u : (k : Fin 4) → Bool) :
    med_aux_posControl.solve u 2 = xor (xor (u 1) (u 0)) (u 2) :=
  rfl

private theorem med_aux_pos_solve3 (u : (k : Fin 4) → Bool) :
    med_aux_posControl.solve u 3 =
      xor (xor (xor (xor (u 1) (u 0)) (u 2) && u 0) (u 1)) (u 3) :=
  rfl

private theorem med_aux_pos_cf2 (x' : Bool) (u : (k : Fin 4) → Bool) :
    med_aux_posControl.counterfactual 0 x' u 2 = xor (xor (u 1) x') (u 2) :=
  rfl

private theorem med_aux_pos_cf3 (x' : Bool) (u : (k : Fin 4) → Bool) :
    med_aux_posControl.counterfactual 0 x' u 3 =
      xor (xor (xor (xor (u 1) x') (u 2) && x') (u 1)) (u 3) :=
  rfl

private theorem med_aux_pos_cf23 (x' z : Bool) (u : (k : Fin 4) → Bool) :
    med_aux_posControl.counterfactual₂ 0 x' 2 z u 3 = xor (xor (z && x') (u 1)) (u 3) :=
  rfl

private theorem med_aux_duple_supp (s t : ℝ) (hs : s ≠ 0) (ht : t ≠ 0) (hs' : 0 ≤ s) (ht' : 0 ≤ t)
    (h : s + t = 1) :
    (StdSimplex.duple true false hs' ht' h).weights.support = ({true, false} : Finset Bool) := by
  rw [StdSimplex.weights_duple]
  ext x
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
    Finset.mem_insert, Finset.mem_singleton]
  cases x <;> simp [hs, ht]

private theorem med_aux_pos_supp (k : Fin 4) :
    (med_aux_posNoise k).weights.support = ({true, false} : Finset Bool) := by
  have s0 : (med_aux_posNoise 0).weights.support = ({true, false} : Finset Bool) := by
    simp only [med_aux_posNoise, Matrix.cons_val_zero]
    unfold fair
    exact med_aux_duple_supp _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have s1 : (med_aux_posNoise 1).weights.support = ({true, false} : Finset Bool) := by
    simp only [med_aux_posNoise, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    unfold fair
    exact med_aux_duple_supp _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have s2 : (med_aux_posNoise 2).weights.support = ({true, false} : Finset Bool) := by
    simp only [med_aux_posNoise, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact med_aux_duple_supp _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have s3 : (med_aux_posNoise 3).weights.support = ({true, false} : Finset Bool) := by
    simp only [med_aux_posNoise, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    exact med_aux_duple_supp _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  fin_cases k
  · exact s0
  · exact s1
  · exact s2
  · exact s3

private theorem med_aux_pos16 :
    Fintype.piFinset (fun k => (med_aux_posNoise k).weights.support) =
      {![true, true, true, true], ![true, true, true, false], ![true, true, false, true],
        ![true, true, false, false], ![true, false, true, true], ![true, false, true, false],
        ![true, false, false, true], ![true, false, false, false], ![false, true, true, true],
        ![false, true, true, false], ![false, true, false, true], ![false, true, false, false],
        ![false, false, true, true], ![false, false, true, false], ![false, false, false, true],
        ![false, false, false, false]} := by
  simp only [med_aux_pos_supp]
  decide

private theorem med_aux_sum16 (f : ((k : Fin 4) → Bool) → ℝ) :
    ∑ u ∈ ({![true, true, true, true], ![true, true, true, false], ![true, true, false, true],
      ![true, true, false, false], ![true, false, true, true], ![true, false, true, false],
      ![true, false, false, true], ![true, false, false, false], ![false, true, true, true],
      ![false, true, true, false], ![false, true, false, true], ![false, true, false, false],
      ![false, false, true, true], ![false, false, true, false], ![false, false, false, true],
      ![false, false, false, false]} : Finset ((k : Fin 4) → Bool)), f u =
      f ![true, true, true, true] + f ![true, true, true, false] + f ![true, true, false, true] +
        f ![true, true, false, false] + f ![true, false, true, true] +
        f ![true, false, true, false] + f ![true, false, false, true] +
        f ![true, false, false, false] + f ![false, true, true, true] +
        f ![false, true, true, false] + f ![false, true, false, true] +
        f ![false, true, false, false] + f ![false, false, true, true] +
        f ![false, false, true, false] + f ![false, false, false, true] +
        f ![false, false, false, false] := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem med_aux_pos_wt (u : (k : Fin 4) → Bool) :
    noiseWeight med_aux_posNoise u =
      (1 / 2) * (1 / 2) * (if u 2 = true then (1 / 4 : ℝ) else 3 / 4) *
        (if u 3 = true then (1 / 3 : ℝ) else 2 / 3) := by
  have w0 : ∀ b : Bool, (med_aux_posNoise 0).weights b = 1 / 2 := by
    intro b
    simp only [med_aux_posNoise, Matrix.cons_val_zero]
    unfold fair
    rw [StdSimplex.weights_duple]
    cases b <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  have w1 : ∀ b : Bool, (med_aux_posNoise 1).weights b = 1 / 2 := by
    intro b
    simp only [med_aux_posNoise, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    unfold fair
    rw [StdSimplex.weights_duple]
    cases b <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  have w2 : ∀ b : Bool, (med_aux_posNoise 2).weights b =
      if b = true then (1 / 4 : ℝ) else 3 / 4 := by
    intro b
    simp only [med_aux_posNoise, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [StdSimplex.weights_duple]
    cases b <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  have w3 : ∀ b : Bool, (med_aux_posNoise 3).weights b =
      if b = true then (1 / 3 : ℝ) else 2 / 3 := by
    intro b
    simp only [med_aux_posNoise, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [StdSimplex.weights_duple]
    cases b <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  unfold noiseWeight
  rw [Fin.prod_univ_four, w0, w1, w2, w3]

private theorem med_aux_pos_Wcases (c : (({1} : Finset (Fin 4))) → Bool) :
    c = (fun _ => true) ∨ c = (fun _ => false) := by
  cases hc : c ⟨1, by simp⟩
  · right
    funext i
    have h1 : (i : Fin 4) = 1 := Finset.mem_singleton.mp i.2
    have hi : i = ⟨1, by simp⟩ := Subtype.ext h1
    rw [hi]
    exact hc
  · left
    funext i
    have h1 : (i : Fin 4) = 1 := Finset.mem_singleton.mp i.2
    have hi : i = ⟨1, by simp⟩ := Subtype.ext h1
    rw [hi]
    exact hc

private theorem med_aux_pos_fCeq (u : (k : Fin 4) → Bool) (b : Bool) :
    ((fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i) = fun _ => b) ↔
      (med_aux_posControl.solve u 1 = b) := by
  constructor
  · intro h
    exact congrFun h ⟨1, by simp⟩
  · intro h
    funext i
    have h1 : (i : Fin 4) = 1 := Finset.mem_singleton.mp i.2
    show med_aux_posControl.solve u ↑i = b
    rw [h1]
    exact h

private theorem med_aux_pos_hXY_TT : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3)
    (fun u => med_aux_posControl.solve u 0)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hXY_TF : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3)
    (fun u => med_aux_posControl.solve u 0)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hXY_FT : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 false 2 true u 3)
    (fun u => med_aux_posControl.solve u 0)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hXY_FF : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 false 2 false u 3)
    (fun u => med_aux_posControl.solve u 0)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hcross_TT : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3)
    (fun u => med_aux_posControl.counterfactual 0 false u 2)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve1,
      med_aux_pos_cf2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hcross_TF : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3)
    (fun u => med_aux_posControl.counterfactual 0 false u 2)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve1,
      med_aux_pos_cf2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hcross_FT : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 false 2 true u 3)
    (fun u => med_aux_posControl.counterfactual 0 false u 2)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve1,
      med_aux_pos_cf2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hcross_FF : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 false 2 false u 3)
    (fun u => med_aux_posControl.counterfactual 0 false u 2)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve1,
      med_aux_pos_cf2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hXZ : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual 0 false u 2)
    (fun u => med_aux_posControl.solve u 0)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_cf2, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_TT_T (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_TT_F (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_TF_T (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_TF_F (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_FT_T (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 true u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 true u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_FT_F (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 true u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 true u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_FF_T (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 false u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 false u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => true)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hZY_FF_F (a b c1 : Bool) :
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 false u 3 = a ∧
          med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) =
    noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 false 2 false u 3 = a ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) *
      noiseProb med_aux_posNoise
        (fun u => med_aux_posControl.solve u 2 = b ∧
          (med_aux_posControl.solve u 0,
            (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i)) =
            (c1, fun _ => false)) := by
  cases a <;> cases b <;> cases c1 <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_PosW : med_aux_PosW med_aux_posControl med_aux_posNoise 0 {1} false := by
  intro w hw
  rcases med_aux_pos_Wcases w with rfl | rfl
  · simp only [lawProb_inducedLaw]
    unfold noiseProb
    rw [med_aux_pos16]
    beta_reduce
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_fCeq]
    norm_num
  · simp only [lawProb_inducedLaw]
    unfold noiseProb
    rw [med_aux_pos16]
    beta_reduce
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_fCeq]
    norm_num

private theorem med_aux_pos_PosZ : med_aux_PosZ med_aux_posControl med_aux_posNoise 0 2 {1} true false := by
  intro w z
  rcases med_aux_pos_Wcases w with rfl | rfl <;> cases z <;>
    simp only [lawProb_inducedLaw] <;> unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_fCeq] <;>
    norm_num

/-- Non-vacuity: H1-H4 and positivity hold in the positive control with `W = {1}`, so
`nde_eq_mediationFormulaNDE` applies (shape check above). -/
example :
    med_aux_FourConditions med_aux_posControl med_aux_posNoise 0 2 3 {1} true false ∧
      med_aux_PosW med_aux_posControl med_aux_posNoise 0 {1} false ∧
      med_aux_PosZ med_aux_posControl med_aux_posNoise 0 2 {1} true false := by
  refine ⟨?_, med_aux_pos_PosW, med_aux_pos_PosZ⟩
  simp only [med_aux_FourConditions]
  refine ⟨?_, ?_, med_aux_pos_hXZ, ?_⟩
  · intro x' hx' z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · cases z
      · exact med_aux_pos_hXY_TF
      · exact med_aux_pos_hXY_TT
    · cases z
      · exact med_aux_pos_hXY_FF
      · exact med_aux_pos_hXY_FT
  · intro x' hx' z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · cases z
      · unfold NoiseCondIndep
        intro a b c
        rcases c with ⟨c1, c2⟩
        rcases med_aux_pos_Wcases c2 with rfl | rfl
        · exact med_aux_pos_hZY_TF_T a b c1
        · exact med_aux_pos_hZY_TF_F a b c1
      · unfold NoiseCondIndep
        intro a b c
        rcases c with ⟨c1, c2⟩
        rcases med_aux_pos_Wcases c2 with rfl | rfl
        · exact med_aux_pos_hZY_TT_T a b c1
        · exact med_aux_pos_hZY_TT_F a b c1
    · cases z
      · unfold NoiseCondIndep
        intro a b c
        rcases c with ⟨c1, c2⟩
        rcases med_aux_pos_Wcases c2 with rfl | rfl
        · exact med_aux_pos_hZY_FF_T a b c1
        · exact med_aux_pos_hZY_FF_F a b c1
      · unfold NoiseCondIndep
        intro a b c
        rcases c with ⟨c1, c2⟩
        rcases med_aux_pos_Wcases c2 with rfl | rfl
        · exact med_aux_pos_hZY_FT_T a b c1
        · exact med_aux_pos_hZY_FT_F a b c1
  · intro x' hx' z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · cases z
      · exact med_aux_pos_hcross_TF
      · exact med_aux_pos_hcross_TT
    · cases z
      · exact med_aux_pos_hcross_FF
      · exact med_aux_pos_hcross_FT

/-- `NDE(1, 0) = -1/12` in the positive control. -/
example : med_aux_posControl.nde med_aux_posNoise 0 2 3 boolVal true false = -1 / 12 := by
  unfold nde noiseExpect
  rw [med_aux_pos16]
  beta_reduce
  simp [med_aux_sum16, med_aux_pos_wt, FiniteSCM.nestedCounterfactual, med_aux_pos_cf2,
    med_aux_pos_cf23, med_aux_pos_cf3, boolVal]
  norm_num

private theorem med_aux_sum_push (s : Finset ((k : Fin 4) → Bool)) (p : Prop) [Decidable p]
    (f : ((k : Fin 4) → Bool) → ℝ) (g : ℝ) :
    (if p then (∑ u ∈ s, f u) * g else 0) = ∑ u ∈ s, if p then f u * g else 0 := by
  by_cases h : p <;> simp [h, Finset.sum_mul]

private theorem med_aux_pos_lawMean_num (E : (Fin 4 → Bool) → Prop) [DecidablePred E] :
    (∑ v with E v, med_aux_posControl.inducedLaw med_aux_posNoise v * boolVal (v 3)) =
      noiseExpect med_aux_posNoise
        (fun u => if E (med_aux_posControl.solve u) then boolVal (med_aux_posControl.solve u 3)
          else 0) := by
  unfold FiniteSCM.inducedLaw noiseExpect
  beta_reduce
  rw [Finset.sum_filter]
  simp only [med_aux_sum_push]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single (med_aux_posControl.solve u)
    (fun v _ hne => by
      by_cases h : E v
      · simp [h, show med_aux_posControl.solve u ≠ v from fun he => hne he.symm]
      · simp [h])
    (fun hcon => by simp at hcon)]
  by_cases h : E (med_aux_posControl.solve u) <;> simp [h]

private theorem med_aux_pos_lawMean (E : (Fin 4 → Bool) → Prop) [DecidablePred E] :
    lawMean (med_aux_posControl.inducedLaw med_aux_posNoise) boolVal 3 E =
      noiseExpect med_aux_posNoise (fun u => if E (med_aux_posControl.solve u) then
        boolVal (med_aux_posControl.solve u 3) else 0) /
      noiseProb med_aux_posNoise (fun u => E (med_aux_posControl.solve u)) := by
  unfold lawMean
  rw [med_aux_pos_lawMean_num, lawProb_inducedLaw]

private theorem med_aux_pos_Wuniv : (Finset.univ : Finset ((({1} : Finset (Fin 4))) → Bool)) =
    {fun _ => true, fun _ => false} := by
  ext c
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  cases hc : c ⟨1, by simp⟩
  · right
    funext i
    have h1 : (i : Fin 4) = 1 := Finset.mem_singleton.mp i.2
    have hi : i = ⟨1, by simp⟩ := Subtype.ext h1
    rw [hi]
    exact hc
  · left
    funext i
    have h1 : (i : Fin 4) = 1 := Finset.mem_singleton.mp i.2
    have hi : i = ⟨1, by simp⟩ := Subtype.ext h1
    rw [hi]
    exact hc

private theorem med_aux_Bool_univ : (Finset.univ : Finset Bool) = {true, false} := by
  ext x
  cases x <;> simp

private theorem med_aux_pos_formW_T : (∑ z : Bool,
    (lawMean (med_aux_posControl.inducedLaw med_aux_posNoise) boolVal 3
        (fun v => v 0 = true ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = fun _ => true) -
      lawMean (med_aux_posControl.inducedLaw med_aux_posNoise) boolVal 3
        (fun v => v 0 = false ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) =
          fun _ => true)) *
    (lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => v 0 = false ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) =
          fun _ => true) /
      lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => v 0 = false ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = fun _ => true)) *
    lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
      (fun v => (fun i : (({1} : Finset (Fin 4))) => v i) = fun _ => true)) = -1 / 8 := by
  rw [med_aux_Bool_univ, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [med_aux_pos_lawMean, lawProb_inducedLaw]
  unfold noiseExpect noiseProb
  rw [med_aux_pos16]
  beta_reduce
  simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
    med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_solve3, med_aux_pos_fCeq, boolVal]
  norm_num

private theorem med_aux_pos_formW_F : (∑ z : Bool,
    (lawMean (med_aux_posControl.inducedLaw med_aux_posNoise) boolVal 3
        (fun v => v 0 = true ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = fun _ => false) -
      lawMean (med_aux_posControl.inducedLaw med_aux_posNoise) boolVal 3
        (fun v => v 0 = false ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) =
          fun _ => false)) *
    (lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => v 0 = false ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) =
          fun _ => false) /
      lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => v 0 = false ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = fun _ => false)) *
    lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
      (fun v => (fun i : (({1} : Finset (Fin 4))) => v i) = fun _ => false)) = 1 / 24 := by
  rw [med_aux_Bool_univ, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [med_aux_pos_lawMean, lawProb_inducedLaw]
  unfold noiseExpect noiseProb
  rw [med_aux_pos16]
  beta_reduce
  simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
    med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_solve3, med_aux_pos_fCeq, boolVal]
  norm_num

/-- The `W`-adjusted formula (Pearl 2014, eq. (14a)) gives the NDE, `-1/12`. -/
example :
    mediationFormulaNDE (med_aux_posControl.inducedLaw med_aux_posNoise) 0 2 3 {1} boolVal true
      false = -1 / 12 := by
  unfold mediationFormulaNDE
  rw [med_aux_pos_Wuniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [med_aux_pos_formW_T, med_aux_pos_formW_F]
  norm_num

private theorem med_aux_empty_Wuniv : (Finset.univ : Finset (((∅ : Finset (Fin 4))) → Bool)) =
    {fun i => (Finset.notMem_empty _ i.2).elim} := by
  ext c
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact med_aux_empty_fun_eq _ _

private theorem med_aux_empty_Etrue (v : Fin 4 → Bool) (w : ((∅ : Finset (Fin 4))) → Bool) :
    ((fun i : ((∅ : Finset (Fin 4))) => v ↑i) = w) ↔ True :=
  iff_of_true (med_aux_empty_fun_eq _ _) trivial

/-- The unadjusted formula (Pearl 2001, eq. (17)) gives `1/12`: H2 and H4 fail with `W = ∅`. -/
example :
    mediationFormulaNDE (med_aux_posControl.inducedLaw med_aux_posNoise) 0 2 3 ∅ boolVal true
      false = 1 / 12 := by
  unfold mediationFormulaNDE
  rw [med_aux_empty_Wuniv, Finset.sum_singleton, med_aux_Bool_univ,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [med_aux_pos_lawMean, lawProb_inducedLaw]
  unfold noiseExpect noiseProb
  rw [med_aux_pos16]
  beta_reduce
  simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
    med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_solve3, med_aux_empty_Etrue, boolVal]
  norm_num

/-- The additive linear mediation model as a `FiniteSCM` on `ℝ` with real noise:
`X = U_X`, `M = a X + U_M`, `Y = c' X + b M + U_Y` on the nodes `0`, `1`, `2`. -/
def toFiniteSCM (mm : MediationModel) : FiniteSCM ℝ 3 (fun _ => ℝ) where
  pa _ := univ
  f k z u :=
    if h0 : (k : ℕ) = 0 then u
    else if h1 : (k : ℕ) = 1 then mm.a * z ⟨⟨0, by omega⟩, mem_univ _⟩ + u
    else mm.c' * z ⟨⟨0, by omega⟩, mem_univ _⟩ + mm.b * z ⟨⟨1, by omega⟩, mem_univ _⟩ + u

private theorem med_aux_counterfactual_mediator (mm : MediationModel) (x : ℝ) (u : Fin 3 → ℝ) :
    (toFiniteSCM mm).counterfactual 0 x u 1 = mm.mediator x (u 1) := by
  simp only [counterfactual, solve, FiniteSCM.solvePrefix, doNode, toFiniteSCM]
  simp
  rw [show (0 : Fin 1) = Fin.last 0 from rfl, show (1 : Fin 3) = Fin.castSucc 1 from rfl,
    Fin.snoc_last, Fin.snoc_castSucc]
  rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
  unfold MediationModel.mediator
  ring

/-- The counterfactual outcome is `LinearMediation`'s potential outcome. -/
theorem toFiniteSCM_counterfactual (mm : MediationModel) (x : ℝ) (u : Fin 3 → ℝ) :
    (toFiniteSCM mm).counterfactual 0 x u 2 = mm.potentialOutcome x (u 1) (u 2) := by
  simp only [counterfactual, solve, FiniteSCM.solvePrefix, doNode, toFiniteSCM]
  simp
  rw [show (0 : Fin 1) = Fin.last 0 from rfl, show (1 : Fin 2) = Fin.last 1 from rfl,
    show (2 : Fin 3) = Fin.last 2 from rfl, Fin.snoc_last, Fin.snoc_last, Fin.snoc_last]
  unfold MediationModel.potentialOutcome MediationModel.mediator MediationModel.outcome
  ring

/-- The nested counterfactual outcome is `LinearMediation`'s nested outcome. -/
theorem toFiniteSCM_nestedCounterfactual (mm : MediationModel) (x x' : ℝ) (u : Fin 3 → ℝ) :
    (toFiniteSCM mm).nestedCounterfactual 0 1 x x' u 2 = mm.nestedOutcome x x' (u 1) (u 2) := by
  unfold nestedCounterfactual
  rw [med_aux_counterfactual_mediator]
  simp only [counterfactual₂, solve, FiniteSCM.solvePrefix, doNode, toFiniteSCM]
  simp
  rw [show (0 : Fin 1) = Fin.last 0 from rfl, show (1 : Fin 2) = Fin.last 1 from rfl,
    show (2 : Fin 3) = Fin.last 2 from rfl, Fin.snoc_last, Fin.snoc_last, Fin.snoc_last]
  unfold MediationModel.nestedOutcome MediationModel.mediator MediationModel.outcome
  ring

/-- The NDE is the average of `LinearMediation`'s unit-level NDE, `c' (x₁ - x₀)`. -/
theorem nde_toFiniteSCM (mm : MediationModel) (μ : (k : Fin 3) → StdSimplex ℝ ℝ)
    (x₀ x₁ : ℝ) :
    (toFiniteSCM mm).nde μ 0 1 2 id x₁ x₀ =
        noiseExpect μ (fun u => mm.naturalDirectEffect x₀ x₁ (u 1) (u 2)) ∧
      (toFiniteSCM mm).nde μ 0 1 2 id x₁ x₀ = mm.c' * (x₁ - x₀) := by
  have hcf : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).counterfactual 0 x₀ u 2 =
      mm.potentialOutcome x₀ (u 1) (u 2) := fun u => toFiniteSCM_counterfactual mm x₀ u
  have hnc : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).nestedCounterfactual 0 1 x₁ x₀ u 2 =
      mm.nestedOutcome x₁ x₀ (u 1) (u 2) := fun u => toFiniteSCM_nestedCounterfactual mm x₁ x₀ u
  have e1 : (toFiniteSCM mm).nde μ 0 1 2 id x₁ x₀ =
      noiseExpect μ (fun u => mm.naturalDirectEffect x₀ x₁ (u 1) (u 2)) := by
    simp only [nde, hcf, hnc, id_eq]
    unfold noiseExpect MediationModel.naturalDirectEffect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hconst : ∀ u : Fin 3 → ℝ, mm.naturalDirectEffect x₀ x₁ (u 1) (u 2) = mm.c' * (x₁ - x₀) := by
    intro u
    unfold MediationModel.naturalDirectEffect MediationModel.nestedOutcome
      MediationModel.potentialOutcome MediationModel.outcome MediationModel.mediator
    ring
  have e2 : (toFiniteSCM mm).nde μ 0 1 2 id x₁ x₀ = mm.c' * (x₁ - x₀) := by
    rw [e1, show (fun u : Fin 3 → ℝ => mm.naturalDirectEffect x₀ x₁ (u 1) (u 2)) =
      (fun _ => mm.c' * (x₁ - x₀)) from funext hconst]
    exact noiseExpect_const μ _
  exact ⟨e1, e2⟩

/-- In the additive model Pearl's NIE (Definition 7) agrees with `LinearMediation`'s
`TE - NDE` indirect effect, `a b (x₁ - x₀)`; the interaction control below shows the two
conventions differ in general. -/
theorem nie_toFiniteSCM (mm : MediationModel) (μ : (k : Fin 3) → StdSimplex ℝ ℝ)
    (x₀ x₁ : ℝ) :
    (toFiniteSCM mm).nie μ 0 1 2 id x₁ x₀ =
        noiseExpect μ (fun u => mm.naturalIndirectEffect x₀ x₁ (u 1) (u 2)) ∧
      (toFiniteSCM mm).nie μ 0 1 2 id x₁ x₀ = mm.a * mm.b * (x₁ - x₀) := by
  have hcf : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).counterfactual 0 x₀ u 2 =
      mm.potentialOutcome x₀ (u 1) (u 2) := fun u => toFiniteSCM_counterfactual mm x₀ u
  have hnc : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).nestedCounterfactual 0 1 x₀ x₁ u 2 =
      mm.nestedOutcome x₀ x₁ (u 1) (u 2) := fun u => toFiniteSCM_nestedCounterfactual mm x₀ x₁ u
  have e1 : (toFiniteSCM mm).nie μ 0 1 2 id x₁ x₀ =
      noiseExpect μ (fun u => mm.naturalIndirectEffect x₀ x₁ (u 1) (u 2)) := by
    simp only [nie, hcf, hnc, id_eq]
    unfold noiseExpect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    unfold MediationModel.naturalIndirectEffect MediationModel.nestedOutcome
      MediationModel.potentialOutcome MediationModel.outcome MediationModel.mediator
    ring
  have hconst : ∀ u : Fin 3 → ℝ, mm.naturalIndirectEffect x₀ x₁ (u 1) (u 2) =
      mm.a * mm.b * (x₁ - x₀) := by
    intro u
    unfold MediationModel.naturalIndirectEffect MediationModel.nestedOutcome
      MediationModel.potentialOutcome MediationModel.outcome MediationModel.mediator
    ring
  have e2 : (toFiniteSCM mm).nie μ 0 1 2 id x₁ x₀ = mm.a * mm.b * (x₁ - x₀) := by
    rw [e1, show (fun u : Fin 3 → ℝ => mm.naturalIndirectEffect x₀ x₁ (u 1) (u 2)) =
      (fun _ => mm.a * mm.b * (x₁ - x₀)) from funext hconst]
    exact noiseExpect_const μ _
  exact ⟨e1, e2⟩

/-- Pearl 2001, eq. (24) in the linear model: `TE = NIE + NDE`. -/
theorem te_toFiniteSCM (mm : MediationModel) (μ : (k : Fin 3) → StdSimplex ℝ ℝ) (x₀ x₁ : ℝ) :
    (toFiniteSCM mm).te μ 0 2 id x₁ x₀ =
      (toFiniteSCM mm).nie μ 0 1 2 id x₁ x₀ + (toFiniteSCM mm).nde μ 0 1 2 id x₁ x₀ := by
  have hcf1 : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).counterfactual 0 x₁ u 2 =
      mm.potentialOutcome x₁ (u 1) (u 2) := fun u => toFiniteSCM_counterfactual mm x₁ u
  have hcf0 : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).counterfactual 0 x₀ u 2 =
      mm.potentialOutcome x₀ (u 1) (u 2) := fun u => toFiniteSCM_counterfactual mm x₀ u
  have hn10 : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).nestedCounterfactual 0 1 x₁ x₀ u 2 =
      mm.nestedOutcome x₁ x₀ (u 1) (u 2) := fun u => toFiniteSCM_nestedCounterfactual mm x₁ x₀ u
  have hn01 : ∀ u : Fin 3 → ℝ, (toFiniteSCM mm).nestedCounterfactual 0 1 x₀ x₁ u 2 =
      mm.nestedOutcome x₀ x₁ (u 1) (u 2) := fun u => toFiniteSCM_nestedCounterfactual mm x₀ x₁ u
  simp only [te, nie, nde, hcf1, hcf0, hn10, hn01, id_eq]
  unfold noiseExpect
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  unfold MediationModel.nestedOutcome MediationModel.potentialOutcome MediationModel.outcome
    MediationModel.mediator
  ring

/-- NDE for `a = 3`, `b = -2`, `c' = 1/2`, contrast `2 → 5`: `3/2` (`LinearMediationTests`). -/
example (μ : (k : Fin 3) → StdSimplex ℝ ℝ) :
    (toFiniteSCM ⟨3, -2, 1/2⟩).nde μ 0 1 2 id 5 2 = 3 / 2 := by
  rw [(nde_toFiniteSCM _ μ 2 5).2]
  norm_num

/-- NIE for the same model and contrast: `-18`. -/
example (μ : (k : Fin 3) → StdSimplex ℝ ℝ) :
    (toFiniteSCM ⟨3, -2, 1/2⟩).nie μ 0 1 2 id 5 2 = -18 := by
  rw [(nie_toFiniteSCM _ μ 2 5).2]
  norm_num

/-- TE for the same model and contrast: `-33/2`. -/
example (μ : (k : Fin 3) → StdSimplex ℝ ℝ) :
    (toFiniteSCM ⟨3, -2, 1/2⟩).te μ 0 2 id 5 2 = -33 / 2 := by
  rw [te_toFiniteSCM, (nie_toFiniteSCM _ μ 2 5).2, (nde_toFiniteSCM _ μ 2 5).2]
  norm_num

/-! ### Interaction negative control -/

/-- `X = U_X`, `M = x + U_M`, `Y = x + m + x m + U_Y` on the nodes `0`, `1`, `2`. -/
def med_aux_interactionSCM : FiniteSCM ℝ 3 (fun _ => ℝ) where
  pa _ := univ
  f k z u :=
    if h0 : (k : ℕ) = 0 then u
    else if h1 : (k : ℕ) = 1 then z ⟨⟨0, by omega⟩, mem_univ _⟩ + u
    else
      z ⟨⟨0, by omega⟩, mem_univ _⟩ + z ⟨⟨1, by omega⟩, mem_univ _⟩ +
        z ⟨⟨0, by omega⟩, mem_univ _⟩ * z ⟨⟨1, by omega⟩, mem_univ _⟩ + u

private theorem med_aux_noiseExpect_sub (μ : (k : Fin 3) → StdSimplex ℝ ℝ)
    (F G : ((k : Fin 3) → ℝ) → ℝ) :
    noiseExpect μ F - noiseExpect μ G = noiseExpect μ (fun u => F u - G u) := by
  unfold noiseExpect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

private theorem med_aux_inter_cf1 (u : Fin 3 → ℝ) :
    med_aux_interactionSCM.counterfactual 0 1 u 2 = 3 + 2 * u 1 + u 2 := by
  have h : med_aux_interactionSCM.counterfactual 0 1 u 2 =
      1 + (1 + u 1) + 1 * (1 + u 1) + u 2 := rfl
  rw [h]
  ring

private theorem med_aux_inter_cf0 (u : Fin 3 → ℝ) :
    med_aux_interactionSCM.counterfactual 0 0 u 2 = u 1 + u 2 := by
  have h : med_aux_interactionSCM.counterfactual 0 0 u 2 =
      0 + (0 + u 1) + 0 * (0 + u 1) + u 2 := rfl
  rw [h]
  ring

private theorem med_aux_inter_nest01 (u : Fin 3 → ℝ) :
    med_aux_interactionSCM.nestedCounterfactual 0 1 0 1 u 2 = 1 + u 1 + u 2 := by
  have h : med_aux_interactionSCM.nestedCounterfactual 0 1 0 1 u 2 =
      0 + (1 + u 1) + 0 * (1 + u 1) + u 2 := rfl
  rw [h]
  ring

private theorem med_aux_inter_nest10 (u : Fin 3 → ℝ) :
    med_aux_interactionSCM.nestedCounterfactual 0 1 1 0 u 2 = 1 + 2 * u 1 + u 2 := by
  have h : med_aux_interactionSCM.nestedCounterfactual 0 1 1 0 u 2 =
      1 + (0 + u 1) + 1 * (0 + u 1) + u 2 := rfl
  rw [h]
  ring

/-- With interaction, Pearl's NIE for the contrast `0 → 1` is `1`, while `TE - NDE` (the
convention of `LinearMediation.MediationModel.naturalIndirectEffect`) is `2`, for every noise
law. -/
example (μ : (k : Fin 3) → StdSimplex ℝ ℝ) :
    med_aux_interactionSCM.nie μ 0 1 2 id 1 0 = 1 ∧
      med_aux_interactionSCM.te μ 0 2 id 1 0 - med_aux_interactionSCM.nde μ 0 1 2 id 1 0 = 2 := by
  constructor
  · unfold nie
    simp only [med_aux_inter_nest01, med_aux_inter_cf0, id]
    rw [med_aux_noiseExpect_sub]
    simp only [show ∀ u : Fin 3 → ℝ, (1 + u 1 + u 2) - (u 1 + u 2) = 1 from fun u => by ring]
    exact noiseExpect_const _ _
  · unfold te nde
    simp only [med_aux_inter_cf1, med_aux_inter_cf0, med_aux_inter_nest10, id]
    have hsub : ∀ E1 E2 E3 : ℝ, (E1 - E3) - (E2 - E3) = E1 - E2 := fun _ _ _ => by ring
    rw [hsub, med_aux_noiseExpect_sub]
    simp only [show ∀ u : Fin 3 → ℝ, (3 + 2 * u 1 + u 2) - (1 + 2 * u 1 + u 2) = 2 from
      fun u => by ring]
    exact noiseExpect_const _ _

private theorem med_aux_pos_hXZ_T : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual 0 true u 2)
    (fun u => med_aux_posControl.solve u 0)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_cf2, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hcross_TT_xT : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 true 2 true u 3)
    (fun u => med_aux_posControl.counterfactual 0 true u 2)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve1,
      med_aux_pos_cf2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_hcross_TF_xT : NoiseCondIndep med_aux_posNoise
    (fun u => med_aux_posControl.counterfactual₂ 0 true 2 false u 3)
    (fun u => med_aux_posControl.counterfactual 0 true u 2)
    (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
  unfold NoiseCondIndep
  intro a b c
  rcases med_aux_pos_Wcases c with rfl | rfl <;> cases a <;> cases b <;>
    unfold noiseProb <;> rw [med_aux_pos16] <;> beta_reduce <;>
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve1,
      med_aux_pos_cf2, med_aux_pos_cf23, med_aux_pos_fCeq] <;>
    norm_num

private theorem med_aux_pos_PosW_T : med_aux_PosW med_aux_posControl med_aux_posNoise 0 {1} true := by
  intro w hw
  rcases med_aux_pos_Wcases w with rfl | rfl
  · simp only [lawProb_inducedLaw]
    unfold noiseProb
    rw [med_aux_pos16]
    beta_reduce
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_fCeq]
    norm_num
  · simp only [lawProb_inducedLaw]
    unfold noiseProb
    rw [med_aux_pos16]
    beta_reduce
    simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
      med_aux_pos_solve1, med_aux_pos_fCeq]
    norm_num
/-- Positive control for the NIE identification theorem: its independence and positivity
hypotheses hold for the positive-control model at `(x, x*) = (false, true)`, and the
identified formula gives the value below, so `nie_eq_mediationFormulaNIE` is not vacuous
on this model. -/
example : med_aux_posControl.nie med_aux_posNoise 0 2 3 boolVal false true =
    mediationFormulaNIE (med_aux_posControl.inducedLaw med_aux_posNoise) 0 2 3 {1} boolVal
      false true := by
  have htm : (0 : Fin 4) ≠ 2 := by decide
  have hXY : ∀ z : Bool, NoiseCondIndep med_aux_posNoise
      (fun u => med_aux_posControl.counterfactual₂ 0 true 2 z u 3)
      (fun u => med_aux_posControl.solve u 0)
      (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
    intro z
    cases z
    · exact med_aux_pos_hXY_TF
    · exact med_aux_pos_hXY_TT
  have hZY : ∀ z : Bool, NoiseCondIndep med_aux_posNoise
      (fun u => med_aux_posControl.counterfactual₂ 0 true 2 z u 3)
      (fun u => med_aux_posControl.solve u 2)
      (fun u => (med_aux_posControl.solve u 0,
        (fun i : (({1} : Finset (Fin 4))) => med_aux_posControl.solve u i))) := by
    intro z
    cases z
    · unfold NoiseCondIndep
      intro a b c
      rcases c with ⟨c1, c2⟩
      rcases med_aux_pos_Wcases c2 with rfl | rfl
      · exact med_aux_pos_hZY_TF_T a b c1
      · exact med_aux_pos_hZY_TF_F a b c1
    · unfold NoiseCondIndep
      intro a b c
      rcases c with ⟨c1, c2⟩
      rcases med_aux_pos_Wcases c2 with rfl | rfl
      · exact med_aux_pos_hZY_TT_T a b c1
      · exact med_aux_pos_hZY_TT_F a b c1
  have hXZ : ∀ x' ∈ ({false, true} : Finset Bool), NoiseCondIndep med_aux_posNoise
      (fun u => med_aux_posControl.counterfactual 0 x' u 2)
      (fun u => med_aux_posControl.solve u 0)
      (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
    intro x' hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact med_aux_pos_hXZ
    · exact med_aux_pos_hXZ_T
  have hcross : ∀ x' ∈ ({false, true} : Finset Bool), ∀ z : Bool,
      NoiseCondIndep med_aux_posNoise
        (fun u => med_aux_posControl.counterfactual₂ 0 true 2 z u 3)
        (fun u => med_aux_posControl.counterfactual 0 x' u 2)
        (fun u (i : (({1} : Finset (Fin 4)))) => med_aux_posControl.solve u i) := by
    intro x' hx' z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · cases z
      · exact med_aux_pos_hcross_TF
      · exact med_aux_pos_hcross_TT
    · cases z
      · exact med_aux_pos_hcross_TF_xT
      · exact med_aux_pos_hcross_TT_xT
  have hposW : ∀ w : ((({1} : Finset (Fin 4))) → Bool),
      lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => (fun i : (({1} : Finset (Fin 4))) => v i) = w) ≠ 0 →
      ∀ x' ∈ ({false, true} : Finset Bool),
        lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
          (fun v => v 0 = x' ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = w) ≠ 0 := by
    intro w hw x' hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl
    · exact med_aux_pos_PosW w hw
    · exact med_aux_pos_PosW_T w hw
  have hposZ : ∀ (w : ((({1} : Finset (Fin 4))) → Bool)) (z : Bool),
      lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => v 0 = false ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = w) ≠ 0 →
      lawProb (med_aux_posControl.inducedLaw med_aux_posNoise)
        (fun v => v 0 = true ∧ v 2 = z ∧ (fun i : (({1} : Finset (Fin 4))) => v i) = w) ≠ 0 :=
    med_aux_pos_PosZ
  exact nie_eq_mediationFormulaNIE med_aux_posControl med_aux_posNoise htm 3 {1} boolVal
    false true hXY hZY hXZ hcross hposW hposZ

example :
    mediationFormulaNIE (med_aux_posControl.inducedLaw med_aux_posNoise) 0 2 3 {1} boolVal
      false true = -1 / 6 := by
  unfold mediationFormulaNIE
  rw [med_aux_pos_Wuniv, Finset.sum_insert (by decide), Finset.sum_singleton,
    med_aux_Bool_univ, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [med_aux_pos_lawMean, lawProb_inducedLaw]
  unfold noiseExpect noiseProb
  rw [med_aux_pos16]
  beta_reduce
  simp [Finset.sum_filter, med_aux_sum16, med_aux_pos_wt, med_aux_pos_solve0,
    med_aux_pos_solve1, med_aux_pos_solve2, med_aux_pos_solve3, med_aux_pos_fCeq, boolVal]
  norm_num

end Cslib.MachineLearning.MediationFormulaTests
