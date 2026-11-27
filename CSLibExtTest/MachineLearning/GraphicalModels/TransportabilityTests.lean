/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.Transportability
public import CSLibExt.MachineLearning.GraphicalModels.InterveningVsConditioning
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Tests for the transport formula

Exact examples for `CSLibExt/MachineLearning/GraphicalModels/Transportability.lean` on
three-node networks over `Bool`, all for the effect of `X = true` on `Y = true` (every value read
off the assignment `fun _ => true`):

* `ce1`: the transport formula fails without S-admissibility. The diagram `Z → X → Y`, `Z → Y`
  (Pearl–Bareinboim 2014, Figure 4(a), Markovian) with selection arrows into `Z` and `Y`, and
  source `InterveningVsConditioning.confoundedNet`: no set is S-admissible, pre-treatment and
  overlap hold, and the formula gives `29/50` against the target effect `1/10`.
* `ce2b`: the transport formula fails without the pre-treatment hypothesis. The chain
  `X → Z → Y` with a selection arrow into `Z`: `Z` is S-admissible (in the sense of the 2014 and of
  the 2011 definition), overlap holds, `Z` is a child of `X`, and the formula gives `1/2` against
  `3/10`.
* `ce3`: the transport formula fails without overlap. The diagram of `ce1` with a selection arrow
  into `Z` only, `P(Z = true) = 0`, `P*(Z = true) = 1` and `Y = X ∧ Z`: S-admissibility and
  pre-treatment hold, and the formula gives `0` against `1`.
* `pi1`: non-vacuity. The diagram of `ce3`, target `P*(Z = true) = 1/5`, `X` and `Y` shared:
  every hypothesis holds, `DomainPair.transport_formula` applies, the formula and the target
  effect are `29/50`, and the unadjusted source effect is `7/10`.

The bundled failure theorems, `pi1_transport_formula` and `pi1_reweighting` are assembled from
the graph facts and values below.
-/

@[expose] public section

namespace Cslib.MachineLearning.TransportabilityTests

open Cslib.MachineLearning GraphicalModels InterveningVsConditioning Finset
  MetaMathlibExt.FiniteWeight
open Function (updateFinset)

/-! ### The quantities of the transport formula at the all-`true` assignment -/

/-- The target effect `P*(Y = true | do(X = true))`: the left side of
`DomainPair.transport_formula` at the assignment `fun _ => true`. -/
noncomputable def targetEffect {D : SelectionDiagram 3} (M : DomainPair Bool D)
    (X Y : Finset (Fin 3)) : ℝ :=
  marginal (M.target.mutilateSet X fun _ => true).joint ↑Y fun _ => true

/-- The source effect `P(Y = true | do(X = true))`. -/
noncomputable def sourceEffect {D : SelectionDiagram 3} (M : DomainPair Bool D)
    (X Y : Finset (Fin 3)) : ℝ :=
  marginal (M.source.mutilateSet X fun _ => true).joint ↑Y fun _ => true

/-- The transport formula `∑_z P(Y = true | do(X = true), z) P*(z)`: the right side of
`DomainPair.transport_formula` at the assignment `fun _ => true`. -/
noncomputable def transportRhs {D : SelectionDiagram 3} (M : DomainPair Bool D)
    (X Y Z : Finset (Fin 3)) : ℝ :=
  ∑ z : Z → Bool,
    marginal (M.source.mutilateSet X fun _ => true).joint ↑(Y ∪ Z)
        (updateFinset (fun _ => true) Z z) /
        marginal (M.source.mutilateSet X fun _ => true).joint ↑Z
          (updateFinset (fun _ => true) Z z) *
      marginal M.target.joint ↑Z (updateFinset (fun _ => true) Z z)

/-- The overlap hypothesis `hov` of `DomainPair.transport_formula` at the assignment
`fun _ => true`: every value of `Z` with positive target probability has positive source
probability. -/
def Overlap {D : SelectionDiagram 3} (M : DomainPair Bool D) (Z : Finset (Fin 3)) : Prop :=
  ∀ z : Z → Bool, marginal M.target.joint ↑Z (updateFinset (fun _ => true) Z z) ≠ 0 →
    marginal M.source.joint ↑Z (updateFinset (fun _ => true) Z z) ≠ 0

/-! ### Diagrams on `Z → X → Y`, `Z → Y` -/

/-- Pearl–Bareinboim 2014, Figure 4(a), Markovian, without its invariance assumption at `Y`: the
diagram `Z → X → Y`, `Z → Y` of `InterveningVsConditioning.confoundedNet` (nodes `Z = 0`,
`X = 1`, `Y = 2`; every earlier node is a parent) with selection arrows into `Z` and `Y`. -/
def ce1Diagram : SelectionDiagram 3 := ⟨fun _ => univ, {0, 2}⟩

/-- The diagram `Z → X → Y`, `Z → Y` with a selection arrow into `Z` only (for `pi1` and
`ce3`). -/
def selZDiagram : SelectionDiagram 3 := ⟨fun _ => univ, {0}⟩

/-- No set is S-admissible for the effect of `X = 1` on `Y = 2` in `ce1Diagram`: the arrow
`S → Y` survives the removal of the arrows into `X`, so the two-node path `[Y, S]` (nodes `3`
and `0` of the augmented diagram) has no interior node and is not blocked. -/
theorem ce1_not_sAdmissible (T : Finset (Fin 3)) : ¬ce1Diagram.SAdmissible {1} {2} T := by
  intro h
  have hY : (({2} : Finset (Fin 3)).map (Fin.succEmb 3)) = {(3 : Fin 4)} := by decide
  have hx : (3 : Fin 4) ∈ ((({2} : Finset (Fin 3)).map (Fin.succEmb 3) : Finset (Fin 4)) :
      Set (Fin 4)) := by simp [hY]
  have hy : (0 : Fin 4) ∈ ((({0} : Finset (Fin 4))) : Set (Fin 4)) := by simp
  have hnodup : ([(3 : Fin 4), 0].Nodup) := by
    rw [List.nodup_cons, List.nodup_cons]
    exact ⟨by decide, by decide, List.nodup_nil⟩
  have hadj : (ce1Diagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 0 := Or.inr (by decide)
  have hchain : List.IsChain (ce1Diagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj [3, 0] :=
    List.IsChain.cons_cons hadj (List.IsChain.singleton _)
  have hpath : (ce1Diagram.toNet.mutilateSet (({1} : Finset (Fin 3)).map (Fin.succEmb 3))
      fun _ => ()).IsPath 3 0 [3, 0] := ⟨hnodup, hchain, rfl, rfl⟩
  have hpb := h 3 hx 0 hy [3, 0] hpath
  obtain ⟨i, hi, _⟩ := hpb
  have hlen : ([(3 : Fin 4), 0].length) = 2 := rfl
  omega

private theorem tp_aux_desc_le {α : Type*} {n : ℕ} (b : BayesNet α n) {i j : Fin n}
    (h : b.IsDescendant i j) : i.val ≤ j.val := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hed ih => exact ih.trans hed.1.le

/-- `Z = 0` is a pre-treatment covariate for `X = 1` in `ce1Diagram`: every arrow goes from a
smaller to a larger index. -/
theorem ce1_preTreatment : ce1Diagram.PreTreatment {1} {0} := by
  intro k hk z hz hdesc
  simp at hk hz
  subst hk hz
  have hle := tp_aux_desc_le ce1Diagram.graph hdesc
  exact (by decide : ¬(1 : Fin 3).val ≤ (0 : Fin 3).val) hle

private theorem tp_aux_nodup_len {m : ℕ} {p : List (Fin m)} (h : p.Nodup) : p.length ≤ m := by
  have h1 := List.toFinset_card_of_nodup h
  have h2 := Finset.card_le_univ p.toFinset
  rw [Fintype.card_fin] at h2
  omega

private instance tp_aux_decAdj {α : Type*} {n : ℕ} (b : BayesNet α n) : DecidableRel b.Adj :=
  fun i j => inferInstanceAs (Decidable (b.Edge i j ∨ b.Edge j i))

/-- `Z = 0` is S-admissible for the effect of `X = 1` on `Y = 2` in `selZDiagram`: removing the
arrows into `X` cuts `Z → X`, and the only path from `Y` to `S` (nodes `3` and `0` of the
augmented diagram) is `Y ← Z ← S`, blocked at `Z`. -/
theorem selZ_sAdmissible : selZDiagram.SAdmissible {1} {2} {0} := by
  have hN3 : ∀ b : Fin 4, (selZDiagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 b ↔
      (b = 1 ∨ b = 2) := by decide
  have hN0 : ∀ b : Fin 4, (selZDiagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj b 0 ↔ b = 1 := by decide
  have hN2 : ∀ b : Fin 4, (selZDiagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 2 b ↔ b = 3 := by decide
  have hAdj11 : ¬(selZDiagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 1 1 := by decide
  have hAdj30 : ¬(selZDiagram.toNet.mutilateSet
      (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 0 := by decide
  intro x hx y hy p hp
  have hY : (({2} : Finset (Fin 3)).map (Fin.succEmb 3)) = {(3 : Fin 4)} := by decide
  rw [hY, Finset.mem_coe, Finset.mem_singleton] at hx
  subst hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hy
  subst hy
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hp
  cases p with
  | nil =>
    rw [List.head?_nil] at hhead
    exact absurd hhead (by decide)
  | cons a t =>
    cases t with
    | nil =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
      rw [hhead] at hlast
      exact absurd hlast (by decide)
    | cons b t2 =>
      cases t2 with
      | nil =>
        simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
          Option.some.injEq] at hhead hlast
        subst hhead hlast
        rw [List.isChain_cons_cons] at hchain
        exact absurd hchain.1 hAdj30
      | cons c t3 =>
        cases t3 with
        | nil =>
          simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
            Option.some.injEq] at hhead hlast
          subst hhead hlast
          simp only [List.isChain_cons_cons] at hchain
          obtain ⟨hab, hbc, _⟩ := hchain
          have hb : b = 1 := (hN0 b).mp hbc
          subst hb
          refine ⟨0, by decide, ?_⟩
          show (selZDiagram.toNet.mutilateSet
            (({1} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).BlockedAt _ 3 1 0
          refine Or.inr ⟨by decide, by decide⟩
        | cons d t4 =>
          cases t4 with
          | nil =>
            simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
              Option.some.injEq] at hhead hlast
            subst hhead hlast
            simp only [List.isChain_cons_cons] at hchain
            obtain ⟨hab, hbc, hcd, _⟩ := hchain
            have hc : c = 1 := (hN0 c).mp hcd
            subst hc
            cases (hN3 b).mp hab with
            | inl hb1 =>
              subst hb1
              exact absurd hbc hAdj11
            | inr hb2 =>
              subst hb2
              have hcontra := (hN2 1).mp hbc
              exact absurd hcontra (by decide)
          | cons e t5 =>
            have hlen := tp_aux_nodup_len hnodup
            simp only [List.length_cons] at hlen
            omega

/-- `Z = 0` is a pre-treatment covariate for `X = 1` in `selZDiagram`. -/
theorem selZ_preTreatment : selZDiagram.PreTreatment {1} {0} := by
  intro k hk z hz hdesc
  simp at hk hz
  subst hk hz
  have hle := tp_aux_desc_le selZDiagram.graph hdesc
  exact (by decide : ¬(1 : Fin 3).val ≤ (0 : Fin 3).val) hle

/-- The target tables of `ce1`: `P*(Z = true) = 1/5`; the table of `X` is that of
`confoundedNet`; `P*(Y = true | X, Z) = 1/10, 1/10, 1/2, 1/10` for
`(X, Z) = (true, true), (true, false), (false, true), (false, false)`. -/
noncomputable def ce1TargetCpt (k : Fin 3) (u : ↥(univ : Finset (Fin k)) → Bool) :
    Convexity.StdSimplex ℝ Bool :=
  if h0 : (k : ℕ) = 0 then coin (1 / 5) (by norm_num) (by norm_num)
  else if h1 : (k : ℕ) = 1 then confoundedNet.cpt k u
  else if u ⟨⟨1, by omega⟩, mem_univ _⟩ then coin (1 / 10) (by norm_num) (by norm_num)
  else if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (1 / 2) (by norm_num) (by norm_num)
  else coin (1 / 10) (by norm_num) (by norm_num)

/-- The source `InterveningVsConditioning.confoundedNet` and the target `ce1TargetCpt` on
`ce1Diagram`: only `X` has no selection arrow, and its table is shared. -/
noncomputable def ce1 : DomainPair Bool ce1Diagram where
  cpt := confoundedNet.cpt
  cpt' := ce1TargetCpt
  cpt'_eq := by
    intro k hk
    fin_cases k
    · exact (hk (by simp [ce1Diagram])).elim
    · rfl
    · exact (hk (by simp [ce1Diagram])).elim

private theorem tp_aux_marginal_ne_zero {n : ℕ} {α : Type*} [Fintype α]
    (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x) (S : Finset (Fin n)) (x : Fin n → α)
    (h : 0 < P x) : marginal P ↑S x ≠ 0 := by
  unfold marginal
  refine ne_of_gt (lt_of_lt_of_le h (Finset.single_le_sum (fun y _ => hP y) ?_))
  simp

private theorem tp_aux_confounded_pos (x : Fin 3 → Bool) : 0 < confoundedNet.joint x := by
  rw [BayesNet.joint_eq_prod]
  apply Finset.prod_pos
  intro k _
  fin_cases k
  · have hc : ∀ (u : confoundedNet.pa 0 → Bool) (b : Bool),
        0 < (confoundedNet.cpt 0 u).weights b := by
      intro u b
      have he : confoundedNet.cpt 0 u = coin (1 / 2) (by norm_num) (by norm_num) := rfl
      rw [he]
      cases b <;> simp only [coin_true, coin_false] <;> norm_num
    exact hc _ _
  · have hc : ∀ (u : confoundedNet.pa 1 → Bool) (b : Bool),
        0 < (confoundedNet.cpt 1 u).weights b := by
      intro u b
      have he : confoundedNet.cpt 1 u =
          (if u ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ then coin (4 / 5) (by norm_num)
              (by norm_num) else coin (1 / 5) (by norm_num) (by norm_num)) := rfl
      rw [he]
      split_ifs
      · cases b <;> simp only [coin_true, coin_false] <;> norm_num
      · cases b <;> simp only [coin_true, coin_false] <;> norm_num
    exact hc _ _
  · have hc : ∀ (u : confoundedNet.pa 2 → Bool) (b : Bool),
        0 < (confoundedNet.cpt 2 u).weights b := by
      intro u b
      have he : confoundedNet.cpt 2 u =
          (if u ⟨⟨1, by omega⟩, Finset.mem_univ _⟩ then
            (if u ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ then coin (9 / 10) (by norm_num)
              (by norm_num) else coin (1 / 2) (by norm_num) (by norm_num))
          else
            (if u ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ then coin (1 / 2) (by norm_num)
              (by norm_num) else coin (1 / 10) (by norm_num) (by norm_num))) := rfl
      rw [he]
      split_ifs
      all_goals (cases b <;> simp only [coin_true, coin_false] <;> norm_num)
    exact hc _ _

/-- Overlap holds in `ce1`: the source law of `Z` is a fair coin. -/
theorem ce1_overlap : Overlap ce1 {0} := by
  intro z _
  apply tp_aux_marginal_ne_zero
  · intro x
    exact ce1.source.toChain.joint_nonneg 3 x
  · exact tp_aux_confounded_pos _

/-- The target effect in `ce1`: `P*(Y = true | do(X = true)) = 1/10 · 1/5 + 1/10 · 4/5 = 1/10`. -/
theorem ce1_target : targetEffect ce1 {1} {2} = 1 / 10 := by
  unfold targetEffect
  rw [marginal_coe]
  simp only [Finset.mem_singleton, forall_eq] at *
  have hsum : (∑ x with x 2 = true,
      ((DomainPair.target ce1).mutilateSet {1} (fun _ => true)).joint x)
      = ∑ x, if x 2 = true then
      ((DomainPair.target ce1).mutilateSet {1} (fun _ => true)).joint x else 0 := by
    rw [Finset.sum_filter]
  rw [hsum]
  rw [expand8]
  simp only [BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp [ce1, DomainPair.target, ce1TargetCpt, confoundedNet, BayesNet.paVal,
    coin_true, coin_false, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The transport formula in `ce1`: `9/10 · 1/5 + 1/2 · 4/5 = 29/50`. -/
theorem ce1_formula : transportRhs ce1 {1} {2} {0} = 29 / 50 := by
  unfold transportRhs
  have huniv : (Finset.univ : Finset (↥({0} : Finset (Fin 3)) → Bool))
      = {fun _ => true, fun _ => false} := by decide
  rw [huniv]
  rw [Finset.sum_pair (by decide : (fun _ : ↥({0} : Finset (Fin 3)) => true)
    ≠ fun _ => false)]
  simp only [marginal_coe, Finset.sum_filter, expand8,
    BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp only [BayesNet.joint_eq_prod, Fin.prod_univ_three] at *
  simp [ce1, DomainPair.source, DomainPair.target, BayesNet.mutilateSet,
    ce1TargetCpt, confoundedNet, BayesNet.paVal, coin_true, coin_false,
    Convexity.StdSimplex.weights_single, Matrix.cons_val_zero,
    Matrix.cons_val_one, Function.updateFinset_def]
  norm_num

/-- **The transport formula fails without S-admissibility.** In `ce1` every other hypothesis of
`DomainPair.transport_formula` holds, and the target effect `1/10` differs from the formula's
`29/50`. -/
theorem ce1_transport_formula_fails :
    Disjoint ({1} : Finset (Fin 3)) {2} ∧ Disjoint ({1} : Finset (Fin 3)) {0} ∧
      Disjoint ({2} : Finset (Fin 3)) {0} ∧ ¬ce1Diagram.SAdmissible {1} {2} {0} ∧
      ce1Diagram.PreTreatment {1} {0} ∧ Overlap ce1 {0} ∧
      targetEffect ce1 {1} {2} ≠ transportRhs ce1 {1} {2} {0} :=
  ⟨by decide, by decide, by decide, ce1_not_sAdmissible {0}, ce1_preTreatment, ce1_overlap,
    by rw [ce1_target, ce1_formula]; norm_num⟩

/-! ### `ce2b`: the formula fails without the pre-treatment hypothesis -/

/-- The chain `X → Z → Y` (nodes `X = 0`, `Z = 1`, `Y = 2`) with exact parent sets `pa 0 = ∅`,
`pa 1 = {0}`, `pa 2 = {1}`, as in `CausalWitnesses.copyChainNet`. -/
def chainPa : (k : Fin 3) → Finset (Fin k) := fun k =>
  if _ : (k : ℕ) = 0 then ∅
  else if _ : (k : ℕ) = 1 then {⟨0, by omega⟩}
  else {⟨1, by omega⟩}

/-- The chain `X → Z → Y` with a selection arrow into `Z`. -/
def ce2bDiagram : SelectionDiagram 3 := ⟨chainPa, {1}⟩

/-- The source tables of `ce2b`: `P(X = true) = 1/2`; `P(Z = true | X) = 3/4, 1/4` for
`X = true, false`; `P(Y = true | Z) = 9/10, 1/10` for `Z = true, false`. -/
noncomputable def ce2bSourceCpt (k : Fin 3) (u : chainPa k → Bool) :
    Convexity.StdSimplex ℝ Bool :=
  if h0 : (k : ℕ) = 0 then coin (1 / 2) (by norm_num) (by norm_num)
  else if h1 : (k : ℕ) = 1 then
    (if u ⟨⟨0, by omega⟩, by simp [chainPa, h1]⟩ then coin (3 / 4) (by norm_num) (by norm_num)
      else coin (1 / 4) (by norm_num) (by norm_num))
  else
    (if u ⟨⟨1, by omega⟩, by simp [chainPa, h0, h1]⟩ then
      coin (9 / 10) (by norm_num) (by norm_num)
      else coin (1 / 10) (by norm_num) (by norm_num))

/-- The target tables of `ce2b`: `P*(Z = true | X) = 1/4, 3/4` for `X = true, false`; the tables
of `X` and `Y` are those of the source. -/
noncomputable def ce2bTargetCpt (k : Fin 3) (u : chainPa k → Bool) :
    Convexity.StdSimplex ℝ Bool :=
  if h1 : (k : ℕ) = 1 then
    (if u ⟨⟨0, by omega⟩, by simp [chainPa, h1]⟩ then coin (1 / 4) (by norm_num) (by norm_num)
      else coin (3 / 4) (by norm_num) (by norm_num))
  else ce2bSourceCpt k u

/-- The source `ce2bSourceCpt` and the target `ce2bTargetCpt` on `ce2bDiagram`. -/
noncomputable def ce2b : DomainPair Bool ce2bDiagram where
  cpt := ce2bSourceCpt
  cpt' := ce2bTargetCpt
  cpt'_eq := by
    intro k hk
    fin_cases k
    · rfl
    · exact (hk (by simp [ce2bDiagram])).elim
    · rfl

/-- `Z = 1` is S-admissible for the effect of `X = 0` on `Y = 2` in `ce2bDiagram`: the only path
from `Y` to `S` (nodes `3` and `0` of the augmented diagram) is `Y ← Z ← S`, blocked at `Z`. -/
theorem ce2b_sAdmissible : ce2bDiagram.SAdmissible {0} {2} {1} := by
  have hN3 : ∀ b : Fin 4, (ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 b ↔ b = 2 := by decide
  have hN0 : ∀ b : Fin 4, (ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj b 0 ↔ b = 2 := by decide
  have hAdj22 : ¬(ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 2 2 := by decide
  have hAdj30 : ¬(ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 0 := by decide
  intro x hx y hy p hp
  have hY : (({2} : Finset (Fin 3)).map (Fin.succEmb 3)) = {(3 : Fin 4)} := by decide
  rw [hY, Finset.mem_coe, Finset.mem_singleton] at hx
  subst hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hy
  subst hy
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hp
  cases p with
  | nil =>
    rw [List.head?_nil] at hhead
    exact absurd hhead (by decide)
  | cons a t =>
    cases t with
    | nil =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
      rw [hhead] at hlast
      exact absurd hlast (by decide)
    | cons b t2 =>
      cases t2 with
      | nil =>
        simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
          Option.some.injEq] at hhead hlast
        subst hhead hlast
        rw [List.isChain_cons_cons] at hchain
        exact absurd hchain.1 hAdj30
      | cons c t3 =>
        cases t3 with
        | nil =>
          simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
            Option.some.injEq] at hhead hlast
          subst hhead hlast
          simp only [List.isChain_cons_cons] at hchain
          obtain ⟨hab, hbc, _⟩ := hchain
          have hb : b = 2 := (hN0 b).mp hbc
          subst hb
          refine ⟨0, by decide, ?_⟩
          show (ce2bDiagram.toNet.mutilateSet
            (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).BlockedAt _ 3 2 0
          refine Or.inr ⟨by decide, by decide⟩
        | cons d t4 =>
          cases t4 with
          | nil =>
            simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
              Option.some.injEq] at hhead hlast
            subst hhead hlast
            simp only [List.isChain_cons_cons] at hchain
            obtain ⟨hab, hbc, hcd, _⟩ := hchain
            have hb : b = 2 := (hN3 b).mp hab
            have hc : c = 2 := (hN0 c).mp hcd
            subst hb hc
            exact absurd hbc hAdj22
          | cons e t5 =>
            have hlen := tp_aux_nodup_len hnodup
            simp only [List.length_cons] at hlen
            omega

/-- `Z = 1` is also S-admissible in the sense of AAAI 2011, Definition 4, whose conditioning set
omits `X`: `(Y ⫫ S | Z)` holds in `D_{\bar X}`. -/
theorem ce2b_sAdmissible_aaai :
    (ce2bDiagram.toNet.mutilateSet (({0} : Finset (Fin 3)).map (Fin.succEmb 3))
        fun _ => ()).DSeparated
      ((({2} : Finset (Fin 3)).map (Fin.succEmb 3) : Finset (Fin (3 + 1))) :
        Set (Fin (3 + 1)))
      (({0} : Finset (Fin (3 + 1))) : Set (Fin (3 + 1)))
      ((({1} : Finset (Fin 3)).map (Fin.succEmb 3) : Finset (Fin (3 + 1))) :
        Set (Fin (3 + 1))) := by
  have hN3 : ∀ b : Fin 4, (ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 b ↔ b = 2 := by decide
  have hN0 : ∀ b : Fin 4, (ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj b 0 ↔ b = 2 := by decide
  have hAdj22 : ¬(ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 2 2 := by decide
  have hAdj30 : ¬(ce2bDiagram.toNet.mutilateSet
      (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).Adj 3 0 := by decide
  intro x hx y hy p hp
  have hY : (({2} : Finset (Fin 3)).map (Fin.succEmb 3)) = {(3 : Fin 4)} := by decide
  rw [hY, Finset.mem_coe, Finset.mem_singleton] at hx
  subst hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hy
  subst hy
  obtain ⟨hnodup, hchain, hhead, hlast⟩ := hp
  cases p with
  | nil =>
    rw [List.head?_nil] at hhead
    exact absurd hhead (by decide)
  | cons a t =>
    cases t with
    | nil =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
      rw [hhead] at hlast
      exact absurd hlast (by decide)
    | cons b t2 =>
      cases t2 with
      | nil =>
        simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
          Option.some.injEq] at hhead hlast
        subst hhead hlast
        rw [List.isChain_cons_cons] at hchain
        exact absurd hchain.1 hAdj30
      | cons c t3 =>
        cases t3 with
        | nil =>
          simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
            Option.some.injEq] at hhead hlast
          subst hhead hlast
          simp only [List.isChain_cons_cons] at hchain
          obtain ⟨hab, hbc, _⟩ := hchain
          have hb : b = 2 := (hN0 b).mp hbc
          subst hb
          refine ⟨0, by decide, ?_⟩
          show (ce2bDiagram.toNet.mutilateSet
            (({0} : Finset (Fin 3)).map (Fin.succEmb 3)) fun _ => ()).BlockedAt _ 3 2 0
          refine Or.inr ⟨by decide, by decide⟩
        | cons d t4 =>
          cases t4 with
          | nil =>
            simp only [List.head?_cons, List.getLast?_singleton, List.getLast?_cons_cons,
              Option.some.injEq] at hhead hlast
            subst hhead hlast
            simp only [List.isChain_cons_cons] at hchain
            obtain ⟨hab, hbc, hcd, _⟩ := hchain
            have hb : b = 2 := (hN3 b).mp hab
            have hc : c = 2 := (hN0 c).mp hcd
            subst hb hc
            exact absurd hbc hAdj22
          | cons e t5 =>
            have hlen := tp_aux_nodup_len hnodup
            simp only [List.length_cons] at hlen
            omega

/-- `Z = 1` is a child of `X = 0`, so it is not a pre-treatment covariate for `X`. -/
theorem ce2b_not_preTreatment : ¬ce2bDiagram.PreTreatment {0} {1} := by
  intro h
  exact h 0 (by decide) 1 (by decide) (Relation.ReflTransGen.single (by decide))

private theorem tp_aux_ce2bsrc_pos (x : Fin 3 → Bool) :
    0 < (⟨chainPa, ce2bSourceCpt⟩ : BayesNet Bool 3).joint x := by
  rw [BayesNet.joint_eq_prod]
  apply Finset.prod_pos
  intro k _
  fin_cases k
  · have hc : ∀ (u : chainPa 0 → Bool) (b : Bool),
        0 < (ce2bSourceCpt 0 u).weights b := by
      intro u b
      have he : ce2bSourceCpt 0 u = coin (1 / 2) (by norm_num) (by norm_num) := rfl
      rw [he]
      cases b <;> simp only [coin_true, coin_false] <;> norm_num
    exact hc ((⟨chainPa, ce2bSourceCpt⟩ : BayesNet Bool 3).paVal 0 x) (x 0)
  · have hc : ∀ (u : chainPa 1 → Bool) (b : Bool),
        0 < (ce2bSourceCpt 1 u).weights b := by
      intro u b
      have he : ce2bSourceCpt 1 u =
          (if u ⟨⟨0, by omega⟩, by decide⟩ then coin (3 / 4) (by norm_num) (by norm_num)
            else coin (1 / 4) (by norm_num) (by norm_num)) := rfl
      rw [he]
      split_ifs
      · cases b <;> simp only [coin_true, coin_false] <;> norm_num
      · cases b <;> simp only [coin_true, coin_false] <;> norm_num
    exact hc ((⟨chainPa, ce2bSourceCpt⟩ : BayesNet Bool 3).paVal 1 x) (x 1)
  · have hc : ∀ (u : chainPa 2 → Bool) (b : Bool),
        0 < (ce2bSourceCpt 2 u).weights b := by
      intro u b
      have he : ce2bSourceCpt 2 u =
          (if u ⟨⟨1, by omega⟩, by decide⟩ then coin (9 / 10) (by norm_num) (by norm_num)
            else coin (1 / 10) (by norm_num) (by norm_num)) := rfl
      rw [he]
      split_ifs
      · cases b <;> simp only [coin_true, coin_false] <;> norm_num
      · cases b <;> simp only [coin_true, coin_false] <;> norm_num
    exact hc ((⟨chainPa, ce2bSourceCpt⟩ : BayesNet Bool 3).paVal 2 x) (x 2)

/-- Overlap holds in `ce2b`: the source law of `Z` is uniform. -/
theorem ce2b_overlap : Overlap ce2b {1} := by
  intro z _
  apply tp_aux_marginal_ne_zero
  · intro x
    exact ce2b.source.toChain.joint_nonneg 3 x
  · exact tp_aux_ce2bsrc_pos _

/-- The target effect in `ce2b`: `P*(Y = true | do(X = true)) = 9/10 · 1/4 + 1/10 · 3/4 =
3/10`. -/
theorem ce2b_target : targetEffect ce2b {0} {2} = 3 / 10 := by
  unfold targetEffect
  rw [marginal_coe]
  simp only [Finset.mem_singleton, forall_eq] at *
  have hsum : (∑ x with x 2 = true,
      ((DomainPair.target ce2b).mutilateSet {0} (fun _ => true)).joint x)
      = ∑ x, if x 2 = true then
      ((DomainPair.target ce2b).mutilateSet {0} (fun _ => true)).joint x else 0 := by
    rw [Finset.sum_filter]
  rw [hsum]
  rw [expand8]
  simp only [BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp [ce2b, ce2bDiagram, DomainPair.target, ce2bTargetCpt, ce2bSourceCpt,
    chainPa, BayesNet.paVal, coin_true, coin_false,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The transport formula in `ce2b`: `9/10 · 1/2 + 1/10 · 1/2 = 1/2`. -/
theorem ce2b_formula : transportRhs ce2b {0} {2} {1} = 1 / 2 := by
  unfold transportRhs
  have huniv : (Finset.univ : Finset (↥({1} : Finset (Fin 3)) → Bool))
      = {fun _ => true, fun _ => false} := by decide
  rw [huniv]
  rw [Finset.sum_pair (by decide : (fun _ : ↥({1} : Finset (Fin 3)) => true)
    ≠ fun _ => false)]
  simp only [marginal_coe, Finset.sum_filter, expand8,
    BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp only [BayesNet.joint_eq_prod, Fin.prod_univ_three] at *
  simp [ce2b, ce2bDiagram, DomainPair.source, DomainPair.target,
    BayesNet.mutilateSet, ce2bSourceCpt, ce2bTargetCpt, chainPa,
    BayesNet.paVal, coin_true, coin_false,
    Convexity.StdSimplex.weights_single, Matrix.cons_val_zero,
    Matrix.cons_val_one, Function.updateFinset_def]
  norm_num

/-- **The transport formula fails without the pre-treatment hypothesis.** In `ce2b` every other
hypothesis of `DomainPair.transport_formula` holds, and the target effect `3/10` differs from the
formula's `1/2`. -/
theorem ce2b_transport_formula_fails :
    Disjoint ({0} : Finset (Fin 3)) {2} ∧ Disjoint ({0} : Finset (Fin 3)) {1} ∧
      Disjoint ({2} : Finset (Fin 3)) {1} ∧ ce2bDiagram.SAdmissible {0} {2} {1} ∧
      ¬ce2bDiagram.PreTreatment {0} {1} ∧ Overlap ce2b {1} ∧
      targetEffect ce2b {0} {2} ≠ transportRhs ce2b {0} {2} {1} :=
  ⟨by decide, by decide, by decide, ce2b_sAdmissible, ce2b_not_preTreatment, ce2b_overlap,
    by rw [ce2b_target, ce2b_formula]; norm_num⟩

/-! ### `ce3`: the formula fails without overlap -/

/-- The source tables of `ce3`: `P(Z = true) = 0`; `X` is a fair coin, independent of `Z`;
`Y = X ∧ Z`. -/
noncomputable def ce3SourceCpt (k : Fin 3) (u : ↥(univ : Finset (Fin k)) → Bool) :
    Convexity.StdSimplex ℝ Bool :=
  if h0 : (k : ℕ) = 0 then coin 0 (by norm_num) (by norm_num)
  else if h1 : (k : ℕ) = 1 then coin (1 / 2) (by norm_num) (by norm_num)
  else if u ⟨⟨1, by omega⟩, mem_univ _⟩ && u ⟨⟨0, by omega⟩, mem_univ _⟩ then
    coin 1 (by norm_num) (by norm_num)
  else coin 0 (by norm_num) (by norm_num)

/-- The target tables of `ce3`: `P*(Z = true) = 1`; the tables of `X` and `Y` are those of the
source. -/
noncomputable def ce3TargetCpt (k : Fin 3) (u : ↥(univ : Finset (Fin k)) → Bool) :
    Convexity.StdSimplex ℝ Bool :=
  if (k : ℕ) = 0 then coin 1 (by norm_num) (by norm_num) else ce3SourceCpt k u

/-- The source `ce3SourceCpt` and the target `ce3TargetCpt` on `selZDiagram`. -/
noncomputable def ce3 : DomainPair Bool selZDiagram where
  cpt := ce3SourceCpt
  cpt' := ce3TargetCpt
  cpt'_eq := by
    intro k hk
    fin_cases k
    · exact (hk (by simp [selZDiagram])).elim
    · rfl
    · rfl

/-- Overlap fails in `ce3`: `P*(Z = true) = 1` while `P(Z = true) = 0`. -/
theorem ce3_no_overlap : ¬Overlap ce3 {0} := by
  intro hcon
  have hx' : ∀ i : Fin 3, updateFinset (fun _ => true) {0} (fun _ => true) i = true := by
    intro i
    by_cases hi : i ∈ ({0} : Finset (Fin 3)) <;> simp [Function.updateFinset_def, hi]
  have htgt : marginal ce3.target.joint ↑({0} : Finset (Fin 3))
      (updateFinset (fun _ => true) {0} fun _ => true) ≠ 0 := by
    apply tp_aux_marginal_ne_zero
    · intro x
      exact ce3.target.toChain.joint_nonneg 3 x
    · rw [BayesNet.joint_eq_prod]
      apply Finset.prod_pos
      intro k _
      fin_cases k
      · have hpos : 0 < (ce3.target.cpt 0
            (ce3.target.paVal 0 (updateFinset (fun _ => true) {0} fun _ => true))).weights
            ((updateFinset (fun _ => true) {0} fun _ => true) (0 : Fin 3)) := by
          have he : ce3.target.cpt 0
              (ce3.target.paVal 0 (updateFinset (fun _ => true) {0} fun _ => true)) =
              coin 1 (by norm_num) (by norm_num) := rfl
          rw [he, hx' 0, coin_true]
          norm_num
        exact hpos
      · have hpos : 0 < (ce3.target.cpt 1
            (ce3.target.paVal 1 (updateFinset (fun _ => true) {0} fun _ => true))).weights
            ((updateFinset (fun _ => true) {0} fun _ => true) (1 : Fin 3)) := by
          have he : ce3.target.cpt 1
              (ce3.target.paVal 1 (updateFinset (fun _ => true) {0} fun _ => true)) =
              coin (1 / 2) (by norm_num) (by norm_num) := rfl
          rw [he, hx' 1, coin_true]
          norm_num
        exact hpos
      · have hpos : 0 < (ce3.target.cpt 2
            (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true))).weights
            ((updateFinset (fun _ => true) {0} fun _ => true) (2 : Fin 3)) := by
          have hr : ce3.target.cpt 2
              (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true)) =
              (if (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true))
                  ⟨⟨1, by omega⟩, Finset.mem_univ _⟩ &&
                  (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true))
                  ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ then
                coin 1 (by norm_num) (by norm_num) else coin 0 (by norm_num)
                (by norm_num)) := rfl
          have hu1 : (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true))
              ⟨⟨1, by omega⟩, Finset.mem_univ _⟩ = true := by decide
          have hu0 : (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true))
              ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ = true := by decide
          have hce : ce3.target.cpt 2
              (ce3.target.paVal 2 (updateFinset (fun _ => true) {0} fun _ => true)) =
              coin 1 (by norm_num) (by norm_num) := by rw [hr, hu1, hu0]; rfl
          rw [hce, hx' 2, coin_true]
          norm_num
        exact hpos
  have hsrc := hcon (fun _ => true) htgt
  have hzero : marginal ce3.source.joint ↑({0} : Finset (Fin 3))
      (updateFinset (fun _ => true) {0} fun _ => true) = 0 := by
    rw [marginal_coe]
    apply Finset.sum_eq_zero
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hy0 : y 0 = true := by
      have h1 := hy 0 (Finset.mem_singleton_self 0)
      rw [hx' 0] at h1
      exact h1
    rw [BayesNet.joint_eq_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ 0)
    rw [hy0]
    have he : ∀ u : ce3.source.pa 0 → Bool,
        ce3.source.cpt 0 u = coin 0 (by norm_num) (by norm_num) := fun u => rfl
    rw [he, coin_true]
  exact hsrc hzero

/-- The target effect in `ce3`: `Z = true` and `X = true` force `Y = true`, so
`P*(Y = true | do(X = true)) = 1`. -/
theorem ce3_target : targetEffect ce3 {1} {2} = 1 := by
  unfold targetEffect
  rw [marginal_coe]
  simp only [Finset.mem_singleton, forall_eq] at *
  have hsum : (∑ x with x 2 = true,
      ((DomainPair.target ce3).mutilateSet {1} (fun _ => true)).joint x)
      = ∑ x, if x 2 = true then
      ((DomainPair.target ce3).mutilateSet {1} (fun _ => true)).joint x else 0 := by
    rw [Finset.sum_filter]
  rw [hsum]
  rw [expand8]
  simp only [BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp [ce3, DomainPair.target, BayesNet.paVal, ce3TargetCpt, ce3SourceCpt,
    coin_true, coin_false, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The transport formula in `ce3`: the stratum `Z = true` has source probability `0`, so its
conditional is `0 / 0 = 0`, and the stratum `Z = false` has `Y = false` and target weight `0`. -/
theorem ce3_formula : transportRhs ce3 {1} {2} {0} = 0 := by
  unfold transportRhs
  have huniv : (Finset.univ : Finset (↥({0} : Finset (Fin 3)) → Bool))
      = {fun _ => true, fun _ => false} := by decide
  rw [huniv]
  rw [Finset.sum_pair (by decide : (fun _ : ↥({0} : Finset (Fin 3)) => true)
    ≠ fun _ => false)]
  simp only [marginal_coe, Finset.sum_filter, expand8,
    BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp only [BayesNet.joint_eq_prod] at *
  simp [ce3, DomainPair.source, DomainPair.target, BayesNet.mutilateSet,
    BayesNet.paVal, ce3SourceCpt, ce3TargetCpt, coin_true, coin_false,
    Convexity.StdSimplex.weights_single, Matrix.cons_val_zero,
    Matrix.cons_val_one, Function.updateFinset_def]

/-- **The transport formula fails without overlap.** In `ce3` every other hypothesis of
`DomainPair.transport_formula` holds, and the target effect `1` differs from the formula's `0`. -/
theorem ce3_transport_formula_fails :
    Disjoint ({1} : Finset (Fin 3)) {2} ∧ Disjoint ({1} : Finset (Fin 3)) {0} ∧
      Disjoint ({2} : Finset (Fin 3)) {0} ∧ selZDiagram.SAdmissible {1} {2} {0} ∧
      selZDiagram.PreTreatment {1} {0} ∧ ¬Overlap ce3 {0} ∧
      targetEffect ce3 {1} {2} ≠ transportRhs ce3 {1} {2} {0} :=
  ⟨by decide, by decide, by decide, selZ_sAdmissible, selZ_preTreatment, ce3_no_overlap,
    by rw [ce3_target, ce3_formula]; norm_num⟩

/-! ### `pi1`: every hypothesis holds -/

/-- The target tables of `pi1`: `P*(Z = true) = 1/5`; the tables of `X` and `Y` are those of
`confoundedNet`. -/
noncomputable def pi1TargetCpt (k : Fin 3) (u : ↥(univ : Finset (Fin k)) → Bool) :
    Convexity.StdSimplex ℝ Bool :=
  if (k : ℕ) = 0 then coin (1 / 5) (by norm_num) (by norm_num) else confoundedNet.cpt k u

/-- The source `InterveningVsConditioning.confoundedNet` and the target `pi1TargetCpt` on
`selZDiagram`. -/
noncomputable def pi1 : DomainPair Bool selZDiagram where
  cpt := confoundedNet.cpt
  cpt' := pi1TargetCpt
  cpt'_eq := by
    intro k hk
    fin_cases k
    · exact (hk (by simp [selZDiagram])).elim
    · rfl
    · rfl

/-- Overlap holds in `pi1`: the source law of `Z` is a fair coin. -/
theorem pi1_overlap : Overlap pi1 {0} := by
  intro z _
  apply tp_aux_marginal_ne_zero
  · intro x
    exact pi1.source.toChain.joint_nonneg 3 x
  · exact tp_aux_confounded_pos _

/-- The target effect in `pi1`: `P*(Y = true | do(X = true)) = 1/5 · 9/10 + 4/5 · 1/2 =
29/50`. -/
theorem pi1_target : targetEffect pi1 {1} {2} = 29 / 50 := by
  unfold targetEffect
  rw [marginal_coe]
  simp only [Finset.mem_singleton, forall_eq] at *
  have hsum : (∑ x with x 2 = true,
      ((DomainPair.target pi1).mutilateSet {1} (fun _ => true)).joint x)
      = ∑ x, if x 2 = true then
      ((DomainPair.target pi1).mutilateSet {1} (fun _ => true)).joint x else 0 := by
    rw [Finset.sum_filter]
  rw [hsum]
  rw [expand8]
  simp only [BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp [pi1, DomainPair.target, pi1TargetCpt, confoundedNet, BayesNet.paVal,
    coin_true, coin_false, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The transport formula in `pi1`: `9/10 · 1/5 + 1/2 · 4/5 = 29/50`. -/
theorem pi1_formula : transportRhs pi1 {1} {2} {0} = 29 / 50 := by
  unfold transportRhs
  have huniv : (Finset.univ : Finset (↥({0} : Finset (Fin 3)) → Bool))
      = {fun _ => true, fun _ => false} := by decide
  rw [huniv]
  rw [Finset.sum_pair (by decide : (fun _ : ↥({0} : Finset (Fin 3)) => true)
    ≠ fun _ => false)]
  simp only [marginal_coe, Finset.sum_filter, expand8,
    BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp only [BayesNet.joint_eq_prod, Fin.prod_univ_three] at *
  simp [pi1, DomainPair.source, DomainPair.target, BayesNet.mutilateSet,
    pi1TargetCpt, confoundedNet, BayesNet.paVal, coin_true, coin_false,
    Convexity.StdSimplex.weights_single, Matrix.cons_val_zero,
    Matrix.cons_val_one, Function.updateFinset_def]
  norm_num

/-- The unadjusted source effect in `pi1` (`InterveningVsConditioning.confoundedNet_intervene`):
`P(Y = true | do(X = true)) = 1/2 · 9/10 + 1/2 · 1/2 = 7/10`. -/
theorem pi1_source_effect : sourceEffect pi1 {1} {2} = 7 / 10 := by
  unfold sourceEffect
  rw [marginal_coe]
  simp only [Finset.mem_singleton, forall_eq] at *
  have hsum : (∑ x with x 2 = true,
      ((DomainPair.source pi1).mutilateSet {1} (fun _ => true)).joint x)
      = ∑ x, if x 2 = true then
      ((DomainPair.source pi1).mutilateSet {1} (fun _ => true)).joint x else 0 := by
    rw [Finset.sum_filter]
  rw [hsum]
  rw [expand8]
  simp only [BayesNet.joint_mutilateSet, Fin.prod_univ_three]
  simp [pi1, DomainPair.source, confoundedNet, BayesNet.paVal,
    coin_true, coin_false, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Non-vacuity**: `DomainPair.transport_formula` applies to `pi1`, with every hypothesis
discharged. -/
theorem pi1_transport_formula : targetEffect pi1 {1} {2} = transportRhs pi1 {1} {2} {0} :=
  pi1.transport_formula (X := {1}) (Y := {2}) (Z := {0}) (fun _ => true) (by decide)
    (by decide) (by decide) selZ_sAdmissible selZ_preTreatment pi1_overlap

/-- Reweighting is needed and correct in `pi1`: the target effect is the formula's value and
differs from the source effect. -/
theorem pi1_reweighting :
    targetEffect pi1 {1} {2} = transportRhs pi1 {1} {2} {0} ∧
      targetEffect pi1 {1} {2} ≠ sourceEffect pi1 {1} {2} :=
  ⟨pi1_transport_formula, by rw [pi1_target, pi1_source_effect]; norm_num⟩

end Cslib.MachineLearning.TransportabilityTests
