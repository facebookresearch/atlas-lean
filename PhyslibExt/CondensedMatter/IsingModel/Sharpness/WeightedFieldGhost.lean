/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaDerivCurrent

/-!
# The β-derivative of the magnetization with general couplings

Gibbs measures with couplings `J` and uniform field `h`, their ghost random-current representation,
and the formula `∂_β ⟨σ_o⟩ = Z⁻² (∑_e J_e Δ_e + h ∑_z Δ_z)` with nonnegative terms.

## i. Overview

This generalizes the field-ghost representation and the derivative formula of `HcovAssembly` from
uniform coupling to arbitrary couplings `J`. The energy is `∑_e J_e σ_e + h ∑_x σ_x`;
differentiating in `β` gives bond and field covariances, and each covariance is a ghost-graph
disconnection sum.

## ii. Key results

- `weightedExpectation` : Gibbs expectations with couplings `J` and field `h`
- `weightedExpectation_eq_currentRatio_even` : the random-current representation
- `hasDerivAt_weightedMagnetization` : `∂_β ⟨σ_o⟩` as covariances
- `weighted_deriv_magnetization_eq_currentDelta` : the random-current form of `∂_β ⟨σ_o⟩`
- `weighted_currentDelta_derivative_nonneg` : nonnegativity

## iii. Table of contents

- A. Gibbs measures with couplings and field
- B. The ghost representation
- C. The β-derivative
- D. The random-current form

## iv. References

- M. Aizenman, D. J. Barsky, R. Fernández, "The phase transition in a general class of Ising-type
  models is sharp", J. Stat. Phys. 47 (1987) 343–374
- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48

-/

@[expose] public section

open Finset BigOperators SimpleGraph
open scoped symmDiff


namespace StatMech
namespace Sharpness
namespace WeightedFieldGhost

open StatMech.Ising
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Gibbs measures with couplings and field -/

/-- The energy `∑_e J_e σ_e + h ∑_x σ_x`. -/
noncomputable def weightedEnergy (J : Sym2 V -> ℝ) (h : ℝ) (s : ConfigSpace V) : ℝ :=
  (∑ e ∈ G.edgeFinset, J e * bond s e) + h * ∑ x, spin s x

/-- The Boltzmann weight `exp(β (∑_e J_e σ_e + h ∑_x σ_x))`. -/
noncomputable def weightedWeight (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ)
    (s : ConfigSpace V) : ℝ :=
  Real.exp (β * weightedEnergy G J h s)

/-- The partition function with couplings `J` and field `h`. -/
noncomputable def weightedZ (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ) : ℝ :=
  ∑ s : ConfigSpace V, weightedWeight G β J h s

/-- The Gibbs expectation with couplings `J` and field `h`. -/
noncomputable def weightedExpectation (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ)
    (f : ConfigSpace V -> ℝ) : ℝ :=
  (∑ s : ConfigSpace V, f s * weightedWeight G β J h s) / weightedZ G β J h

lemma weightedZ_pos (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ) :
    0 < weightedZ G β J h := by
  unfold weightedZ weightedWeight
  positivity

lemma weightedZ_ne_zero (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ) :
    weightedZ G β J h ≠ 0 := (weightedZ_pos G β J h).ne'

/-! ## B. The ghost representation -/

lemma ghost_weight_eq_weighted (β h : ℝ) (J : Sym2 V -> ℝ)
    (s : ConfigSpace (Option V)) :
    boltzmannJ (withGhost G) β (ghostCoupling h β J) s =
      weightedWeight G β J (h * spin s none) (fun z => s (some z)) := by
  unfold boltzmannJ weightedWeight weightedEnergy
  rw [ghost_bondSum]
  congr 1
  have hb :
      (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e)) =
        ∑ e ∈ G.edgeFinset, J e * bond (fun z => s (some z)) e :=
    Finset.sum_congr rfl (fun e _ => by rw [bond_map_some])
  have hs : (∑ x : V, spin s (some x)) =
      ∑ x : V, spin (fun z => s (some z)) x := rfl
  rw [hb, hs]

omit [DecidableEq V] in
lemma weightedEnergy_flip (J : Sym2 V -> ℝ) (h : ℝ) (s : ConfigSpace V) :
    weightedEnergy G J (-h) (flipV s) = weightedEnergy G J h s := by
  unfold weightedEnergy
  have hb : (∑ e ∈ G.edgeFinset, J e * bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, J e * bond s e :=
    Finset.sum_congr rfl (fun e _ => by rw [bond_flipV])
  have hs : (∑ x, spin (flipV s) x) = -∑ x, spin s x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => spin_flipV s x)
  rw [hb, hs]
  ring

omit [DecidableEq V] in
lemma weightedWeight_flip (β h : ℝ) (J : Sym2 V -> ℝ) (s : ConfigSpace V) :
    weightedWeight G β J (-h) (flipV s) = weightedWeight G β J h s := by
  unfold weightedWeight
  rw [weightedEnergy_flip]

lemma weightedZ_neg (β h : ℝ) (J : Sym2 V -> ℝ) :
    weightedZ G β J (-h) = weightedZ G β J h := by
  unfold weightedZ
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  exact Finset.sum_congr rfl (fun s _ => weightedWeight_flip G β h J s)

lemma weightedNum_neg_even (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J (-h) s) =
      ∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_even A hA, weightedWeight_flip]

lemma weightedNum_neg_odd (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J (-h) s) =
      -∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_odd A hA, weightedWeight_flip]
  ring

lemma partition_ghost_eq_weightedZ (β h : ℝ) (J : Sym2 V -> ℝ) :
    partitionJ (withGhost G) β (ghostCoupling h β J) = 2 * weightedZ G β J h := by
  unfold partitionJ
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
          boltzmannJ (withGhost G) β (ghostCoupling h β J)
            (fun a => Option.rec b t a)) =
        weightedZ G β J (h * spinB b) := by
    intro b
    unfold weightedZ
    exact Finset.sum_congr rfl (fun t _ => by
      rw [ghost_weight_eq_weighted, split_ghost_spin])
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : spinB false = -1 := rfl
  have htrue : spinB true = 1 := rfl
  rw [hfalse, htrue, mul_neg_one, mul_one]
  rw [weightedZ_neg]
  ring

lemma num_ghost_eq_weighted_even (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (A.map someEmb) s *
        boltzmannJ (withGhost G) β (ghostCoupling h β J) s) =
      2 * ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J h t := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
          spinProd (A.map someEmb) (fun a => Option.rec b t a) *
            boltzmannJ (withGhost G) β (ghostCoupling h β J)
              (fun a => Option.rec b t a)) =
        ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J (h * spinB b) t := by
    intro b
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [spinProd_map_some, ghost_weight_eq_weighted, split_ghost_spin]
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : spinB false = -1 := rfl
  have htrue : spinB true = 1 := rfl
  rw [hfalse, htrue, mul_neg_one, mul_one]
  rw [weightedNum_neg_even G β h J A hA]
  ring

lemma num_ghost_eq_weighted_odd (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (insert none (A.map someEmb)) s *
        boltzmannJ (withGhost G) β (ghostCoupling h β J) s) =
      2 * ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J h t := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
          spinProd (insert none (A.map someEmb)) (fun a => Option.rec b t a) *
            boltzmannJ (withGhost G) β (ghostCoupling h β J)
              (fun a => Option.rec b t a)) =
        ∑ t : ConfigSpace V, (spinB b * spinProd A t) *
          weightedWeight G β J (h * spinB b) t := by
    intro b
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [spinProd_insert_none_map_some, ghost_weight_eq_weighted, split_ghost_spin]
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : spinB false = -1 := rfl
  have htrue : spinB true = 1 := rfl
  simp only [hfalse, htrue, one_mul, neg_one_mul, mul_one, mul_neg_one]
  rw [show (∑ t : ConfigSpace V, -spinProd A t * weightedWeight G β J (-h) t) =
      -∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J (-h) t by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun t _ => by ring)]
  rw [weightedNum_neg_odd G β h J A hA]
  ring

lemma weightedExpectation_eq_currentRatio_even (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Even A.card) :
    weightedExpectation G β J h (spinProd A) =
      currentSum (withGhost G) β (ghostCoupling h β J) (A.map someEmb) /
        currentSum (withGhost G) β (ghostCoupling h β J) ∅ := by
  rw [← current_representation]
  unfold expectationJ weightedExpectation
  rw [partition_ghost_eq_weightedZ, num_ghost_eq_weighted_even G β h J A hA]
  field_simp [weightedZ_ne_zero G β J h]

lemma weightedExpectation_eq_currentRatio_odd (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Odd A.card) :
    weightedExpectation G β J h (spinProd A) =
      currentSum (withGhost G) β (ghostCoupling h β J)
          (insert none (A.map someEmb)) /
        currentSum (withGhost G) β (ghostCoupling h β J) ∅ := by
  rw [← current_representation]
  unfold expectationJ weightedExpectation
  rw [partition_ghost_eq_weightedZ, num_ghost_eq_weighted_odd G β h J A hA]
  field_simp [weightedZ_ne_zero G β J h]

/-! ## C. The β-derivative -/

omit [DecidableEq V] in
lemma hasDerivAt_weightedWeight (β h : ℝ) (J : Sym2 V -> ℝ)
    (s : ConfigSpace V) :
    HasDerivAt (fun β => weightedWeight G β J h s)
      (weightedWeight G β J h s * weightedEnergy G J h s) β := by
  unfold weightedWeight
  refine ((Real.hasDerivAt_exp (β * weightedEnergy G J h s)).comp β
      ((hasDerivAt_id β).mul_const (weightedEnergy G J h s))).congr_deriv ?_
  ring

lemma hasDerivAt_weightedNum (β h : ℝ) (J : Sym2 V -> ℝ)
    (f : ConfigSpace V -> ℝ) :
    HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * weightedWeight G β J h s)
      (∑ s : ConfigSpace V,
        f s * (weightedWeight G β J h s * weightedEnergy G J h s)) β := by
  have hrw : (fun β => ∑ s : ConfigSpace V, f s * weightedWeight G β J h s) =
      ∑ s : ConfigSpace V, (fun β => f s * weightedWeight G β J h s) := by
    rw [Finset.sum_fn]
  rw [hrw]
  exact HasDerivAt.sum
    (fun s _ => (hasDerivAt_weightedWeight G β h J s).const_mul (f s))

lemma hasDerivAt_weightedZ (β h : ℝ) (J : Sym2 V -> ℝ) :
    HasDerivAt (fun β => weightedZ G β J h)
      (∑ s : ConfigSpace V, weightedWeight G β J h s * weightedEnergy G J h s) β := by
  simpa [weightedZ] using hasDerivAt_weightedNum G β h J (fun _ => 1)

lemma hasDerivAt_weightedExpectation (β h : ℝ) (J : Sym2 V -> ℝ)
    (f : ConfigSpace V -> ℝ) :
    HasDerivAt (fun β => weightedExpectation G β J h f)
      (weightedExpectation G β J h (fun s => f s * weightedEnergy G J h s) -
        weightedExpectation G β J h f *
          weightedExpectation G β J h (weightedEnergy G J h)) β := by
  have hN := hasDerivAt_weightedNum G β h J f
  have hZ := hasDerivAt_weightedZ G β h J
  have hZne := weightedZ_ne_zero G β J h
  have hdiv := hN.div hZ hZne
  have e1 : weightedExpectation G β J h (fun s => f s * weightedEnergy G J h s) =
      (∑ s : ConfigSpace V, (f s * weightedEnergy G J h s) * weightedWeight G β J h s) /
        weightedZ G β J h := rfl
  have e2 : weightedExpectation G β J h f =
      (∑ s : ConfigSpace V, f s * weightedWeight G β J h s) / weightedZ G β J h := rfl
  have e3 : weightedExpectation G β J h (weightedEnergy G J h) =
      (∑ s : ConfigSpace V, weightedEnergy G J h s * weightedWeight G β J h s) /
        weightedZ G β J h := rfl
  rw [e1, e2, e3]
  refine hdiv.congr_deriv ?_
  field_simp [hZne]
  rw [show (∑ s : ConfigSpace V,
      f s * weightedEnergy G J h s * weightedWeight G β J h s) =
      ∑ s : ConfigSpace V,
        f s * weightedWeight G β J h s * weightedEnergy G J h s by
      exact Finset.sum_congr rfl (fun s _ => by ring),
    show (∑ s : ConfigSpace V,
      weightedEnergy G J h s * weightedWeight G β J h s) =
      ∑ s : ConfigSpace V,
        weightedWeight G β J h s * weightedEnergy G J h s by
      exact Finset.sum_congr rfl (fun s _ => by ring)]
  ring

lemma weightedExpectation_sum {ι : Type*} (β h : ℝ) (J : Sym2 V -> ℝ)
    (S : Finset ι) (f : ι -> ConfigSpace V -> ℝ) :
    weightedExpectation G β J h (fun s => ∑ i ∈ S, f i s) =
      ∑ i ∈ S, weightedExpectation G β J h (f i) := by
  unfold weightedExpectation
  rw [← Finset.sum_div]
  congr 1
  calc
    (∑ s : ConfigSpace V, (∑ i ∈ S, f i s) * weightedWeight G β J h s) =
        ∑ s : ConfigSpace V, ∑ i ∈ S, f i s * weightedWeight G β J h s := by
          exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_mul])
    _ = ∑ i ∈ S, ∑ s : ConfigSpace V, f i s * weightedWeight G β J h s :=
      Finset.sum_comm

lemma weightedExpectation_add (β h : ℝ) (J : Sym2 V -> ℝ)
    (f g : ConfigSpace V -> ℝ) :
    weightedExpectation G β J h (fun s => f s + g s) =
      weightedExpectation G β J h f + weightedExpectation G β J h g := by
  unfold weightedExpectation
  rw [← add_div, ← Finset.sum_add_distrib]
  exact congrArg (fun x => x / weightedZ G β J h)
    (Finset.sum_congr rfl (fun s _ => by ring))

lemma weightedExpectation_const_mul (β h c : ℝ) (J : Sym2 V -> ℝ)
    (f : ConfigSpace V -> ℝ) :
    weightedExpectation G β J h (fun s => c * f s) =
      c * weightedExpectation G β J h f := by
  unfold weightedExpectation
  rw [show (∑ s : ConfigSpace V, (fun s => c * f s) s * weightedWeight G β J h s) =
      c * ∑ s : ConfigSpace V, f s * weightedWeight G β J h s by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun s _ => by ring)]
  ring

lemma hasDerivAt_weightedMagnetization (β h : ℝ) (J : Sym2 V -> ℝ) (o : V) :
    HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o))
      ((∑ e ∈ G.edgeFinset, J e *
          (weightedExpectation G β J h (fun s => spin s o * bond s e) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => bond s e))) +
        h * ∑ z,
          (weightedExpectation G β J h (fun s => spin s o * spin s z) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => spin s z))) β := by
  have hd := hasDerivAt_weightedExpectation G β h J (fun s => spin s o)
  have hmul : weightedExpectation G β J h
      (fun s => spin s o * weightedEnergy G J h s) =
      (∑ e ∈ G.edgeFinset, J e *
        weightedExpectation G β J h (fun s => spin s o * bond s e)) +
        h * ∑ z, weightedExpectation G β J h (fun s => spin s o * spin s z) := by
    rw [show (fun s => spin s o * weightedEnergy G J h s) =
        (fun s => (∑ e ∈ G.edgeFinset, J e * (spin s o * bond s e)) +
          h * ∑ z, spin s o * spin s z) by
      funext s
      unfold weightedEnergy
      rw [mul_add]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by ring)
      · rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)]
    rw [weightedExpectation_add]
    rw [weightedExpectation_sum G β h J G.edgeFinset
      (fun e s => J e * (spin s o * bond s e))]
    rw [Finset.sum_congr rfl (fun e _ => weightedExpectation_const_mul G β h (J e) J _)]
    rw [weightedExpectation_const_mul]
    congr 1
    rw [weightedExpectation_sum G β h J Finset.univ
      (fun z s => spin s o * spin s z)]
  have henergy : weightedExpectation G β J h (weightedEnergy G J h) =
      (∑ e ∈ G.edgeFinset, J e * weightedExpectation G β J h (fun s => bond s e)) +
        h * ∑ z, weightedExpectation G β J h (fun s => spin s z) := by
    unfold weightedEnergy
    rw [weightedExpectation_add]
    rw [weightedExpectation_sum G β h J G.edgeFinset (fun e s => J e * bond s e)]
    rw [Finset.sum_congr rfl (fun e _ => weightedExpectation_const_mul G β h (J e) J _)]
    rw [weightedExpectation_const_mul]
    congr 1
    rw [weightedExpectation_sum G β h J Finset.univ (fun z s => spin s z)]
  let m := weightedExpectation G β J h (fun s => spin s o)
  have hb :
      (∑ e ∈ G.edgeFinset, J e *
        (weightedExpectation G β J h (fun s => spin s o * bond s e) -
          m * weightedExpectation G β J h (fun s => bond s e))) =
      (∑ e ∈ G.edgeFinset,
        J e * weightedExpectation G β J h (fun s => spin s o * bond s e)) -
        m * ∑ e ∈ G.edgeFinset,
          J e * weightedExpectation G β J h (fun s => bond s e) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have hf :
      h * ∑ z, (weightedExpectation G β J h (fun s => spin s o * spin s z) -
        m * weightedExpectation G β J h (fun s => spin s z)) =
      h * ∑ z, weightedExpectation G β J h (fun s => spin s o * spin s z) -
        m * (h * ∑ z, weightedExpectation G β J h (fun s => spin s z)) := by
    rw [Finset.sum_sub_distrib, mul_sub]
    simp only [Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro z _; ring
  have hvalue :
      (∑ e ∈ G.edgeFinset, J e *
          (weightedExpectation G β J h (fun s => spin s o * bond s e) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => bond s e))) +
        h * ∑ z,
          (weightedExpectation G β J h (fun s => spin s o * spin s z) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => spin s z)) =
      weightedExpectation G β J h (fun s => spin s o * weightedEnergy G J h s) -
        m * weightedExpectation G β J h (weightedEnergy G J h) := by
    rw [hb, hf, hmul, henergy]
    ring
  rw [hvalue]
  exact hd

open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum endsM)
open StatMech.Sharpness.RandomCurrent (connK)
open StatMech.Sharpness.HcovAssembly

/-! ## D. The random-current form -/

/-- The bond term: the ghost-graph disconnection sum for `Cov(σ_o, σ_e)` with couplings `J`. -/
noncomputable def weightedBondDelta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o : V) (e : Sym2 V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J)
    (hcaBondSource o e) ∅ (some o) none

/-- The field term: the ghost-graph disconnection sum for `Cov(σ_o, σ_z)` with couplings `J`. -/
noncomputable def weightedFieldDelta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o z : V) : ℝ :=
  sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J)
    (hcaFieldSource o z) ∅ (some o) none

omit [Fintype V] in
private lemma odd_source_card (o x y : V) (hxy : x ≠ y) :
    Odd ((({o} : Finset V) ∆ {x, y}).card) := by
  by_cases hox : o = x
  · subst x
    have heq : ({o} : Finset V) ∆ {o, y} = {y} := by
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      aesop
    rw [heq]
    simp
  · by_cases hoy : o = y
    · subst y
      have heq : ({o} : Finset V) ∆ {x, o} = {x} := by
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        aesop
      rw [heq]
      simp
    · have heq : ({o} : Finset V) ∆ {x, y} = {o, x, y} := by
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        aesop
      rw [heq, Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      decide

private lemma even_field_source_card (o z : V) :
    Even ((({o} : Finset V) ∆ {z}).card) := by
  by_cases hoz : o = z
  · subst z
    simp
  · have heq : ({o} : Finset V) ∆ {z} = {o, z} := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      aesop
    rw [heq, Finset.card_insert_of_notMem (by simp [hoz]), Finset.card_singleton]
    decide

lemma weightedBond_covariance_sourcePair (β h : ℝ) (J : Sym2 V -> ℝ)
    (o x y : V) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (spinProd (({o} : Finset V) ∆ {x, y})) -
          weightedExpectation G β J h (spinProd ({x, y} : Finset V)) *
            weightedExpectation G β J h (spinProd ({o} : Finset V))) =
      weightedBondDelta G β h J o s(x, y) := by
  let S : Finset V := ({o} : Finset V) ∆ {x, y}
  let A : Finset (Option V) := insert none (S.map someEmb)
  have hSodd : Odd S.card := odd_source_card o x y hxy
  have hpair : Even (({x, y} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    decide
  have hsingle : Odd (({o} : Finset V).card) := by simp
  have hrepS := weightedExpectation_eq_currentRatio_odd G β h J S hSodd
  have hrepPair := weightedExpectation_eq_currentRatio_even G β h J
    ({x, y} : Finset V) hpair
  have hrepO := weightedExpectation_eq_currentRatio_odd G β h J
    ({o} : Finset V) hsingle
  have hdiff : A ∆ {some o, none} = ({x, y} : Finset V).map someEmb := by
    ext z
    cases z with
    | none => simp [A, Finset.mem_symmDiff, someEmb]
    | some w =>
        simp only [A, S, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_map, someEmb_apply,
          Option.some.injEq, Option.some_ne_none, false_or, exists_eq_right]
        tauto
  have hpairSource : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext z
    simp [someEmb]
    aesop
  change weightedExpectation G β J h (spinProd S) =
    currentSum (withGhost G) β (ghostCoupling h β J) A /
      currentSum (withGhost G) β (ghostCoupling h β J) ∅ at hrepS
  rw [← hdiff] at hrepPair
  rw [← hpairSource] at hrepO
  have hZne : currentSum (withGhost G) β (ghostCoupling h β J) ∅ ≠ 0 :=
    ne_of_gt (Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J))
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β J) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅)
    (weightedExpectation G β J h (spinProd S))
    (weightedExpectation G β J h (spinProd ({x, y} : Finset V)))
    (weightedExpectation G β J h (spinProd ({o} : Finset V)))
    rfl hZne hrepS hrepPair hrepO
  simpa [weightedBondDelta, hcaBondSource, A, S] using hgcr

lemma weightedField_covariance_sourcePair (β h : ℝ) (J : Sym2 V -> ℝ)
    (o z : V) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (spinProd (({o} : Finset V) ∆ {z})) -
          weightedExpectation G β J h (spinProd ({z} : Finset V)) *
            weightedExpectation G β J h (spinProd ({o} : Finset V))) =
      weightedFieldDelta G β h J o z := by
  let S : Finset V := ({o} : Finset V) ∆ {z}
  let A : Finset (Option V) := S.map someEmb
  have hSeven : Even S.card := even_field_source_card o z
  have hzodd : Odd (({z} : Finset V).card) := by simp
  have hood : Odd (({o} : Finset V).card) := by simp
  have hrepS := weightedExpectation_eq_currentRatio_even G β h J S hSeven
  have hrepZ := weightedExpectation_eq_currentRatio_odd G β h J ({z} : Finset V) hzodd
  have hrepO := weightedExpectation_eq_currentRatio_odd G β h J ({o} : Finset V) hood
  have hdiff : A ∆ {some o, none} = insert none (({z} : Finset V).map someEmb) := by
    ext w
    cases w with
    | none => simp [A, Finset.mem_symmDiff, someEmb]
    | some v =>
        simp only [A, S, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_map, someEmb_apply,
          Option.some.injEq, Option.some_ne_none, false_or, exists_eq_right]
        tauto
  have hpairSource : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext w
    simp [someEmb]
    aesop
  change weightedExpectation G β J h (spinProd S) =
    currentSum (withGhost G) β (ghostCoupling h β J) A /
      currentSum (withGhost G) β (ghostCoupling h β J) ∅ at hrepS
  rw [← hdiff] at hrepZ
  rw [← hpairSource] at hrepO
  have hZne : currentSum (withGhost G) β (ghostCoupling h β J) ∅ ≠ 0 :=
    ne_of_gt (Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J))
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β J) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅)
    (weightedExpectation G β J h (spinProd S))
    (weightedExpectation G β J h (spinProd ({z} : Finset V)))
    (weightedExpectation G β J h (spinProd ({o} : Finset V)))
    rfl hZne hrepS hrepZ hrepO
  simpa [weightedFieldDelta, hcaFieldSource, A, S] using hgcr

omit [Fintype V] in
private lemma weighted_spin_mul_bond (o x y : V) (hxy : x ≠ y) :
    (fun s : ConfigSpace V => spin s o * bond s s(x, y)) =
      spinProd (({o} : Finset V) ∆ {x, y}) := by
  funext s
  rw [show spin s o = spinProd ({o} : Finset V) s by simp [spinProd],
    show bond s s(x, y) = spinProd ({x, y} : Finset V) s by
      rw [bond_mk, spinProd, Finset.prod_pair hxy], spinProd_mul_self]

omit [Fintype V] in
private lemma weighted_bond_pair (x y : V) (hxy : x ≠ y) :
    (fun s : ConfigSpace V => bond s s(x, y)) = spinProd ({x, y} : Finset V) := by
  funext s
  rw [bond_mk, spinProd, Finset.prod_pair hxy]

omit [Fintype V] in
private lemma weighted_spin_mul_spin (o z : V) :
    (fun s : ConfigSpace V => spin s o * spin s z) =
      spinProd (({o} : Finset V) ∆ {z}) := by
  funext s
  rw [show spin s o = spinProd ({o} : Finset V) s by simp [spinProd],
    show spin s z = spinProd ({z} : Finset V) s by simp [spinProd], spinProd_mul_self]

omit [Fintype V] [DecidableEq V] in
private lemma weighted_spin_single (z : V) :
    (fun s : ConfigSpace V => spin s z) = spinProd ({z} : Finset V) := by
  funext s
  simp [spinProd]

lemma weightedBond_covariance_eq_delta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o : V) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (fun s => spin s o * bond s e) -
          weightedExpectation G β J h (fun s => spin s o) *
            weightedExpectation G β J h (fun s => bond s e)) =
      weightedBondDelta G β h J o e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : G.Adj x y := by simpa using (SimpleGraph.mem_edgeFinset.mp he)
      have hxy := G.ne_of_adj hadj
      rw [weighted_spin_mul_bond o x y hxy, weighted_bond_pair x y hxy,
        weighted_spin_single o, mul_comm
          (weightedExpectation G β J h (spinProd ({o} : Finset V)))]
      exact weightedBond_covariance_sourcePair G β h J o x y hxy

lemma weightedField_covariance_eq_delta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o z : V) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (fun s => spin s o * spin s z) -
          weightedExpectation G β J h (fun s => spin s o) *
            weightedExpectation G β J h (fun s => spin s z)) =
      weightedFieldDelta G β h J o z := by
  rw [weighted_spin_mul_spin o z, weighted_spin_single o, weighted_spin_single z,
    mul_comm (weightedExpectation G β J h (spinProd ({o} : Finset V)))]
  exact weightedField_covariance_sourcePair G β h J o z

lemma weighted_deriv_magnetization_eq_currentDelta
    (β h : ℝ) (J : Sym2 V -> ℝ) (o : V) :
    HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o))
      ((1 / (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2) *
        ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
          h * ∑ z, weightedFieldDelta G β h J o z)) β := by
  let Z : ℝ := currentSum (withGhost G) β (ghostCoupling h β J) ∅
  let bondCov : Sym2 V -> ℝ := fun e =>
    weightedExpectation G β J h (fun s => spin s o * bond s e) -
      weightedExpectation G β J h (fun s => spin s o) *
        weightedExpectation G β J h (fun s => bond s e)
  let fieldCov : V -> ℝ := fun z =>
    weightedExpectation G β J h (fun s => spin s o * spin s z) -
      weightedExpectation G β J h (fun s => spin s o) *
        weightedExpectation G β J h (fun s => spin s z)
  have hZne : Z ≠ 0 := ne_of_gt
    (Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J))
  have hbond (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      Z ^ 2 * bondCov e = weightedBondDelta G β h J o e := by
    simpa [Z, bondCov] using weightedBond_covariance_eq_delta G β h J o e he
  have hfield (z : V) :
      Z ^ 2 * fieldCov z = weightedFieldDelta G β h J o z := by
    simpa [Z, fieldCov] using weightedField_covariance_eq_delta G β h J o z
  have hbondSum :
      Z ^ 2 * (∑ e ∈ G.edgeFinset, J e * bondCov e) =
        ∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e he => by rw [← hbond e he]; ring)
  have hfieldSum :
      Z ^ 2 * (∑ z, fieldCov z) = ∑ z, weightedFieldDelta G β h J o z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hfield z)
  have hscaled :
      Z ^ 2 * ((∑ e ∈ G.edgeFinset, J e * bondCov e) + h * ∑ z, fieldCov z) =
        (∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
          h * ∑ z, weightedFieldDelta G β h J o z := by
    calc
      Z ^ 2 * ((∑ e ∈ G.edgeFinset, J e * bondCov e) + h * ∑ z, fieldCov z) =
          Z ^ 2 * (∑ e ∈ G.edgeFinset, J e * bondCov e) +
            h * (Z ^ 2 * ∑ z, fieldCov z) := by ring
      _ = _ := by rw [hbondSum, hfieldSum]
  have hvalue :
      (∑ e ∈ G.edgeFinset, J e * bondCov e) + h * ∑ z, fieldCov z =
        (1 / Z ^ 2) *
          ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
            h * ∑ z, weightedFieldDelta G β h J o z) := by
    rw [← hscaled]
    field_simp
  have hd := hasDerivAt_weightedMagnetization G β h J o
  change HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o))
    ((1 / Z ^ 2) *
      ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
        h * ∑ z, weightedFieldDelta G β h J o z)) β
  rw [← hvalue]
  simpa [bondCov, fieldCov] using hd

omit [Fintype V] [DecidableEq V] in
private lemma ghostCoupling_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e) :
    ∀ e : Sym2 (Option V), 0 ≤ ghostCoupling h β J e := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      cases a <;> cases b <;> simp [ghostCoupling, hh, hJ]

lemma weightedBondDelta_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (e : Sym2 V) : 0 ≤ weightedBondDelta G β h J o e := by
  rw [weightedBondDelta, ← HcovAssembly.hca_pairSum_disconn_eq (withGhost G) β
    (ghostCoupling h β J) (hcaBondSource o e) (by simp)]
  exact HcovAssembly.hca_pairSum_nonneg (withGhost G) β (ghostCoupling h β J)
    hβ (ghostCoupling_nonneg β h J hh hJ) (hcaBondSource o e) (by simp)
    (fun m => ¬ connK (endsM (withGhost G) m) univ (some o) none) (fun _ hm => hm)

lemma weightedFieldDelta_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e)
    (o z : V) : 0 ≤ weightedFieldDelta G β h J o z := by
  rw [weightedFieldDelta, ← HcovAssembly.hca_pairSum_disconn_eq (withGhost G) β
    (ghostCoupling h β J) (hcaFieldSource o z) (by simp)]
  exact HcovAssembly.hca_pairSum_nonneg (withGhost G) β (ghostCoupling h β J)
    hβ (ghostCoupling_nonneg β h J hh hJ) (hcaFieldSource o z) (by simp)
    (fun m => ¬ connK (endsM (withGhost G) m) univ (some o) none) (fun _ hm => hm)

lemma weighted_currentDelta_derivative_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e) (o : V) :
    0 ≤ (1 / (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2) *
      ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
        h * ∑ z, weightedFieldDelta G β h J o z) := by
  have hZpos := Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J)
  refine mul_nonneg (by positivity) (add_nonneg ?_ (mul_nonneg hh ?_))
  · exact Finset.sum_nonneg (fun e _ =>
      mul_nonneg (hJ e) (weightedBondDelta_nonneg G β h J hβ hh hJ o e))
  · exact Finset.sum_nonneg (fun z _ =>
      weightedFieldDelta_nonneg G β h J hβ hh hJ o z)

end WeightedFieldGhost
end Sharpness
end StatMech
