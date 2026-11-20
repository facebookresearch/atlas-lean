/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib
import Code.Sharpness.HighTempSimon
import Code.Sharpness.FieldGhostDict

open Finset SimpleGraph
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

namespace StatMech
namespace Sharpness

open Ising
open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def vertexGhostCoupling (J : Sym2 V → ℝ) (H : V → ℝ)
    (e : Sym2 (Option V)) : ℝ :=
  Sym2.lift ⟨fun a b ↦
    match a, b with
    | some x, some y => J s(x, y)
    | some x, none => H x
    | none, some y => H y
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩ e

@[simp] theorem vertexGhostCoupling_some_some
    (J : Sym2 V → ℝ) (H : V → ℝ) (x y : V) :
    vertexGhostCoupling J H s(some x, some y) = J s(x, y) := rfl

@[simp] theorem vertexGhostCoupling_some_none
    (J : Sym2 V → ℝ) (H : V → ℝ) (x : V) :
    vertexGhostCoupling J H s(some x, none) = H x := rfl


noncomputable def vertexFieldWeight (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (β * ((∑ e ∈ G.edgeFinset, J e * bond s e) +
    ∑ x : V, H x * spin s x))


noncomputable def vertexFieldZ (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, vertexFieldWeight G β J H s


noncomputable def vertexFieldExpectation (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (f : ConfigSpace V → ℝ) : ℝ :=
  (∑ s : ConfigSpace V, f s * vertexFieldWeight G β J H s) /
    vertexFieldZ G β J H



noncomputable def vertexFieldTwoPoint (β : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (a b : V) : ℝ :=
  vertexFieldExpectation G β J H (spinProd (sourcePair a b))



theorem vertexGhost_bondSum (J : Sym2 V → ℝ) (H : V → ℝ)
    (s : ConfigSpace (Option V)) :
    (∑ e ∈ (withGhost G).edgeFinset,
        vertexGhostCoupling J H e * bond s e) =
      (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e)) +
        spin s none * ∑ x : V, H x * spin s (some x) := by
  rw [withGhost_edgeFinset_eq, Finset.sum_union (disjoint_orig_ghost G)]
  congr 1
  · rw [origEdges, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun e _ ↦ ?_)
      induction e with
      | h x y => rw [Sym2.map_mk, vertexGhostCoupling_some_some]
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective V) hab
  · rw [ghostEdges, Finset.sum_image]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      rw [vertexGhostCoupling_some_none, bond_mk]
      ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact Option.some_injective V h1
      · exact absurd h2 (by simp)



theorem vertexGhost_weight_eq (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ)
    (s : ConfigSpace (Option V)) :
    boltzmannJ (withGhost G) beta (vertexGhostCoupling J H) s =
      vertexFieldWeight G beta J (fun x ↦ spin s none * H x)
        (fun x ↦ s (some x)) := by
  unfold boltzmannJ vertexFieldWeight
  rw [vertexGhost_bondSum]
  congr 1
  have hb : (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e)) =
      ∑ e ∈ G.edgeFinset, J e * bond (fun x ↦ s (some x)) e :=
    Finset.sum_congr rfl (fun e _ ↦ by rw [bond_map_some])
  rw [hb]
  have hf : spin s none * ∑ x : V, H x * spin s (some x) =
      ∑ x : V, (spin s none * H x) * spin s (some x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ ↦ by ring)
  rw [hf]
  rfl



theorem vertexFieldWeight_flip (beta : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (s : ConfigSpace V) :
    vertexFieldWeight G beta J (fun x ↦ -H x) (flipV s) =
      vertexFieldWeight G beta J H s := by
  unfold vertexFieldWeight
  congr 1
  have hb : (∑ e ∈ G.edgeFinset, J e * bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, J e * bond s e :=
    Finset.sum_congr rfl (fun e _ ↦ by rw [bond_flipV])
  have hh : (∑ x : V, -H x * spin (flipV s) x) =
      ∑ x : V, H x * spin s x :=
    Finset.sum_congr rfl (fun x _ ↦ by rw [spin_flipV]; ring)
  rw [hb, hh]


theorem vertexFieldZ_neg (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ) :
    vertexFieldZ G beta J (fun x ↦ -H x) = vertexFieldZ G beta J H := by
  unfold vertexFieldZ
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  exact Finset.sum_congr rfl (fun s _ ↦ vertexFieldWeight_flip G beta J H s)


theorem vertexFieldNum_neg_even (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ)
    (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace V,
        spinProd A s * vertexFieldWeight G beta J (fun x ↦ -H x) s) =
      ∑ s : ConfigSpace V, spinProd A s * vertexFieldWeight G beta J H s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  rw [spinProd_flipV_even A hA, vertexFieldWeight_flip]



theorem vertexGhost_partition_eq (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ) :
    partitionJ (withGhost G) beta (vertexGhostCoupling J H) =
      2 * vertexFieldZ G beta J H := by
  unfold partitionJ
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
        boltzmannJ (withGhost G) beta (vertexGhostCoupling J H)
          (fun a ↦ Option.rec b t a)) =
        vertexFieldZ G beta J (fun x ↦ spinB b * H x) := by
    intro b
    unfold vertexFieldZ
    exact Finset.sum_congr rfl (fun t _ ↦ by
      rw [vertexGhost_weight_eq, split_ghost_spin])
  rw [Fintype.sum_bool, hb, hb]
  simp only [show spinB true = (1 : ℝ) from rfl,
    show spinB false = (-1 : ℝ) from rfl, one_mul, neg_one_mul]
  rw [vertexFieldZ_neg]
  ring



theorem vertexGhost_expectation_eq (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ)
    (A : Finset V) (hA : Even A.card) :
    expectationJ (withGhost G) beta (vertexGhostCoupling J H) (A.map someEmb) =
      vertexFieldExpectation G beta J H (spinProd A) := by
  unfold expectationJ vertexFieldExpectation
  rw [vertexGhost_partition_eq]
  have hnum :
      (∑ s : ConfigSpace (Option V), spinProd (A.map someEmb) s *
        boltzmannJ (withGhost G) beta (vertexGhostCoupling J H) s) =
      2 * ∑ t : ConfigSpace V,
        spinProd A t * vertexFieldWeight G beta J H t := by
    rw [sum_option_config]
    have hb : ∀ b : Bool,
        (∑ t : ConfigSpace V,
          spinProd (A.map someEmb) (fun a ↦ Option.rec b t a) *
            boltzmannJ (withGhost G) beta (vertexGhostCoupling J H)
              (fun a ↦ Option.rec b t a)) =
        ∑ t : ConfigSpace V,
          spinProd A t * vertexFieldWeight G beta J
            (fun x ↦ spinB b * H x) t := by
      intro b
      refine Finset.sum_congr rfl (fun t _ ↦ ?_)
      rw [spinProd_map_some, vertexGhost_weight_eq, split_ghost_spin]
    rw [Fintype.sum_bool, hb, hb]
    simp only [show spinB true = (1 : ℝ) from rfl,
      show spinB false = (-1 : ℝ) from rfl, one_mul, neg_one_mul]
    rw [vertexFieldNum_neg_even G beta J H A hA]
    ring
  rw [hnum]
  exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)


theorem vertexGhost_twoPoint_eq (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ)
    (a b : V) :
    twoPointJ (withGhost G) beta (vertexGhostCoupling J H) (some a) (some b) =
      vertexFieldTwoPoint G beta J H a b := by
  unfold twoPointJ vertexFieldTwoPoint
  rw [show sourcePair (some a) (some b) =
      (sourcePair a b).map someEmb by
    unfold sourcePair
    rw [FieldGhostDict.map_symmDiff']
    simp]
  apply vertexGhost_expectation_eq
  by_cases hab : a = b
  · subst b
    simp [sourcePair]
  · rw [sourcePair_eq_pair hab]
    simp [hab]


theorem vertexFieldTwoPoint_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (H : V → ℝ) (hbeta : 0 ≤ beta)
    (hJ : ∀ e, 0 ≤ J e) (hH : ∀ x, 0 ≤ H x) (a b : V) :
    0 ≤ vertexFieldTwoPoint G beta J H a b := by
  rw [← vertexGhost_twoPoint_eq G beta J H a b]
  apply twoPointJ_nonneg (withGhost G) beta (vertexGhostCoupling J H) hbeta
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
      cases x <;> cases y <;> simp [vertexGhostCoupling, hJ, hH]



theorem couplingIn_vertexGhost_map_some (J : Sym2 V → ℝ) (H : V → ℝ)
    (S : Finset V) :
    couplingIn (vertexGhostCoupling J H) (S.map someEmb) =
      vertexGhostCoupling (couplingIn J S) (fun _ ↦ 0) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      cases a <;> cases b <;>
        simp [couplingIn, edgeInside, vertexGhostCoupling, someEmb]



theorem vertexFieldTwoPoint_zero (beta : ℝ) (J : Sym2 V → ℝ) (a b : V) :
    vertexFieldTwoPoint G beta J (fun _ ↦ 0) a b =
      twoPointJ G beta J a b := by
  unfold vertexFieldTwoPoint vertexFieldExpectation vertexFieldZ
    vertexFieldWeight twoPointJ expectationJ partitionJ boltzmannJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]



theorem twoPointJ_couplingIn_vertexGhost_map_some
    (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ)
    (S : Finset V) (a b : V) :
    twoPointJ (withGhost G) beta
        (couplingIn (vertexGhostCoupling J H) (S.map someEmb))
        (some a) (some b) =
      twoPointJ G beta (couplingIn J S) a b := by
  rw [couplingIn_vertexGhost_map_some (J := J) (H := H) (S := S),
    vertexGhost_twoPoint_eq, vertexFieldTwoPoint_zero]





theorem vertexFieldTwoPoint_simon_finite
    (beta : ℝ) (J : Sym2 V → ℝ) (H : V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (hH : ∀ x, 0 ≤ H x)
    (S : Finset V) (hHS : ∀ x ∈ S, H x = 0)
    (o z : V) (ho : o ∈ S) (hz : z ∉ S) :
    vertexFieldTwoPoint G beta J H o z ≤
      ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S),
        Real.tanh (beta * J s(x, y)) *
          twoPointJ G beta (couplingIn J S) o x *
          vertexFieldTwoPoint G beta J H y z := by
  classical
  have hghost : ∀ e : Sym2 (Option V),
      0 ≤ vertexGhostCoupling J H e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b =>
        cases a <;> cases b <;>
          simp [vertexGhostCoupling, hJ, hH]
  have hsim := twoPointJ_simon_finite (withGhost G) beta
    (vertexGhostCoupling J H) hbeta hghost (S.map someEmb)
    (some o) (some z) (by simp [ho]) (by simp [hz])
  rw [couplingIn_vertexGhost_map_some (J := J) (H := H) (S := S)] at hsim
  rw [vertexGhost_twoPoint_eq G beta J H o z] at hsim
  let f : V → V → ℝ := fun x y ↦
    Real.tanh (beta * J s(x, y)) *
      twoPointJ G beta (couplingIn J S) o x *
      vertexFieldTwoPoint G beta J H y z
  let q : V → ℝ := fun x ↦
    Real.tanh (beta * H x) *
      twoPointJ G beta (couplingIn J S) o x *
      twoPointJ (withGhost G) beta (vertexGhostCoupling J H) none (some z)
  have hsim' : vertexFieldTwoPoint G beta J H o z ≤
      (∑ x ∈ S, (q x + ∑ y : V, f x y)) -
        ∑ x ∈ S, ∑ y ∈ S, f x y := by
    simpa [f, q, vertexGhostCoupling, vertexGhost_twoPoint_eq G,
      vertexFieldTwoPoint_zero G] using hsim
  have hq : (∑ x ∈ S, (q x + ∑ y : V, f x y)) =
      ∑ x ∈ S, ∑ y : V, f x y := by
    apply Finset.sum_congr rfl
    intro x hx
    have hzero : q x = 0 := by
      simp [q, hHS x hx]
    rw [hzero, zero_add]
  calc
    vertexFieldTwoPoint G beta J H o z ≤
        (∑ x ∈ S, (q x + ∑ y : V, f x y)) -
          ∑ x ∈ S, ∑ y ∈ S, f x y := hsim'
    _ = (∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), f x y) := by
      rw [hq]
      symm
      calc
        (∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), f x y) =
            ∑ x ∈ S, ((∑ y : V, f x y) - ∑ y ∈ S, f x y) := by
          apply Finset.sum_congr rfl
          intro x _
          change (∑ y ∈ (Finset.univ \ S), f x y) =
            (∑ y ∈ (Finset.univ : Finset V), f x y) - ∑ y ∈ S, f x y
          have hs := Finset.sum_sdiff (f := fun y ↦ f x y)
            (Finset.subset_univ S)
          linarith
        _ = (∑ x ∈ S, ∑ y : V, f x y) -
            ∑ x ∈ S, ∑ y ∈ S, f x y := by
          rw [Finset.sum_sub_distrib]
    _ = _ := rfl

end Sharpness
end StatMech
