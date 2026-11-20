/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Ising.GKS
import Code.Sharpness.CurrentRep
import Code.Sharpness.RandomCurrent
import Code.Sharpness.GhostCurrentRep

open Finset SimpleGraph
open scoped symmDiff
open StatMech StatMech.Ising StatMech.Sharpness

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness
namespace FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




instance decRelWithGhost : DecidableRel (withGhost G).Adj := by
  intro a b
  rcases a with _ | x <;> rcases b with _ | y <;> simp only [withGhost] <;> infer_instance




noncomputable def origEdges : Finset (Sym2 (Option V)) := G.edgeFinset.image (Sym2.map some)


noncomputable def ghostEdges (V : Type*) [Fintype V] [DecidableEq V] :
    Finset (Sym2 (Option V)) := (univ : Finset V).image (fun x => s(some x, none))


theorem withGhost_edgeFinset_eq : (withGhost G).edgeFinset = origEdges G ∪ ghostEdges V := by
  ext e
  rw [mem_edgeFinset, Finset.mem_union]
  induction e with
  | h a b =>
    simp only [origEdges, ghostEdges, Finset.mem_image, mem_edgeFinset, SimpleGraph.mem_edgeSet,
      mem_univ, true_and]
    rcases a with _ | x <;> rcases b with _ | y
    · constructor
      · intro h; exact absurd h (by trivial)
      · rintro (⟨e1, _, he⟩ | ⟨x, hx⟩)
        · induction e1 with | h c d => rw [Sym2.map_mk, Sym2.eq_iff] at he; simp_all
        · rw [Sym2.eq_iff] at hx; simp_all
    · constructor
      · intro _; right; exact ⟨y, by rw [Sym2.eq_swap]⟩
      · intro _; show (withGhost G).Adj none (some y); simp only [withGhost]
    · constructor
      · intro _; right; exact ⟨x, rfl⟩
      · intro _; show (withGhost G).Adj (some x) none; simp only [withGhost]
    · rw [withGhost_adj_some_some]
      constructor
      · intro h; left; exact ⟨s(x, y), h, by rw [Sym2.map_mk]⟩
      · rintro (⟨e1, he1, he⟩ | ⟨z, hz⟩)
        · induction e1 with
          | h c d => rw [Sym2.map_mk, Sym2.eq_iff] at he
                     rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
                     · rw [Option.some_inj.mp h1, Option.some_inj.mp h2] at he1; exact he1
                     · rw [Option.some_inj.mp h1, Option.some_inj.mp h2] at he1; exact he1.symm
        · rw [Sym2.eq_iff] at hz; simp_all


theorem disjoint_orig_ghost : Disjoint (origEdges G) (ghostEdges V) := by
  rw [Finset.disjoint_left]
  intro e he hg
  simp only [origEdges, ghostEdges, Finset.mem_image, mem_edgeFinset, mem_univ, true_and] at he hg
  obtain ⟨e1, he1, rfl⟩ := he
  obtain ⟨x, hx⟩ := hg
  induction e1 with
  | h a b => rw [Sym2.map_mk, Sym2.eq_iff] at hx; rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all







noncomputable def ghostCoupling (h β : ℝ) (J : Sym2 V → ℝ) (e : Sym2 (Option V)) : ℝ :=
  Sym2.lift ⟨fun a b =>
    match a, b with
    | some x, some y => J s(x, y)
    | some _, none => h
    | none, some _ => h
    | none, none => 0,
    by rintro (_ | x) (_ | y) <;> simp only [] <;> rw [Sym2.eq_swap]⟩ e

@[simp] theorem ghostCoupling_some_some (h β : ℝ) (J : Sym2 V → ℝ) (x y : V) :
    ghostCoupling h β J s(some x, some y) = J s(x, y) := rfl

@[simp] theorem ghostCoupling_some_none (h β : ℝ) (J : Sym2 V → ℝ) (x : V) :
    ghostCoupling h β J s(some x, none) = h := rfl




theorem bond_map_some (s : ConfigSpace (Option V)) (e : Sym2 V) :
    bond s (Sym2.map some e) = bond (fun x => s (some x)) e := by
  induction e with | h x y => rw [Sym2.map_mk, bond_mk, bond_mk]; rfl






theorem ghost_bondSum (h β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace (Option V)) :
    (∑ e ∈ (withGhost G).edgeFinset, ghostCoupling h β J e * bond s e)
      = (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e))
        + h * spin s none * ∑ x : V, spin s (some x) := by
  rw [withGhost_edgeFinset_eq, Finset.sum_union (disjoint_orig_ghost G)]
  congr 1
  · rw [origEdges, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      induction e with
      | h x y => rw [Sym2.map_mk]; simp only [ghostCoupling_some_some]
    · intro a _ b _ hab; exact Sym2.map.injective (Option.some_injective V) hab
  · rw [ghostEdges, Finset.sum_image]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [ghostCoupling_some_none, bond_mk]; ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab; rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact Option.some_injective V h1
      · exact absurd h2 (by simp)








theorem fgd_ghost_weight_eq (β h : ℝ) (s : ConfigSpace (Option V)) :
    boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s
      = isingWeight G β (h * spin s none) (fun z => s (some z)) := by
  unfold boltzmannJ isingWeight hamiltonian
  rw [ghost_bondSum]
  congr 1
  have hbond : (∑ e ∈ G.edgeFinset, (1 : ℝ) * bond s (Sym2.map some e))
      = ∑ e ∈ G.edgeFinset, bond (fun z => s (some z)) e :=
    Finset.sum_congr rfl (fun e _ => by rw [one_mul, bond_map_some])
  have hspin : (∑ x : V, spin s (some x)) = ∑ x : V, spin (fun z => s (some z)) x := rfl
  rw [hbond, hspin]; ring




def flipV (s : ConfigSpace V) : ConfigSpace V := fun v => ! s v

@[simp] theorem flipV_apply (s : ConfigSpace V) (v : V) : flipV s v = ! s v := rfl


theorem spin_flipV (s : ConfigSpace V) (v : V) : spin (flipV s) v = - spin s v := by
  simp only [flipV, spin]; by_cases h : s v <;> simp [h]


theorem bond_flipV (s : ConfigSpace V) (e : Sym2 V) : bond (flipV s) e = bond s e := by
  induction e with | h x y => rw [bond_mk, bond_mk, spin_flipV, spin_flipV]; ring


theorem flipV_involutive : Function.Involutive (flipV (V := V)) := by
  intro s; ext v; simp [flipV]




theorem isingWeight_flip (β h : ℝ) (s : ConfigSpace V) :
    isingWeight G β (-h) (flipV s) = isingWeight G β h s := by
  unfold isingWeight hamiltonian
  congr 1
  have hb : (∑ e ∈ G.edgeFinset, bond (flipV s) e) = ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ => bond_flipV s e)
  have hs : (∑ x, spin (flipV s) x) = - ∑ x, spin s x := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun x _ => spin_flipV s x)
  rw [hb, hs]; ring


theorem fgd_isingZ_neg (β h : ℝ) : isingZ G β (-h) = isingZ G β h := by
  unfold isingZ
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  exact Finset.sum_congr rfl (fun s _ => isingWeight_flip G β h s)


theorem spinProd_flipV (A : Finset V) (s : ConfigSpace V) :
    spinProd A (flipV s) = (-1) ^ A.card * spinProd A s := by
  unfold spinProd
  rw [Finset.prod_congr rfl (fun x _ => spin_flipV s x)]
  rw [Finset.prod_congr rfl (fun x _ => (neg_one_mul (spin s x)).symm)]
  rw [Finset.prod_mul_distrib, Finset.prod_const]


theorem spinProd_flipV_even (A : Finset V) (hA : Even A.card) (s : ConfigSpace V) :
    spinProd A (flipV s) = spinProd A s := by
  rw [spinProd_flipV, hA.neg_one_pow, one_mul]


theorem spinProd_flipV_odd (A : Finset V) (hA : Odd A.card) (s : ConfigSpace V) :
    spinProd A (flipV s) = -spinProd A s := by
  rw [spinProd_flipV, hA.neg_one_pow, neg_one_mul]



theorem fgd_num_neg_even (β h : ℝ) (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s)
      = ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_even A hA, isingWeight_flip]




theorem fgd_num_neg_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G β (-h) s)
      = -∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_odd A hA, isingWeight_flip]
  ring




def someEmb : V ↪ Option V := ⟨some, Option.some_injective V⟩

@[simp] theorem someEmb_apply (x : V) : someEmb x = some x := rfl



theorem sum_option_config (f : (Option V → Bool) → ℝ) :
    (∑ s : Option V → Bool, f s)
      = ∑ b : Bool, ∑ τ : V → Bool, f (fun a => Option.rec b τ a) := by
  rw [← Equiv.sum_comp Equiv.piOptionEquivProd.symm f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun τ _ => ?_))
  congr 1


theorem split_some (b : Bool) (τ : V → Bool) (x : V) :
    (fun z => (fun a => Option.rec b τ a : Option V → Bool) (some z)) x = τ x := rfl


theorem split_ghost_spin (b : Bool) (τ : V → Bool) :
    spin (fun a => Option.rec b τ a : Option V → Bool) none = StatMech.Ising.spinB b := rfl


theorem spinProd_map_some (A : Finset V) (b : Bool) (τ : V → Bool) :
    spinProd (A.map someEmb) (fun a => Option.rec b τ a : Option V → Bool) = spinProd A τ := by
  unfold spinProd
  rw [Finset.prod_map]
  rfl



theorem spinProd_insert_none_map_some (A : Finset V) (b : Bool) (τ : V → Bool) :
    spinProd (insert none (A.map someEmb))
        (fun a => Option.rec b τ a : Option V → Bool)
      = StatMech.Ising.spinB b * spinProd A τ := by
  unfold spinProd
  rw [Finset.prod_insert (by simp [someEmb]), Finset.prod_map]
  rfl







theorem fgd_partitionJ_ghost_eq (β h : ℝ) :
    partitionJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) = 2 * isingZ G β h := by
  unfold partitionJ
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ τ : V → Bool, boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (fun a => Option.rec b τ a))
        = ∑ τ : V → Bool, isingWeight G β (h * StatMech.Ising.spinB b) τ := by
    intro b
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [fgd_ghost_weight_eq, split_ghost_spin]
  rw [Fintype.sum_bool, hb, hb]
  show (∑ τ : V → Bool, isingWeight G β (h * StatMech.Ising.spinB true) τ)
      + (∑ τ : V → Bool, isingWeight G β (h * StatMech.Ising.spinB false) τ) = _
  have hfalse : StatMech.Ising.spinB false = -1 := rfl
  have htrue : StatMech.Ising.spinB true = 1 := rfl
  rw [hfalse, htrue, mul_neg_one, mul_one]
  show isingZ G β h + isingZ G β (-h) = 2 * isingZ G β h
  rw [fgd_isingZ_neg]; ring








theorem fgd_num_ghost_eq (β h : ℝ) (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (A.map someEmb) s
        * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s)
      = 2 * ∑ τ : ConfigSpace V, spinProd A τ * isingWeight G β h τ := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ τ : V → Bool, spinProd (A.map someEmb) (fun a => Option.rec b τ a)
          * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (fun a => Option.rec b τ a))
        = ∑ τ : V → Bool, spinProd A τ * isingWeight G β (h * StatMech.Ising.spinB b) τ := by
    intro b
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [fgd_ghost_weight_eq, split_ghost_spin, spinProd_map_some]
  rw [Fintype.sum_bool, hb, hb]
  show (∑ τ : V → Bool, spinProd A τ * isingWeight G β (h * StatMech.Ising.spinB true) τ)
      + (∑ τ : V → Bool, spinProd A τ * isingWeight G β (h * StatMech.Ising.spinB false) τ) = _
  have hfalse : StatMech.Ising.spinB false = -1 := rfl
  have htrue : StatMech.Ising.spinB true = 1 := rfl
  rw [hfalse, htrue, mul_neg_one, mul_one]
  rw [fgd_num_neg_even G β h A hA]; ring





theorem fgd_num_ghost_eq_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (insert none (A.map someEmb)) s
        * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) s)
      = 2 * ∑ τ : ConfigSpace V, spinProd A τ * isingWeight G β h τ := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ τ : V → Bool,
          spinProd (insert none (A.map someEmb)) (fun a => Option.rec b τ a)
            * boltzmannJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (fun a => Option.rec b τ a))
        = ∑ τ : V → Bool,
            (StatMech.Ising.spinB b * spinProd A τ)
              * isingWeight G β (h * StatMech.Ising.spinB b) τ := by
    intro b
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [fgd_ghost_weight_eq, split_ghost_spin, spinProd_insert_none_map_some]
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : StatMech.Ising.spinB false = -1 := rfl
  have htrue : StatMech.Ising.spinB true = 1 := rfl
  simp only [hfalse, htrue, mul_neg_one, mul_one, one_mul, neg_one_mul]
  rw [show (∑ τ : V → Bool, -spinProd A τ * isingWeight G β (-h) τ)
      = -∑ τ : V → Bool, spinProd A τ * isingWeight G β (-h) τ by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun τ _ => by ring)]
  rw [fgd_num_neg_odd G β h A hA]
  ring







theorem fgd_expectationJ_ghost_eq (β h : ℝ) (A : Finset V) (hA : Even A.card) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb)
      = isingExpectation G β h (spinProd A) := by
  unfold expectationJ isingExpectation isingProb
  rw [fgd_partitionJ_ghost_eq]
  rw [fgd_num_ghost_eq G β h A hA]
  rw [show (∑ s : ConfigSpace V, isingWeight G β h s / isingZ G β h * spinProd A s)
        = (∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s) / isingZ G β h from by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun s _ => by ring)]
  rw [mul_comm (2 : ℝ), mul_div_assoc]
  rw [show (2 : ℝ) / (2 * isingZ G β h) = 1 / isingZ G β h from by
    rw [eq_div_iff (isingZ_ne_zero G β h)]
    field_simp
    rw [div_self (isingZ_ne_zero G β h)]]
  rw [mul_one_div]



theorem fgd_expectationJ_ghost_eq_odd (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
        (insert none (A.map someEmb))
      = isingExpectation G β h (spinProd A) := by
  unfold expectationJ isingExpectation isingProb
  rw [fgd_partitionJ_ghost_eq]
  rw [fgd_num_ghost_eq_odd G β h A hA]
  rw [show (∑ s : ConfigSpace V, isingWeight G β h s / isingZ G β h * spinProd A s)
        = (∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s) / isingZ G β h from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun s _ => by ring)]
  rw [mul_comm (2 : ℝ), mul_div_assoc]
  rw [show (2 : ℝ) / (2 * isingZ G β h) = 1 / isingZ G β h from by
    rw [eq_div_iff (isingZ_ne_zero G β h)]
    field_simp
    rw [div_self (isingZ_ne_zero G β h)]]
  rw [mul_one_div]















theorem fgd_isingExpectation_eq_currentSum_ratio (β h : ℝ) (A : Finset V) (hA : Even A.card) :
    isingExpectation G β h (spinProd A)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb)
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  rw [← fgd_expectationJ_ghost_eq G β h A hA, current_representation]



theorem fgd_isingExpectation_eq_currentSum_ratio_odd
    (β h : ℝ) (A : Finset V) (hA : Odd A.card) :
    isingExpectation G β h (spinProd A)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert none (A.map someEmb))
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ := by
  rw [← fgd_expectationJ_ghost_eq_odd G β h A hA, current_representation]





theorem fgd_expectationJ_ghost_eq_nonvacuous :
    expectationJ (withGhost (⊤ : SimpleGraph (Fin 3))) 1
        (ghostCoupling 1 1 (fun _ => 1)) (({0, 1} : Finset (Fin 3)).map someEmb)
      = isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) :=
  fgd_expectationJ_ghost_eq (⊤ : SimpleGraph (Fin 3)) 1 1 ({0, 1} : Finset (Fin 3)) (by decide)


theorem fgd_isingExpectation_eq_currentSum_ratio_nonvacuous :
    isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3)))
      = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
            (({0, 1} : Finset (Fin 3)).map someEmb)
          / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  fgd_isingExpectation_eq_currentSum_ratio (⊤ : SimpleGraph (Fin 3)) 1 1
    ({0, 1} : Finset (Fin 3)) (by decide)













open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum)

omit [Fintype V] in

theorem map_symmDiff' {W : Type*} [DecidableEq W] (A B : Finset V) (f : V ↪ W) :
    (A ∆ B).map f = (A.map f) ∆ (B.map f) := by
  ext z
  simp only [Finset.mem_map, Finset.mem_symmDiff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨⟨x, hA, rfl⟩, fun ⟨y, hy, hfy⟩ => hB (by rwa [f.injective hfy] at hy)⟩
    · exact Or.inr ⟨⟨x, hB, rfl⟩, fun ⟨y, hy, hfy⟩ => hA (by rwa [f.injective hfy] at hy)⟩
  · rintro (⟨⟨x, hA, rfl⟩, hB⟩ | ⟨⟨x, hB, rfl⟩, hA⟩)
    · exact ⟨x, Or.inl ⟨hA, fun hxB => hB ⟨x, hxB, rfl⟩⟩, rfl⟩
    · exact ⟨x, Or.inr ⟨hB, fun hxA => hA ⟨x, hxA, rfl⟩⟩, rfl⟩















theorem fgd_ghostCurrentRep_unconditional (β h : ℝ) (A : Finset V) {u v : V} (huv : u ≠ v)
    (hA : Even A.card) (hAuv : Even ((A ∆ {u, v}).card)) (huvcard : Even (({u, v} : Finset V).card))
    (hZne : currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ ≠ 0) :
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅) ^ 2
        * (isingExpectation G β h (spinProd A)
            - isingExpectation G β h (spinProd (A ∆ {u, v}))
              * isingExpectation G β h (spinProd {u, v}))
      = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          (A.map someEmb) ∅ (some u) (some v) := by
  
  have hsuv : (some u : Option V) ≠ some v := fun hc => huv (Option.some_injective V hc)
  
  have hrep₃ := fgd_isingExpectation_eq_currentSum_ratio G β h A hA
  have hrep₁ := fgd_isingExpectation_eq_currentSum_ratio G β h (A ∆ {u, v}) hAuv
  have hrep₂ := fgd_isingExpectation_eq_currentSum_ratio G β h ({u, v} : Finset V) huvcard
  
  have hmapdiff :
      (A ∆ {u, v}).map someEmb = (A.map someEmb) ∆ ({some u, some v} : Finset (Option V)) := by
    rw [map_symmDiff']
    congr 1
    ext z; simp [someEmb]
  have hmappair : ({u, v} : Finset V).map someEmb = ({some u, some v} : Finset (Option V)) := by
    ext z; simp [someEmb]
  rw [hmapdiff] at hrep₁
  rw [hmappair] at hrep₂
  
  exact GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β (fun _ => 1)) (A.map someEmb) hsuv
    (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅)
    (isingExpectation G β h (spinProd A))
    (isingExpectation G β h (spinProd (A ∆ {u, v})))
    (isingExpectation G β h (spinProd {u, v}))
    rfl hZne hrep₃ hrep₁ hrep₂

end FieldGhostDict
end Sharpness
end StatMech
