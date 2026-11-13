/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































































import Mathlib
import Code.IsingFK.FvES
import Code.IsingFK.EsWired
import Code.IsingFK.EsInfinite
import Code.IsingFK.Q2
import Code.FK.EsCorrelations
import Code.FK.InfiniteVolume
import Code.Ising.Magnetization

open MeasureTheory
open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation






section AbstractGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]






noncomputable def isingBond (σ : V → Fin 2) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => isingSpin (σ x) * isingSpin (σ y), fun _ _ => mul_comm _ _⟩ e

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem isingBond_mk (σ : V → Fin 2) (x y : V) :
    isingBond σ s(x, y) = isingSpin (σ x) * isingSpin (σ y) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem monoIndicator_eq_isingBond (σ : V → Fin 2) (e : Sym2 V) :
    monoIndicator σ e = isingBond σ e / 2 + 1 / 2 := by
  induction e with
  | _ x y =>
    rw [monoIndicator_mk, isingBond_mk, isingSpin_mul]
    by_cases h : σ x = σ y <;> simp [h] <;> ring

omit [DecidableEq V] in


theorem agreement_eq_isingBondSum (σ : V → Fin 2) :
    agreement G σ
      = (∑ e ∈ G.edgeFinset, isingBond σ e) / 2 + (G.edgeFinset.card : ℝ) / 2 := by
  unfold agreement
  rw [Finset.sum_congr rfl (fun e _ => monoIndicator_eq_isingBond σ e),
    Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
  ring







noncomputable def isingWiredWeight (β : ℝ) (σ : V → Fin 2) : ℝ :=
  if BoundaryFixed bdry (0 : Fin 2) σ then
    Real.exp (β * ∑ e ∈ G.edgeFinset, isingBond σ e) else 0


noncomputable def isingWiredZ (β : ℝ) : ℝ := ∑ σ : V → Fin 2, isingWiredWeight G bdry β σ




noncomputable def isingWiredOnePoint (β : ℝ) (x : V) : ℝ :=
  (∑ σ : V → Fin 2, isingWiredWeight G bdry β σ * isingSpin (σ x)) / isingWiredZ G bdry β

omit [DecidableEq V] in



theorem pottsWeightWired_eq_isingWiredWeight (β : ℝ) (σ : V → Fin 2) :
    pottsWeightWired G bdry (0 : Fin 2) (2 * β) 1 σ
      = Real.exp (β * G.edgeFinset.card) * isingWiredWeight G bdry β σ := by
  unfold pottsWeightWired isingWiredWeight Potts.pottsWeight
  by_cases h : BoundaryFixed bdry (0 : Fin 2) σ
  · rw [if_pos h, if_pos h, agreement_eq_isingBondSum, ← Real.exp_add]
    congr 1; ring
  · rw [if_neg h, if_neg h, mul_zero]








theorem esWiredOnePoint_eq_pottsWiredOnePoint (β J : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (1 - Real.exp (-(β * J))) x
      = (∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) β J σ * isingSpin (σ x))
          / pottsZWired G bdry 2 (0 : Fin 2) β J := by
  unfold esWiredOnePoint
  rw [esZWired_eq_pottsZWired]
  have hnum : (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin 2,
        esWeightWired G bdry (0 : Fin 2) (1 - Real.exp (-(β * J))) σ ω * isingSpin (σ x))
      = esFirstConst G β J
          * ∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) β J σ * isingSpin (σ x) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Finset.sum_mul, esWeightWired_sum_omega]; ring
  rw [hnum, mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']



















theorem esWiredOnePoint_eq_isingWiredOnePoint (β : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (1 - Real.exp (-2 * β)) x
      = isingWiredOnePoint G bdry β x := by
  have hp : (1 - Real.exp (-2 * β)) = 1 - Real.exp (-((2 * β) * 1)) := by ring_nf
  rw [hp, esWiredOnePoint_eq_pottsWiredOnePoint]
  have hnum : (∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) (2 * β) 1 σ * isingSpin (σ x))
      = Real.exp (β * G.edgeFinset.card)
          * ∑ σ : V → Fin 2, isingWiredWeight G bdry β σ * isingSpin (σ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [pottsWeightWired_eq_isingWiredWeight]; ring
  have hden : pottsZWired G bdry 2 (0 : Fin 2) (2 * β) 1
      = Real.exp (β * G.edgeFinset.card) * isingWiredZ G bdry β := by
    unfold pottsZWired isingWiredZ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => pottsWeightWired_eq_isingWiredWeight G bdry β σ)
  rw [hnum, hden, isingWiredOnePoint, mul_div_mul_left _ _ (Real.exp_pos _).ne']




theorem esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint (β : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (pOfBeta β) x = isingWiredOnePoint G bdry β x := by
  rw [pOfBeta]; exact esWiredOnePoint_eq_isingWiredOnePoint G bdry β x

end AbstractGraph



section Lattice

variable {d : ℕ}










theorem fvMagnetization_eq_fvProb_sum (d : ℕ) (β : ℝ) (n : ℕ) :
    fvMagnetization d β n
      = ∑ τ : {x // x ∈ box d n} → Bool,
          fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ
            * spin (glue (plusField d) τ) (origin d) := by
  unfold fvMagnetization plusMeasure fvProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [fvMeasure, integral_finsetSum_measure ?_]
  · refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [integral_smul_measure, MeasureTheory.integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (fvProb_nonneg _ _ _ _ _ _)]
  · intro τ _
    apply Integrable.smul_measure (integrable_spin _ _)
    simp [ENNReal.ofReal_ne_top]





def bToF (b : Bool) : Fin 2 := if b then 0 else 1



theorem isingSpin_bToF (b : Bool) : isingSpin (bToF b) = (if b then (1 : ℝ) else -1) := by
  unfold bToF isingSpin; cases b <;> simp






noncomputable def latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    boxVerts d (n + 1) → Fin 2 :=
  fun v => if h : (v : Site d) ∈ box d n then bToF (τ ⟨v, h⟩) else 0






theorem isingSpin_latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) (v : boxVerts d (n + 1)) :
    isingSpin (latToBox d n τ v) = spin (glue (plusField d) τ) (v : Site d) := by
  unfold spin
  by_cases h : (v : Site d) ∈ box d n
  · rw [latToBox, dif_pos h, glue_mem _ _ h]
    unfold bToF isingSpin
    cases hb : τ ⟨v, h⟩ <;> simp
  · rw [latToBox, dif_neg h, glue_not_mem _ _ h]
    unfold plusField isingSpin
    simp




theorem boundaryFixed_latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) (latToBox d n τ) := by
  intro v hv
  rw [boxBoundary, mem_vertexBoundary] at hv
  have hnotin : (v : Site d) ∉ box d n := by simpa using hv.2
  rw [latToBox, dif_neg hnotin]























end Lattice

end IsingFK

end StatMech
