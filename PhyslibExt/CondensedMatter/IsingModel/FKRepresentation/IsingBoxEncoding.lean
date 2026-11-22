/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.EsInfinite
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.FvES

/-!
# The Ising model in a box as a wired two-state Potts model

The plus-boundary Ising model in the box `Λ_n` is the wired `q = 2` Potts model on the graph of
`Λ_{n+1}` with boundary color `0`, so its magnetization is a wired Edwards–Sokal one-point
function.

## i. Overview

On a finite graph with boundary, the Ising weight with spins fixed to `+` on the boundary is, up
to the constant `e^{β|E|}`, the wired Potts weight with `q = 2`, `βJ = 2β` and boundary color `0`.
Hence the wired Ising one-point function equals the wired Edwards–Sokal one-point function at
`p = 1 - e^{-2β}`. On the lattice, configurations in `Λ_n` extended by `+` outside correspond to
colorings of `Λ_{n+1}` with boundary color `0` (`latToBox`), which identifies the finite-volume
lattice magnetization with the wired Ising one-point function of the box graph.

## ii. Key results

- `isingWiredOnePoint` : the one-point function `⟨σ_x⟩⁺` of the wired Ising model on a graph.
- `esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint` : it equals the wired Edwards–Sokal one-point
  function at `p = 1 - e^{-2β}`.
- `latToBox` : a configuration in `Λ_n` as a coloring of `Λ_{n+1}` with boundary color `0`.
- `isingSpin_latToBox` : the encoding preserves spins.

## iii. Table of contents

- A. The wired Ising model on a graph
- B. Lattice configurations as box colorings

## iv. References

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972) 536–564.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988) 2009–2012.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 1.4.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation

section AbstractGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-! ## A. The wired Ising model on a graph -/

/-- The Ising bond `σ_x σ_y` of a two-state coloring, with color `0` as spin `+1`. See also
`Ising.bond` for Boolean configurations. -/
noncomputable def isingBond (σ : V → Fin 2) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => isingSpin (σ x) * isingSpin (σ y), fun _ _ => mul_comm _ _⟩ e

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma isingBond_mk (σ : V → Fin 2) (x y : V) :
    isingBond σ s(x, y) = isingSpin (σ x) * isingSpin (σ y) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma monoIndicator_eq_isingBond (σ : V → Fin 2) (e : Sym2 V) :
    monoIndicator σ e = isingBond σ e / 2 + 1 / 2 := by
  induction e with
  | _ x y =>
    rw [monoIndicator_mk, isingBond_mk, isingSpin_mul]
    by_cases h : σ x = σ y <;> simp [h] <;> ring

omit [DecidableEq V] in
lemma agreement_eq_isingBondSum (σ : V → Fin 2) :
    agreement G σ
      = (∑ e ∈ G.edgeFinset, isingBond σ e) / 2 + (G.edgeFinset.card : ℝ) / 2 := by
  unfold agreement
  rw [Finset.sum_congr rfl (fun e _ => monoIndicator_eq_isingBond σ e),
    Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The Ising weight `exp (β ∑_e σ_x σ_y)` of a two-state coloring with boundary color `0`, and `0`
otherwise. -/
noncomputable def isingWiredWeight (β : ℝ) (σ : V → Fin 2) : ℝ :=
  if BoundaryFixed bdry (0 : Fin 2) σ then
    Real.exp (β * ∑ e ∈ G.edgeFinset, isingBond σ e) else 0

/-- The partition function of the Ising model with `+` boundary condition on a graph. -/
noncomputable def isingWiredZ (β : ℝ) : ℝ := ∑ σ : V → Fin 2, isingWiredWeight G bdry β σ

/-- The one-point function `⟨σ_x⟩⁺` of the Ising model with `+` boundary condition on a graph. -/
noncomputable def isingWiredOnePoint (β : ℝ) (x : V) : ℝ :=
  (∑ σ : V → Fin 2, isingWiredWeight G bdry β σ * isingSpin (σ x)) / isingWiredZ G bdry β

omit [DecidableEq V] in
lemma pottsWeightWired_eq_isingWiredWeight (β : ℝ) (σ : V → Fin 2) :
    pottsWeightWired G bdry (0 : Fin 2) (2 * β) 1 σ
      = Real.exp (β * G.edgeFinset.card) * isingWiredWeight G bdry β σ := by
  unfold pottsWeightWired isingWiredWeight Potts.pottsWeight
  by_cases h : BoundaryFixed bdry (0 : Fin 2) σ
  · rw [ite_eq_left h, ite_eq_left h, agreement_eq_isingBondSum, ← Real.exp_add]
    congr 1; ring
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

lemma esWiredOnePoint_eq_pottsWiredOnePoint (β J : ℝ) (x : V) :
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

lemma esWiredOnePoint_eq_isingWiredOnePoint (β : ℝ) (x : V) :
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

lemma esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint (β : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (pOfBeta β) x = isingWiredOnePoint G bdry β x := by
  rw [pOfBeta]; exact esWiredOnePoint_eq_isingWiredOnePoint G bdry β x

end AbstractGraph

section Lattice

variable {d : ℕ}

/-! ## B. Lattice configurations as box colorings -/

lemma fvMagnetization_eq_fvProb_sum (d : ℕ) (β : ℝ) (n : ℕ) :
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

/-- The two-state color of a Boolean spin: `true ↦ 0`, `false ↦ 1`. -/
def bToF (b : Bool) : Fin 2 := if b then 0 else 1

lemma isingSpin_bToF (b : Bool) : isingSpin (bToF b) = (if b then (1 : ℝ) else -1) := by
  unfold bToF isingSpin; cases b <;> simp

/-- A configuration in the box `Λ_n` as a two-state coloring of `Λ_{n+1}`, with color `0` (spin `+`)
outside `Λ_n`. -/
noncomputable def latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    boxVerts d (n + 1) → Fin 2 :=
  fun v => if h : (v : Site d) ∈ box d n then bToF (τ ⟨v, h⟩) else 0

lemma isingSpin_latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) (v : boxVerts d (n + 1)) :
    isingSpin (latToBox d n τ v) = spin (glue (plusField d) τ) (v : Site d) := by
  unfold spin
  by_cases h : (v : Site d) ∈ box d n
  · rw [latToBox, dite_eq_left h, glue_mem _ _ h]
    unfold bToF isingSpin
    cases hb : τ ⟨v, h⟩ <;> simp
  · rw [latToBox, dite_eq_right h, glue_not_mem _ _ h]
    unfold plusField isingSpin
    simp

lemma boundaryFixed_latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) (latToBox d n τ) := by
  intro v hv
  rw [boxBoundary, mem_vertexBoundary] at hv
  have hnotin : (v : Site d) ∉ box d n := by simpa using hv.2
  rw [latToBox, dite_eq_right hnotin]

end Lattice

end IsingFK

end StatMech
