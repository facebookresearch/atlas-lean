/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.GroundedKronBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Grounded Kron reduction checks

Focused checks for `PhyslibExt.Circuits.GroundedKronBridge` on three
nodes and two branches `0 → 1` and `1 → 2`, grounded at `0`, with
node `2` the port and node `1` interior:

- two positive resistors in series meet the provider hypotheses and
  Kron-reduce to the one-port conductance `(R₁ + R₂)⁻¹`;
- a disconnected resistor graph (only branch `0 → 1`) fails the
  connectivity hypothesis, and its grounded matrix is not positive
  definite;
- a resistance value `0` fails the positivity hypothesis, and its
  grounded matrix is not positive definite: the totalized stamp gives
  that branch conductance `0⁻¹ = 0`, an open branch, whereas a
  physical zero-ohm short would force equal endpoint potentials.

These are elaboration and non-vacuity checks, not new results.
-/

@[expose] public section

namespace PhyslibExtTest.Circuits.GroundedKronBridge

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork
  MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity
  PhyslibExt.Circuits.LinearMNAStamping
  PhyslibExt.Circuits.GroundedNodalConductance
  PhyslibExt.Circuits.GroundedKronBridge

private theorem nodalConductance_apply {nN nB : ℕ} (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset : Finset (Fin nB)) (Rval : Fin nB → ℝ) (u v : Fin nN) :
    nodalConductance B Rset Rval u v = ∑ e ∈ Rset, B u e * (Rval e)⁻¹ * B v e := by
  rw [nodalConductance, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, resistorIncidence, transpose_apply]
  exact Finset.sum_coe_sort Rset (fun e => B u e * (Rval e)⁻¹ * B v e)

/-- Fixture tails: branch `0` is `0 → 1`, branch `1` is `1 → 2`. -/
def seriesTail : Fin 2 → Fin 3 := ![0, 1]

/-- Fixture heads: branch `0` is `0 → 1`, branch `1` is `1 → 2`. -/
def seriesHead : Fin 2 → Fin 3 := ![1, 2]

/-- Fixture labelling with ground `0`: node `2` is the port, node `1` is interior. -/
def seriesLabel : Unit ⊕ Unit ≃ {v : Fin 3 // v ≠ 0} where
  toFun := Sum.elim (fun _ => ⟨2, by decide⟩) (fun _ => ⟨1, by decide⟩)
  invFun v := if v.1 = 2 then Sum.inl () else Sum.inr ()
  left_inv := by
    rintro (⟨⟩ | ⟨⟩) <;> rfl
  right_inv := by
    rintro ⟨v, hv⟩
    fin_cases v <;> first | exact (hv rfl).elim | rfl

/-- The series fixture with positive resistances meets the provider hypotheses. -/
theorem series_hypotheses (R₁ R₂ : ℝ) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    (∀ e ∈ (Finset.univ : Finset (Fin 2)), 0 < (![R₁, R₂] : Fin 2 → ℝ) e) ∧
      (resistorGraph seriesTail seriesHead Finset.univ).Connected := by
  refine ⟨fun e _ => ?_, ?_⟩
  · fin_cases e <;> simp [h₁, h₂]
  · have h01 : (resistorGraph seriesTail seriesHead Finset.univ).Adj 0 1 :=
      (SimpleGraph.fromRel_adj _ _ _).mpr ⟨by decide, Or.inl ⟨0, Finset.mem_univ _, rfl, rfl⟩⟩
    have h12 : (resistorGraph seriesTail seriesHead Finset.univ).Adj 1 2 :=
      (SimpleGraph.fromRel_adj _ _ _).mpr ⟨by decide, Or.inl ⟨1, Finset.mem_univ _, rfl, rfl⟩⟩
    have r0 : ∀ v, (resistorGraph seriesTail seriesHead Finset.univ).Reachable 0 v := by
      intro v
      fin_cases v
      · rfl
      · exact h01.reachable
      · exact h01.reachable.trans h12.reachable
    exact ⟨fun u v => (r0 u).symm.trans (r0 v)⟩

/-- Two resistors in series, ground at one end and the port at the other, Kron-reduce to the
one-port conductance `(R₁ + R₂)⁻¹`. -/
theorem series_kronConductance (R₁ R₂ : ℝ) (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    kronConductance seriesTail seriesHead Finset.univ ![R₁, R₂] seriesLabel () () =
      (R₁ + R₂)⁻¹ := by
  have hA : portBlock seriesTail seriesHead Finset.univ ![R₁, R₂] seriesLabel =
      of fun _ _ => R₂⁻¹ := by
    ext i k
    simp [portBlock, portInteriorConductance, toBlocks₁₁, seriesLabel, nodalConductance_apply,
      physicalIncidence, incidenceMatrix, seriesTail, seriesHead, Fin.sum_univ_two]
  have hB : couplingBlock seriesTail seriesHead Finset.univ ![R₁, R₂] seriesLabel =
      of fun _ _ => -R₂⁻¹ := by
    ext i k
    simp [couplingBlock, portInteriorConductance, toBlocks₁₂, seriesLabel,
      nodalConductance_apply, physicalIncidence, incidenceMatrix, seriesTail, seriesHead,
      Fin.sum_univ_two]
  have hD : interiorBlock seriesTail seriesHead Finset.univ ![R₁, R₂] seriesLabel =
      of fun _ _ => R₁⁻¹ + R₂⁻¹ := by
    ext i k
    simp [interiorBlock, portInteriorConductance, toBlocks₂₂, seriesLabel,
      nodalConductance_apply, physicalIncidence, incidenceMatrix, seriesTail, seriesHead,
      Fin.sum_univ_two]
  have hpos : 0 < R₁⁻¹ + R₂⁻¹ := by positivity
  have hDinv : (of fun _ _ => R₁⁻¹ + R₂⁻¹ : Matrix Unit Unit ℝ)⁻¹ =
      of fun _ _ => (R₁⁻¹ + R₂⁻¹)⁻¹ := by
    apply inv_eq_right_inv
    ext i k
    simp [Matrix.mul_apply, hpos.ne']
  simp only [kronConductance, schurComplement, hA, hB, hD, hDinv]
  simp [Matrix.mul_apply, Matrix.sub_apply]
  field_simp
  ring

/-- A disconnected resistor graph (only branch `0`, node `2` isolated) fails the connectivity
hypothesis, and its grounded matrix is not positive definite. -/
theorem disconnected_counterexample :
    ¬ (resistorGraph seriesTail seriesHead {0}).Connected ∧
      ¬ (portInteriorConductance seriesTail seriesHead {0} (fun _ => 1) seriesLabel).PosDef := by
  refine ⟨fun hc => ?_, fun hpd => ?_⟩
  · have key : ∀ {u v : Fin 3} (w : (resistorGraph seriesTail seriesHead {0}).Walk u v),
        v = 2 → u = 2 := by
      intro u v w
      induction w with
      | nil => exact id
      | cons hadj p ih =>
        intro hv
        have hw := ih hv
        subst hw
        exfalso
        simp [resistorGraph, SimpleGraph.fromRel_adj, seriesTail, seriesHead] at hadj
    obtain ⟨w⟩ := hc.preconnected 0 2
    exact absurd (key w rfl) (by decide)
  · have h := hpd.diag_pos (i := Sum.inl ())
    simp [portInteriorConductance, seriesLabel, nodalConductance_apply, physicalIncidence,
      incidenceMatrix, seriesTail, seriesHead] at h

/-- A resistance value `0` on branch `1` fails the positivity hypothesis, and its grounded matrix
is not positive definite. The totalized stamp gives that branch conductance `0⁻¹ = 0`, an open
branch; a physical zero-ohm short would instead force equal endpoint potentials, which no
conductance stamp expresses. -/
theorem zeroResistance_counterexample :
    ¬ (∀ e ∈ (Finset.univ : Finset (Fin 2)), 0 < (![1, 0] : Fin 2 → ℝ) e) ∧
      ¬ (portInteriorConductance seriesTail seriesHead Finset.univ ![1, 0] seriesLabel).PosDef := by
  refine ⟨fun h => ?_, fun hpd => ?_⟩
  · have h1 := h 1 (Finset.mem_univ _)
    simp at h1
  · have h := hpd.diag_pos (i := Sum.inl ())
    simp [portInteriorConductance, seriesLabel, nodalConductance_apply, physicalIncidence,
      incidenceMatrix, seriesTail, seriesHead, Fin.sum_univ_two] at h

end PhyslibExtTest.Circuits.GroundedKronBridge
