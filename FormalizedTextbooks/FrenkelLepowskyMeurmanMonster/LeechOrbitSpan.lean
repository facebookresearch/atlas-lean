/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Conway orbit of Ω spans the entire binary lattice quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual lattice isometry represented by a certificate word. -/
noncomputable def omegaOrbitWordIsometry : List (Fin 5) → leechIsomSubgroup
  | [] => 1
  | k :: w => omegaOrbitWordIsometry w * omegaOrbitIsometry k

/-- Word evaluation agrees with the genuine lattice quotient action. -/
theorem omegaOrbitWord_binary (w : List (Fin 5)) (v : Fin 24 → ZMod 2) :
    w.foldl (fun v k => omegaOrbitBinaryMatrices k *ᵥ v) v =
      leechBinaryAction (omegaOrbitWordIsometry w) v := by
  induction w generalizing v with
  | nil => simp [omegaOrbitWordIsometry]
  | cons k w ih =>
    simp only [List.foldl_cons, omegaOrbitWordIsometry, map_mul]
    rw [ih, ← omegaOrbitIsometry_binary]
    rfl

/-- Each certified column belongs to the actual Co₁ orbit of Ω. -/
theorem omegaOrbitColumns_mem_actualOrbit (j : Fin 24) :
    ∃ c : Co1, (fun i => omegaOrbitColumns i j) =
      co1BinaryAction c (toAdd (qQuotHom sourceOmegaQ)) := by
  refine ⟨QuotientGroup.mk' signsSubgroup (omegaOrbitWordIsometry (omegaOrbitWords j)), ?_⟩
  have hs : toAdd (qQuotHom sourceOmegaQ) = (Pi.single 11 1 : Fin 24 → ZMod 2) := rfl
  change (fun i => omegaOrbitColumns i j) =
    leechBinaryAction (omegaOrbitWordIsometry (omegaOrbitWords j)) _
  rw [hs, ← omegaOrbitWord_binary, omegaOrbit_words_certificate]

/-- The checked spanning family discharges the actual Conway orbit-span hypothesis. -/
theorem sourceOmegaQ_actualOrbit_span : Submodule.span (ZMod 2)
    {v | ∃ c : Co1, v = co1BinaryAction c (toAdd (qQuotHom sourceOmegaQ))} = ⊤ := by
  apply top_unique
  intro v _
  let S := Submodule.span (ZMod 2)
    {v | ∃ c : Co1, v = co1BinaryAction c (toAdd (qQuotHom sourceOmegaQ))}
  have hc (j : Fin 24) : (fun i => omegaOrbitColumns i j) ∈ S :=
    Submodule.subset_span (omegaOrbitColumns_mem_actualOrbit j)
  have hv : omegaOrbitColumns *ᵥ (omegaOrbitColumnsInverse *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, omegaOrbit_inverse_certificate, Matrix.one_mulVec]
  have hsum : omegaOrbitColumns *ᵥ (omegaOrbitColumnsInverse *ᵥ v) =
      ∑ j, (omegaOrbitColumnsInverse *ᵥ v) j • (fun i => omegaOrbitColumns i j) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [← hv, hsum]
  exact S.sum_mem fun j _ => S.smul_mem _ (hc j)

/-- Every normal subgroup with nontrivial local intersection contains actual Q. -/
theorem generated_q_range_le_of_nontrivial_local_intersection
    (N : Subgroup ↥G) [N.Normal] (hN : N.comap localIntoGenerated ≠ ⊥) :
    qIntoGenerated.range ≤ N :=
  generated_q_range_le_of_Omega_orbit_span N hN sourceOmegaQ_actualOrbit_span

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
