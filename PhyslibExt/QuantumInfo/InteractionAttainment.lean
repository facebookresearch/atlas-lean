/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Interaction
public import PhyslibExt.QuantumInfo.ChannelTopology

/-!
# Attainment of the value of a quantum interaction

## i. Overview

At a fixed nonempty finite prover workspace in the verifier-first
even-message model of `PhyslibExt.QuantumInfo.Interaction`, the value
of a verifier (the supremum of its acceptance probability over prover
strategies) is attained: the strategy space — an initial state together
with finitely many channels — is compact, and the acceptance
probability is continuous in the strategy through the continuity of
channel application, composition, tensor products, and measurement
from `PhyslibExt.QuantumInfo.ChannelTopology`. This is the
finite-dimensional attainment statement for that fixed workspace.

## ii. Key results

- `exists_acceptProb_eq_value`: some prover attains the value.

## iii. Table of contents

- Continuity in the strategy: `continuous_acceptProb`.
- Attainment: `exists_acceptProb_eq_value`.

## iv. References

John Watrous, "Quantum computational complexity", in Encyclopedia of
Complexity and Systems Science, Springer, 2009 (arXiv:0804.3401), Section
on quantum interactive proof systems.
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.Interaction

set_option autoImplicit false

open PhyslibExt.QuantumInfo.ChannelTopology

variable {dV dM dP : Type*} [Fintype dV] [DecidableEq dV] [Fintype dM]
  [DecidableEq dM] [Fintype dP] [DecidableEq dP]

/-- A round is continuous in the prover's channel. -/
private lemma continuous_round (Vi : CPTPMap (dV × dM) (dV × dM)) :
    Continuous (fun Pi : CPTPMap (dM × dP) (dM × dP) => round Vi Pi) := by
  change Continuous (fun Pi : CPTPMap (dM × dP) (dM × dP) =>
    (CPTPMap.assoc ∘ₘ (Vi ⊗ᶜᵖ (CPTPMap.id : CPTPMap dP dP)) ∘ₘ
      CPTPMap.assoc') ∘ₘ ((CPTPMap.id : CPTPMap dV dV) ⊗ᶜᵖ Pi))
  have hB : Continuous (fun Pi : CPTPMap (dM × dP) (dM × dP) =>
      (CPTPMap.id : CPTPMap dV dV) ⊗ᶜᵖ Pi) := by
    have hId : Continuous (fun _ : CPTPMap (dM × dP) (dM × dP) =>
        (CPTPMap.id : CPTPMap dV dV)) := continuous_const
    exact (Continuous.comp continuous_tensor (hId.prodMk continuous_id) :
      Continuous _)
  have hA : Continuous (fun _ : CPTPMap (dM × dP) (dM × dP) =>
      CPTPMap.assoc ∘ₘ (Vi ⊗ᶜᵖ (CPTPMap.id : CPTPMap dP dP)) ∘ₘ
        CPTPMap.assoc') :=
    continuous_const
  exact (Continuous.comp continuous_compose (hA.prodMk hB) : Continuous _)

/-- The `k`-round channel is continuous in the prover's channels. -/
private lemma continuous_run (k : ℕ)
    (Vs : Fin k → CPTPMap (dV × dM) (dV × dM)) :
    Continuous
      (fun Ps : Fin k → CPTPMap (dM × dP) (dM × dP) => run k Vs Ps) := by
  induction k with
  | zero =>
    change Continuous (fun _ : Fin 0 → CPTPMap (dM × dP) (dM × dP) =>
      (CPTPMap.id : CPTPMap (dV × dM × dP) (dV × dM × dP)))
    exact continuous_const
  | succ k ih =>
    have heq : (fun Ps : Fin (k + 1) → CPTPMap (dM × dP) (dM × dP) =>
          run (k + 1) Vs Ps)
        = (fun Ps => round (Vs (Fin.last k)) (Ps (Fin.last k)) ∘ₘ
          run k (fun i => Vs i.castSucc) (fun i => Ps i.castSucc)) :=
      funext (fun Ps => run_succ k Vs Ps)
    rw [heq]
    have hround : Continuous
        (fun Ps : Fin (k + 1) → CPTPMap (dM × dP) (dM × dP) =>
          round (Vs (Fin.last k)) (Ps (Fin.last k))) :=
      (Continuous.comp (continuous_round (Vs (Fin.last k)))
        (continuous_apply (Fin.last k)) : Continuous _)
    have hprefix : Continuous
        (fun Ps : Fin (k + 1) → CPTPMap (dM × dP) (dM × dP) =>
          (fun i : Fin k => Ps i.castSucc)) :=
      continuous_pi_iff.2 (fun i => continuous_apply i.castSucc)
    have hrec : Continuous
        (fun Ps : Fin (k + 1) → CPTPMap (dM × dP) (dM × dP) =>
          run k (fun i => Vs i.castSucc) (fun i => Ps i.castSucc)) :=
      (Continuous.comp (ih (fun i => Vs i.castSucc)) hprefix : Continuous _)
    exact (Continuous.comp continuous_compose (hround.prodMk hrec) : Continuous _)

/-- Acceptance is continuous in the prover strategy, viewed as the pair of
its initial state and its tuple of channels. -/
lemma continuous_acceptProb {k : ℕ} (V : Verifier k dV dM) :
    Continuous (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
      acceptProb V ⟨P.1, P.2⟩) := by
  have hfin : Continuous
      (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
        finalState V ⟨P.1, P.2⟩) := by
    change Continuous
      (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
        (CPTPMap.traceRight ∘ₘ CPTPMap.assoc' ∘ₘ run k V.step P.2)
          ((V.init ⊗ᴹ P.1).assoc))
    have hrun : Continuous
        (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
          run k V.step P.2) :=
      (Continuous.comp (continuous_run k V.step) continuous_snd : Continuous _)
    have hY : Continuous
        (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
          (CPTPMap.assoc' :
            CPTPMap (dV × (dM × dP)) ((dV × dM) × dP)) ∘ₘ
            run k V.step P.2) := by
      have hA' : Continuous
          (fun _ : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
            (CPTPMap.assoc' :
              CPTPMap (dV × (dM × dP)) ((dV × dM) × dP))) :=
        continuous_const
      exact (Continuous.comp continuous_compose (hA'.prodMk hrun) : Continuous _)
    have hchan : Continuous
        (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
          (CPTPMap.traceRight : CPTPMap ((dV × dM) × dP) (dV × dM)) ∘ₘ
            (CPTPMap.assoc' :
              CPTPMap (dV × (dM × dP)) ((dV × dM) × dP)) ∘ₘ
            run k V.step P.2) := by
      have hT : Continuous
          (fun _ : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
            (CPTPMap.traceRight : CPTPMap ((dV × dM) × dP) (dV × dM))) :=
        continuous_const
      exact (Continuous.comp continuous_compose (hT.prodMk hY) : Continuous _)
    have hprod : Continuous
        (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
          V.init ⊗ᴹ P.1) := by
      have hV : Continuous
          (fun _ : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
            V.init) :=
        continuous_const
      exact (Continuous.comp continuous_state_prod (hV.prodMk continuous_fst) :
        Continuous _)
    have hassoc : Continuous (fun ρ : MState ((dV × dM) × dP) => ρ.assoc) := by
      have heq : (fun ρ : MState ((dV × dM) × dP) => ρ.assoc)
          = (fun ρ : MState ((dV × dM) × dP) => (CPTPMap.assoc :
            CPTPMap ((dV × dM) × dP) (dV × (dM × dP))) ρ) := by
        funext ρ
        rw [CPTPMap.assoc_eq_MState_assoc]
      rw [heq]
      have hA : Continuous (fun _ : MState ((dV × dM) × dP) =>
          (CPTPMap.assoc :
            CPTPMap ((dV × dM) × dP) (dV × (dM × dP)))) :=
        continuous_const
      exact (Continuous.comp continuous_channel_apply (hA.prodMk continuous_id) :
        Continuous _)
    have hstate : Continuous
        (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
          (V.init ⊗ᴹ P.1).assoc) :=
      (Continuous.comp hassoc hprod : Continuous _)
    exact (Continuous.comp continuous_channel_apply (hchan.prodMk hstate) :
      Continuous _)
  exact (Continuous.comp (continuous_measure V.accept true) hfin : Continuous _)

/-- **Attainment:** at a fixed nonempty finite prover workspace, some
prover strategy attains the value. -/
lemma exists_acceptProb_eq_value [Nonempty dP] {k : ℕ} (V : Verifier k dV dM) :
    ∃ P : Prover k dM dP, acceptProb V P = value V dP := by
  have hcont : Continuous
      (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
        acceptProb V ⟨P.1, P.2⟩) :=
    continuous_acceptProb V
  have hcontR : Continuous
      (fun P : MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)) =>
        ((acceptProb V ⟨P.1, P.2⟩ : Prob) : ℝ)) :=
    (Continuous.comp continuous_subtype_val hcont : Continuous _)
  have hcompact : IsCompact
      (Set.univ :
        Set (MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)))) :=
    isCompact_univ
  have hne : (Set.univ :
      Set (MState dP × (Fin k → CPTPMap (dM × dP) (dM × dP)))).Nonempty :=
    ⟨(default, fun _ => CPTPMap.id), Set.mem_univ _⟩
  obtain ⟨a, -, hmax⟩ := hcompact.exists_isMaxOn hne hcontR.continuousOn
  refine ⟨⟨a.1, a.2⟩, ?_⟩
  apply le_antisymm
  · exact le_value V ⟨a.1, a.2⟩
  · rw [value_le_iff]
    intro P
    obtain ⟨i, s⟩ := P
    have h := isMaxOn_iff.1 hmax (i, s) (Set.mem_univ _)
    exact Subtype.coe_le_coe.mp h

end PhyslibExt.QuantumInfo.Interaction
