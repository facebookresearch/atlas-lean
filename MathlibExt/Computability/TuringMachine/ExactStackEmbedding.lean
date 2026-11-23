/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
Modifications: adapt `ToTuring/TM/Rename.lean` at commit
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5` to the existing stack embedding API,
with dependent alphabets, label maps, and exact program matching.
-/

module

public import MathlibExt.Computability.TuringMachine.StackEmbedding

/-!
# Exact stack embedding, including halted endpoints

Exact matching at every source label transports runs with arbitrary optional endpoints.
Unlike `Embeds`, the matching premise also constrains host code at source halt statements.
The supplied-stack result recovers the endpoint contract of the source's `run_renK`.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Embedding

open MetaMathlibExt.TM2Program Turing Function

variable {K K' : Type} [DecidableEq K] [DecidableEq K']
  {Γ : K → Type} {Γ' : K' → Type} {Λ Λ' σ : Type}
  (E : SEmb Γ Γ') (φ : Λ → Λ')
  {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ' Λ' σ}

/-- Exact program matching transports a run, including a halted endpoint, while preserving
the local state, embedded stacks, untouched host stacks, and exact number of steps. -/
theorem run_embed_exact (hM : ∀ l, M' (φ l) = mapS E φ (M l))
    {n : ℕ} {l l' : Option Λ} {v v' : σ}
    {S T : ∀ k, List (Γ k)} {S' : ∀ k', List (Γ' k')}
    (h : Run M n ⟨l, v, S⟩ ⟨l', v', T⟩) (hA : Agree E S S') :
    ∃ T', Run M' n ⟨l.map φ, v, S'⟩ ⟨l'.map φ, v', T'⟩ ∧
      Agree E T T' ∧ Frame E S' T' := by
  induction n generalizing l v S S' with
  | zero =>
      simp only [Run, iterate_zero, id_eq, Option.some.injEq, TM2.Cfg.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨S', Run.zero _, hA, Frame.refl S'⟩
  | succ n ih =>
      unfold Run at h
      rw [iterate_succ_apply] at h
      rcases l with _ | l
      · have hnone : (flip bind (TM2.step M))
            (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
        rw [hnone, iter_none] at h
        cases h
      · have hstep : (flip bind (TM2.step M))
            (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
            some (TM2.stepAux (M l) v S) := rfl
        rw [hstep] at h
        obtain ⟨T₁, h1, h2, h3⟩ := stepAux_mapS φ (M l) v S S' hA
        obtain ⟨T', hr, h4, h5⟩ := ih h h2
        refine ⟨T', Run.head ?_ hr, h4, h3.trans h5⟩
        simp only [Option.map_some, TM2.step, hM l, h1]

omit [DecidableEq K] [DecidableEq K'] in
private theorem agree_frame_ext
    {S : ∀ k, List (Γ k)} {H S₁ S₂ : ∀ k', List (Γ' k')}
    (hA₁ : Agree E S S₁) (hA₂ : Agree E S S₂)
    (hF₁ : Frame E H S₁) (hF₂ : Frame E H S₂) : S₁ = S₂ := by
  classical
  funext k'
  by_cases hk : ∃ k, E.e k = k'
  · obtain ⟨k, rfl⟩ := hk
    exact (hA₁ k).trans (hA₂ k).symm
  · have hnot : ∀ k, E.e k ≠ k' := fun k he => hk ⟨k, he⟩
    exact (hF₁ k' hnot).trans (hF₂ k' hnot).symm

/-- Source-shaped transport to supplied host final stacks: agreement fixes embedded slots
and the frame condition fixes every other slot, so the host endpoint is exact. -/
theorem run_embed_exact_of_agree_frame (hM : ∀ l, M' (φ l) = mapS E φ (M l))
    {n : ℕ} {l l' : Option Λ} {v v' : σ}
    {S T : ∀ k, List (Γ k)} {S' T' : ∀ k', List (Γ' k')}
    (h : Run M n ⟨l, v, S⟩ ⟨l', v', T⟩) (hA : Agree E S S')
    (hT : Agree E T T') (hF : Frame E S' T') :
    Run M' n ⟨l.map φ, v, S'⟩ ⟨l'.map φ, v', T'⟩ := by
  obtain ⟨T'', hr, hA', hF'⟩ := run_embed_exact E φ hM h hA
  have heq := agree_frame_ext E hA' hT hF' hF
  rwa [heq] at hr

/-- Exact matching transports a bounded run with arbitrary optional endpoints, retaining
the same step witness and budget as well as agreement and the host frame. -/
theorem runLe_embed_exact (hM : ∀ l, M' (φ l) = mapS E φ (M l))
    {B : ℕ} {l l' : Option Λ} {v v' : σ}
    {S T : ∀ k, List (Γ k)} {S' : ∀ k', List (Γ' k')}
    (h : RunLe M B ⟨l, v, S⟩ ⟨l', v', T⟩) (hA : Agree E S S') :
    ∃ T', RunLe M' B ⟨l.map φ, v, S'⟩ ⟨l'.map φ, v', T'⟩ ∧
      Agree E T T' ∧ Frame E S' T' := by
  obtain ⟨n, hn, hr⟩ := h
  obtain ⟨T', hr', hT, hF⟩ := run_embed_exact E φ hM hr hA
  exact ⟨T', ⟨n, hn, hr'⟩, hT, hF⟩

end MetaMathlibExt.TM2Embedding
