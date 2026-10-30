/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Emb.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Emb.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`MetaMathlibExt` namespaces, `iter_none` moved to `MetaMathlibExt.TM2Program` (shared with
`TM2Composition`).
-/

module

public import MathlibExt.Computability.TuringMachine.Program

/-!
# Stack embedding: running a sub-machine inside a host machine

An arbitrary **renaming/embedding of stacks and labels**, so that separately built machines,
each written against its own local stack type, run unchanged as sub-machines of one combined
machine.

* `SEmb Γ Γ'`: an injective stack renaming `e : K → K'` with a per-stack alphabet bijection
  `ι k : Γ k ≃ Γ' (e k)` (in every instance `Equiv.refl` after a case split: no casts);
* `mapS E φ`: a statement of the sub-machine, rewritten to act on stacks `e k` and labels `φ l`;
* `Embeds E φ M M'`: the host runs `mapS (M l)` at `φ l`, except where `M` halts;
* `Agree`/`Frame`: the host holds the sub-machine's stacks on the image of `e` / is unchanged
  outside it.

`run_embed`: a run of `M` that ends at a live label is a run of `M'` of the same length, and the
host's stacks at the end agree with `M`'s on the image of `e` and are untouched elsewhere.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Embedding

open MetaMathlibExt.TM2Program Turing Function

/-- A stack embedding: injective renaming plus a bijection of each stack's alphabet. -/
structure SEmb {K K' : Type} (Γ : K → Type) (Γ' : K' → Type) where
  /-- The stack renaming. -/
  e : K → K'
  /-- Distinct sub-machine stacks go to distinct host stacks. -/
  inj : Injective e
  /-- The alphabet of each sub-machine stack, identified with its host stack's. -/
  ι : ∀ k, Γ k ≃ Γ' (e k)

section Embed

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {Γ : K → Type} {Γ' : K' → Type}
  {Λ Λ' σ : Type} (E : SEmb Γ Γ') (φ : Λ → Λ')

/-- A sub-machine statement acting on the embedded stacks and renamed labels. -/
def mapS : TM2.Stmt Γ Λ σ → TM2.Stmt Γ' Λ' σ
  | .push k f q => .push (E.e k) (fun s => E.ι k (f s)) (mapS q)
  | .peek k f q => .peek (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .pop k f q => .pop (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .load a q => .load a (mapS q)
  | .branch f q₁ q₂ => .branch f (mapS q₁) (mapS q₂)
  | .goto f => .goto fun s => φ (f s)
  | .halt => .halt

/-- The host runs the sub-machine's statements (embedded) at the images of its labels, except at
labels where the sub-machine halts (there the host may continue with anything). -/
def Embeds (M : Λ → TM2.Stmt Γ Λ σ) (M' : Λ' → TM2.Stmt Γ' Λ' σ) : Prop :=
  ∀ l, M' (φ l) = mapS E φ (M l) ∨ M l = .halt

/-- The host's stacks hold the sub-machine's stacks on the image of `e`. -/
def Agree (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k, S' (E.e k) = (S k).map (E.ι k)

/-- Host stacks outside the image of `e` are unchanged from `S'` to `S''`. -/
def Frame (S' S'' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k', (∀ k, E.e k ≠ k') → S'' k' = S' k'

variable {E}

omit [DecidableEq K] [DecidableEq K'] in
theorem Frame.refl (S' : ∀ k', List (Γ' k')) : Frame E S' S' := fun _ _ => rfl

omit [DecidableEq K] [DecidableEq K'] in
theorem Frame.trans {S₁ S₂ S₃ : ∀ k', List (Γ' k')} (h₁ : Frame E S₁ S₂) (h₂ : Frame E S₂ S₃) :
    Frame E S₁ S₃ := fun k' hk => (h₂ k' hk).trans (h₁ k' hk)

omit [DecidableEq K] in
theorem Frame.update (S' : ∀ k', List (Γ' k')) (k : K) (l : List (Γ' (E.e k))) :
    Frame E S' (update S' (E.e k) l) := fun _ hk => update_of_ne (hk k).symm _ _

theorem Agree.update {S : ∀ k, List (Γ k)} {S' : ∀ k', List (Γ' k')} (h : Agree E S S') (k : K)
    (l : List (Γ k)) :
    Agree E (Function.update S k l) (Function.update S' (E.e k) (l.map (E.ι k))) := by
  intro k₂
  by_cases hk : k₂ = k
  · subst hk; simp
  · rw [update_of_ne (E.inj.ne hk), update_of_ne hk]; exact h k₂

/-- One block of statements: the host's result is the sub-machine's, embedded. -/
theorem stepAux_mapS (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k'))
    (hA : Agree E S S') :
    ∃ T' : ∀ k', List (Γ' k'),
      TM2.stepAux (mapS E φ q) v S' =
        ⟨(TM2.stepAux q v S).l.map φ, (TM2.stepAux q v S).var, T'⟩ ∧
      Agree E (TM2.stepAux q v S).stk T' ∧ Frame E S' T' := by
  induction q generalizing v S S' with
  | push k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih v _ _ (hA.update k (f v :: S k))
      refine ⟨T', ?_, h2, (Frame.update S' k _).trans h3⟩
      simp only [mapS, TM2.stepAux, hA k]
      exact h1
  | peek k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (f v (S k).head?) S S' hA
      refine ⟨T', ?_, h2, h3⟩
      simp only [mapS, TM2.stepAux, hA k, List.head?_map, Option.map_map, Equiv.symm_comp_self,
        Option.map_id_fun, id_eq]
      exact h1
  | pop k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (f v (S k).head?) _ _ (hA.update k (S k).tail)
      refine ⟨T', ?_, h2, (Frame.update S' k _).trans h3⟩
      simp only [mapS, TM2.stepAux, hA k, List.head?_map, Option.map_map, Equiv.symm_comp_self,
        Option.map_id_fun, id_eq, ← List.map_tail]
      exact h1
  | load a q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (a v) S S' hA
      exact ⟨T', by simpa only [mapS, TM2.stepAux] using h1, h2, h3⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases hf : f v
      · obtain ⟨T', h1, h2, h3⟩ := ih₂ v S S' hA
        exact ⟨T', by simpa only [mapS, TM2.stepAux, hf, Bool.cond_false] using h1,
          by simpa only [TM2.stepAux, hf, Bool.cond_false] using h2, h3⟩
      · obtain ⟨T', h1, h2, h3⟩ := ih₁ v S S' hA
        exact ⟨T', by simpa only [mapS, TM2.stepAux, hf, Bool.cond_true] using h1,
          by simpa only [TM2.stepAux, hf, Bool.cond_true] using h2, h3⟩
  | goto f => exact ⟨S', by simp [mapS, TM2.stepAux], hA, Frame.refl S'⟩
  | halt => exact ⟨S', by simp [mapS, TM2.stepAux], hA, Frame.refl S'⟩

/-- **Run embedding.** A run of the sub-machine ending at a live label is a run of the host of the
same length, from any host stacks agreeing with the sub-machine's; at the end the host agrees with
the sub-machine on the image of `e` and is unchanged outside it. -/
theorem run_embed {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ' Λ' σ} (hM : Embeds E φ M M') :
    ∀ (n : ℕ) (l : Option Λ) (v : σ) (S : ∀ k, List (Γ k)) (l' : Λ) (v' : σ)
      (T : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')),
      Run M n ⟨l, v, S⟩ ⟨some l', v', T⟩ → Agree E S S' →
      ∃ T' : ∀ k', List (Γ' k'),
        Run M' n ⟨l.map φ, v, S'⟩ ⟨some (φ l'), v', T'⟩ ∧ Agree E T T' ∧ Frame E S' T' := by
  intro n
  induction n with
  | zero =>
      intro l v S l' v' T S' h hA
      simp only [Run, iterate_zero, id_eq, Option.some.injEq, TM2.Cfg.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨S', Run.zero _, hA, Frame.refl S'⟩
  | succ n ih =>
      intro l v S l' v' T S' h hA
      unfold Run at h
      rw [iterate_succ_apply] at h
      rcases l with _ | l
      · have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
        rw [this, iter_none] at h
        exact absurd h (by simp)
      · have e : (flip bind (TM2.step M)) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
            some (TM2.stepAux (M l) v S) := rfl
        rw [e] at h
        rcases hM l with hl | hl
        · obtain ⟨T₁, h1, h2, h3⟩ := stepAux_mapS φ (M l) v S S' hA
          obtain ⟨T', r, h4, h5⟩ := ih _ _ _ _ _ _ T₁ h h2
          refine ⟨T', Run.head ?_ r, h4, h3.trans h5⟩
          simp only [Option.map_some, TM2.step, hl, h1]
        · rw [hl] at h
          simp only [TM2.stepAux] at h
          cases n with
          | zero => simp at h
          | succ n =>
              rw [iterate_succ_apply] at h
              have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none :=
                rfl
              rw [this, iter_none] at h
              exact absurd h (by simp)

/-- `run_embed` for bounded runs (the form the generators' time lemmas use). -/
theorem runLe_embed {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ' Λ' σ} (hM : Embeds E φ M M')
    {B : ℕ} {l : Λ} {v : σ} {S : ∀ k, List (Γ k)} {l' : Λ} {v' : σ} {T : ∀ k, List (Γ k)}
    {S' : ∀ k', List (Γ' k')} (h : RunLe M B ⟨some l, v, S⟩ ⟨some l', v', T⟩) (hA : Agree E S S') :
    ∃ T' : ∀ k', List (Γ' k'),
      RunLe M' B ⟨some (φ l), v, S'⟩ ⟨some (φ l'), v', T'⟩ ∧ Agree E T T' ∧ Frame E S' T' := by
  obtain ⟨n, hn, r⟩ := h
  obtain ⟨T', r', h1, h2⟩ := run_embed φ hM n (some l) v S l' v' T S' r hA
  exact ⟨T', ⟨n, hn, r'⟩, h1, h2⟩

end Embed

end MetaMathlibExt.TM2Embedding
