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

/-- **Stack embedding.** Given a family of stack alphabets $\Gamma$ indexed by the stacks $K$ of a
sub-machine and a family $\Gamma'$ indexed by the stacks $K'$ of a host, a stack embedding
consists of an injective map $e : K \to K'$ renaming the stacks together with, for each stack
$k \in K$, a bijection $\iota_k : \Gamma_k \to \Gamma'_{e(k)}$ from the alphabet of $k$ onto the
alphabet of its image. -/
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

/-- **Translating a statement along a stack embedding.** Let $E$ be a stack embedding with stack
renaming $e$ and alphabet bijections $\iota_k$, and let $\varphi$ map the sub-machine's labels to
the host's labels. The translation of a sub-machine statement is the host statement obtained
recursively, where $s$ denotes the current state. A push of the symbol $f(s)$ on stack $k$
becomes a push of $\iota_k(f(s))$ on stack $e(k)$. A peek or pop on stack $k$ becomes a peek or
pop on stack $e(k)$ whose result is mapped back by $\iota_k^{-1}$ before the state update. A jump
to label $f(s)$ becomes a jump to $\varphi(f(s))$. State updates, branches and halt are kept, with
their sub-statements translated. -/
def mapS : TM2.Stmt Γ Λ σ → TM2.Stmt Γ' Λ' σ
  | .push k f q => .push (E.e k) (fun s => E.ι k (f s)) (mapS q)
  | .peek k f q => .peek (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .pop k f q => .pop (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .load a q => .load a (mapS q)
  | .branch f q₁ q₂ => .branch f (mapS q₁) (mapS q₂)
  | .goto f => .goto fun s => φ (f s)
  | .halt => .halt

/-- **Embedding of a machine in a host.** Let $E$ be a stack embedding and $\varphi$ a map from
the labels of a machine $M$ to the labels of a host machine $M'$ over the same internal states.
Then $M$ embeds in $M'$ along $E$ and $\varphi$ when, for every label $\ell$ of $M$, either the
statement of $M'$ at $\varphi(\ell)$ is the statement of $M$ at $\ell$ translated along $E$ and
$\varphi$, or the statement of $M$ at $\ell$ is the halt statement (in which case $M'$ may do
anything at $\varphi(\ell)$). -/
def Embeds (M : Λ → TM2.Stmt Γ Λ σ) (M' : Λ' → TM2.Stmt Γ' Λ' σ) : Prop :=
  ∀ l, M' (φ l) = mapS E φ (M l) ∨ M l = .halt

/-- **Agreement of host and sub-machine stacks.** Let $E$ be a stack embedding with stack
renaming $e$ and alphabet bijections $\iota_k$. Stack contents $S$ of the sub-machine and $S'$
of the host agree when, for every sub-machine stack $k$, the host stack $e(k)$ holds the list
obtained from $S(k)$ by applying $\iota_k$ to each symbol. -/
def Agree (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k, S' (E.e k) = (S k).map (E.ι k)

/-- **Frame condition for a stack embedding.** Let $E$ be a stack embedding with stack renaming
$e$. Two contents $S'$ and $S''$ of the host's stacks satisfy the frame condition when every host
stack $k'$ outside the image of $e$ has the same contents in both: $S''(k') = S'(k')$ whenever
$e(k) \ne k'$ for every sub-machine stack $k$. -/
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

/-- **Executing a translated statement.** Let $E$ be a stack embedding with stack renaming $e$, and
let $\varphi$ map sub-machine labels to host labels. Let $q$ be a sub-machine statement, $v$ a
state, $S$ sub-machine stacks and $S'$ host stacks that agree with $S$. Let executing $q$ from
state $v$ and stacks $S$ yield the next label $\ell$ (possibly none), state $w$ and stacks $T$.
Then there are host stacks $T'$ such that executing the translation of $q$ along $E$ and
$\varphi$ from state $v$ and stacks $S'$ yields the next label $\varphi(\ell)$ (none if $\ell$ is
none), state $w$ and stacks $T'$. Moreover $T'$ agrees with $T$, and $S'$, $T'$ satisfy the frame
condition. -/
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

/-- **Run embedding.** Let $E$ be a stack embedding with stack renaming $e$, let $\varphi$ map the
labels of a machine $M$ to those of a host machine $M'$, and suppose $M$ embeds in $M'$ along $E$
and $\varphi$. Suppose $M$ goes in exactly $n$ steps from label $\ell$, state $v$ and stacks $S$ to
a live label $\ell'$, state $v'$ and stacks $T$, where the start may also be the halted
configuration with no label (whose image under $\varphi$ again has no label). If host stacks $S'$
agree with $S$, then there are host stacks $T'$ such that $M'$ goes in exactly $n$ steps from
label $\varphi(\ell)$, state $v$ and stacks $S'$ to label $\varphi(\ell')$, state $v'$ and stacks
$T'$. Moreover $T'$ agrees with $T$, and $S'$, $T'$ satisfy the frame condition: host stacks
outside the image of $e$ are unchanged. -/
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

/-- **Run embedding for bounded runs.** Let $E$ be a stack embedding with stack renaming $e$, let
$\varphi$ map the labels of a machine $M$ to those of a host machine $M'$, and suppose $M$ embeds
in $M'$ along $E$ and $\varphi$. Suppose $M$ goes in at most $B$ steps from label $\ell$, state $v$
and stacks $S$ to label $\ell'$, state $v'$ and stacks $T$, and host stacks $S'$ agree with $S$.
Then there are host stacks $T'$ such that $M'$ goes in at most $B$ steps from label
$\varphi(\ell)$, state $v$ and stacks $S'$ to label $\varphi(\ell')$, state $v'$ and stacks $T'$.
Moreover $T'$ agrees with $T$, and $S'$, $T'$ satisfy the frame condition: host stacks outside
the image of $e$ are unchanged. -/
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
