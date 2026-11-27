/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup

/-!
# Symbolic simulation for a Shoup-style generic-group bound

This file is the symbolic-simulation half of a Shoup Theorem 1-style bound,
proved with Shoup's game in a Nechaev-style deep-embedded model: equality tests
are free and only group operations are counted. Following Shoup, only an
`O(m^2/p)`-style bound is targeted here: no explicit constant is claimed in
this file, and Shoup's bitstring model is not claimed either.

Reference: Victor Shoup, "Lower Bounds for Discrete Logarithms and Related
Problems", EUROCRYPT 1997 (revised version), Section 2, Theorem 1 and its
proof game.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

inductive GTree (α : Type) : Nat → Type where
  | out {n} (a : α) : GTree α n
  | mul {n} (i j : Fin n) (k : GTree α (n + 1)) : GTree α n
  | inv {n} (i : Fin n) (k : GTree α (n + 1)) : GTree α n
  | eqTest {n} (i j : Fin n) (kt kf : GTree α n) : GTree α n

def GTree.eval {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat} (env : Fin n → L) :
    GTree α n → α
  | .out a => a
  | .mul i j k => GTree.eval O (snocEnv env (O (.inl (env i, env j)))) k
  | .inv i k => GTree.eval O (snocEnv env (O (.inr (env i)))) k
  | .eqTest i j kt kf => if env i = env j then GTree.eval O env kt else GTree.eval O env kf

private theorem GTree.eval_out {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (a : α) : GTree.eval O env (.out a) = a := rfl

private theorem GTree.eval_mul {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (k : GTree α (n + 1)) :
    GTree.eval O env (.mul i j k)
      = GTree.eval O (snocEnv env (O (.inl (env i, env j)))) k := rfl

private theorem GTree.eval_inv {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i : Fin n) (k : GTree α (n + 1)) :
    GTree.eval O env (.inv i k) = GTree.eval O (snocEnv env (O (.inr (env i)))) k := rfl

private theorem GTree.eval_eqTest {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (kt kf : GTree α n) :
    GTree.eval O env (.eqTest i j kt kf)
      = (if env i = env j then GTree.eval O env kt else GTree.eval O env kf) := rfl

def GTree.numQueries {α : Type} {n : Nat} : GTree α n → Nat
  | .out _ => 0
  | .mul _ _ k => 1 + GTree.numQueries k
  | .inv _ k => 1 + GTree.numQueries k
  | .eqTest _ _ kt kf => max (GTree.numQueries kt) (GTree.numQueries kf)

private theorem GTree.numQueries_out {α : Type} {n : Nat} (a : α) :
    GTree.numQueries (.out a : GTree α n) = 0 := rfl

private theorem GTree.numQueries_mul {α : Type} {n : Nat} (i j : Fin n)
    (k : GTree α (n + 1)) :
    GTree.numQueries (.mul i j k) = 1 + GTree.numQueries k := rfl

private theorem GTree.numQueries_inv {α : Type} {n : Nat} (i : Fin n)
    (k : GTree α (n + 1)) :
    GTree.numQueries (.inv i k) = 1 + GTree.numQueries k := rfl

private theorem GTree.numQueries_eqTest {α : Type} {n : Nat} (i j : Fin n)
    (kt kf : GTree α n) :
    GTree.numQueries (.eqTest i j kt kf) = max (GTree.numQueries kt) (GTree.numQueries kf) :=
  rfl

def GTree.compile {L α : Type} [DecidableEq L] {n : Nat} (env : Fin n → L) :
    GTree α n → OracleComp (Query L) L α
  | .out a => .pure a
  | .mul i j k => OracleComp.query (.inl (env i, env j)) fun ans =>
      GTree.compile (snocEnv env ans) k
  | .inv i k => OracleComp.query (.inr (env i)) fun ans =>
      GTree.compile (snocEnv env ans) k
  | .eqTest i j kt kf =>
      if env i = env j then GTree.compile env kt else GTree.compile env kf

private theorem GTree.compile_out {L α : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (a : α) : GTree.compile env (.out a) = .pure a := rfl

private theorem GTree.compile_mul {L α : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i j : Fin n) (k : GTree α (n + 1)) :
    GTree.compile env (.mul i j k) = OracleComp.query (.inl (env i, env j)) fun ans =>
      GTree.compile (snocEnv env ans) k := rfl

private theorem GTree.compile_inv {L α : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i : Fin n) (k : GTree α (n + 1)) :
    GTree.compile env (.inv i k) = OracleComp.query (.inr (env i)) fun ans =>
      GTree.compile (snocEnv env ans) k := rfl

private theorem GTree.compile_eqTest {L α : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i j : Fin n) (kt kf : GTree α n) :
    GTree.compile env (.eqTest i j kt kf)
      = (if env i = env j then GTree.compile env kt else GTree.compile env kf) := rfl

theorem GTree.compile_run {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (p : GTree α n) :
    OracleComp.run O (GTree.compile env p) = GTree.eval O env p := by
  induction p with
  | out a => rfl
  | mul i j k ih => exact ih _
  | inv i k ih => exact ih _
  | eqTest i j kt kf iht ihf =>
    simp only [GTree.compile_eqTest, GTree.eval_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then GTree.compile env kt else GTree.compile env kf)
          = GTree.compile env kt := by simp [h]
      rw [e]
      have e' : (if env i = env j then GTree.eval O env kt else GTree.eval O env kf)
          = GTree.eval O env kt := by simp [h]
      rw [e']
      exact iht _
    · have e : (if env i = env j then GTree.compile env kt else GTree.compile env kf)
          = GTree.compile env kf := by simp [h]
      rw [e]
      have e' : (if env i = env j then GTree.eval O env kt else GTree.eval O env kf)
          = GTree.eval O env kf := by simp [h]
      rw [e']
      exact ihf _

theorem GTree.isQueryBounded_compile {L α : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (p : GTree α n) :
    FreeM.IsQueryBounded (GTree.numQueries p) (GTree.compile env p) := by
  induction p with
  | out a =>
    simp only [GTree.compile_out, GTree.numQueries_out]
    exact FreeM.isQueryBounded_pure _ _
  | mul i j k ih =>
    simp only [GTree.compile_mul, GTree.numQueries_mul]
    rw [add_comm (1 : ℕ)]
    exact FreeM.isQueryBounded_liftBind fun b => ih _
  | inv i k ih =>
    simp only [GTree.compile_inv, GTree.numQueries_inv]
    rw [add_comm (1 : ℕ)]
    exact FreeM.isQueryBounded_liftBind fun b => ih _
  | eqTest i j kt kf iht ihf =>
    simp only [GTree.compile_eqTest, GTree.numQueries_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then GTree.compile env kt else GTree.compile env kf)
          = GTree.compile env kt := by simp [h]
      rw [e]
      exact FreeM.IsQueryBounded.mono (Nat.le_max_left _ _) (iht _)
    · have e : (if env i = env j then GTree.compile env kt else GTree.compile env kf)
          = GTree.compile env kf := by simp [h]
      rw [e]
      exact FreeM.IsQueryBounded.mono (Nat.le_max_right _ _) (ihf _)

def GTree.answers {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat} (env : Fin n → L) :
    GTree α n → List L
  | .out _ => []
  | .mul i j k =>
      O (.inl (env i, env j)) :: GTree.answers O (snocEnv env (O (.inl (env i, env j)))) k
  | .inv i k => O (.inr (env i)) :: GTree.answers O (snocEnv env (O (.inr (env i)))) k
  | .eqTest i j kt kf =>
      if env i = env j then GTree.answers O env kt else GTree.answers O env kf

private theorem GTree.answers_out {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (a : α) : GTree.answers O env (.out a) = [] := rfl

private theorem GTree.answers_mul {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (k : GTree α (n + 1)) :
    GTree.answers O env (.mul i j k)
      = O (.inl (env i, env j)) :: GTree.answers O (snocEnv env (O (.inl (env i, env j)))) k :=
  rfl

private theorem GTree.answers_inv {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i : Fin n) (k : GTree α (n + 1)) :
    GTree.answers O env (.inv i k)
      = O (.inr (env i)) :: GTree.answers O (snocEnv env (O (.inr (env i)))) k := rfl

private theorem GTree.answers_eqTest {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (kt kf : GTree α n) :
    GTree.answers O env (.eqTest i j kt kf)
      = (if env i = env j then GTree.answers O env kt else GTree.answers O env kf) := rfl

theorem GTree.length_answers_le {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (p : GTree α n) :
    (GTree.answers O env p).length ≤ GTree.numQueries p := by
  induction p with
  | out a => simp [GTree.answers_out, GTree.numQueries_out]
  | mul i j k ih =>
    simp only [GTree.answers_mul, GTree.numQueries_mul, List.length_cons]
    have h := ih (snocEnv env (O (.inl (env i, env j))))
    omega
  | inv i k ih =>
    simp only [GTree.answers_inv, GTree.numQueries_inv, List.length_cons]
    have h := ih (snocEnv env (O (.inr (env i))))
    omega
  | eqTest i j kt kf iht ihf =>
    simp only [GTree.answers_eqTest, GTree.numQueries_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then GTree.answers O env kt else GTree.answers O env kf)
          = GTree.answers O env kt := by simp [h]
      rw [e]
      exact (iht env).trans (Nat.le_max_left _ _)
    · have e : (if env i = env j then GTree.answers O env kt else GTree.answers O env kf)
          = GTree.answers O env kf := by simp [h]
      rw [e]
      exact (ihf env).trans (Nat.le_max_right _ _)

def GTree.pathLabels {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat} (env : Fin n → L)
    (p : GTree α n) : List L :=
  List.ofFn env ++ GTree.answers O env p

theorem GTree.length_pathLabels_le {L α : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (p : GTree α n) :
    (GTree.pathLabels O env p).length ≤ n + GTree.numQueries p := by
  simp only [GTree.pathLabels, List.length_append, List.length_ofFn]
  have h := GTree.length_answers_le O env p
  omega

private theorem GTree.snoc_hom {L L' : Type} (h : L → L') {n : Nat} (env1 : Fin n → L)
    (env2 : Fin n → L') (henv : ∀ i, env2 i = h (env1 i)) (x1 : L) (x2 : L')
    (hx : x2 = h x1) (t : Fin (n + 1)) :
    snocEnv env2 x2 t = h (snocEnv env1 x1 t) := by
  by_cases ht : (t : Nat) < n
  · rw [snocEnv_pos _ _ _ ht, snocEnv_pos _ _ _ ht, henv]
  · rw [snocEnv_neg _ _ _ ht, snocEnv_neg _ _ _ ht, hx]

private theorem GTree.mem_pathLabels_here {L α : Type} [DecidableEq L] (O : Query L → L)
    {n : Nat} (env : Fin n → L) (p : GTree α n) (i : Fin n) :
    env i ∈ GTree.pathLabels O env p := by
  simp only [GTree.pathLabels]
  apply List.mem_append_left
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩

private theorem GTree.mem_pathLabels_mul {L α : Type} [DecidableEq L] (O : Query L → L)
    {n : Nat} (env : Fin n → L) (i j : Fin n) (k : GTree α (n + 1)) (w : L)
    (hw : w ∈ GTree.pathLabels O (snocEnv env (O (.inl (env i, env j)))) k) :
    w ∈ GTree.pathLabels O env (.mul i j k) := by
  simp only [GTree.pathLabels, GTree.answers_mul] at hw ⊢
  rcases List.mem_append.mp hw with h1 | h2
  · rw [List.mem_ofFn] at h1
    obtain ⟨t, ht⟩ := h1
    by_cases htn : (t : Nat) < n
    · have hwt : w = env ⟨(t : Nat), htn⟩ := by
        rw [← ht, snocEnv_pos _ _ _ htn]
      rw [hwt]
      apply List.mem_append_left
      rw [List.mem_ofFn]
      exact ⟨⟨(t : Nat), htn⟩, rfl⟩
    · have hwt : w = O (.inl (env i, env j)) := by
        rw [← ht, snocEnv_neg _ _ _ htn]
      rw [hwt]
      apply List.mem_append_right
      exact List.mem_cons_self
  · apply List.mem_append_right
    exact List.mem_cons_of_mem _ h2

private theorem GTree.mem_pathLabels_inv {L α : Type} [DecidableEq L] (O : Query L → L)
    {n : Nat} (env : Fin n → L) (i : Fin n) (k : GTree α (n + 1)) (w : L)
    (hw : w ∈ GTree.pathLabels O (snocEnv env (O (.inr (env i)))) k) :
    w ∈ GTree.pathLabels O env (.inv i k) := by
  simp only [GTree.pathLabels, GTree.answers_inv] at hw ⊢
  rcases List.mem_append.mp hw with h1 | h2
  · rw [List.mem_ofFn] at h1
    obtain ⟨t, ht⟩ := h1
    by_cases htn : (t : Nat) < n
    · have hwt : w = env ⟨(t : Nat), htn⟩ := by
        rw [← ht, snocEnv_pos _ _ _ htn]
      rw [hwt]
      apply List.mem_append_left
      rw [List.mem_ofFn]
      exact ⟨⟨(t : Nat), htn⟩, rfl⟩
    · have hwt : w = O (.inr (env i)) := by
        rw [← ht, snocEnv_neg _ _ _ htn]
      rw [hwt]
      apply List.mem_append_right
      exact List.mem_cons_self
  · apply List.mem_append_right
    exact List.mem_cons_of_mem _ h2

theorem GTree.eval_hom {L L' α : Type} [DecidableEq L] [DecidableEq L'] (O1 : Query L → L)
    (O2 : Query L' → L') (h : L → L')
    (hmul : ∀ a b, O2 (.inl (h a, h b)) = h (O1 (.inl (a, b))))
    (hinv : ∀ a, O2 (.inr (h a)) = h (O1 (.inr a))) {n : Nat} (p : GTree α n)
    (env1 : Fin n → L) (env2 : Fin n → L') (henv : ∀ i, env2 i = h (env1 i))
    (hinj : ∀ u ∈ GTree.pathLabels O1 env1 p, ∀ v ∈ GTree.pathLabels O1 env1 p,
      h u = h v → u = v) :
    GTree.eval O2 env2 p = GTree.eval O1 env1 p := by
  induction p with
  | out a => rfl
  | mul i j k ih =>
    simp only [GTree.eval_mul]
    refine ih (snocEnv env1 (O1 (.inl (env1 i, env1 j))))
      (snocEnv env2 (O2 (.inl (env2 i, env2 j)))) ?_ ?_
    · intro t
      refine GTree.snoc_hom h env1 env2 henv _ _ ?_ t
      rw [henv i, henv j]
      exact hmul _ _
    · intro u hu v hv huv
      refine hinj u ?_ v ?_ huv
      · exact GTree.mem_pathLabels_mul O1 env1 i j k u hu
      · exact GTree.mem_pathLabels_mul O1 env1 i j k v hv
  | inv i k ih =>
    simp only [GTree.eval_inv]
    refine ih (snocEnv env1 (O1 (.inr (env1 i)))) (snocEnv env2 (O2 (.inr (env2 i)))) ?_ ?_
    · intro t
      refine GTree.snoc_hom h env1 env2 henv _ _ ?_ t
      rw [henv i]
      exact hinv _
    · intro u hu v hv huv
      refine hinj u ?_ v ?_ huv
      · exact GTree.mem_pathLabels_inv O1 env1 i k u hu
      · exact GTree.mem_pathLabels_inv O1 env1 i k v hv
  | eqTest i j kt kf iht ihf =>
    simp only [GTree.eval_eqTest]
    have hiff : env2 i = env2 j ↔ env1 i = env1 j := by
      constructor
      · intro h2
        have hh : h (env1 i) = h (env1 j) := by
          rw [← henv i, ← henv j]
          exact h2
        exact hinj _ (GTree.mem_pathLabels_here O1 env1 _ i) _
          (GTree.mem_pathLabels_here O1 env1 _ j) hh
      · intro h1
        rw [henv i, henv j, h1]
    by_cases h : env1 i = env1 j
    · have e2 : (if env2 i = env2 j then GTree.eval O2 env2 kt else GTree.eval O2 env2 kf)
          = GTree.eval O2 env2 kt := by simp [hiff.mpr h]
      have e1 : (if env1 i = env1 j then GTree.eval O1 env1 kt else GTree.eval O1 env1 kf)
          = GTree.eval O1 env1 kt := by simp [h]
      rw [e2, e1]
      refine iht env1 env2 henv ?_
      intro u hu v hv huv
      have eans : (if env1 i = env1 j then GTree.answers O1 env1 kt
          else GTree.answers O1 env1 kf) = GTree.answers O1 env1 kt := by simp [h]
      have heq : GTree.pathLabels O1 env1 (.eqTest i j kt kf)
          = GTree.pathLabels O1 env1 kt := by
        simp only [GTree.pathLabels, GTree.answers_eqTest, eans]
      have hu' : u ∈ GTree.pathLabels O1 env1 (.eqTest i j kt kf) := by
        rw [heq]
        exact hu
      have hv' : v ∈ GTree.pathLabels O1 env1 (.eqTest i j kt kf) := by
        rw [heq]
        exact hv
      exact hinj u hu' v hv' huv
    · have e2 : (if env2 i = env2 j then GTree.eval O2 env2 kt else GTree.eval O2 env2 kf)
          = GTree.eval O2 env2 kf := by
        simp [show env2 i ≠ env2 j from fun hh => h (hiff.mp hh)]
      have e1 : (if env1 i = env1 j then GTree.eval O1 env1 kt else GTree.eval O1 env1 kf)
          = GTree.eval O1 env1 kf := by simp [h]
      rw [e2, e1]
      refine ihf env1 env2 henv ?_
      intro u hu v hv huv
      have eans : (if env1 i = env1 j then GTree.answers O1 env1 kt
          else GTree.answers O1 env1 kf) = GTree.answers O1 env1 kf := by simp [h]
      have heq : GTree.pathLabels O1 env1 (.eqTest i j kt kf)
          = GTree.pathLabels O1 env1 kf := by
        simp only [GTree.pathLabels, GTree.answers_eqTest, eans]
      have hu' : u ∈ GTree.pathLabels O1 env1 (.eqTest i j kt kf) := by
        rw [heq]
        exact hu
      have hv' : v ∈ GTree.pathLabels O1 env1 (.eqTest i j kt kf) := by
        rw [heq]
        exact hv
      exact hinj u hu' v hv' huv

abbrev Aff (q : ℕ) : Type := ZMod q × ZMod q

def affOracle {q : ℕ} : Query (Aff q) → Aff q
  | .inl (u, v) => u + v
  | .inr u => -u

def affEval {q : ℕ} (x : ZMod q) (u : Aff q) : ZMod q := u.1 + u.2 * x

@[simp] theorem affEval_add {q : ℕ} (x : ZMod q) (u v : Aff q) :
    affEval x (u + v) = affEval x u + affEval x v := by
  simp only [affEval, Prod.fst_add, Prod.snd_add, add_mul]
  abel

@[simp] theorem affEval_neg {q : ℕ} (x : ZMod q) (u : Aff q) :
    affEval x (-u) = -affEval x u := by
  simp only [affEval, Prod.fst_neg, Prod.snd_neg, neg_mul]
  abel

def dlogForms (q : ℕ) : Fin 3 → Aff q := ![(0, 0), (1, 0), (0, 1)]

def dlogInputs {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (x : ZMod q) :
    Fin 3 → Label q :=
  ![enc 0, enc 1, enc x]

def symLabels {q : ℕ} {α : Type} (A : GTree α 3) : List (Aff q) :=
  GTree.pathLabels affOracle (dlogForms q) A

theorem length_symLabels_le {q : ℕ} {α : Type} (A : GTree α 3) :
    (symLabels (q := q) A).length ≤ 3 + GTree.numQueries A :=
  GTree.length_pathLabels_le affOracle (dlogForms q) A

theorem dlog_eval_eq_sym {q : ℕ} [Fact (1 < q)] {α : Type} (enc : Equiv.Perm (ZMod q))
    (x : ZMod q) (A : GTree α 3)
    (hnc : ∀ u ∈ symLabels (q := q) A, ∀ v ∈ symLabels (q := q) A,
      affEval x u = affEval x v → u = v) :
    GTree.eval (oracleOf enc) (dlogInputs enc x) A = GTree.eval affOracle (dlogForms q) A := by
  refine GTree.eval_hom affOracle (oracleOf enc) (fun u => enc (affEval x u)) ?_ ?_ A
    (dlogForms q) (dlogInputs enc x) ?_ ?_
  · intro a b
    simp only [oracleOf_inl, affOracle, Equiv.symm_apply_apply, ← affEval_add]
  · intro a
    simp only [oracleOf, affOracle, Equiv.symm_apply_apply, ← affEval_neg]
  · intro i
    fin_cases i <;> simp [dlogForms, dlogInputs, affEval]
  · intro u hu v hv huv
    exact hnc u hu v hv (enc.injective huv)

theorem dlog_success_imp {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (x : ZMod q)
    (A : GTree (ZMod q) 3)
    (hs : GTree.eval (oracleOf enc) (dlogInputs enc x) A = x) :
    GTree.eval affOracle (dlogForms q) A = x ∨
      ∃ u ∈ symLabels (q := q) A, ∃ v ∈ symLabels (q := q) A,
        u ≠ v ∧ affEval x u = affEval x v := by
  by_cases hnc : ∀ u ∈ symLabels (q := q) A, ∀ v ∈ symLabels (q := q) A,
    affEval x u = affEval x v → u = v
  · exact Or.inl (by rw [← dlog_eval_eq_sym enc x A hnc]; exact hs)
  · push Not at hnc
    obtain ⟨u, hu, v, hv, heq, hne⟩ := hnc
    exact Or.inr ⟨u, hu, v, hv, hne, heq⟩

end Cslib.Crypto.Framework.GenericGroup
