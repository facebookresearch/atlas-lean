/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Probability.DTMCReachability

/-!
# Exact-rational checking for next and bounded until

A computable rational recursion evaluates the horizon probabilities of
`DTMCReachability` exactly; it agrees with the first-hit path-sum
definition on every genuine chain. The checkers evaluate it by
tabulation, one Bellman pass per horizon over a list of the states:
about `k * m^2` rational operations for `m` states and horizon `k`.
The next-step probability is, by
definition, the one-step sum of transition probabilities into the
target set. Threshold comparisons (five directions, against rational
thresholds) are decided on those values. Guarded entry points first
validate that a raw matrix is stochastic and reject it otherwise: a
guarded `false` means the matrix was rejected or the formula fails;
call `stochastic` to tell the two apart. Background: C. Baier and J.-P. Katoen,
*Principles of Model Checking*, MIT Press, 2008, Chapter 10.
-/

@[expose] public section

namespace Cslib.Probability

variable {S : Type*} [Fintype S] [DecidableEq S] (A B : Finset S)

/-- A computable rational evaluation of the horizon probabilities, by
the Bellman recursion. Its agreement with the path-sum definition is
`hitProbC_eq`. This is the reference recursion: it recomputes
sub-horizons for every state, so its cost is exponential in the
horizon; it is not memoized, and the checkers evaluate the tabulated
`hitProbTab` instead. -/
def hitProbC (P : S → S → ℚ) (A B : Finset S) : ℕ → S → ℚ
  | 0 => fun s => if s ∈ B then 1 else 0
  | (n + 1) => fun s =>
      if s ∈ B then 1 else if s ∉ A then 0
        else ∑ t, P s t * hitProbC P A B n t

private theorem foldl_add_map_sum {α : Type*} (l : List α)
    (g : α → ℚ) :
    l.foldl (fun acc x => acc + g x) 0 = (l.map g).sum := by
  have h1 : (l.map g).sum = List.foldl (fun x1 x2 => x1 + x2) 0 (l.map g) :=
    List.sum_eq_foldl
  have h2 : List.foldl (fun x1 x2 => x1 + x2) 0 (l.map g)
      = l.foldl (fun acc x => acc + g x) 0 :=
    List.foldl_map
  rw [h1, h2]

omit [Fintype S] [DecidableEq S] in
private theorem zip_map_eq (P : S → S → ℚ) (s : S) (f : S → ℚ)
    (l : List S) :
    ((l.zip (l.map f)).map (fun p : S × ℚ => P s p.1 * p.2))
      = l.map (fun t => P s t * f t) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.map_cons, ih]

omit [DecidableEq S] in
private theorem fold_zip_sum (P : S → S → ℚ) (s : S) (f : S → ℚ)
    (l : {l : List S // l.Nodup ∧ ∀ t, t ∈ l}) :
    (l.1.zip (l.1.map f)).foldl (fun acc p => acc + P s p.1 * p.2) 0
      = ∑ t, P s t * f t := by
  classical
  rw [foldl_add_map_sum, zip_map_eq P s f l.1, ← List.sum_toFinset _ l.2.1]
  congr 1
  ext t
  simp only [List.mem_toFinset, Finset.mem_univ, l.2.2 t]

/-- Tabulated horizon probabilities over a list of all states, each
listed once: the values at the listed states, in order, computed level
by level. Each level is computed once from the previous list, so
compiled evaluation takes about `k * m^2` rational operations for `m`
states. -/
def hitTabOn (P : S → S → ℚ) (A B : Finset S)
    (l : {l : List S // l.Nodup ∧ ∀ s, s ∈ l}) : ℕ → List ℚ
  | 0 => l.1.map fun s => if s ∈ B then 1 else 0
  | (n + 1) =>
    let v := hitTabOn P A B l n
    l.1.map fun s =>
      if s ∈ B then 1 else if s ∉ A then 0
      else (l.1.zip v).foldl (fun acc p => acc + P s p.1 * p.2) 0

/-- The tabulated list is the reference recursion evaluated at every
listed state. -/
theorem hitTabOn_eq_map (P : S → S → ℚ) (A B : Finset S)
    (l : {l : List S // l.Nodup ∧ ∀ s, s ∈ l}) (k : ℕ) :
    hitTabOn P A B l k = l.1.map (hitProbC P A B k) := by
  induction k with
  | zero => simp only [hitTabOn, hitProbC]
  | succ n ih =>
    simp only [hitTabOn, hitProbC]
    rw [ih]
    congr 1
    funext s
    by_cases hsB : s ∈ B
    · simp [hsB]
    · by_cases hsA : s ∈ A
      · simp only [hsB, hsA, ite_false, not_true_eq_false]
        exact fold_zip_sum P s (hitProbC P A B n) l
      · simp [hsB, hsA]

/-- Looking a state up in the tabulated list, at its position in the
state list, gives the reference recursion. -/
theorem hitTabOn_getD_idxOf (P : S → S → ℚ) (A B : Finset S)
    (l : {l : List S // l.Nodup ∧ ∀ s, s ∈ l}) (k : ℕ) (s : S) :
    (hitTabOn P A B l k).getD (l.1.idxOf s) 0 = hitProbC P A B k s := by
  have h : l.1.idxOf s < l.1.length := List.idxOf_lt_length_of_mem (l.2.2 s)
  rw [hitTabOn_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, List.getElem_idxOf h]
  rfl

/-- Tabulated horizon probabilities for any finite state type: the
states are listed once through `Fintype.truncFinBijection`, and the
value at `s` is read from `hitTabOn`, so compiled evaluation takes
about `k * m^2` rational operations for `m` states. The value does not
depend on the listing: it is the reference recursion
(`hitProbTab_eq`). -/
def hitProbTab (P : S → S → ℚ) (A B : Finset S) (k : ℕ) (s : S) : ℚ :=
  Trunc.lift
    (fun f : {f : Fin (Fintype.card S) → S // Function.Bijective f} =>
      let l : {l : List S // l.Nodup ∧ ∀ t, t ∈ l} :=
        ⟨List.ofFn f.1, List.nodup_ofFn.mpr f.2.1,
          fun t => List.mem_ofFn.mpr (f.2.2 t)⟩
      (hitTabOn P A B l k).getD (l.1.idxOf s) 0)
    (fun _ _ => (hitTabOn_getD_idxOf P A B _ k s).trans
      (hitTabOn_getD_idxOf P A B _ k s).symm)
    (Fintype.truncFinBijection S)

/-- The tabulated horizon probability is the reference recursion. -/
theorem hitProbTab_eq (P : S → S → ℚ) (A B : Finset S) (k : ℕ) (s : S) :
    hitProbTab P A B k s = hitProbC P A B k s := by
  unfold hitProbTab
  induction Fintype.truncFinBijection S using Trunc.ind
  exact hitTabOn_getD_idxOf P A B _ k s

/-- Threshold comparisons for probabilistic formulae. -/
inductive Cmp where
  | le | lt | eq | ge | gt
deriving DecidableEq, Repr

/-- The proposition a comparison expresses. -/
def Cmp.holds : Cmp → ℚ → ℚ → Prop
  | .le, x, q => x ≤ q
  | .lt, x, q => x < q
  | .eq, x, q => x = q
  | .ge, x, q => x ≥ q
  | .gt, x, q => x > q

/-- The decision procedure for a comparison. -/
def Cmp.eval : Cmp → ℚ → ℚ → Bool
  | .le, x, q => decide (x ≤ q)
  | .lt, x, q => decide (x < q)
  | .eq, x, q => decide (x = q)
  | .ge, x, q => decide (x ≥ q)
  | .gt, x, q => decide (x > q)

/-- The decision procedure agrees with the expressed comparison, for
every comparison and all rationals. -/
theorem cmp_eval_correct (c : Cmp) (x q : ℚ) :
    c.eval x q = true ↔ c.holds x q := by
  cases c <;> simp [Cmp.eval, Cmp.holds]

/-- Exact-rational check of a next-step threshold formula: the
probability of being in `A` after one step, compared against `q`. -/
def checkNext (P : S → S → ℚ) (A : Finset S) (s : S) (c : Cmp) (q : ℚ) :
    Bool :=
  c.eval (∑ t ∈ A, P s t) q

/-- Exact-rational check of a bounded-until threshold formula over
horizon `k`, on the tabulated value `hitProbTab`. -/
def checkBoundedUntil (P : S → S → ℚ) (A B : Finset S) (k : ℕ) (s : S)
    (c : Cmp) (q : ℚ) : Bool :=
  c.eval (hitProbTab P A B k s) q

/-- The bounded-until checker decides the comparison on the reference
recursion, for every rational matrix. -/
theorem checkBoundedUntil_eq (P : S → S → ℚ) (A B : Finset S) (k : ℕ)
    (s : S) (c : Cmp) (q : ℚ) :
    checkBoundedUntil P A B k s c q = c.eval (hitProbC P A B k s) q := by
  rw [checkBoundedUntil, hitProbTab_eq]

/-- Decidable validation of a raw rational matrix: nonnegative entries
and every row summing to `1`. -/
def stochastic (P : S → S → ℚ) : Bool :=
  decide (∀ s t, 0 ≤ P s t) && decide (∀ s, ∑ t, P s t = 1)

/-- Every genuine chain passes validation. -/
theorem stochastic_complete (D : DTMC S) : stochastic D.P = true := by
  simp only [stochastic, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨D.nonneg, D.row_sum⟩

/-- The computable evaluation agrees with the path-sum definition on
every genuine chain. -/
theorem hitProbC_eq (D : DTMC S) (n : ℕ) (s : S) :
    hitProbC D.P A B n s = D.hitProb A B n s := by
  induction n generalizing s with
  | zero =>
    by_cases hs : s ∈ B <;> simp only [hitProbC, hs, hitProb_zero]
  | succ n ih =>
    simp only [hitProbC]
    rw [hitProb_succ]
    by_cases hsB : s ∈ B
    · rw [ite_eq_left hsB, ite_eq_left hsB]
    · rw [ite_eq_right hsB, ite_eq_right hsB]
      by_cases hsA : s ∉ A
      · rw [ite_eq_left hsA, ite_eq_left hsA]
      · rw [ite_eq_right hsA, ite_eq_right hsA]
        exact Finset.sum_congr rfl (fun t _ => by rw [ih t])

/-- The next-step checker is exact: it returns `true` exactly when the
one-step probability satisfies the comparison. -/
theorem checkNext_correct (D : DTMC S) (A : Finset S) (s : S) (c : Cmp)
    (q : ℚ) :
    checkNext D.P A s c q = true ↔ c.holds (∑ t ∈ A, D.P s t) q := by
  simp only [checkNext]
  exact cmp_eval_correct _ _ _

/-- The bounded-until checker is exact against the path-sum
semantics. -/
theorem checkBoundedUntil_correct (D : DTMC S) (k : ℕ) (s : S) (c : Cmp)
    (q : ℚ) :
    checkBoundedUntil D.P A B k s c q = true ↔
      c.holds (D.hitProb A B k s) q := by
  simp only [checkBoundedUntil_eq, hitProbC_eq]
  exact cmp_eval_correct _ _ _

/-- Guarded next-step checker: invalid matrices are rejected. -/
def checkNextG (P : S → S → ℚ) (A : Finset S) (s : S) (c : Cmp) (q : ℚ) :
    Bool :=
  if stochastic P then checkNext P A s c q else false

/-- Guarded bounded-until checker: invalid matrices are rejected. -/
def checkBoundedUntilG (P : S → S → ℚ) (A B : Finset S) (k : ℕ) (s : S)
    (c : Cmp) (q : ℚ) : Bool :=
  if stochastic P then checkBoundedUntil P A B k s c q else false

omit [DecidableEq S] in
/-- The guarded next-step checker rejects every invalid matrix. -/
theorem checkNextG_invalid (P : S → S → ℚ) (h : stochastic P = false)
    (A : Finset S) (s : S) (c : Cmp) (q : ℚ) :
    checkNextG P A s c q = false := by
  simp only [checkNextG, h, Bool.false_eq_true, ite_false]

/-- The guarded bounded-until checker rejects every invalid matrix. -/
theorem checkBoundedUntilG_invalid (P : S → S → ℚ)
    (h : stochastic P = false) (k : ℕ) (s : S) (c : Cmp) (q : ℚ) :
    checkBoundedUntilG P A B k s c q = false := by
  simp only [checkBoundedUntilG, h, Bool.false_eq_true, ite_false]

/-- On a genuine chain the guarded next-step checker agrees with the
unguarded one, hence with the semantics. -/
theorem checkNextG_correct (D : DTMC S) (A : Finset S) (s : S) (c : Cmp)
    (q : ℚ) :
    checkNextG D.P A s c q = true ↔ c.holds (∑ t ∈ A, D.P s t) q := by
  simp only [checkNextG, stochastic_complete, ite_true]
  exact checkNext_correct _ _ _ _ _

/-- On a genuine chain the guarded bounded-until checker agrees with
the unguarded one, hence with the path-sum semantics. -/
theorem checkBoundedUntilG_correct (D : DTMC S) (k : ℕ) (s : S) (c : Cmp)
    (q : ℚ) :
    checkBoundedUntilG D.P A B k s c q = true ↔
      c.holds (D.hitProb A B k s) q := by
  simp only [checkBoundedUntilG, stochastic_complete, ite_true]
  exact checkBoundedUntil_correct _ _ _ _ _ _ _

/-- A matrix passing validation is the transition matrix of a genuine
chain. -/
theorem stochastic_sound (P : S → S → ℚ) (h : stochastic P = true) :
    ∃ D : DTMC S, D.P = P := by
  simp only [stochastic, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨P, Matrix.mem_rowStochastic_iff_sum.mpr h⟩, rfl⟩

/-- Tabulated horizon probabilities: the list of values at every
state, in `List.finRange m` order, computed level by level. Each level
is computed once from the previous list, so compiled evaluation takes
about `k * m^2` rational operations. -/
def hitTab {m : ℕ} (P : Fin m → Fin m → ℚ) (A B : Finset (Fin m)) :
    ℕ → List ℚ :=
  hitTabOn P A B ⟨List.finRange m, List.nodup_finRange m, List.mem_finRange⟩

/-- The tabulated value at a state. -/
def lookupTab {m : ℕ} (P : Fin m → Fin m → ℚ) (A B : Finset (Fin m))
    (k : ℕ) (i : Fin m) : ℚ :=
  (hitTab P A B k).getD i.val 0

/-- The tabulated list has one entry per state. -/
theorem hitTab_length {m : ℕ} (P : Fin m → Fin m → ℚ) (A B : Finset (Fin m))
    (k : ℕ) : (hitTab P A B k).length = m := by
  induction k with
  | zero => simp only [hitTab, hitTabOn, List.length_map, List.length_finRange]
  | succ n ih => simp only [hitTab, hitTabOn, List.length_map, List.length_finRange]

/-- The tabulated list is exactly the reference recursion evaluated at
every state. -/
theorem hitTab_eq_map {m : ℕ} (P : Fin m → Fin m → ℚ) (A B : Finset (Fin m))
    (k : ℕ) :
    hitTab P A B k = (List.finRange m).map (fun i => hitProbC P A B k i) :=
  hitTabOn_eq_map P A B _ k

/-- Looking up a state in the table gives the reference recursion. -/
theorem lookupTab_eq {m : ℕ} (P : Fin m → Fin m → ℚ) (A B : Finset (Fin m))
    (k : ℕ) (i : Fin m) :
    lookupTab P A B k i = hitProbC P A B k i := by
  unfold lookupTab
  rw [hitTab_eq_map P A B k]
  have hlt_map : i.val < ((List.finRange m).map (fun j => hitProbC P A B k j)).length := by
    simp only [List.length_map, List.length_finRange]
    exact i.isLt
  have hget : ((List.finRange m).map (fun j => hitProbC P A B k j)).getD i.val 0
      = ((List.finRange m).map (fun j => hitProbC P A B k j))[i.val]'hlt_map :=
    (List.getElem_eq_getD 0).symm
  rw [hget]
  rw [List.getElem_map]
  have hfin : (List.finRange m)[i.val]'(by
      rw [List.length_finRange]
      exact i.isLt) = i := by
    rw [List.getElem_finRange]
    simp
  simp only [hfin]

/-- Bounded-until checking on the tabulated values. -/
def checkBoundedUntilTab {m : ℕ} (P : Fin m → Fin m → ℚ)
    (A B : Finset (Fin m)) (k : ℕ) (i : Fin m) (c : Cmp) (q : ℚ) : Bool :=
  Cmp.eval c (lookupTab P A B k i) q

/-- The tabulated bounded-until checker is exact against the path-sum
semantics. -/
theorem checkBoundedUntilTab_correct {m : ℕ} (D : DTMC (Fin m))
    (A B : Finset (Fin m)) (k : ℕ) (i : Fin m) (c : Cmp) (q : ℚ) :
    checkBoundedUntilTab D.P A B k i c q = true ↔
      c.holds (D.hitProb A B k i) q := by
  simp only [checkBoundedUntilTab, lookupTab_eq, hitProbC_eq]
  exact cmp_eval_correct _ _ _

end Cslib.Probability
