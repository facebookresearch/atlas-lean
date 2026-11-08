/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathCheck
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import Mathlib.Tactic.Linarith

/-!
# SAT ≤ HAMPATH: the construction in the order the emitter builds it

Spec-side lemmas for the emitter machine `Cslib.Complexity.Karp.EmitHam`: the instance as
unary blocks and arc bits (`toHam_eq`, through `Karp.edgeBits`), a diamond's arcs split into its
frame (`frameE`), its row (`rowE`) and the detours of each clause (`detE`), and the distinct
variables as a right fold that inserts a name when it is new (`foldr_insV`), the order in which
the machine meets the names on the token stack. The last section bounds the vertex numbers and
sizes the step count needs: every arc of `hamEdges φ` has both ends at most `hpT m k`
(`hamEdges_bound`), there are at most `k (10 m + 4)` arcs (`hamEdges_length`), an edge list with
ends at most `B` has at most `2 B + 2` bits per edge (`edgeBits_length_le`), and names are
shorter than the token list (`name_le`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitHam

open Cslib.CookLevin Cslib.Logic.PL Computability Cslib.Complexity.SatVerifier

/-- The instance: `s = m`, `t`, `n = t + 1` in unary, then the arcs. -/
theorem toHam_eq (φ : CNF) : toHam φ = List.replicate φ.length true ++ false ::
    (List.replicate (hpT φ.length (hamVars φ).length) true ++ false ::
      (List.replicate (hpT φ.length (hamVars φ).length + 1) true ++ false ::
        Karp.edgeBits (hamEdges φ))) := by
  simp [toHam, Path.encodeP, encodeE, hpT]; rfl

/-- The frame of diamond `i`. -/
def frameE (m i : ℕ) : List (ℕ × ℕ) :=
  [(hpT m i, hpR m i 0), (hpT m i, hpR m i (3 * m)), (hpR m i 0, hpT m (i + 1)),
    (hpR m i (3 * m), hpT m (i + 1))]

/-- The two row arcs between row vertices `l` and `l + 1` of diamond `i`. -/
def rowE (m i l : ℕ) : List (ℕ × ℕ) := [(hpR m i l, hpR m i (l + 1)), (hpR m i (l + 1), hpR m i l)]

/-- The detours of clause `j` (contents `C`) in diamond `i` of variable `x`. -/
def detE (m i x j : ℕ) (C : CNFClause) : List (ℕ × ℕ) :=
  (if (x, true) ∈ C then [(hpR m i (3 * j + 1), j), (j, hpR m i (3 * j + 2))] else []) ++
    (if (x, false) ∈ C then [(hpR m i (3 * j + 2), j), (j, hpR m i (3 * j + 1))] else [])

theorem diamondEdges_eq (φ : CNF) (i x : ℕ) : diamondEdges φ i x =
    frameE φ.length i ++ (List.range (3 * φ.length)).flatMap (rowE φ.length i) ++
      (List.range φ.length).flatMap fun j => detE φ.length i x j (φ.getD j []) := rfl

/-- The next diamond top is the row end plus one. -/
theorem hpT_succ_eq_hpR (m i : ℕ) : hpT m (i + 1) = hpR m i (3 * m) + 1 := by
  simp only [hpT, hpR, Nat.add_mul, Nat.one_mul]; omega

/-- The detours of the clauses `pre ++ post`, indexed from `0`: those of `pre`, then those of
`post` from `pre.length`. -/
theorem range_flatMap_getD {α : Type} (f : ℕ → CNFClause → List α) (pre : CNF) (C : CNFClause)
    (post : CNF) :
    (List.range (pre.length + 1)).flatMap (fun j => f j ((pre ++ C :: post).getD j [])) =
      (List.range pre.length).flatMap (fun j => f j ((pre ++ C :: post).getD j [])) ++
        f pre.length C := by
  rw [List.range_succ, List.flatMap_append]
  simp

/-- Insert a name when it is new. -/
def insV (x : ℕ) (vs : List ℕ) : List ℕ := if x ∈ vs then vs else x :: vs

/-- The distinct variables are the right fold of `insV`. -/
theorem foldr_insV (l : List ℕ) : l.foldr insV [] = l.dedup := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldr_cons, ih, insV]
      by_cases h : a ∈ l
      · simp only [List.mem_dedup.2 h, ite_true, List.dedup_cons_of_mem h]
      · simp only [mt List.mem_dedup.1 h, ite_false, List.dedup_cons_of_notMem h]

theorem hamVars_eq (φ : CNF) : hamVars φ = (varsOf φ).foldr insV [] := (foldr_insV _).symm

theorem varsOf_cons (C : CNFClause) (φ : CNF) : varsOf (C :: φ) = C.map Prod.fst ++ varsOf φ := by
  simp [varsOf]

/-! ### Arithmetic of the vertex numbers, tokens, sizes -/

theorem hpR_succ (m i l : ℕ) : hpR m i (l + 1) = hpR m i l + 1 := by simp [hpR]; omega

theorem hpR_two (m i j : ℕ) : hpR m i (3 * j + 2) = hpR m i (3 * j + 1) + 1 := hpR_succ _ _ _

theorem hpR_mono (m i l l' : ℕ) (h : l ≤ l') : hpR m i l ≤ hpR m i l' := by
  simp [hpR]; omega

theorem hpT_le_hpR (m i l : ℕ) : hpT m i ≤ hpR m i l := by simp [hpR]; omega

theorem toks_append (φ ψ : CNF) : toks (φ ++ ψ) = toks φ ++ toks ψ := by
  simp [toks, List.flatMap_append]

theorem toks_cons (C : CNFClause) (φ : CNF) : toks (C :: φ) = clauseToks C ++ toks φ := by
  simp [toks]

theorem length_le_toks (φ : CNF) : φ.length ≤ (toks φ).length := by
  induction φ with
  | nil => simp
  | cons C φ ih => simp [toks_cons, clauseToks]; omega

theorem foldr_lits (C : CNFClause) (vs : List ℕ) :
    C.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs = (C.map Prod.fst).foldr insV vs := by
  simp [List.foldr_map]

theorem flag_pos (pp : Bool) (y : ℕ) (l : ℕ × Bool) (Ls : List (ℕ × Bool)) :
    ((pp || (decide (l.1 = y) && l.2)) || decide ((y, true) ∈ Ls)) =
      (pp || decide ((y, true) ∈ l :: Ls)) := by
  obtain ⟨z, b⟩ := l
  by_cases h : z = y
  · subst h; cases b <;> cases pp <;> simp
  · have h' : y ≠ z := Ne.symm h
    cases b <;> cases pp <;> simp [h, h']

theorem flag_neg (pn : Bool) (y : ℕ) (l : ℕ × Bool) (Ls : List (ℕ × Bool)) :
    ((pn || (decide (l.1 = y) && !l.2)) || decide ((y, false) ∈ Ls)) =
      (pn || decide ((y, false) ∈ l :: Ls)) := by
  obtain ⟨z, b⟩ := l
  by_cases h : z = y
  · subst h; cases b <;> cases pn <;> simp
  · have h' : y ≠ z := Ne.symm h
    cases b <;> cases pn <;> simp [h, h']

/-- The bits of an edge list whose ends are at most `B`: at most `2 B + 2` per edge. -/
theorem edgeBits_length_le (B : ℕ) : ∀ (es : List (ℕ × ℕ)), (∀ e ∈ es, e.1 ≤ B ∧ e.2 ≤ B) →
    (Karp.edgeBits es).length ≤ es.length * (2 * B + 2) := by
  intro es
  induction es with
  | nil => simp
  | cons e es ih =>
      intro h
      have h1 := h e (by simp)
      have h2 := ih (fun e' he' => h e' (by simp [he']))
      obtain ⟨u, v⟩ := e
      simp only [HamVerify.edgeBits_cons, List.length_append, List.length_replicate,
        List.length_cons] at h1 ⊢
      nlinarith

theorem detE_length (m i x j : ℕ) (C : CNFClause) : (detE m i x j C).length ≤ 4 := by
  unfold detE; split_ifs <;> simp

/-- Mathlib's `List.sum_le_length_nsmul` for a mapped list. -/
private theorem sum_map_le {α : Type} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ a ∈ l, f a ≤ c) : (l.map f).sum ≤ l.length * c := by
  simpa using List.sum_le_length_nsmul (l.map f) c (by simpa using h)

theorem diamondEdges_length (φ : CNF) (i x : ℕ) :
    (diamondEdges φ i x).length ≤ 10 * φ.length + 4 := by
  rw [diamondEdges_eq]
  simp only [List.length_append, List.length_flatMap, frameE, rowE, List.length_cons,
    List.length_nil]
  have h := sum_map_le (List.range φ.length)
    (fun j => (detE φ.length i x j (φ.getD j [])).length) 4
    (fun j _ => detE_length _ _ _ _ _)
  have h2 := sum_map_le (List.range (3 * φ.length)) (fun _ => 0 + 1 + 1) 2 (fun _ _ => le_refl _)
  simp only [List.length_range] at h h2
  omega

theorem diamondEdges_bound (φ : CNF) (i x : ℕ) :
    ∀ e ∈ diamondEdges φ i x, e.1 ≤ hpT φ.length (i + 1) ∧ e.2 ≤ hpT φ.length (i + 1) := by
  intro e he
  rw [diamondEdges_eq] at he
  have h1 : hpT φ.length (i + 1) = hpT φ.length i + 3 * φ.length + 2 := by
    rw [hpT_succ_eq_hpR]; simp [hpR]; omega
  rw [h1]
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, frameE, rowE, detE,
    List.mem_cons, List.not_mem_nil, or_false] at he
  have hmT : φ.length ≤ hpT φ.length i := by simp [hpT]
  rcases he with ((h | h | h | h) | ⟨l, hl, h | h⟩) | ⟨j, hj, h⟩
  · subst h; simp [hpR]; omega
  · subst h; simp [hpR]; omega
  · subst h; simp [hpR]; omega
  · subst h; simp [hpR]; omega
  · subst h; simp [hpR]; omega
  · subst h; simp [hpR]; omega
  · rcases h with h | h <;> split_ifs at h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      rcases h with rfl | rfl <;> simp [hpR] <;> omega

theorem hamEdges_length (φ : CNF) :
    (hamEdges φ).length ≤ (hamVars φ).length * (10 * φ.length + 4) := by
  unfold hamEdges
  rw [List.length_flatMap]
  have := sum_map_le (List.range (hamVars φ).length)
    (fun i => (diamondEdges φ i ((hamVars φ).getD i 0)).length) (10 * φ.length + 4)
    (fun i _ => diamondEdges_length _ _ _)
  simpa using this

theorem hamEdges_bound (φ : CNF) : ∀ e ∈ hamEdges φ,
    e.1 ≤ hpT φ.length (hamVars φ).length ∧ e.2 ≤ hpT φ.length (hamVars φ).length := by
  intro e he
  simp only [hamEdges, List.mem_flatMap, List.mem_range] at he
  obtain ⟨i, hi, he⟩ := he
  have := diamondEdges_bound φ i _ e he
  have hm := Karp.hpT_mono (m := φ.length) (i := i + 1) (i' := (hamVars φ).length) hi
  omega

theorem q_length (φ : CNF) : (Karp.edgeBits (hamEdges φ)).length ≤
    (hamVars φ).length * (10 * φ.length + 4) * (2 * hpT φ.length (hamVars φ).length + 2) :=
  le_trans (edgeBits_length_le _ _ (hamEdges_bound φ)) (Nat.mul_le_mul_right _ (hamEdges_length φ))

theorem lits_le (C : CNFClause) : C.length ≤ (C.flatMap litToks).length := by
  induction C with
  | nil => simp
  | cons l C ih => simp [litToks]; omega

theorem litToks_le (C : CNFClause) : ∀ l ∈ C, (litToks l).length ≤ (C.flatMap litToks).length := by
  induction C with
  | nil => simp
  | cons l' C ih =>
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp
      · have := ih l hl; simp only [List.flatMap_cons, List.length_append]; omega

theorem length_varsOf_le (φ : CNF) : (varsOf φ).length ≤ (toks φ).length := by
  induction φ with
  | nil => simp [varsOf]
  | cons C φ ih =>
      have := lits_le C
      simp only [varsOf_cons, toks_cons, clauseToks, List.length_append, List.length_map,
        List.length_singleton] at ih ⊢
      omega

theorem name_le (φ : CNF) : ∀ y ∈ varsOf φ, (encodeNat y).length ≤ (toks φ).length := by
  induction φ with
  | nil => simp [varsOf]
  | cons C φ ih =>
      intro y hy
      rw [varsOf_cons, List.mem_append] at hy
      simp only [toks_cons, clauseToks, List.length_append, List.length_singleton]
      rcases hy with hy | hy
      · simp only [List.mem_map] at hy
        obtain ⟨l, hl, rfl⟩ := hy
        have h1 := litToks_le C l hl
        have h2 : (litToks l).length = (encodeNat l.1).length + 1 := by simp [litToks]
        omega
      · have := ih y hy; omega

end Cslib.Complexity.Karp.EmitHam
