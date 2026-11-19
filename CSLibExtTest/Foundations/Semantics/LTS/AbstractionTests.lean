/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.Abstraction

/-!
# Tests for existential abstraction

Positive safety through the identity abstraction (T1), a spurious abstract
path whose edges are pairwise realizable but admit no single consistent
concrete sequence (T2), and execution mapping (T3). All checks exercise the
public API; abstract safety conclusions are safety (reachability) only: no
liveness and no ACTL* or CEGAR claim.
-/

@[expose] public section

namespace Cslib

namespace LTS

namespace AbstractionTests

/-- T1 concrete system on `Fin 3` with `Unit` labels: edges `0 → 1` and
`1 → 1`, with the label ignored. -/
def lts1 : LTS (Fin 3) Unit where
  Tr := fun s _ t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 1)

/-- T1 multistep induction helper: from `0` or `1`, only `0` or `1` is
reachable. -/
theorem lts1_mtr_inv : ∀ {s : Fin 3} {μs : List Unit} {t : Fin 3},
    lts1.MTr s μs t → (s = 0 ∨ s = 1) → t = 0 ∨ t = 1 := by
  intro s μs t h
  induction h
  case refl s1' =>
    intro hs
    exact hs
  case stepL s1 μ s2 μs' s3 htr hmtr ih =>
    intro hs
    apply ih
    have e : (s1 = 0 ∧ s2 = 1) ∨ (s1 = 1 ∧ s2 = 1) := htr
    rcases hs with rfl | rfl
    · rcases e with ⟨-, h2⟩ | ⟨hc, -⟩
      · exact Or.inr h2
      · exact absurd hc (by decide)
    · rcases e with ⟨hc, -⟩ | ⟨-, h2⟩
      · exact absurd hc (by decide)
      · exact Or.inr h2

/-- T1 reachable invariant: only `0` or `1` is reachable from `0`. -/
theorem lts1_reach_inv : ∀ t, lts1.CanReach 0 t → t = 0 ∨ t = 1 := by
  intro t h
  obtain ⟨μs, hm⟩ := h
  exact lts1_mtr_inv hm (Or.inl rfl)

/-- T1 abstract-side multistep helper under the identity abstraction,
discharged through A1. -/
theorem lts1_abs_mtr_inv : ∀ {s : Fin 3} {μs : List Unit} {a : Fin 3},
    (existsAbs lts1 id).MTr s μs a → (s = 0 ∨ s = 1) → a = 0 ∨ a = 1 := by
  intro s μs a h
  induction h
  case refl s1' =>
    intro hs
    exact hs
  case stepL s1 μ s2 μs' s3 htr hmtr ih =>
    intro hs
    apply ih
    have htr2 := (existsAbs_tr_iff lts1 id s1 μ s2).mp htr
    obtain ⟨sc, tc, hsc, htc, htrc⟩ := htr2
    have hsc' : sc = s1 := hsc
    have htc' : tc = s2 := htc
    rw [← htc']
    rw [← hsc'] at hs
    have e : (sc = 0 ∧ tc = 1) ∨ (sc = 1 ∧ tc = 1) := htrc
    rcases hs with rfl | rfl
    · rcases e with ⟨-, h2⟩ | ⟨hc, -⟩
      · exact Or.inr h2
      · exact absurd hc (by decide)
    · rcases e with ⟨hc, -⟩ | ⟨-, h2⟩
      · exact absurd hc (by decide)
      · exact Or.inr h2

/-- T1 abstract-side reachable invariant. -/
theorem lts1_abs_reach_inv : ∀ a, (existsAbs lts1 id).CanReach 0 a →
    a = 0 ∨ a = 1 := by
  intro a h
  obtain ⟨μs, hm⟩ := h
  exact lts1_abs_mtr_inv hm (Or.inl rfl)

/-- T1 safety through A4: state `2` is unreachable from `0`. -/
theorem lts1_safe : ∀ t, lts1.CanReach 0 t → ¬ t = 2 := by
  have hprem : ∀ a : Fin 3,
      (∃ s₀, s₀ = 0 ∧ (existsAbs lts1 id).CanReach (id s₀) a) →
      ¬ ∃ s, (s = 2) ∧ id s = a := by
    intro a ha
    obtain ⟨s₀, hs0, hreach⟩ := ha
    subst hs0
    rintro ⟨s, hs, hsa⟩
    subst hs
    subst hsa
    have h02 : (existsAbs lts1 id).CanReach 0 2 := hreach
    have hdisj := lts1_abs_reach_inv 2 h02
    rcases hdisj with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  have hSafe :=
    safe_of_existsAbs lts1 id (fun s => s = 0) (fun s => s = 2) hprem
  intro t hReach
  exact hSafe 0 t rfl hReach

/-- T2 concrete system on `Fin 4` with `Fin 2` labels: edges `0 -0→ 1` and
`2 -1→ 3`. -/
def lts4 : LTS (Fin 4) (Fin 2) where
  Tr := fun s μ t => (s = 0 ∧ μ = 0 ∧ t = 1) ∨ (s = 2 ∧ μ = 1 ∧ t = 3)

/-- T2 abstraction map `Fin 4 → Fin 3`: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ 1`,
`3 ↦ 2`. -/
def abs4 : Fin 4 → Fin 3 := fun i =>
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 1 else 2

/-- T2 initial states: `0` only. -/
def init4 : Fin 4 → Prop := fun s => s = 0

/-- T2 abstract path `0 → 1 → 2`. -/
def pathP : ℕ → Fin 3 := fun i => if i = 0 then 0 else if i = 1 then 1 else 2

/-- T2 abstract labels `0, 1, …`. -/
def pathL : ℕ → Fin 2 := fun i => if i = 0 then 0 else 1

/-- T2 first abstract edge, witnessed by `0 -0→ 1` through A1. -/
theorem abs_edge1 : (existsAbs lts4 abs4).Tr 0 0 1 :=
  (existsAbs_tr_iff lts4 abs4 0 0 1).mpr
    ⟨0, 1, by decide, by decide, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- T2 second abstract edge, witnessed by `2 -1→ 3` through A1. -/
theorem abs_edge2 : (existsAbs lts4 abs4).Tr 1 1 2 :=
  (existsAbs_tr_iff lts4 abs4 1 1 2).mpr
    ⟨2, 3, by decide, by decide, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- T2 abstract two-step execution `0 -[0, 1]→ 2`. -/
theorem abs_mtr2 : (existsAbs lts4 abs4).MTr 0 [0, 1] 2 :=
  MTr.stepL abs_edge1 (MTr.single _ abs_edge2)

/-- T2 feasible prefix at index `0`. -/
theorem c0_mem :
    (0 : Fin 4) ∈ constrainedReach lts4 abs4 init4 pathP pathL 0 := by
  rw [mem_constrainedReach_zero]
  refine ⟨rfl, by decide⟩

/-- T2 feasible prefix at index `1`: the discriminating positive, proved
through A6 and not restated from A7. -/
theorem c1_mem :
    (1 : Fin 4) ∈ constrainedReach lts4 abs4 init4 pathP pathL 1 := by
  have hlab : pathL 0 = 0 := by decide
  have htr : lts4.Tr 0 (pathL 0) 1 := by
    rw [hlab]
    exact Or.inl ⟨rfl, rfl, rfl⟩
  have hiff := mem_constrainedReach_succ lts4 abs4 init4 pathP pathL 0 1
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  exact hiff.mpr ⟨by decide, 0, c0_mem, htr⟩

/-- T2 spurious path: the constrained set at index `2` is empty, through
A8. Any realizer would force `ss 1 = 1` then `ss 1 = 2`. -/
theorem c2_empty : constrainedReach lts4 abs4 init4 pathP pathL 2 = ∅ := by
  rw [constrainedReach_eq_empty_iff]
  rintro ⟨ss, hInit, -, hTr⟩
  have h0 : ss 0 = 0 := hInit
  have hT0 := hTr 0 (by omega)
  have hT1 := hTr 1 (by omega)
  have hL0 : pathL 0 = 0 := by decide
  have hL1 : pathL 1 = 1 := by decide
  rw [hL0] at hT0
  rw [hL1] at hT1
  have e0 : (ss 0 = 0 ∧ (0 : Fin 2) = 0 ∧ ss 1 = 1) ∨
      (ss 0 = 2 ∧ (0 : Fin 2) = 1 ∧ ss 1 = 3) := hT0
  have e1 : (ss 1 = 0 ∧ (1 : Fin 2) = 0 ∧ ss 2 = 1) ∨
      (ss 1 = 2 ∧ (1 : Fin 2) = 1 ∧ ss 2 = 3) := hT1
  have hs1a : ss 1 = 1 := by
    rcases e0 with ⟨-, -, h⟩ | ⟨hc, -, -⟩
    · exact h
    · rw [h0] at hc
      exact absurd hc (by decide)
  have hs1b : ss 1 = 2 := by
    rcases e1 with ⟨-, hc, -⟩ | ⟨h, -, -⟩
    · exact absurd hc (by decide)
    · exact h
  rw [hs1a] at hs1b
  exact absurd hs1b (by decide)

/-- T2 no-realizer statement, a direct corollary of A8. -/
theorem no_realizer : ¬ ∃ ss : ℕ → Fin 4, init4 (ss 0) ∧
    (∀ i ≤ 2, abs4 (ss i) = pathP i) ∧
    (∀ i < 2, lts4.Tr (ss i) (pathL i) (ss (i + 1))) :=
  (constrainedReach_eq_empty_iff lts4 abs4 init4 pathP pathL 2).mp c2_empty

/-- T3 mapping of the concrete step `0 -0→ 1` through A3. -/
theorem map_reach : (existsAbs lts4 abs4).CanReach (abs4 0) (abs4 1) := by
  have h01 : lts4.Tr 0 0 1 := Or.inl ⟨rfl, rfl, rfl⟩
  apply existsAbs_canReach
  exact ⟨[0], MTr.single _ h01⟩

/-- T3 instance of A2 at the concrete step `0 -0→ 1`. -/
theorem sim_inst :
    ∃ a', (existsAbs lts4 abs4).Tr (abs4 0) 0 a' ∧ abs4 1 = a' :=
  (isSimulation_existsAbs lts4 abs4) rfl 0 1 (Or.inl ⟨rfl, rfl, rfl⟩)

#guard abs4 2 = 1

#guard abs4 3 = 2

#print axioms lts1_mtr_inv

#print axioms lts1_reach_inv

#print axioms lts1_abs_mtr_inv

#print axioms lts1_abs_reach_inv

#print axioms lts1_safe

#print axioms abs_edge1

#print axioms abs_edge2

#print axioms abs_mtr2

#print axioms c0_mem

#print axioms c1_mem

#print axioms c2_empty

#print axioms no_realizer

#print axioms map_reach

#print axioms sim_inst

end AbstractionTests

end LTS

end Cslib
