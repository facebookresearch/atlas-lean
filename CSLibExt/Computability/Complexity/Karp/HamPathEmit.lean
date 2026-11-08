/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathEmitMachine

/-!
# SAT ≤ HAMPATH, component 2: the diamonds and the emitter theorem

The second half of the emitter machine of `HamPathEmitMachine` (the machine itself, its quiescent
states `MS`, the copy sites and phase A live there). Each diamond (`diamond_run`) is its front
(`N := P + M + 1` and the frame, `dfront_run`), its row (a `for` loop over `M`, `drow_run`), its
detours (a walk over the clauses, `dwalk_run`, comparing each literal's name with the diamond's
variable) and its end (`dback_run`: tokens back to `F`, `P := N + 1`). `diamonds_run` iterates over
`hamVars φ`, `final_run` moves the arcs to `O` and pushes the prefix, and `run` assembles phase A,
the diamonds and the output within `2000 (|toks φ| + 1)⁵` steps.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitHam

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier
open Cslib.Complexity.SatVerifier.Lookup (isBitBlock_map isBitBlock_rev)

/-! ### Diamonds: one-step lemmas and the arc bits of the sites -/

/-- Tokens moved between `T` and `F`. -/
def isTok : Sym → Bool
  | .bit _ | .lit _ | .cl => true
  | _ => false

section DiaSteps

variable (s : MS) (v : Bool)

theorem h0_nil (h : s.v = []) : Run prog 1 ⟨some .h0, v, s.stk⟩ ⟨some .z0, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem h0_cons (x : Sym) (R : List Sym) (h : s.v = x :: R) :
    Run prog 1 ⟨some .h0, v, s.stk⟩ ⟨some .h1, false, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem h5_step : Run prog 1 ⟨some .h5, v, s.stk⟩
    ⟨some (.cpA .f1u false), v, {s with n := s.n + 1}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_N, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem r2_step : Run prog 1 ⟨some .r2, v, s.stk⟩ ⟨some .r3, v, {s with r := s.r + 1}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_R, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem wi_step : Run prog 1 ⟨some .wi, v, s.stk⟩ ⟨some .r3, v, {s with r := s.r + 1}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_R, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem e2_step : Run prog 1 ⟨some .e2, v, s.stk⟩
    ⟨some (.dw false false), v, {s with d := s.d + 2}.stk⟩ :=
  Run.single (by
    simp only [prog, stepAux_pushList, TM2.stepAux, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, stk_D, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem dw_nil (pp pn : Bool) (h : s.f = []) :
    Run prog 1 ⟨some (.dw pp pn), v, s.stk⟩ ⟨some .t0, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem dw_cl (pp pn : Bool) (R : List Sym) (h : s.f = .cl :: R) :
    Run prog 1 ⟨some (.dw pp pn), v, s.stk⟩ ⟨some (clEnd pp pn), true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem dw_lit (pp pn : Bool) (x : Sym) (R : List Sym) (h : s.f = x :: R) (hx : x ≠ .cl) :
    Run prog 1 ⟨some (.dw pp pn), v, s.stk⟩ ⟨some (.dk pp pn), false, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h, hx])

theorem dl_step (pp pn b q : Bool) (R : List Sym) (h : s.f = .lit q :: R) :
    Run prog 1 ⟨some (.dl pp pn b), v, s.stk⟩
      ⟨some (.dw (pp || (b && q)) (pn || (b && !q))), q,
        {s with f := R, t := .lit q :: s.t}.stk⟩ :=
  Run.single (by cases q <;> simp [prog, TM2.stepAux, h])

theorem dj_step (R : List Sym) (h : s.f = .cl :: R) :
    Run prog 1 ⟨some .dj, v, s.stk⟩ ⟨some (.dw false false), v,
      { s with f := R, t := .cl :: s.t, j := s.j + 1, d := s.d + 3 }.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_F, h, List.tail_cons, upd_F, ne_eq, reduceCtorEq,
      not_false_eq_true, update_of_ne, stk_T, upd_T, stk_J, stepAux_pushList, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, stk_D, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem t0_nil (h : s.t = []) : Run prog 1 ⟨some .t0, v, s.stk⟩ ⟨some .t1, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem t0_step (x : Sym) (hx : isTok x = true) (R : List Sym) (h : s.t = x :: R) :
    ∃ v', Run prog 1 ⟨some .t0, v, s.stk⟩ ⟨some .t0, v', {s with t := R, f := x :: s.f}.stk⟩ := by
  cases x with
  | bit b => exact ⟨b, Run.single (by cases b <;> simp [prog, TM2.stepAux, h, isBit, bitOf,
      Sym.bit?])⟩
  | lit q => exact ⟨q, Run.single (by cases q <;> simp [prog, TM2.stepAux, h, isBit, Sym.bit?])⟩
  | cl => exact ⟨true, Run.single (by simp [prog, TM2.stepAux, h])⟩
  | _ => simp [isTok] at hx

theorem t2_step (R : List Sym) (h : s.v = .cl :: R) :
    Run prog 1 ⟨some .t2, v, s.stk⟩ ⟨some .t3, v, {s with v := R}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem t5_step : Run prog 1 ⟨some .t5, v, s.stk⟩ ⟨some .t6, v, {s with p := s.p + 1}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_P, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

end DiaSteps

theorem frame_bits (s : MS) (m i : ℕ) (hp : s.p = hpT m i) (hn : s.n = hpR m i (3 * m)) :
    ([Site.f1u, .f1v, .f2u, .f2v, .f3u, .f3v, .f4u, .f4v].map (atom s)).flatten =
      Karp.edgeBits (frameE m i) := by
  simp [atom, Site.src, Site.ext, MS.val, frameE, Karp.edgeBits, hp, hn, hpT_succ_eq_hpR, hpR]

theorem row_bits (s : MS) (m i l : ℕ) (hr : s.r = hpR m i l) :
    ([Site.w1u, .w1v, .w2u, .w2v].map (atom s)).flatten = Karp.edgeBits (rowE m i l) := by
  simp [atom, Site.src, Site.ext, MS.val, rowE, Karp.edgeBits, hr, hpR_succ]

theorem pos_bits (s : MS) (m i j : ℕ) (hd : s.d = hpR m i (3 * j + 1)) (hj : s.j = j) :
    ([Site.d1u, .d1v, .d2u, .d2v].map (atom s)).flatten =
      Karp.edgeBits [(hpR m i (3 * j + 1), j), (j, hpR m i (3 * j + 2))] := by
  simp [atom, Site.src, Site.ext, MS.val, Karp.edgeBits, hd, hj, hpR_two]

theorem neg_bits (s : MS) (m i j : ℕ) (hd : s.d = hpR m i (3 * j + 1)) (hj : s.j = j) :
    ([Site.d3u, .d3v, .d4u, .d4v].map (atom s)).flatten =
      Karp.edgeBits [(hpR m i (3 * j + 2), j), (j, hpR m i (3 * j + 1))] := by
  simp [atom, Site.src, Site.ext, MS.val, Karp.edgeBits, hd, hj, hpR_two]

/-! ### Diamonds: the detour walk -/

theorem litToks_head (l : ℕ × Bool) : ∃ x R, litToks l = x :: R ∧ x ≠ .cl := by
  obtain ⟨z, b⟩ := l
  cases h : encodeNat z with
  | nil => exact ⟨.lit b, [], by simp [litToks, h], by simp⟩
  | cons c t => exact ⟨.bit c, t.map Sym.bit ++ [Sym.lit b], by simp [litToks, h], by simp⟩

/-- One literal of the detour walk: compare its name with the entry `y`, update the flags, move
its tokens to `T`. -/
theorem dlit_run (y : ℕ) (VR : List Sym) (l : ℕ × Bool) (R : List Sym) (pp pn : Bool) (s : MS)
    (v : Bool) (hf : s.f = litToks l ++ R) (hv : s.v = name y ++ Sym.cl :: VR) (hx : s.x = []) :
    ∃ v', RunLe prog (3 * (encodeNat y).length + (litToks l).length + 5)
      ⟨some (.dw pp pn), v, s.stk⟩
      ⟨some (.dw (pp || (decide (l.1 = y) && l.2)) (pn || (decide (l.1 = y) && !l.2))), v',
        {s with f := R, t := (litToks l).reverse ++ s.t}.stk⟩ := by
  obtain ⟨z, b⟩ := l
  obtain ⟨x0, R0, h0, hx0⟩ := litToks_head (z, b)
  have r₁ := dw_lit s v pp pn x0 (R0 ++ R) (by simp [hf, h0]) hx0
  obtain ⟨v₂, r₂⟩ := cmpR_run (lc := .dk pp pn) (r1 := .dr1 pp pn) (r2 := .dr2 pp pn)
    (nx := .dm pp pn) (bT := true) (bF := false) rfl (fun _ => rfl) (fun _ => rfl) s false
    (encodeNat z) (encodeNat y) (Sym.lit b :: R) (Sym.cl :: VR) rfl rfl
    (by simp [hf, litToks]) (by simp [hv]) hx
  have hbm : (if encodeNat z = encodeNat y then true else false) = decide (z = y) := by
    by_cases h : z = y
    · subst h; simp
    · have : encodeNat z ≠ encodeNat y := fun e => h (encodeNat_inj.1 e)
      simp [this, h]
  rw [hbm] at r₂
  obtain ⟨v₃, S₃, r₃, h3F, h3T, h3k⟩ := moveB_run (M := prog) (self := .dm pp pn (decide (z = y)))
    (next := .dl pp pn (decide (z = y))) (a := .F) (b := .T) (d := Sym.bit?) (g := Sym.bit) rfl
    (by decide) (encodeNat z) (name z) (Sym.lit b :: R) v₂ s.stk (by simp [hf, litToks])
    (isBitBlock_map _) rfl
  have hS₃ : S₃ = {s with f := Sym.lit b :: R, t := (name z).reverse ++ s.t}.stk := by
    funext k; cases k <;> simp [h3F, h3T, h3k]
  rw [hS₃] at r₃
  have r₄ := dl_step {s with f := Sym.lit b :: R, t := (name z).reverse ++ s.t} v₃ pp pn
    (decide (z = y)) b R rfl
  refine ⟨b, runLe_cast ((r₁.le le_rfl).trans (r₂.trans ((r₃.trans r₄).le le_rfl))) ?_ ?_⟩
  · simp [litToks]; omega
  · simp [litToks]

/-- The literals `Ls` of a clause: the flags collect the occurrences of `y`. -/
theorem dlits_run (y : ℕ) (VR : List Sym) (R : List Sym) :
    ∀ (Ls : List (ℕ × Bool)) (pp pn : Bool) (s : MS) (v : Bool),
      s.f = Ls.flatMap litToks ++ R → s.v = name y ++ Sym.cl :: VR → s.x = [] →
      ∃ v', RunLe prog ((Ls.flatMap litToks).length * (3 * (encodeNat y).length + 6))
        ⟨some (.dw pp pn), v, s.stk⟩
        ⟨some (.dw (pp || decide ((y, true) ∈ Ls)) (pn || decide ((y, false) ∈ Ls))), v',
          {s with f := R, t := (Ls.flatMap litToks).reverse ++ s.t}.stk⟩ := by
  intro Ls
  induction Ls with
  | nil =>
      intro pp pn s v hf _ _
      have e : ({s with f := R} : MS) = s := by cases s; simp_all
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by simp [e])⟩
  | cons l Ls ih =>
      intro pp pn s v hf hv hx
      obtain ⟨v₁, r₁⟩ := dlit_run y VR l (Ls.flatMap litToks ++ R) pp pn s v (by simp [hf]) hv hx
      obtain ⟨v₂, r₂⟩ := ih (pp || (decide (l.1 = y) && l.2)) (pn || (decide (l.1 = y) && !l.2))
        {s with f := Ls.flatMap litToks ++ R, t := (litToks l).reverse ++ s.t} v₁ rfl hv hx
      rw [flag_pos, flag_neg] at r₂
      have hl : 1 ≤ (litToks l).length := by simp [litToks]
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ ?_⟩
      · simp only [List.flatMap_cons, List.length_append]; nlinarith
      · simp

theorem clEnd_run (Bd : ℕ) (pp pn : Bool) (s : MS) (v : Bool) (hB : ∀ u, s.val u ≤ Bd) :
    ∃ v', RunLe prog (8 * (2 * Bd + 3)) ⟨some (clEnd pp pn), v, s.stk⟩
      ⟨some .dj, v', {s with q := s.q ++
        (if pp then ([Site.d1u, .d1v, .d2u, .d2v].map (atom s)).flatten else []) ++
        (if pn then ([Site.d3u, .d3v, .d4u, .d4v].map (atom s)).flatten else [])}.stk⟩ := by
  have hneg : ∀ (s' : MS) (v' : Bool), (∀ u, s'.val u ≤ Bd) → ∃ v'', RunLe prog (4 * (2 * Bd + 3))
      ⟨some (.cpA .d3u false), v', s'.stk⟩
      ⟨some .dj, v'', {s' with q := s'.q ++
        ([Site.d3u, .d3v, .d4u, .d4v].map (atom s')).flatten}.stk⟩ := fun s' v' hB' => by
    obtain ⟨v'', r⟩ := chain_run [.d3u, .d3v, .d4u, .d4v] s' false (.cpA .d3u false) .dj rfl v'
    exact ⟨v'', (r.le le_rfl).mono (chainCost_le s' Bd hB' _)⟩
  cases pp <;> cases pn
  · exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by simp [clEnd])⟩
  · obtain ⟨v', r⟩ := hneg s v hB
    exact ⟨v', runLe_cast r (by omega) (by simp)⟩
  · obtain ⟨v', r⟩ := chain_run [.d1u, .d1v, .d2u, .d2v] s false (clEnd true false) .dj rfl v
    exact ⟨v', runLe_cast ((r.le le_rfl).mono (chainCost_le s Bd hB _)) (by simp)
      (by simp)⟩
  · obtain ⟨v₁, r₁⟩ := chain_run [.d1u, .d1v, .d2u, .d2v] s true (clEnd true true)
      (.cpA .d3u false) rfl v
    set s₁ := {s with q := s.q ++ ([Site.d1u, .d1v, .d2u, .d2v].map (atom s)).flatten}
    obtain ⟨v₂, r₂⟩ := hneg s₁ v₁ (fun u => by
      have := hB u; cases u <;> simpa [s₁, MS.val] using this)
    rw [atom_q] at r₂
    refine ⟨v₂, runLe_cast (((r₁.le le_rfl).mono (chainCost_le s Bd hB _)).trans r₂)
      (by simp; omega) (by simp [s₁, List.append_assoc])⟩

theorem detE_bits (s : MS) (m i y j : ℕ) (C : CNFClause) (hd : s.d = hpR m i (3 * j + 1))
    (hj : s.j = j) :
    (if decide ((y, true) ∈ C) then ([Site.d1u, .d1v, .d2u, .d2v].map (atom s)).flatten
        else []) ++
      (if decide ((y, false) ∈ C) then ([Site.d3u, .d3v, .d4u, .d4v].map (atom s)).flatten
        else []) = Karp.edgeBits (detE m i y j C) := by
  rw [pos_bits s m i j hd hj, neg_bits s m i j hd hj]
  by_cases h1 : (y, true) ∈ C <;> by_cases h2 : (y, false) ∈ C <;>
    simp [detE, h1, h2, ← HamVerify.edgeBits_append]

/-- One clause of the detour walk: its detours are pushed, its tokens go to `T`. -/
theorem dclause_run (Bd m dI y j : ℕ) (C : CNFClause) (R VR : List Sym) (s : MS) (v : Bool)
    (hf : s.f = clauseToks C ++ R) (hv : s.v = name y ++ Sym.cl :: VR) (hx : s.x = [])
    (hj : s.j = j) (hd : s.d = hpR m dI (3 * j + 1)) (hB : ∀ u, s.val u ≤ Bd)
    (hy : (encodeNat y).length ≤ Bd) :
    ∃ v', RunLe prog ((clauseToks C).length * (3 * Bd + 6) + 16 * Bd + 26)
      ⟨some (.dw false false), v, s.stk⟩
      ⟨some (.dw false false), v', { s with
        f := R, t := (clauseToks C).reverse ++ s.t, j := j + 1, d := s.d + 3,
        q := s.q ++ Karp.edgeBits (detE m dI y j C) }.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := dlits_run y VR (Sym.cl :: R) C false false s v
    (by simp [hf, clauseToks]) hv hx
  simp only [Bool.false_or] at r₁
  set s₁ : MS := {s with f := Sym.cl :: R, t := (C.flatMap litToks).reverse ++ s.t}
  have r₂ := dw_cl s₁ v₁ (decide ((y, true) ∈ C)) (decide ((y, false) ∈ C)) R rfl
  obtain ⟨v₃, r₃⟩ := clEnd_run Bd (decide ((y, true) ∈ C)) (decide ((y, false) ∈ C)) s₁ true
    (fun u => by have := hB u; cases u <;> simpa [s₁, MS.val] using this)
  set s₃ : MS := {s₁ with q := s₁.q ++
    (if decide ((y, true) ∈ C) then ([Site.d1u, .d1v, .d2u, .d2v].map (atom s₁)).flatten
      else []) ++
    (if decide ((y, false) ∈ C) then ([Site.d3u, .d3v, .d4u, .d4v].map (atom s₁)).flatten
      else [])}
  have r₄ := dj_step s₃ v₃ R rfl
  have hbits := detE_bits s₁ m dI y j C hd hj
  refine ⟨v₃, runLe_cast (r₁.trans (((r₂.le le_rfl).trans r₃).trans (r₄.le le_rfl))) ?_ ?_⟩
  · have := Nat.mul_le_mul_right (C.flatMap litToks).length
      (show 3 * (encodeNat y).length + 6 ≤ 3 * Bd + 6 by omega)
    simp only [clauseToks, List.length_append, List.length_singleton]
    nlinarith
  · simp only [s₃, s₁, List.append_assoc] at hbits ⊢
    rw [hbits]
    simp [clauseToks, hj]

/-- The detour walk over the clauses `post`, the clauses `pre` already walked. -/
theorem dwalk_run (Bd m dI y : ℕ) (φ : CNF) (hm : φ.length = m) (VR : List Sym)
    (q0 : List Bool) (hy : (encodeNat y).length ≤ Bd) (hR : hpR m dI (3 * m) ≤ Bd) :
    ∀ (post pre : CNF), φ = pre ++ post → ∀ (s : MS) (v : Bool), s.f = toks post →
      s.t = (toks pre).reverse → s.v = name y ++ Sym.cl :: VR → s.x = [] →
      s.j = pre.length → s.d = hpR m dI (3 * pre.length + 1) →
      s.q = q0 ++ Karp.edgeBits ((List.range pre.length).flatMap
        (fun j => detE m dI y j (φ.getD j []))) →
      s.p ≤ Bd → s.n ≤ Bd → s.r ≤ Bd →
      ∃ v', RunLe prog ((toks post).length * (3 * Bd + 6) + post.length * (16 * Bd + 26) + 1)
        ⟨some (.dw false false), v, s.stk⟩
        ⟨some .t0, v', { s with
          f := [], t := (toks φ).reverse, j := m, d := hpR m dI (3 * m + 1),
          q := q0 ++ Karp.edgeBits ((List.range m).flatMap
            (fun j => detE m dI y j (φ.getD j []))) }.stk⟩ := by
  intro post
  induction post with
  | nil =>
      intro pre hφ s v hf ht _ _ hj hd hq _ _ _
      rw [List.append_nil] at hφ
      subst hφ
      have r := dw_nil s v false false (by simp [hf, toks])
      have e : ({ s with
          f := [], t := (toks φ).reverse, j := m, d := hpR m dI (3 * m + 1),
          q := q0 ++ Karp.edgeBits ((List.range m).flatMap
            (fun j => detE m dI y j (φ.getD j []))) } : MS) = s := by
        subst hm
        cases s; simp_all [toks]
      exact ⟨true, runLe_cast (r.le le_rfl) (by omega) (by rw [e])⟩
  | cons C post ih =>
      intro pre hφ s v hf ht hv hx hj hd hq hp hn hr
      have hlen : pre.length + 1 + post.length = m := by
        rw [← hm, hφ]; simp; omega
      obtain ⟨v₁, r₁⟩ := dclause_run Bd m dI y pre.length C (toks post) VR s v
        (by rw [hf, toks_cons]) hv hx hj hd (fun u => by
          cases u
          · exact hp
          · exact hn
          · exact hr
          · simp only [MS.val, hj]
            have : m ≤ hpR m dI (3 * m) := by unfold hpR hpT; omega
            omega
          · simp only [MS.val, hd]
            exact le_trans (hpR_mono m dI _ _ (by omega)) hR) hy
      obtain ⟨v₂, r₂⟩ := ih (pre ++ [C]) (by rw [hφ]; simp) { s with
        f := toks post, t := (clauseToks C).reverse ++ s.t, j := pre.length + 1, d := s.d + 3,
        q := s.q ++ Karp.edgeBits (detE m dI y pre.length C) } v₁ rfl
        (by simp [ht, toks]) hv hx (by simp) (by simp [hd, hpR]; omega)
        (by
          simp only [hq, List.length_append, List.length_singleton, List.append_assoc]
          rw [hφ, range_flatMap_getD (fun j C => detE m dI y j C) pre C post]
          simp [HamVerify.edgeBits_append])
        hp hn hr
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ (by simp)⟩
      simp [toks_cons]
      nlinarith

/-! ### Diamonds: frame and row -/

/-- The frame sites. -/
def frameSites : List Site := [.f1u, .f1v, .f2u, .f2v, .f3u, .f3v, .f4u, .f4v]

/-- The row sites. -/
def rowSites : List Site := [.w1u, .w1v, .w2u, .w2v]

/-- The head of a diamond: `N := P + M + 1`, then the frame. -/
theorem dfront_run (Bd m dI : ℕ) (s : MS) (v : Bool) (x0 : Sym) (R0 : List Sym)
    (hv : s.v = x0 :: R0) (hp : s.p = hpT m dI) (hmm : s.mm = 3 * m) (hn : s.n = 0)
    (hr : s.r ≤ Bd) (hj : s.j ≤ Bd) (hd : s.d ≤ Bd) (hB : hpR m dI (3 * m) ≤ Bd) :
    ∃ v', RunLe prog (20 * Bd + 30) ⟨some .h0, v, s.stk⟩
      ⟨some .r0, v', { s with
        n := hpR m dI (3 * m), q := s.q ++ Karp.edgeBits (frameE m dI) }.stk⟩ := by
  have r₁ := h0_cons s v x0 R0 hv
  obtain ⟨v₂, r₂⟩ := cp_run (a := .P) (c := .N) Sym.cl Sym.cl (by decide) (by decide)
    (by decide) (l₁ := .h1) (l₂ := .h2) (next := .h3) rfl rfl s.p false s.stk rfl rfl
  have e₂ : update s.stk .N (cnt Sym.cl s.p ++ s.stk .N) = {s with n := s.p}.stk := by
    funext k; cases k <;> simp [hn]
  rw [e₂] at r₂
  obtain ⟨v₃, r₃⟩ := cp_run (a := .M) (c := .N) Sym.cl Sym.cl (by decide) (by decide)
    (by decide) (l₁ := .h3) (l₂ := .h4) (next := .h5) rfl rfl s.mm v₂ {s with n := s.p}.stk
    rfl rfl
  have e₃ : update {s with n := s.p}.stk .N (cnt Sym.cl s.mm ++ {s with n := s.p}.stk .N) =
      {s with n := s.mm + s.p}.stk := by
    funext k; cases k <;> simp
  rw [e₃] at r₃
  have r₄ := h5_step {s with n := s.mm + s.p} v₃
  set s₄ : MS := {s with n := s.mm + s.p + 1}
  have hn₄ : s₄.n = hpR m dI (3 * m) := by simp [s₄, hp, hmm, hpR]; omega
  obtain ⟨v₅, r₅⟩ := chain_run frameSites s₄ false (.cpA .f1u false) .r0 rfl v₃
  have hc := chainCost_le s₄ Bd (fun u => by
    have := hpT_le_hpR m dI (3 * m)
    cases u
    · change s.p ≤ Bd; omega
    · rw [MS.val, hn₄]; exact hB
    · exact hr
    · exact hj
    · exact hd) frameSites
  have hfb := frame_bits s₄ m dI (by simp [s₄, hp]) hn₄
  simp only [frameSites] at r₅
  rw [hfb] at r₅
  have hB' : hpT m dI + 1 + 3 * m ≤ Bd := by simpa [hpR] using hB
  simp only [frameSites, List.length_cons, List.length_nil] at hc
  refine ⟨v₅, runLe_cast ((((r₁.trans r₂).trans r₃).trans r₄).le le_rfl |>.trans (r₅.le hc))
    ?_ ?_⟩
  · rw [hp, hmm]; omega
  · have es₄ : s₄ = {s with n := hpR m dI (3 * m)} := by rw [← hn₄]
    rw [es₄]

/-- The row loop: from `r3` with `R = hpR m dI 0`, push the row arcs for `l < 3 m`. -/
theorem drow_run (Bd m dI : ℕ) (s : MS) (v : Bool) (hmm : s.mm = 3 * m) (hl : s.l = 0)
    (hr : s.r = hpR m dI 0) (hp : s.p ≤ Bd) (hn : s.n ≤ Bd) (hj : s.j ≤ Bd) (hd : s.d ≤ Bd)
    (hB : hpR m dI (3 * m) ≤ Bd) (hmB : 3 * m ≤ Bd) :
    ∃ v', RunLe prog (Bd * (8 * Bd + 15) + 2) ⟨some .r3, v, s.stk⟩
      ⟨some .e0, v', { s with
        r := hpR m dI (3 * m),
        q := s.q ++ Karp.edgeBits ((List.range (3 * m)).flatMap (rowE m dI)) }.stk⟩ := by
  let rs : ℕ → MS := fun i => { s with
    r := hpR m dI i, q := s.q ++ Karp.edgeBits ((List.range i).flatMap (rowE m dI)) }
  let P : ℕ → (∀ k, List (Γ k)) → Prop := fun i S => ∀ k, k ≠ .M → k ≠ .L → S k = (rs i).stk k
  have hval : ∀ i, i ≤ 3 * m → ∀ u, (rs i).val u ≤ Bd := fun i hi u => by
    have := hpR_mono m dI i (3 * m) hi
    cases u <;> simp [MS.val, rs] <;> omega
  obtain ⟨S', hrun, hSc, hScd, hPn⟩ := forLoop_run (M := prog) (c := .M) (cd := .L)
    (uc := Sym.cl) (ucd := Sym.cl) (head := .r3) (body := .cpA .w1u false) (rest := .r4)
    (next := .e0) rfl rfl (by decide) (3 * m) P
    (fun i S S' h hP k h1 h2 => by rw [h k h1 h2, hP k h1 h2])
    (fun i => chainCost (rs i) rowSites + 1)
    (fun i hi S hSc hScd hP => by
      have hS : S = { rs i with mm := 3 * m - 1 - i, l := i + 1 }.stk := by
        funext k
        cases k <;> first | exact hSc | exact hScd | exact hP _ (by decide) (by decide)
      subst hS
      set s₁ : MS := { rs i with mm := 3 * m - 1 - i, l := i + 1 } with hs₁
      obtain ⟨v₁, r₁⟩ := chain_run rowSites s₁ false (.cpA .w1u false) .wi rfl true
      have r₂ := wi_step { s₁ with q := s₁.q ++ (rowSites.map (atom s₁)).flatten } v₁
      refine ⟨v₁, _, (r₁.trans r₂).of_eq rfl, rfl, rfl, fun k h1 h2 => ?_⟩
      have hb : (rowSites.map (atom s₁)).flatten = Karp.edgeBits (rowE m dI i) :=
        row_bits _ m dI i rfl
      rw [hb]
      cases k <;> simp_all [rs, List.range_succ, List.flatMap_append, hpR_succ,
        HamVerify.edgeBits_append])
    v s.stk (by simp [hmm]) (by simp [hl]) (fun k h1 h2 => by
      have e : rs 0 = s := by simp only [rs]; cases s; simp_all
      rw [e])
  have hS' : S' = (rs (3 * m)).stk := by
    funext k
    cases k <;> first | (simp only [hSc]; simp [rs, hmm]) | (simp only [hScd]; simp [rs, hl]) |
      exact hPn _ (by decide) (by decide)
  rw [hS'] at hrun
  refine ⟨_, runLe_cast (hrun.le le_rfl) ?_ rfl⟩
  have hsum := sumFrom_le (f := fun i => chainCost (rs i) rowSites + 1 + 1)
    (c := 4 * (2 * Bd + 3) + 2) 0 (3 * m) (fun t _ ht => by
      have := chainCost_le (rs t) Bd (hval t (by omega)) rowSites
      simp [rowSites] at this ⊢; omega)
  have : 3 * m * (4 * (2 * Bd + 3) + 2) ≤ Bd * (8 * Bd + 14) := by nlinarith
  have : Bd * (8 * Bd + 15) = Bd * (8 * Bd + 14) + Bd := by
    rw [show 8 * Bd + 15 = (8 * Bd + 14) + 1 by omega, Nat.mul_add, Nat.mul_one]
  omega

/-! ### Diamonds: assembly -/

theorem addU_nil (i : ℕ) (S : ∀ k, List (Γ k)) : addU [] i S = S := by
  funext k; simp [addU]

/-- Drain a counter. -/
theorem drain_run {k : K} {self next : Lab} (h : prog self = xfer k [] self next) (u : Γ k)
    (n : ℕ) (v : Bool) (S : ∀ k, List (Γ k)) (hS : S k = cnt u n) :
    Run prog (n + 1) ⟨some self, v, S⟩ ⟨some next, false, update S k []⟩ := by
  have := xfer_run h (by simp) (by simp) u n v S hS
  rwa [addU_nil] at this

/-- Move `T` back onto `F`. -/
theorem t0_run : ∀ (L : List Sym), (∀ x ∈ L, isTok x = true) → ∀ (s : MS) (v : Bool),
    s.t = L → ∃ v', Run prog (L.length + 1) ⟨some .t0, v, s.stk⟩
      ⟨some .t1, v', {s with t := [], f := L.reverse ++ s.f}.stk⟩ := by
  intro L
  induction L with
  | nil =>
      intro _ s v h
      have e : ({s with t := [], f := ([] : List Sym).reverse ++ s.f} : MS) = s := by
        cases s; simp_all
      exact ⟨true, by rw [e]; exact t0_nil s v h⟩
  | cons x L ih =>
      intro hL s v h
      obtain ⟨v₁, r₁⟩ := t0_step s v x (hL x (by simp)) L h
      obtain ⟨v₂, r₂⟩ := ih (fun y hy => hL y (by simp [hy])) {s with t := L, f := x :: s.f} v₁
        rfl
      exact ⟨v₂, by simpa [Nat.add_comm] using r₁.trans r₂⟩

theorem isTok_toks (φ : CNF) : ∀ x ∈ (toks φ).reverse, isTok x = true := by
  intro x hx
  simp only [List.mem_reverse, toks, clauseToks, litToks, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_singleton] at hx
  obtain ⟨_, -, ⟨_, -, ⟨b, -, rfl⟩ | rfl⟩ | rfl⟩ := hx <;> rfl

/-- The row: `R := P + 1`, then the loop. -/
theorem drowFull_run (Bd m dI : ℕ) (s : MS) (v : Bool) (hp : s.p = hpT m dI)
    (hmm : s.mm = 3 * m) (hl : s.l = 0) (hr : s.r = 0) (hn : s.n ≤ Bd) (hj : s.j ≤ Bd)
    (hd : s.d ≤ Bd) (hB : hpR m dI (3 * m) ≤ Bd) :
    ∃ v', RunLe prog (Bd * (8 * Bd + 15) + 2 * Bd + 5) ⟨some .r0, v, s.stk⟩
      ⟨some .e0, v', { s with
        r := hpR m dI (3 * m),
        q := s.q ++ Karp.edgeBits ((List.range (3 * m)).flatMap (rowE m dI)) }.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := cp_run (a := .P) (c := .R) Sym.cl Sym.cl (by decide) (by decide)
    (by decide) (l₁ := .r0) (l₂ := .r1) (next := .r2) rfl rfl s.p v s.stk rfl rfl
  have e₁ : update s.stk .R (cnt Sym.cl s.p ++ s.stk .R) = {s with r := s.p}.stk := by
    funext k; cases k <;> simp [hr]
  rw [e₁] at r₁
  have r₂ := r2_step {s with r := s.p} v₁
  have hB' : hpT m dI + 1 + 3 * m ≤ Bd := by simpa [hpR] using hB
  obtain ⟨v₃, r₃⟩ := drow_run Bd m dI {s with r := s.p + 1} v₁ hmm hl (by simp [hp, hpR])
    (by simp [hp]; omega) hn hj hd hB (by omega)
  refine ⟨v₃, runLe_cast (((r₁.trans r₂).le le_rfl).trans r₃) (by rw [hp]; omega) (by simp)⟩

/-- The detours: `D := P + 2`, then the walk over all clauses. -/
theorem ddet_run (Bd dI y : ℕ) (φ : CNF) (VR : List Sym) (s : MS) (v : Bool)
    (hf : s.f = toks φ) (ht : s.t = []) (hv : s.v = name y ++ Sym.cl :: VR) (hx : s.x = [])
    (hp : s.p = hpT φ.length dI) (hj : s.j = 0) (hd : s.d = 0) (hn : s.n ≤ Bd) (hr : s.r ≤ Bd)
    (hy : (encodeNat y).length ≤ Bd) (hB : hpR φ.length dI (3 * φ.length) ≤ Bd) :
    ∃ v', RunLe prog ((toks φ).length * (3 * Bd + 6) + φ.length * (16 * Bd + 26) + 2 * Bd + 5)
      ⟨some .e0, v, s.stk⟩
      ⟨some .t0, v', { s with
        f := [], t := (toks φ).reverse, j := φ.length, d := hpR φ.length dI (3 * φ.length + 1),
        q := s.q ++ Karp.edgeBits ((List.range φ.length).flatMap
          (fun j => detE φ.length dI y j (φ.getD j []))) }.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := cp_run (a := .P) (c := .D) Sym.cl Sym.cl (by decide) (by decide)
    (by decide) (l₁ := .e0) (l₂ := .e1) (next := .e2) rfl rfl s.p v s.stk rfl rfl
  have e₁ : update s.stk .D (cnt Sym.cl s.p ++ s.stk .D) = {s with d := s.p}.stk := by
    funext k; cases k <;> simp [hd]
  rw [e₁] at r₁
  have r₂ := e2_step {s with d := s.p} v₁
  have hpB : s.p ≤ Bd := by rw [hp]; exact le_trans (hpT_le_hpR _ _ _) hB
  obtain ⟨v₃, r₃⟩ := dwalk_run Bd φ.length dI y φ rfl VR s.q hy hB φ [] (by simp)
    {s with d := s.p + 2} v₁ hf (by simp [ht, toks]) hv hx hj (by simp [hp, hpR])
    (by simp) hpB hn hr
  refine ⟨v₃, runLe_cast (((r₁.trans r₂).le le_rfl).trans r₃) (by omega) (by simp)⟩

/-- The end of a diamond: tokens back to `F`, drop the entry, `P := N + 1`, clear the
counters. -/
theorem dback_run (φ : CNF) (y : ℕ) (VR : List Sym) (s : MS) (v : Bool)
    (ht : s.t = (toks φ).reverse) (hf : s.f = []) (hv : s.v = name y ++ Sym.cl :: VR) :
    ∃ v', Run prog ((toks φ).length + (encodeNat y).length + s.n + s.p + s.r + s.j + s.d + 9)
      ⟨some .t0, v, s.stk⟩
      ⟨some .h0, v', { s with
        t := [], f := toks φ, v := VR, g := (name y).reverse ++ s.g, p := s.n + 1, n := 0,
        r := 0, j := 0, d := 0 }.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := t0_run (toks φ).reverse (isTok_toks φ) s v ht
  set s₁ : MS := {s with t := [], f := (toks φ).reverse.reverse ++ s.f}
  obtain ⟨v₂, S₂, r₂, h2V, h2G, h2k⟩ := moveB_run (M := prog) (self := .t1) (next := .t2)
    (a := .V) (b := .G) (d := Sym.bit?) (g := Sym.bit) rfl (by decide) (encodeNat y) (name y)
    (Sym.cl :: VR) v₁ s₁.stk (by simp [s₁, hv]) (isBitBlock_map _) rfl
  have hS₂ : S₂ = {s₁ with v := Sym.cl :: VR, g := (name y).reverse ++ s.g}.stk := by
    funext k; cases k <;> simp [h2V, h2G, h2k, s₁]
  rw [hS₂] at r₂
  have r₃ := t2_step {s₁ with v := Sym.cl :: VR, g := (name y).reverse ++ s.g} v₂ VR rfl
  set s₃ : MS := {s₁ with v := VR, g := (name y).reverse ++ s.g}
  have r₄ := drain_run (self := .t3) (next := .t4) (k := .P) rfl Sym.cl s.p v₂ s₃.stk rfl
  have r₅ := xfer_run (M := prog) (self := .t4) (next := .t5) (k := .N) (ps := [⟨.P, Sym.cl⟩])
    rfl (by simp) (by simp) Sym.cl s.n false (update s₃.stk .P []) rfl
  have e₅ : addU ([⟨K.P, Sym.cl⟩] : List (Σ k, Γ k)) s.n (update (update s₃.stk .P []) .N []) =
      {s₃ with p := s.n, n := 0}.stk := by
    funext k
    by_cases hk : k = .P
    · subst hk; rw [addU_single_self]; simp
    · rw [addU_single_ne _ _ _ hk]; cases k <;> simp_all
  rw [e₅] at r₅
  have r₆ := t5_step {s₃ with p := s.n, n := 0} false
  set s₆ : MS := {s₃ with p := s.n + 1, n := 0}
  have r₇ := drain_run (self := .t6) (next := .t7) (k := .R) rfl Sym.cl s.r false s₆.stk rfl
  have r₈ := drain_run (self := .t7) (next := .t8) (k := .J) rfl Sym.cl s.j false
    (update s₆.stk .R []) (by rw [update_of_ne (by decide)]; rfl)
  have hD9 : (update (update s₆.stk .R []) .J []) K.D = cnt Sym.cl s.d := by
    rw [update_of_ne (by decide), update_of_ne (by decide)]; rfl
  have r₉ := drain_run (self := .t8) (next := .h0) (k := .D) rfl Sym.cl s.d false
    (update (update s₆.stk .R []) .J []) hD9
  have efin : update (update (update s₆.stk .R []) .J []) .D [] = { s with
      t := [], f := toks φ, v := VR, g := (name y).reverse ++ s.g, p := s.n + 1, n := 0,
      r := 0, j := 0, d := 0 }.stk := by
    funext k; cases k <;> simp [s₆, s₃, s₁, hf]
  have r := (((((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).trans r₇).trans
    r₈).trans r₉
  rw [efin] at r
  exact ⟨false, r.of_eq (by simp; omega)⟩

theorem vstk_cons (y : ℕ) (ys : List ℕ) : vstk (y :: ys) = name y ++ Sym.cl :: vstk ys := by
  simp [vstk]

/-- **One diamond**: from `h0` with the entry `y` on top of `V`, push the arcs of diamond `dI`
and advance `P` to the next diamond top. -/
theorem diamond_run (Bd : ℕ) (φ : CNF) (dI y : ℕ) (ys : List ℕ) (s : MS) (v : Bool)
    (ht : s.t = []) (hf : s.f = toks φ) (hv : s.v = vstk (y :: ys)) (hx : s.x = [])
    (hp : s.p = hpT φ.length dI) (hmm : s.mm = 3 * φ.length) (hn : s.n = 0) (hr : s.r = 0)
    (hl : s.l = 0) (hj : s.j = 0) (hd : s.d = 0) (hBd : hpT φ.length (dI + 1) ≤ Bd)
    (hy : (encodeNat y).length ≤ Bd) (hL : (toks φ).length ≤ Bd) :
    ∃ v', RunLe prog (30 * Bd * Bd + 100 * Bd + 100) ⟨some .h0, v, s.stk⟩
      ⟨some .h0, v', { s with
        v := vstk ys, p := hpT φ.length (dI + 1), q := s.q ++ Karp.edgeBits (diamondEdges φ dI y),
        g := (name y).reverse ++ s.g }.stk⟩ := by
  set m := φ.length with hm
  have hB : hpR m dI (3 * m) ≤ Bd := by rw [hpT_succ_eq_hpR] at hBd; omega
  have hv' : s.v = name y ++ Sym.cl :: vstk ys := by rw [hv, vstk_cons]
  obtain ⟨x0, R0, hx0⟩ : ∃ x0 R0, s.v = x0 :: R0 := by
    rw [hv']
    cases h : encodeNat y with
    | nil => exact ⟨Sym.cl, vstk ys, by simp [name, h]⟩
    | cons b t => exact ⟨Sym.bit b, t.map Sym.bit ++ Sym.cl :: vstk ys, by simp [name, h]⟩
  obtain ⟨v₁, r₁⟩ := dfront_run Bd m dI s v x0 R0 hx0 hp hmm hn (by omega) (by omega) (by omega)
    hB
  set s₁ : MS := { s with n := hpR m dI (3 * m), q := s.q ++ Karp.edgeBits (frameE m dI) }
  obtain ⟨v₂, r₂⟩ := drowFull_run Bd m dI s₁ v₁ hp hmm hl hr hB (by simp [s₁, hj])
    (by simp [s₁, hd]) hB
  set s₂ : MS := { s₁ with
    r := hpR m dI (3 * m), q := s₁.q ++ Karp.edgeBits ((List.range (3 * m)).flatMap (rowE m dI)) }
  obtain ⟨v₃, r₃⟩ := ddet_run Bd dI y φ (vstk ys) s₂ v₂ hf ht hv' hx hp hj hd hB hB hy hB
  set s₃ : MS := { s₂ with
    f := [], t := (toks φ).reverse, j := φ.length, d := hpR φ.length dI (3 * φ.length + 1),
    q := s₂.q ++ Karp.edgeBits ((List.range φ.length).flatMap
      (fun j => detE φ.length dI y j (φ.getD j []))) }
  obtain ⟨v₄, r₄⟩ := dback_run φ y (vstk ys) s₃ v₃ rfl rfl hv'
  have hlm := length_le_toks φ
  have hd3 : hpR m dI (3 * m + 1) = hpT m (dI + 1) := by rw [hpT_succ_eq_hpR, hpR_succ]
  refine ⟨v₄, runLe_cast ((r₁.trans r₂).trans (r₃.trans (r₄.le le_rfl))) ?_ ?_⟩
  · simp only [s₃, s₂, s₁, hp]
    have h1 := Nat.mul_le_mul_right (3 * Bd + 6) hL
    have h2 := Nat.mul_le_mul_right (16 * Bd + 26) (le_trans hlm hL)
    have h3 : hpT m dI ≤ Bd := le_trans (hpT_le_hpR _ _ _) hB
    nlinarith
  · simp only [s₃, s₂, s₁, diamondEdges_eq, HamVerify.edgeBits_append, List.append_assoc]
    rw [hpT_succ_eq_hpR, ht, hf, hn, hr, hj, hd]

/-- **The diamonds**: from `h0` with the variables `ys` left on `V` (`pre` already done), push
the remaining diamonds. -/
theorem diamonds_run (Bd : ℕ) (φ : CNF) (hBd : hpT φ.length (hamVars φ).length ≤ Bd)
    (hL : (toks φ).length ≤ Bd) (hnm : ∀ y ∈ hamVars φ, (encodeNat y).length ≤ Bd) :
    ∀ (ys pre : List ℕ), hamVars φ = pre ++ ys → ∀ (s : MS) (v : Bool), s.t = [] →
      s.f = toks φ → s.v = vstk ys → s.x = [] → s.p = hpT φ.length pre.length →
      s.mm = 3 * φ.length → s.n = 0 → s.r = 0 → s.l = 0 → s.j = 0 → s.d = 0 →
      s.q = Karp.edgeBits ((List.range pre.length).flatMap
        (fun i => diamondEdges φ i ((hamVars φ).getD i 0))) →
      ∃ v' g', RunLe prog (ys.length * (30 * Bd * Bd + 100 * Bd + 100)) ⟨some .h0, v, s.stk⟩
        ⟨some .h0, v', { s with
          v := [], p := hpT φ.length (hamVars φ).length, q := Karp.edgeBits (hamEdges φ),
          g := g' }.stk⟩ := by
  intro ys
  induction ys with
  | nil =>
      intro pre hpre s v ht hf hv hx hp hmm hn hr hl hj hd hq
      rw [List.append_nil] at hpre
      have e : ({ s with
          v := [], p := hpT φ.length (hamVars φ).length, q := Karp.edgeBits (hamEdges φ),
          g := s.g } : MS) = s := by
        rw [← hpre] at hp hq
        cases s; simp_all [vstk, hamEdges]
      exact ⟨v, s.g, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by rw [e])⟩
  | cons y ys ih =>
      intro pre hpre s v ht hf hv hx hp hmm hn hr hl hj hd hq
      have hk : (hamVars φ).length = pre.length + 1 + ys.length := by rw [hpre]; simp; omega
      obtain ⟨v₁, r₁⟩ := diamond_run Bd φ pre.length y ys s v ht hf hv hx hp hmm hn hr hl hj hd
        (le_trans (Karp.hpT_mono (by omega)) hBd) (hnm y (by rw [hpre]; simp)) hL
      obtain ⟨v₂, g₂, r₂⟩ := ih (pre ++ [y]) (by rw [hpre]; simp) { s with
        v := vstk ys, p := hpT φ.length (pre.length + 1),
        q := s.q ++ Karp.edgeBits (diamondEdges φ pre.length y), g := (name y).reverse ++ s.g } v₁
        ht hf rfl hx (by simp) hmm hn hr hl hj hd (by
          have hy : (hamVars φ).getD pre.length 0 = y := by
            rw [hpre]; simp [List.getD_eq_getElem?_getD]
          simp only [hq, List.length_append, List.length_singleton, List.range_succ,
            List.flatMap_append, List.flatMap_singleton, hy, HamVerify.edgeBits_append])
      refine ⟨v₂, g₂, runLe_cast (r₁.trans r₂) (by simp only [List.length_cons]; nlinarith) rfl⟩

/-- **The output**: move the arcs to `O`, then push `n = t + 1`, `t = P` and `s = C`. -/
theorem final_run (s : MS) (v : Bool) (hv : s.v = []) :
    ∃ v' S', Run prog (s.q.length + 4 * s.p + 2 * s.c + 11) ⟨some .h0, v, s.stk⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = List.replicate s.c true ++ false ::
        (List.replicate s.p true ++ false :: (List.replicate (s.p + 1) true ++ false ::
          (s.q ++ s.o))) := by
  have r₁ := h0_nil s v hv
  obtain ⟨v₂, S₂, r₂, h2Q, h2O, h2k⟩ := moveB_run (M := prog) (self := .z0) (next := .z1)
    (a := .Q) (b := .O) (d := Sym.bit?) (g := id) rfl (by decide) s.q.reverse
    (s.q.reverse.map Sym.bit) [] true s.stk (by simp) (isBitBlock_map _) rfl
  have hS₂ : S₂ = {s with q := [], o := s.q ++ s.o}.stk := by
    funext k; cases k <;> simp [h2Q, h2O, h2k]
  rw [hS₂] at r₂
  set s₂ : MS := {s with q := [], o := s.q ++ s.o}
  have r₃ : Run prog 1 ⟨some .z1, v₂, s₂.stk⟩
      ⟨some .z2, v₂, {s₂ with o := true :: false :: s₂.o}.stk⟩ :=
    Run.single (by simp [prog, TM2.stepAux, stepAux_pushList])
  set s₃ : MS := {s₂ with o := true :: false :: s₂.o}
  obtain ⟨v₄, r₄⟩ := cp_run (a := .P) (c := .O) Sym.cl true (by decide) (by decide) (by decide)
    (l₁ := .z2) (l₂ := .z3) (next := .z4) rfl rfl s.p v₂ s₃.stk rfl rfl
  rw [upd_O] at r₄
  set s₄ : MS := {s₃ with o := cnt true s.p ++ s₃.stk .O}
  have r₅ : Run prog 1 ⟨some .z4, v₄, s₄.stk⟩
      ⟨some .z5, v₄, {s₄ with o := false :: s₄.o}.stk⟩ :=
    Run.single (by simp [prog, TM2.stepAux])
  set s₅ : MS := {s₄ with o := false :: s₄.o}
  obtain ⟨v₆, r₆⟩ := cp_run (a := .P) (c := .O) Sym.cl true (by decide) (by decide) (by decide)
    (l₁ := .z5) (l₂ := .z6) (next := .z7) rfl rfl s.p v₄ s₅.stk rfl rfl
  rw [upd_O] at r₆
  set s₆ : MS := {s₅ with o := cnt true s.p ++ s₅.stk .O}
  have r₇ : Run prog 1 ⟨some .z7, v₆, s₆.stk⟩
      ⟨some .z8, v₆, {s₆ with o := false :: s₆.o}.stk⟩ :=
    Run.single (by simp [prog, TM2.stepAux])
  set s₇ : MS := {s₆ with o := false :: s₆.o}
  obtain ⟨v₈, r₈⟩ := cp_run (a := .C) (c := .O) Sym.cl true (by decide) (by decide) (by decide)
    (l₁ := .z8) (l₂ := .z9) (next := .done) rfl rfl s.c v₆ s₇.stk rfl rfl
  refine ⟨v₈, _, ((((((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).trans r₇).trans
    r₈)).of_eq (by simp; omega), ?_⟩
  simp [s₇, s₆, s₅, s₄, s₃, s₂, List.replicate_succ']

/-! ### Sizes -/

/-- **The emitter.** From `start`, with the token stack `(toks φ).reverse`, the output stack `o`
and every other stack empty, the machine reaches `done` within `2000 (|toks φ| + 1)⁵` steps with
Sipser's HAMPATH instance `toHam φ` pushed on the output stack (read top-first). -/
theorem run (φ : CNF) (o : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hT : St .T = (toks φ).reverse) (hO : St .O = o) (h0 : ∀ k, k ≠ .T → k ≠ .O → St k = []) :
    ∃ v' S', RunLe prog (2000 * ((toks φ).length + 1) ^ 5) ⟨some start, v, St⟩
      ⟨some .done, v', S'⟩ ∧ S' .O = toHam φ ++ o := by
  have hSt : St = (initMS φ o).stk := by
    funext k
    cases k <;> first | exact hT | exact hO | exact h0 _ (by decide) (by decide)
  set L := (toks φ).length with hL
  set k := (hamVars φ).length with hk
  set m := φ.length with hm
  set N := L + 1 with hN
  have hkL : k ≤ L := le_trans (List.dedup_sublist _).length_le (length_varsOf_le φ)
  have hmL : m ≤ L := length_le_toks φ
  have hT2 : hpT m k ≤ 4 * N * N := by
    simp only [hpT]
    have := Nat.mul_le_mul hkL (show 3 * m + 2 ≤ 3 * L + 2 by omega)
    nlinarith
  have hnm : ∀ y ∈ hamVars φ, (encodeNat y).length ≤ 4 * N * N := fun y hy => by
    have := name_le φ y (List.mem_dedup.1 hy); nlinarith
  obtain ⟨v₁, r₁⟩ := phaseA_run φ o v
  obtain ⟨v₂, g₂, r₂⟩ := diamonds_run (4 * N * N) φ hT2 (by nlinarith) hnm (hamVars φ) []
    (by simp) (diaMS φ o) v₁ rfl rfl rfl rfl (by simp [diaMS, hpT]) rfl rfl rfl rfl rfl rfl
    (by simp [diaMS])
  set s₂ : MS := { diaMS φ o with
    v := [], p := hpT m k, q := Karp.edgeBits (hamEdges φ), g := g₂ }
  obtain ⟨v₃, S₃, r₃, hO₃⟩ := final_run s₂ v₂ rfl
  refine ⟨v₃, S₃, ?_, ?_⟩
  · rw [hSt]
    refine (r₁.trans (r₂.trans (r₃.le le_rfl))).mono ?_
    change L * (8 * L + 12) + 2 * m + 3 + (k * (30 * (4 * N * N) * (4 * N * N) +
      100 * (4 * N * N) + 100) + ((Karp.edgeBits (hamEdges φ)).length + 4 * hpT m k + 2 * m + 11))
        ≤ 2000 * N ^ 5
    have hq := q_length φ
    have hN1 : 1 ≤ N := by omega
    have hkN : k ≤ N := by omega
    have hmN : m ≤ N := by omega
    have hLN : L ≤ N := by omega
    have hq' : (Karp.edgeBits (hamEdges φ)).length ≤ 140 * (N * N * N * N) := by
      have h1 : 10 * m + 4 ≤ 14 * N := by omega
      have h2 : 2 * hpT m k + 2 ≤ 10 * (N * N) := by nlinarith
      have h3 := Nat.mul_le_mul (Nat.mul_le_mul hkN h1) h2
      nlinarith
    have hA : L * (8 * L + 12) + 2 * m + 3 ≤ 25 * (N * N) := by nlinarith
    have hD : k * (30 * (4 * N * N) * (4 * N * N) + 100 * (4 * N * N) + 100) ≤
        N * (480 * (N * N * N * N) + 400 * (N * N) + 100) := by
      apply Nat.mul_le_mul hkN; nlinarith
    have p2 : N ^ 1 ≤ N ^ 2 := Nat.pow_le_pow_right hN1 (by norm_num)
    have p3 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN1 (by norm_num)
    have p4 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by norm_num)
    have p5 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right hN1 (by norm_num)
    have p1 : 1 ≤ N ^ 1 := by simpa using hN1
    nlinarith
  · rw [hO₃, toHam_eq]
    simp [s₂, diaMS, hm, hk]

end Cslib.Complexity.Karp.EmitHam
