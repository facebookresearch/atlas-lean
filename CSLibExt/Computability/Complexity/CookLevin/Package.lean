/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Pkg.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Pkg.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, the reduction stated with the identity output encoding, and the final hardness step
rewritten against formal-math definitions (`Hardness.lean`); module docstring rewritten for this
repository (the source's notes and status lines dropped), missing docstrings added, long lines
wrapped.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Precompute

/-!
# Cook-Levin: halting cleanup and packaging of the reduction machine

`Precompute.full_run` stops at the host's `fin` label with the formula on the output stack, but
`TM2OutputsInTime` needs the run to end in exactly `haltList` (label `none`, initial state, every
other stack empty).

* Generic stack growth for any `FinTM2`: `run_height` (from `Situation.runI_of_iterate` and
  `Situation.runI_height`).
* A generic drain phase: `xfer_drain`, `drainS`, `drain_run`.
* The composed machine `gprog`/`gTM` (the full machine relabelled, `fin` redirected to the
  drain) and `g_run`: initial configuration to `haltList (encodeCNF (Phi …))`, no hypotheses.
* `g_outputs` and `gComp`: the reduction as `TM2ComputableInPolyTime ea (fun l => l) (fR …)`,
  parametric in the verifier data.
-/

@[expose] public section



namespace Cslib.Complexity.CookLevin.Package

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Cslib.Complexity.CookLevin.Precompute Turing Function

/-! ## [GROW] Generic stack growth -/

section Grow

open Cslib.Complexity.CookLevin.Situation

theorem run_height {M : FinTM2} {n : ℕ} {c d : M.Cfg} (h : Run M.m n c d) (k : M.K) :
    (d.stk k).length ≤ (c.stk k).length + n * depth M := by
  rw [← runI_of_iterate M n c d h]
  exact runI_height c k n

end Grow

/-! ## [DRAIN] A generic drain phase -/

section Drain

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [Flag σ]
  {M : Λ → TM2.Stmt Γ Λ σ}

/-- `xfer k []` empties stack `k` whatever it holds, in `|S k| + 1` steps. -/
theorem xfer_drain {self next : Λ} {k : K} (hp : M self = xfer k [] self next) :
    ∀ (l : List (Γ k)) (v : σ) (S : ∀ k, List (Γ k)), S k = l →
      Run M (l.length + 1) ⟨some self, v, S⟩ ⟨some next, Flag.tag false, update S k []⟩ := by
  intro l
  induction l with
  | nil =>
      intro v S hS
      have hu : update S k [] = S := by rw [← hS, update_eq_self]
      refine Run.single ?_
      simp only [hp, xfer, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, List.tail_nil,
        Flag.untag_tag, Bool.cond_false, hu]
  | cons x l ih =>
      intro v S hS
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some self, Flag.tag true, update S k l⟩ := by
        simp only [TM2.step, hp, xfer, TM2.stepAux, hS, List.head?_cons, Option.isSome_some,
          List.tail_cons, Flag.untag_tag, Bool.cond_true, pushAll, List.foldr_nil]
      have key := Run.head hstep (ih (Flag.tag true) (update S k l) (by simp))
      rw [update_idem] at key
      exact key.of_eq (by simp)

/-- The drain program: stage `i < |ks|` empties `ks[i]`; stage `|ks|` resets the state and halts. -/
def drainS (ks : List K) (lab : ℕ → Λ) (i : ℕ) : TM2.Stmt Γ Λ σ :=
  match ks[i]? with
  | some k => xfer k [] (lab i) (lab (i + 1))
  | none => .load (fun _ => Flag.tag false) .halt

/-- Steps of the drain. -/
def drainB (ks : List K) (S : ∀ k, List (Γ k)) : ℕ :=
  (ks.map fun k => (S k).length + 1).sum + 1

/-- **The drain.** Empties every stack of `ks` and halts with state `tag false`. -/
theorem drain_run :
    ∀ (ks : List K) (lab : ℕ → Λ), ks.Nodup → (∀ i ≤ ks.length, M (lab i) = drainS ks lab i) →
      ∀ (v : σ) (S : ∀ k, List (Γ k)),
        Run M (drainB ks S) ⟨some (lab 0), v, S⟩
          ⟨none, Flag.tag false, fun k => if k ∈ ks then [] else S k⟩ := by
  intro ks
  induction ks with
  | nil =>
      intro lab _ hp v S
      refine Run.single ?_
      rw [hp 0 le_rfl]
      simp [drainS, TM2.stepAux]
  | cons k ks ih =>
      intro lab hnd hp v S
      rw [List.nodup_cons] at hnd
      have r1 := xfer_drain (M := M) (self := lab 0) (next := lab 1) (k := k)
        (by rw [hp 0 (by simp)]; rfl) (S k) v S rfl
      have r2 := ih (fun j => lab (j + 1)) hnd.2 (fun i hi => by
        rw [hp (i + 1) (by simp; omega)]; rfl) (Flag.tag false) (update S k [])
      have e1 : drainB ks (update S k []) = drainB ks S := by
        unfold drainB
        congr 2
        refine List.map_congr_left fun k' hk' => ?_
        rw [update_of_ne (fun h : k' = k => hnd.1 (h ▸ hk'))]
      have e2 : (fun k' => if k' ∈ ks then [] else update S k [] k') =
          fun k' => if k' ∈ k :: ks then [] else S k' := by
        funext k'
        by_cases h1 : k' = k
        · subst h1; simp
        · by_cases h2 : k' ∈ ks <;> simp [h1, h2]
      rw [e1, e2] at r2
      exact (r1.trans r2).of_eq (by simp [drainB]; omega)

end Drain

/-! ## [GLUE] The composed machine: full machine, then the drain -/

section Glue

/-- Labels of the composed machine: the full machine's, and the drain stages `0..n`. -/
inductive DL (Λ : Type) (n : ℕ)
  | f (l : Λ)
  | dr (i : Fin (n + 1))
  deriving DecidableEq, Fintype

/-- Drain stage `j` (clamped to `n`). -/
def dlab {Λ : Type} (n j : ℕ) : DL Λ n := .dr ⟨min j n, by omega⟩

/-- The identity stack embedding (pure relabelling). -/
def idE {K : Type} (Γ : K → Type) : SEmb Γ Γ := ⟨id, injective_id, fun _ => Equiv.refl _⟩

/-- Stacks emptied by the drain: every stack except the output. -/
noncomputable def dks : List FK := (Finset.univ.erase (FK.h .out)).toList

theorem mem_dks (q : FK) : q ∈ dks ↔ q ≠ FK.h .out := by simp [dks]

theorem dks_nodup : dks.Nodup := Finset.nodup_toList _

/-- After the drain only the output stack survives. -/
theorem drained {Γ : FK → Type} (T : ∀ k, List (Γ k)) :
    (fun q => if q ∈ dks then [] else T q) = fun q => if q = FK.h .out then T q else [] := by
  funext q
  by_cases hq : q = FK.h .out
  · rw [ite_eq_left hq, ite_eq_right (by rw [mem_dks]; exact not_not.2 hq)]
  · rw [ite_eq_right hq, ite_eq_left ((mem_dks q).2 hq)]

variable {g r : ℕ} {Λ : Type} [DecidableEq Λ]

/-- **The composed program**: the program `P` relabelled, except that its halting label `fin`
jumps to the drain. -/
noncomputable def gprog (P : Λ → TM2.Stmt (FΓ g r) Λ Bool) (fin : Λ) :
    DL Λ dks.length → TM2.Stmt (FΓ g r) (DL Λ dks.length) Bool
  | .f l => if l = fin then .goto (fun _ => dlab _ 0) else mapS (idE _) DL.f (P l)
  | .dr i => drainS dks (dlab _) i.val

theorem embeds_g {P : Λ → TM2.Stmt (FΓ g r) Λ Bool} {fin : Λ} (hfin : P fin = .halt) :
    Embeds (idE (FΓ g r)) DL.f P (gprog P fin) := by
  intro l
  by_cases hl : l = fin
  · exact Or.inr (hl ▸ hfin)
  · exact Or.inl (by simp only [gprog, ite_eq_right hl])

/-- Composed run: `P`'s run to `fin`, one jump, the drain. -/
theorem g_run_gen {P : Λ → TM2.Stmt (FΓ g r) Λ Bool} {fin : Λ} (hfin : P fin = .halt)
    {B : ℕ} {l : Λ} {v v' : Bool} {S T : ∀ k, List (FΓ g r k)}
    (h : RunLe P B ⟨some l, v, S⟩ ⟨some fin, v', T⟩) :
    RunLe (gprog P fin) (B + 1 + drainB dks T) ⟨some (.f l), v, S⟩
      ⟨none, false, fun k => if k ∈ dks then [] else T k⟩ := by
  obtain ⟨T', r1, a1, -⟩ := runLe_embed (E := idE (FΓ g r)) DL.f (embeds_g hfin) h
    (S' := S) (fun _ => (List.map_id _).symm)
  have hT : T' = T := funext fun k => (a1 k).trans (List.map_id _)
  subst hT
  have r2 : Run (gprog P fin) 1 ⟨some (.f fin), v', T'⟩ ⟨some (dlab _ 0), v', T'⟩ :=
    Run.single (by simp [gprog, TM2.stepAux])
  have r3 := drain_run (M := gprog P fin) dks (dlab _) dks_nodup
    (fun i hi => by simp [gprog, dlab, min_eq_left hi]) v' T'
  exact (r1.trans (r2.le le_rfl)).trans (r3.le le_rfl)

/-- Drain steps from a uniform height bound. -/
theorem drainB_le {T : ∀ k, List (FΓ g r k)} {h : ℕ} (hT : ∀ k, (T k).length ≤ h) :
    drainB dks T ≤ dks.length * (h + 1) + 1 := by
  unfold drainB
  have := List.sum_le_length_nsmul (dks.map fun k => (T k).length + 1) (h + 1) (by
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact Nat.add_le_add_right (hT k) 1)
  simp only [List.length_map, smul_eq_mul] at this
  omega

end Glue

/-! ## [REAL] The composed machine on the real generators -/

section Real

open Cslib.Complexity.CookLevin.Situation Cslib.Complexity.CookLevin.Assembly

variable {r : ℕ} {M : FinTM2} (E : Enc M)

theorem fullProg_fin (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : fullProg E Ys acc ι sep k c e (.h .fin) = .halt := rfl

/-- **The reduction machine as a `FinTM2`**: the full machine followed by the drain. -/
noncomputable def gTM (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : FinTM2 where
  K := FK
  k₀ := .raw
  k₁ := .h .out
  Γ := FΓ E.layout.g r
  Λ := DL (FL _ _) dks.length
  main := .f .rd
  σ := Bool
  initialState := false
  m := gprog (fullProg E Ys acc ι sep k c e) (.h .fin)

/-- The emitted formula for raw input `s`. -/
noncomputable def phiOf (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) : List Bool :=
  encodeCNF (Phi E (s.map ι ++ [sep]) Ys acc (mOf k s.length) (TOf k c e s.length))

/-- Step bound of the composed machine (`D = depth` of the full machine, a constant). -/
noncomputable def gB (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e n : ℕ) : ℕ :=
  fullB E Ys k c e n + 1 +
    (dks.length * (n + fullB E Ys k c e n * depth (fullTM E Ys acc ι sep k c e) + 1) + 1)

theorem initList_g (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) :
    initList (gTM E Ys acc ι sep k c e) s = ⟨some (.f .rd), false, fst s [] 0 []⟩ := by
  simp only [initList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · cases x <;> rfl

theorem haltList_g (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (T : ∀ k, List (FΓ E.layout.g r k)) :
    haltList (gTM E Ys acc ι sep k c e) (T (.h .out)) =
      ⟨none, false, fun q : FK => if q = FK.h .out then T q else []⟩ := by
  classical
  simp only [haltList]
  congr 1
  funext q
  rcases q with q | _ | x
  · cases q <;> rfl
  · rfl
  · rfl

/-- **The composed machine, raw input to `haltList`.** From `initList` on the raw input `s`, the
reduction machine halts in exactly `haltList (phiOf s)` within `gB |s|` steps. No hypotheses. -/
theorem g_run (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) (s : List (Fin r)) :
    RunLe (gTM E Ys acc ι sep k c e).m (gB E Ys acc ι sep k c e s.length)
      (initList (gTM E Ys acc ι sep k c e) s)
      (haltList (gTM E Ys acc ι sep k c e) (phiOf E Ys acc ι sep k c e s)) := by
  obtain ⟨v, S, ⟨n1, hn1, r1⟩, hout⟩ := full_run E Ys acc ι sep k c e s []
  rw [List.append_nil] at hout
  -- stack heights at the end of the full machine's run (generic growth lemma)
  have hh : ∀ q, (S q).length ≤
      s.length + fullB E Ys k c e s.length * depth (fullTM E Ys acc ι sep k c e) := by
    intro q
    have r1' : Run (fullTM E Ys acc ι sep k c e).m n1 (initList (fullTM E Ys acc ι sep k c e) s)
        ⟨some (.h .fin), v, S⟩ := by rw [initList_full]; exact r1
    have h1 := run_height r1' q
    have h2 : ((initList (fullTM E Ys acc ι sep k c e) s).stk q).length ≤ s.length :=
      initList_height (M := fullTM E Ys acc ι sep k c e) s q
    have h3 := Nat.mul_le_mul_right (depth (fullTM E Ys acc ι sep k c e)) hn1
    exact h1.trans (by omega)
  have hg := g_run_gen (fullProg_fin E Ys acc ι sep k c e) ⟨n1, hn1, r1⟩
  rw [drained] at hg
  rw [initList_g, show phiOf E Ys acc ι sep k c e s = S (.h .out) from hout.symm, haltList_g]
  refine hg.mono ?_
  have := drainB_le hh
  unfold gB
  omega

end Real

/-! ## [PKG] `TM2OutputsInTime` and `TM2ComputableInPolyTime` -/

section Pkg

open Cslib.Complexity.CookLevin.Situation Cslib.Complexity.CookLevin.Assembly

/-- A bounded run from `initList` to `haltList` is a `TM2OutputsInTime` certificate. -/
noncomputable def outputsOfRunLe {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)}
    {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l')) :
    TM2OutputsInTime tm l (some l') B where
  steps := Classical.choose h
  evals_in_steps := (Classical.choose_spec h).2
  steps_le_m := (Classical.choose_spec h).1

/-- `outputsOfRunLe` up to an equation on the output. -/
noncomputable def outputsOfRunLe' {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' l'' : List (tm.Γ tm.k₁)} {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l''))
    (he : l'' = l') : TM2OutputsInTime tm l (some l') B :=
  outputsOfRunLe (he ▸ h)

variable {r : ℕ} {M : FinTM2} (E : Enc M)

theorem gB_poly (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) : IsPoly (gB E Ys acc ι sep k c e) := by
  unfold gB
  generalize depth (fullTM E Ys acc ι sep k c e) = D
  generalize (dks : List FK).length = L
  have hf := fullB_poly E Ys k c e
  exact (hf.add (IsPoly.const 1)).add (((IsPoly.const L).mul
    ((IsPoly.id.add (hf.mul (IsPoly.const D))).add (IsPoly.const 1))).add (IsPoly.const 1))

/-- **One polynomial** bounding the composed machine on every input. -/
theorem g_outputs (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀)
    (sep : M.Γ M.k₀) (k : Polynomial ℕ) (c e : ℕ) :
    ∃ p : Polynomial ℕ, ∀ s : List (Fin r),
      Nonempty (TM2OutputsInTime (gTM E Ys acc ι sep k c e) s
        (some (phiOf E Ys acc ι sep k c e s)) (p.eval s.length)) := by
  obtain ⟨p, hp⟩ := gB_poly E Ys acc ι sep k c e
  exact ⟨p, fun s => ⟨outputsOfRunLe ((g_run E Ys acc ι sep k c e s).mono (hp _).le)⟩⟩

/-- The reduction function on encoded inputs: decode the raw symbols, emit `Phi`. -/
noncomputable def fR {α αΓ : Type} (ea : α → List αΓ) (eqv : Fin r ≃ αΓ)
    (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k : Polynomial ℕ) (c e : ℕ) (a : α) : List Bool :=
  phiOf E Ys acc ι sep k c e ((ea a).map eqv.invFun)

/-- **The packaged reduction machine**: `TM2ComputableInPolyTime` from `ea` to the identity
encoding of `List Bool`, computing `fR`. Still parametric in the verifier data. -/
noncomputable def gComp {α αΓ : Type} (ea : α → List αΓ) (eqv : Fin r ≃ αΓ)
    (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (ι : Fin r → M.Γ M.k₀) (sep : M.Γ M.k₀)
    (k : Polynomial ℕ) (c e : ℕ) :
    TM2ComputableInPolyTime ea (fun l : List Bool => l)
      (fR E ea eqv Ys acc ι sep k c e) where
  tm := gTM E Ys acc ι sep k c e
  inputAlphabet := eqv
  outputAlphabet := Equiv.refl Bool
  time := Classical.choose (gB_poly E Ys acc ι sep k c e)
  outputsFun a := outputsOfRunLe' (by
    have h := g_run E Ys acc ι sep k c e ((ea a).map eqv.invFun)
    rw [List.length_map, Classical.choose_spec (gB_poly E Ys acc ι sep k c e)] at h
    exact h) (List.map_id _).symm

end Pkg

end Cslib.Complexity.CookLevin.Package
