/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Clique
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.Program

/-!
# Karp reductions, component: CLIQUE → INDEPENDENT-SET and INDEPENDENT-SET → VERTEX-COVER

One `TM2` machine `prog m` computing `flipKG` (`m = .flip`) or `isToVc` (`m = .vc`) of
`Cslib.Complexity.Karp` on raw bits, in linear time.

The input `x` lies on stack `X` as `Sym.bit`s, the output is built on the `Bool` stack `O`, top
first. The machine reads `k` in unary onto the counter `A`, then `n` onto the counters `B` and
`D`, and moves the remaining bits to `Y` as `Sym.val`s, which reverses them. For `vc` it then
subtracts `A` from `D`, leaving `n - k` on `D` (or failing if `k > n`). Finally it pops `Y`
onto `O` (complementing each bit for `flip`), pushes `false`, `n` units of `true` (draining `B`),
`false`, and drains `A` (`flip`) or `D` (`vc`) as `true`s. If `X` ends inside the unary prefix,
or `k > n` for `vc`, the output is `noKG`.

`run`: from `start` with `x` on `X` and the other stacks empty, `prog m` reaches `done` within
`3 · (|x| + 1)` steps with `O = m.f x`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.KGMap

open Turing Function MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Complexity.SatVerifier

/-- The two reductions computed by the machine. -/
inductive Mode | flip | vc
  deriving DecidableEq

instance Mode.instFintypeEnumFix : Fintype Mode where
  elems := ⟨↑[Mode.flip, .vc], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The map a mode computes: `flipKG` (CLIQUE to INDEPENDENT-SET) or `isToVc`
(INDEPENDENT-SET to VERTEX-COVER). -/
def Mode.f : Mode → List Bool → List Bool
  | .flip => flipKG
  | .vc => isToVc

/-- Stacks: input `X`, output `O`, counters `A` (`k`), `B` (`n`), `D` (`n`, then `n - k`), and
the reversed pair bits `Y`. -/
inductive K | X | O | A | B | D | Y
  deriving DecidableEq

instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .O, .A, .B, .D, .Y], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Stack alphabets: the output stack holds `Bool`s, every other stack `Sym`s. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- Labels: read `k`, read `n`, move the pair bits, subtract (`vc`), output the pair bits, `n`,
the separator and the last number; `bad` writes `noKG`. -/
inductive Lab | rdK | rdN | mv | sub | outY | outB | sep | outK | bad | done
  deriving DecidableEq

instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdK, .rdN, .mv, .sub, .outY, .outB, .sep, .outK, .bad, .done], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The unit symbol of the counters `A`, `B`, `D`. -/
abbrev U : Sym := .cl

/-- Is the popped symbol the input bit `true`? -/
def isT : Option Sym → Bool
  | some (.bit true) => true
  | _ => false

/-- Is the popped symbol the moved bit `val true`? -/
def isV : Option Sym → Bool
  | some (.val true) => true
  | _ => false

@[simp] theorem isT_bit (b : Bool) : isT (some (.bit b)) = b := by cases b <;> rfl

@[simp] theorem isV_val (b : Bool) : isV (some (.val b)) = b := by cases b <;> rfl

/-- What happens to a pair bit: complemented for `flip`, kept for `vc`. -/
def Mode.fb : Mode → Bool → Bool
  | .flip => not
  | .vc => id

/-- Where the machine goes after moving the pair bits: output (`flip`) or subtract (`vc`). -/
def Mode.next : Mode → Lab
  | .flip => .outY
  | .vc => .sub

/-- The counter holding the output's first number: `A` (`k`, `flip`) or `D` (`n - k`, `vc`). -/
def Mode.ctr : Mode → K
  | .flip => .A
  | .vc => .D

/-- The machine. -/
def prog (m : Mode) : Lab → TM2.Stmt Γ Lab Bool
  | .rdK => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .bad) <|
      .pop .X (fun _ o => isT o) <| .branch id
        (.push .A (fun _ => U) (.goto fun _ => .rdK)) (.goto fun _ => .rdN)
  | .rdN => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .bad) <|
      .pop .X (fun _ o => isT o) <| .branch id
        (.push .B (fun _ => U) <| .push .D (fun _ => U) <| .goto fun _ => .rdN)
        (.goto fun _ => .mv)
  | .mv => .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => m.next) <|
      .pop .X (fun _ o => isT o) <| .push .Y (fun s => Sym.val s) <| .goto fun _ => .mv
  | .sub => .pop .A (fun _ o => o.isSome) <| .branch id
      (.pop .D (fun _ o => o.isSome) <| .branch id (.goto fun _ => .sub) (.goto fun _ => .bad))
      (.goto fun _ => .outY)
  | .outY => .peek .Y (fun _ o => o.isNone) <| .branch id
      (.push .O (fun _ => false) (.goto fun _ => .outB)) <|
      .pop .Y (fun _ o => isV o) <| .push .O (fun s => m.fb s) <| .goto fun _ => .outY
  | .outB => xfer .B [⟨.O, true⟩] .outB .sep
  | .sep => emit .O [false] .outK
  | .outK => xfer m.ctr [⟨.O, true⟩] .outK .done
  | .bad => emitR .O noKG .done
  | .done => .halt

/-- The start label. -/
def start : Lab := .rdK

/-! ### One-step lemmas -/

section Steps

variable (m : Mode) (v : Bool) (St : ∀ k, List (Γ k))

theorem rdK_true (r : List Sym) (h : St .X = Sym.bit true :: r) :
    Run (prog m) 1 ⟨some .rdK, v, St⟩
      ⟨some .rdK, true, update (update St .X r) .A (U :: St .A)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdK_false (r : List Sym) (h : St .X = Sym.bit false :: r) :
    Run (prog m) 1 ⟨some .rdK, v, St⟩ ⟨some .rdN, false, update St .X r⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdK_nil (h : St .X = []) : Run (prog m) 1 ⟨some .rdK, v, St⟩ ⟨some .bad, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdN_true (r : List Sym) (h : St .X = Sym.bit true :: r) :
    Run (prog m) 1 ⟨some .rdN, v, St⟩
      ⟨some .rdN, true, update (update (update St .X r) .B (U :: St .B)) .D (U :: St .D)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdN_false (r : List Sym) (h : St .X = Sym.bit false :: r) :
    Run (prog m) 1 ⟨some .rdN, v, St⟩ ⟨some .mv, false, update St .X r⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem rdN_nil (h : St .X = []) : Run (prog m) 1 ⟨some .rdN, v, St⟩ ⟨some .bad, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem mv_bit (b : Bool) (r : List Sym) (h : St .X = Sym.bit b :: r) :
    Run (prog m) 1 ⟨some .mv, v, St⟩
      ⟨some .mv, b, update (update St .X r) .Y (Sym.val b :: St .Y)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem mv_nil (h : St .X = []) : Run (prog m) 1 ⟨some .mv, v, St⟩ ⟨some m.next, true, St⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem sub_pos (a d : List Sym) (ha : St .A = U :: a) (hd : St .D = U :: d) :
    Run (prog m) 1 ⟨some .sub, v, St⟩ ⟨some .sub, true, update (update St .A a) .D d⟩ :=
  Run.single (by simp [prog, TM2.stepAux, ha, hd])

theorem sub_bad (a : List Sym) (ha : St .A = U :: a) (hd : St .D = []) :
    Run (prog m) 1 ⟨some .sub, v, St⟩ ⟨some .bad, false, update (update St .A a) .D []⟩ :=
  Run.single (by simp [prog, TM2.stepAux, ha, hd])

theorem sub_zero (ha : St .A = []) :
    Run (prog m) 1 ⟨some .sub, v, St⟩ ⟨some .outY, false, update St .A []⟩ :=
  Run.single (by simp [prog, TM2.stepAux, ha])

theorem outY_val (b : Bool) (ys : List Sym) (h : St .Y = Sym.val b :: ys) :
    Run (prog m) 1 ⟨some .outY, v, St⟩
      ⟨some .outY, b, update (update St .Y ys) .O (m.fb b :: St .O)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem outY_nil (h : St .Y = []) :
    Run (prog m) 1 ⟨some .outY, v, St⟩ ⟨some .outB, true, update St .O (false :: St .O)⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem bad_run : Run (prog m) 1 ⟨some .bad, v, St⟩ ⟨some .done, v, update St .O (noKG ++ St .O)⟩ :=
  emitR_run (M := prog m) (self := .bad) rfl v St

end Steps

/-! ### Loops -/

section Loops

variable (m : Mode)

/-- Reading `k`: each `true` adds a unit to `A`; the closing `false` moves on to `n`. -/
theorem rdK_some (k : ℕ) : ∀ (i : ℕ) (v : Bool) (St : ∀ k, List (Γ k)) (r : List Bool),
    St .X = (List.replicate k true ++ false :: r).map Sym.bit → St .A = cnt U i →
    ∃ v' S', Run (prog m) (k + 1) ⟨some .rdK, v, St⟩ ⟨some .rdN, v', S'⟩ ∧
      S' .X = r.map Sym.bit ∧ S' .A = cnt U (i + k) ∧ ∀ j, j ≠ .X → j ≠ .A → S' j = St j := by
  induction k with
  | zero =>
      intro i v St r hX hA
      exact ⟨_, _, rdK_false m v St _ (by simpa using hX), by simp, by simpa using hA,
        fun j h1 _ => by simp [update_of_ne h1]⟩
  | succ k ih =>
      intro i v St r hX hA
      have h₁ := rdK_true m v St ((List.replicate k true ++ false :: r).map Sym.bit)
        (by simp [hX, List.replicate_succ])
      obtain ⟨v', S', h₂, hX', hA', hS'⟩ := ih (i + 1) true
        (update (update St .X ((List.replicate k true ++ false :: r).map Sym.bit)) .A
          (U :: St .A)) r (by simp) (by simp [hA, List.replicate_succ])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), hX', by rw [hA']; congr 1; omega, ?_⟩
      intro j h1 h2
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- A unary `k` that never ends: `bad` within `|r| + 1` steps. -/
theorem rdK_none : ∀ (r : List Bool), readUnaryLength r = none →
    ∀ (v : Bool) (St : ∀ k, List (Γ k)), St .X = r.map Sym.bit →
      ∃ v' S', Run (prog m) (r.length + 1) ⟨some .rdK, v, St⟩ ⟨some .bad, v', S'⟩ ∧
        ∀ j, j ≠ .X → j ≠ .A → S' j = St j
  | [], _, v, St, hX => ⟨_, _, rdK_nil m v St (by simpa using hX), fun _ _ _ => rfl⟩
  | false :: r, h, _, _, _ => by simp [readUnaryLength] at h
  | true :: r, h, v, St, hX => by
      have hr : readUnaryLength r = none := by simpa [readUnaryLength] using h
      have h₁ := rdK_true m v St (r.map Sym.bit) (by simpa using hX)
      obtain ⟨v', S', h₂, hS'⟩ := rdK_none r hr true
        (update (update St .X (r.map Sym.bit)) .A (U :: St .A)) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), fun j h1 h2 => ?_⟩
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- Reading `n`: each `true` adds a unit to `B` and to `D`; the closing `false` moves on to the
pair bits. -/
theorem rdN_some (n : ℕ) : ∀ (i : ℕ) (v : Bool) (St : ∀ k, List (Γ k)) (r : List Bool),
    St .X = (List.replicate n true ++ false :: r).map Sym.bit → St .B = cnt U i →
    St .D = cnt U i →
    ∃ v' S', Run (prog m) (n + 1) ⟨some .rdN, v, St⟩ ⟨some .mv, v', S'⟩ ∧
      S' .X = r.map Sym.bit ∧ S' .B = cnt U (i + n) ∧ S' .D = cnt U (i + n) ∧
      ∀ j, j ≠ .X → j ≠ .B → j ≠ .D → S' j = St j := by
  induction n with
  | zero =>
      intro i v St r hX hB hD
      exact ⟨_, _, rdN_false m v St _ (by simpa using hX), by simp, by simpa using hB,
        by simpa using hD, fun j h1 _ _ => by simp [update_of_ne h1]⟩
  | succ n ih =>
      intro i v St r hX hB hD
      have h₁ := rdN_true m v St ((List.replicate n true ++ false :: r).map Sym.bit)
        (by simp [hX, List.replicate_succ])
      obtain ⟨v', S', h₂, hX', hB', hD', hS'⟩ := ih (i + 1) true
        (update (update (update St .X ((List.replicate n true ++ false :: r).map Sym.bit)) .B
          (U :: St .B)) .D (U :: St .D)) r (by simp) (by simp [hB, List.replicate_succ])
        (by simp [hD, List.replicate_succ])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), hX', by rw [hB']; congr 1; omega,
        by rw [hD']; congr 1; omega, ?_⟩
      intro j h1 h2 h3
      rw [hS' j h1 h2 h3]
      simp [update_of_ne h1, update_of_ne h2, update_of_ne h3]

/-- A unary `n` that never ends: `bad` within `|r| + 1` steps. -/
theorem rdN_none : ∀ (r : List Bool), readUnaryLength r = none →
    ∀ (v : Bool) (St : ∀ k, List (Γ k)), St .X = r.map Sym.bit →
      ∃ v' S', Run (prog m) (r.length + 1) ⟨some .rdN, v, St⟩ ⟨some .bad, v', S'⟩ ∧
        ∀ j, j ≠ .X → j ≠ .B → j ≠ .D → S' j = St j
  | [], _, v, St, hX => ⟨_, _, rdN_nil m v St (by simpa using hX), fun _ _ _ _ => rfl⟩
  | false :: r, h, _, _, _ => by simp [readUnaryLength] at h
  | true :: r, h, v, St, hX => by
      have hr : readUnaryLength r = none := by simpa [readUnaryLength] using h
      have h₁ := rdN_true m v St (r.map Sym.bit) (by simpa using hX)
      obtain ⟨v', S', h₂, hS'⟩ := rdN_none r hr true
        (update (update (update St .X (r.map Sym.bit)) .B (U :: St .B)) .D (U :: St .D))
        (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), fun j h1 h2 h3 => ?_⟩
      rw [hS' j h1 h2 h3]
      simp [update_of_ne h1, update_of_ne h2, update_of_ne h3]

/-- Moving the pair bits: `X` is emptied onto `Y` as `Sym.val`s, reversed. -/
theorem mv_run (r : List Bool) : ∀ (v : Bool) (St : ∀ k, List (Γ k)) (ys : List Sym),
    St .X = r.map Sym.bit → St .Y = ys →
    ∃ v' S', Run (prog m) (r.length + 1) ⟨some .mv, v, St⟩ ⟨some m.next, v', S'⟩ ∧
      S' .Y = (r.map Sym.val).reverse ++ ys ∧ ∀ j, j ≠ .X → j ≠ .Y → S' j = St j := by
  induction r with
  | nil =>
      intro v St ys hX hY
      exact ⟨_, _, mv_nil m v St (by simpa using hX), by simpa using hY, fun _ _ _ => rfl⟩
  | cons b r ih =>
      intro v St ys hX hY
      have h₁ := mv_bit m v St b (r.map Sym.bit) (by simpa using hX)
      obtain ⟨v', S', h₂, hY', hS'⟩ := ih b
        (update (update St .X (r.map Sym.bit)) .Y (Sym.val b :: St .Y)) (Sym.val b :: ys)
        (by simp) (by simp [hY])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), by simp [hY'], ?_⟩
      intro j h1 h2
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- Subtraction for `k ≤ n`: `D` ends at `n - k`. -/
theorem sub_le (k : ℕ) : ∀ (n : ℕ) (v : Bool) (St : ∀ k, List (Γ k)), k ≤ n →
    St .A = cnt U k → St .D = cnt U n →
    ∃ v' S', Run (prog m) (k + 1) ⟨some .sub, v, St⟩ ⟨some .outY, v', S'⟩ ∧
      S' .D = cnt U (n - k) ∧ ∀ j, j ≠ .A → j ≠ .D → S' j = St j := by
  induction k with
  | zero =>
      intro n v St _ hA hD
      exact ⟨_, _, sub_zero m v St (by simpa using hA), by simp [hD],
        fun j h1 _ => by simp [update_of_ne h1]⟩
  | succ k ih =>
      intro n v St hkn hA hD
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have h₁ := sub_pos m v St (cnt U k) (cnt U n) (by simp [hA, List.replicate_succ])
        (by simp [hD, List.replicate_succ])
      obtain ⟨v', S', h₂, hD', hS'⟩ := ih n true
        (update (update St .A (cnt U k)) .D (cnt U n)) (by omega) (by simp) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), by rw [hD']; congr 1; omega, ?_⟩
      intro j h1 h2
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- Subtraction for `k > n`: `bad` after `n + 1` steps. -/
theorem sub_gt (n : ℕ) : ∀ (k : ℕ) (v : Bool) (St : ∀ k, List (Γ k)), n < k →
    St .A = cnt U k → St .D = cnt U n →
    ∃ v' S', Run (prog m) (n + 1) ⟨some .sub, v, St⟩ ⟨some .bad, v', S'⟩ ∧
      ∀ j, j ≠ .A → j ≠ .D → S' j = St j := by
  induction n with
  | zero =>
      intro k v St hnk hA hD
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ⟨_, _, sub_bad m v St (cnt U k) (by simp [hA, List.replicate_succ])
        (by simpa using hD), fun j h1 h2 => by simp [update_of_ne h1, update_of_ne h2]⟩
  | succ n ih =>
      intro k v St hnk hA hD
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h₁ := sub_pos m v St (cnt U k) (cnt U n) (by simp [hA, List.replicate_succ])
        (by simp [hD, List.replicate_succ])
      obtain ⟨v', S', h₂, hS'⟩ := ih k true
        (update (update St .A (cnt U k)) .D (cnt U n)) (by omega) (by simp) (by simp)
      refine ⟨v', S', (h₁.trans h₂).of_eq (by omega), fun j h1 h2 => ?_⟩
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

/-- Outputting the pair bits: `Y` (as `Sym.val`s, top first) is popped onto `O`, each bit
through `m.fb`, then `false` is pushed. -/
theorem outY_run (ys : List Bool) : ∀ (v : Bool) (St : ∀ k, List (Γ k)) (o : List Bool),
    St .Y = ys.map Sym.val → St .O = o →
    ∃ v' S', Run (prog m) (ys.length + 1) ⟨some .outY, v, St⟩ ⟨some .outB, v', S'⟩ ∧
      S' .O = false :: ((ys.map m.fb).reverse ++ o) ∧ ∀ j, j ≠ .Y → j ≠ .O → S' j = St j := by
  induction ys with
  | nil =>
      intro v St o hY hO
      exact ⟨_, _, outY_nil m v St (by simpa using hY), by simp [hO],
        fun j _ h2 => by simp [update_of_ne h2]⟩
  | cons b ys ih =>
      intro v St o hY hO
      have h₁ := outY_val m v St b (ys.map Sym.val) (by simpa using hY)
      obtain ⟨v', S', h₂, hO', hS'⟩ := ih b
        (update (update St .Y (ys.map Sym.val)) .O (m.fb b :: St .O)) (m.fb b :: o)
        (by simp) (by simp [hO])
      refine ⟨v', S', (h₁.trans h₂).of_eq (by simp; omega), by simp [hO'], ?_⟩
      intro j h1 h2
      rw [hS' j h1 h2]
      simp [update_of_ne h1, update_of_ne h2]

theorem ctr_ne : m.ctr ≠ .O ∧ m.ctr ≠ .B ∧ m.ctr ≠ .Y ∧ m.ctr ≠ .X := by
  cases m <;> decide

/-- The numbers: drain `B` as `true`s onto `O`, push `false`, drain `m.ctr` as `true`s. -/
theorem tail_run (n c : ℕ) (u : Γ m.ctr) (v : Bool) (St : ∀ k, List (Γ k))
    (hB : St .B = cnt U n) (hC : St m.ctr = cnt u c) :
    ∃ v' S', Run (prog m) (n + c + 3) ⟨some .outB, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = List.replicate c true ++ false :: (List.replicate n true ++ St .O) := by
  obtain ⟨hcO, hcB, -, -⟩ := ctr_ne m
  have h₁ := xfer_run (M := prog m) (self := .outB) (next := .sep) (k := .B)
    (ps := [⟨.O, true⟩]) rfl (single_nodupKeys _) (by simp [List.keys]) U n v St hB
  set S₁ := addU [⟨.O, true⟩] n (update St .B []) with hS₁
  have h₂ := emit_run (M := prog m) (self := .sep) rfl (Flag.tag false) S₁
  set S₂ := update S₁ .O ([false].reverse ++ S₁ .O) with hS₂
  have hC₂ : S₂ m.ctr = cnt u c := by
    rw [hS₂, update_of_ne hcO, hS₁, addU_single_ne _ _ _ hcO, update_of_ne hcB, hC]
  have h₃ := xfer_run (M := prog m) (self := .outK) (next := .done) (k := m.ctr)
    (ps := [⟨.O, true⟩]) rfl (single_nodupKeys _) (by simp [List.keys, hcO]) u c
    (Flag.tag false) S₂ hC₂
  refine ⟨_, _, ((h₁.trans h₂).trans h₃).of_eq (by omega), ?_⟩
  rw [addU_single_self, update_of_ne hcO.symm, hS₂, update_self, hS₁, addU_single_self,
    update_of_ne (by decide : K.O ≠ K.B)]
  rfl

/-- The output phase: from `outY` with the reversed pair bits on `Y`, `n` on `B`, `c` on
`m.ctr` and `O` empty, reach `done` with `O = encodeKG c n (r.map m.fb)`. -/
theorem out_run (r : List Bool) (n c : ℕ) (u : Γ m.ctr) (v : Bool) (St : ∀ k, List (Γ k))
    (hY : St .Y = (r.map Sym.val).reverse) (hB : St .B = cnt U n) (hC : St m.ctr = cnt u c)
    (hO : St .O = []) :
    ∃ v' S', Run (prog m) (r.length + n + c + 4) ⟨some .outY, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = encodeKG c n (r.map m.fb) := by
  obtain ⟨hcO, -, hcY, -⟩ := ctr_ne m
  obtain ⟨v₁, S₁, h₁, hO₁, hS₁⟩ := outY_run m r.reverse v St [] (by simp [hY, List.map_reverse])
    hO
  obtain ⟨v₂, S₂, h₂, hO₂⟩ := tail_run m n c u v₁ S₁ (by rw [hS₁ _ (by decide) (by decide), hB])
    (by rw [hS₁ _ hcY hcO, hC])
  refine ⟨v₂, S₂, (h₁.trans h₂).of_eq (by simp; omega), ?_⟩
  rw [hO₂, hO₁]
  simp [encodeKG, List.map_reverse]

end Loops

/-- **The component.** From `start` with `x` on `X` (as `Sym.bit`s) and the other stacks empty,
`prog m` reaches `done` within `3 · (|x| + 1)` steps with `m.f x` on `O`, top first. -/
theorem run (m : Mode) (x : List Bool) (v : Bool) (St : ∀ k, List (Γ k))
    (hX : St .X = x.map Sym.bit) (h0 : ∀ k, k ≠ .X → St k = []) :
    ∃ v' S', RunLe (prog m) (3 * (x.length + 1)) ⟨some start, v, St⟩ ⟨some .done, v', S'⟩ ∧
      S' .O = m.f x := by
  rcases h1 : readUnaryLength x with _ | ⟨k, x'⟩
  · obtain ⟨v₁, S₁, h₁, hS₁⟩ := rdK_none m x h1 v St hX
    have h₂ := bad_run m v₁ S₁
    refine ⟨_, _, (h₁.trans h₂).le (by omega), ?_⟩
    rw [update_self, hS₁ _ (by decide) (by decide), h0 _ (by decide)]
    cases m <;> simp [Mode.f, flipKG, isToVc, decodeKG, h1]
  obtain rfl := (readUnaryLength_eq_some_iff x k x').1 h1
  obtain ⟨v₁, S₁, h₁, hX₁, hA₁, hS₁⟩ := rdK_some m k 0 v St x' hX (h0 _ (by decide))
  rcases h2 : readUnaryLength x' with _ | ⟨n, r⟩
  · obtain ⟨v₂, S₂, h₂, hS₂⟩ := rdN_none m x' h2 v₁ S₁ hX₁
    have h₃ := bad_run m v₂ S₂
    refine ⟨_, _, ((h₁.trans h₂).trans h₃).le (by simp; omega), ?_⟩
    rw [update_self, hS₂ _ (by decide) (by decide) (by decide), hS₁ _ (by decide) (by decide),
      h0 _ (by decide)]
    cases m <;> simp [Mode.f, flipKG, isToVc, decodeKG, h2]
  obtain rfl := (readUnaryLength_eq_some_iff x' n r).1 h2
  obtain ⟨v₂, S₂, h₂, hX₂, hB₂, hD₂, hS₂⟩ := rdN_some m n 0 v₁ S₁ r hX₁
    (by rw [hS₁ _ (by decide) (by decide), h0 _ (by decide)]; rfl)
    (by rw [hS₁ _ (by decide) (by decide), h0 _ (by decide)]; rfl)
  obtain ⟨v₃, S₃, h₃, hY₃, hS₃⟩ := mv_run m r v₂ S₂ [] hX₂
    (by rw [hS₂ _ (by decide) (by decide) (by decide), hS₁ _ (by decide) (by decide),
      h0 _ (by decide)])
  have hO₃ : S₃ .O = [] := by
    rw [hS₃ _ (by decide) (by decide), hS₂ _ (by decide) (by decide) (by decide),
      hS₁ _ (by decide) (by decide), h0 _ (by decide)]
  have hB₃ : S₃ .B = cnt U n := by rw [hS₃ _ (by decide) (by decide), hB₂, Nat.zero_add]
  have hD₃ : S₃ .D = cnt U n := by rw [hS₃ _ (by decide) (by decide), hD₂, Nat.zero_add]
  have hA₃ : S₃ .A = cnt U k := by
    rw [hS₃ _ (by decide) (by decide), hS₂ _ (by decide) (by decide) (by decide), hA₁,
      Nat.zero_add]
  rw [List.append_nil] at hY₃
  cases m with
  | flip =>
      obtain ⟨v₄, S₄, h₄, hO₄⟩ := out_run .flip r n k U v₃ S₃ hY₃ hB₃ hA₃ hO₃
      refine ⟨v₄, S₄, (((h₁.trans h₂).trans h₃).trans h₄).le (by simp; omega), ?_⟩
      rw [hO₄]
      simp [Mode.f, flipKG, decodeKG, Mode.fb]
  | vc =>
      by_cases hkn : k ≤ n
      · obtain ⟨v₄, S₄, h₄, hD₄, hS₄⟩ := sub_le .vc k n v₃ S₃ hkn hA₃ hD₃
        obtain ⟨v₅, S₅, h₅, hO₅⟩ := out_run .vc r n (n - k) U v₄ S₄
          (by rw [hS₄ _ (by decide) (by decide), hY₃])
          (by rw [hS₄ _ (by decide) (by decide), hB₃]) hD₄
          (by rw [hS₄ _ (by decide) (by decide), hO₃])
        refine ⟨v₅, S₅, ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).le (by simp; omega), ?_⟩
        rw [hO₅]
        simp [Mode.f, isToVc, decodeKG, Mode.fb, hkn]
      · obtain ⟨v₄, S₄, h₄, hS₄⟩ := sub_gt .vc n k v₃ S₃ (by omega) hA₃ hD₃
        have h₅ := bad_run .vc v₄ S₄
        refine ⟨_, _, ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).le (by simp; omega), ?_⟩
        rw [update_self, hS₄ _ (by decide) (by decide), hO₃]
        simp [Mode.f, isToVc, decodeKG, hkn]

end Cslib.Complexity.Karp.KGMap
