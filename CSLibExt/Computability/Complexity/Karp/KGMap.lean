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

/-- **Modes of the CLIQUE/VERTEX-COVER reduction machine.** A mode is one of two values, the
flip mode and the vertex-cover mode. They select the reduction that the machine of this module
computes: CLIQUE to INDEPENDENT-SET in the flip mode, INDEPENDENT-SET to VERTEX-COVER in the
vertex-cover mode. -/
inductive Mode | flip | vc
  deriving DecidableEq

instance Mode.instFintypeEnumFix : Fintype Mode where
  elems := ⟨↑[Mode.flip, .vc], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Reduction computed in each mode.** The map on bit strings that a mode of the
CLIQUE/VERTEX-COVER reduction machine computes: in the flip mode it is the reduction from CLIQUE
to INDEPENDENT-SET on bit strings, and in the vertex-cover mode it is the reduction from
INDEPENDENT-SET to VERTEX-COVER on bit strings. -/
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

/-- **Stack alphabets of the clique reduction machine.** The alphabet $\Gamma(k)$ of a stack $k$
is the Booleans if $k$ is the output stack $O$, and the token alphabet $\mathrm{Sym}$ for every
other stack ($X$, $A$, $B$, $D$ and $Y$). -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Labels of the KG-map machine.** The type of the ten instruction labels of the KG-map
machine: read $k$, read $n$, move the pair bits, subtract, output the pair bits, output $n$, write
the separator, output the last number, the failure label and the halting label.

The machine reaches the subtraction label only in the vertex-cover mode, and at the failure label
it writes the fixed no-instance. -/
inductive Lab | rdK | rdN | mv | sub | outY | outB | sep | outK | bad | done
  deriving DecidableEq

instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.rdK, .rdN, .mv, .sub, .outY, .outB, .sep, .outK, .bad, .done], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Counter unit symbol of the clique reduction machine.** $U$ is the symbol $\mathsf{cl}$ of
the token alphabet $\mathrm{Sym}$.

It is the unit of the counter stacks $A$, $B$ and $D$, which hold a number $n$ as $n$ copies of
$U$. -/
abbrev U : Sym := .cl

/-- **Test for the input bit true.** A test on the result of popping a stack: it is true
exactly when a symbol was popped and that symbol is $\mathrm{bit}(\mathrm{true})$, and false for
every other symbol and for an empty stack. -/
def isT : Option Sym → Bool
  | some (.bit true) => true
  | _ => false

/-- **Test for the moved bit true.** A test on the result of popping a stack: it is true
exactly when a symbol was popped and that symbol is $\mathrm{val}(\mathrm{true})$, and false for
every other symbol and for an empty stack. -/
def isV : Option Sym → Bool
  | some (.val true) => true
  | _ => false

@[simp] theorem isT_bit (b : Bool) : isT (some (.bit b)) = b := by cases b <;> rfl

@[simp] theorem isV_val (b : Bool) : isV (some (.val b)) = b := by cases b <;> rfl

/-- **Pair-bit transform of each mode.** For a mode of the CLIQUE/VERTEX-COVER reduction
machine, the map on booleans applied to each pair bit as it is written to the output: negation in
the flip mode and the identity in the vertex-cover mode. -/
def Mode.fb : Mode → Bool → Bool
  | .flip => not
  | .vc => id

/-- **Label after the move phase of the KG-map machine.** The map from the modes of the KG-map
machine to its labels that sends the flip mode to the label output the pair bits and the
vertex-cover mode to the subtraction label. The machine goes to this label after moving the pair
bits. -/
def Mode.next : Mode → Lab
  | .flip => .outY
  | .vc => .sub

/-- **Counter of the first output number of the KG-map machine.** The map from the modes of the
KG-map machine to its stacks that sends the flip mode to the counter $A$ and the vertex-cover
mode to the counter $D$.

This is the counter the machine drains last, as the first number of its output: $A$ holds $k$,
and in the vertex-cover mode $D$ holds $n - k$ by then. -/
def Mode.ctr : Mode → K
  | .flip => .A
  | .vc => .D

/-- **The KG-map machine.** For a mode $m$ (flip or vc), the KG-map machine $M_m$ is the
multi-stack machine with stacks $X$, $A$, $B$, $D$, $Y$ of symbols and an output stack $O$ of
bits, whose labels act as follows; the counters $A$, $B$, $D$ use a fixed unit symbol.

- Read $k$: if $X$ is empty, go to the failure label. Otherwise pop $X$; if the popped symbol is
  the input bit $\mathrm{bit}(\mathit{true})$, push a unit onto $A$ and repeat, else go to read $n$.
- Read $n$: if $X$ is empty, go to the failure label. Otherwise pop $X$; if the popped symbol is
  $\mathrm{bit}(\mathit{true})$, push a unit onto $B$ and onto $D$ and repeat, else go to move.
- Move: if $X$ is empty, go to output pair bits (flip) or subtract (vc). Otherwise pop $X$, push
  $\mathrm{val}(b)$ onto $Y$, where $b$ is true exactly when the popped symbol was
  $\mathrm{bit}(\mathit{true})$, and repeat.
- Subtract: pop $A$. If $A$ was empty, go to output pair bits. Otherwise pop $D$; if $D$ was
  nonempty repeat, else go to the failure label.
- Output pair bits: if $Y$ is empty, push false onto $O$ and go to output $n$. Otherwise pop $Y$,
  push $\beta_m(b)$ onto $O$, where $b$ is true exactly when the popped symbol was
  $\mathrm{val}(\mathit{true})$ and $\beta_m$ is negation for flip and the identity for vc, and
  repeat.
- Output $n$: pop $B$; if $B$ was nonempty, push true onto $O$ and repeat, else go to separator.
- Separator: push false onto $O$ and go to output last number.
- Output last number: as output $n$, but popping the counter of $m$ ($A$ for flip, $D$ for vc)
  and going to the halting label when it is empty.
- Failure: push the bits true, false, false of the fixed no-instance (the encoding of $k = 1$ on
  the empty graph) onto $O$ so that $O$ starts with them, and go to the halting label.
- Halting label: halt. -/
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

/-- **Start label of the KG-map machine.** The KG-map machine starts at the label read $k$. -/
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

/-- **Reading the first unary number in the KG-map machine.** Let $m$ be a mode, $k$ and $i$
natural numbers and $r$ a list of bits. Consider a configuration of the KG-map machine $M_m$ at
the label read $k$, with any internal bit, in which stack $X$ holds the input symbols
$\mathrm{bit}(b)$ for the bits $b$ of the list of $k$ trues, a false and then $r$, top first, and
stack $A$ holds $i$ copies of the unit symbol. Then in exactly $k + 1$ steps $M_m$ reaches the
label read $n$ with $X$ holding $\mathrm{bit}(b)$ for the bits $b$ of $r$, $A$ holding $i + k$
copies of the unit symbol, and every stack other than $X$ and $A$ unchanged. -/
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

/-- **Unterminated first unary number in the KG-map machine.** Let $m$ be a mode and $r$ a list
of bits on which reading a unary length prefix fails (this happens exactly when $r$ contains no
false). From any configuration of the KG-map machine $M_m$ at the label read $k$, with any
internal bit, in which stack $X$ holds the input symbols $\mathrm{bit}(b)$ for the bits $b$ of
$r$, top first, $M_m$ reaches the failure label in exactly $|r| + 1$ steps, with every stack
other than $X$ and $A$ unchanged. -/
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

/-- **Reading the second unary number in the KG-map machine.** Let $m$ be a mode, $n$ and $i$
natural numbers and $r$ a list of bits. Consider a configuration of the KG-map machine $M_m$ at
the label read $n$, with any internal bit, in which stack $X$ holds the input symbols
$\mathrm{bit}(b)$ for the bits $b$ of the list of $n$ trues, a false and then $r$, top first, and
stacks $B$ and $D$ each hold $i$ copies of the unit symbol. Then in exactly $n + 1$ steps $M_m$
reaches the label move with $X$ holding $\mathrm{bit}(b)$ for the bits $b$ of $r$, $B$ and $D$
each holding $i + n$ copies of the unit symbol, and every stack other than $X$, $B$ and $D$
unchanged. -/
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

/-- **Unterminated second unary number in the KG-map machine.** Let $m$ be a mode and $r$ a list
of bits on which reading a unary length prefix fails (this happens exactly when $r$ contains no
false). From any configuration of the KG-map machine $M_m$ at the label read $n$, with any
internal bit, in which stack $X$ holds the input symbols $\mathrm{bit}(b)$ for the bits $b$ of
$r$, top first, $M_m$ reaches the failure label in exactly $|r| + 1$ steps, with every stack
other than $X$, $B$ and $D$ unchanged. -/
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

/-- **Moving the pair bits onto stack $Y$.** Fix a mode $m$ of the CLIQUE/VERTEX-COVER
reduction machine, a list of bits $r$ and a list of symbols $y$. Start the machine for $m$ at the
label for moving the pair bits, with any internal state and any stacks such that stack $X$ holds
$r$ as the symbols $\mathrm{bit}(b)$ and stack $Y$ holds $y$. Then after exactly $|r| + 1$ steps
it is at the label that follows moving the pair bits in mode $m$, with some internal state and
stacks in which $Y$ holds the symbols $\mathrm{val}(b)$ for the bits $b$ of $r$, in reverse
order, on top of $y$, and every stack other than $X$ and $Y$ is unchanged. -/
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

/-- **Subtraction loop of the clique reduction machine.** Let $m$ be a mode of the machine, let
$k \le n$ be natural numbers, and let $S$ be stack contents in which the counter stack $A$ holds
$U^k$ ($k$ copies of the unit symbol $U$) and the counter stack $D$ holds $U^n$. Then for every
Boolean local state $v$ there are a local state $v'$ and stack contents $S'$ such that the machine
of mode $m$ runs in exactly $k + 1$ steps from label $\mathsf{sub}$ with local state $v$ and
stacks $S$ to label $\mathsf{outY}$ with local state $v'$ and stacks $S'$, the stack $D$ of $S'$
holds $U^{n-k}$, and every stack other than $A$ and $D$ has the same contents in $S'$ as in $S$. -/
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

/-- **Failed subtraction in the KG-map machine.** Let $m$ be a mode and $n < k$ natural numbers.
From any configuration of the KG-map machine $M_m$ at the label subtract, with any internal bit,
in which stack $A$ holds $k$ copies of the unit symbol and stack $D$ holds $n$ copies, $M_m$
reaches the failure label in exactly $n + 1$ steps, with every stack other than $A$ and $D$
unchanged. -/
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

/-- **Output loop for the pair bits of the KG-map machine.** Let $m$ be a mode and $y$ and $o$
lists of bits. Consider a configuration of the KG-map machine $M_m$ at the label output pair
bits, with any internal bit, in which stack $Y$ holds the symbols $\mathrm{val}(b)$ for the bits
$b$ of $y$, the first bit of $y$ on top, and the output stack $O$ holds $o$. Then in exactly
$|y| + 1$ steps $M_m$ reaches the label output $n$ with $O$ equal, top first, to false, then the
reverse of $\beta_m(y)$, then $o$, where $\beta_m$ negates every bit for flip and leaves the
bits unchanged for vc; every stack other than $Y$ and $O$ is unchanged. -/
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

/-- **Number output of the clique reduction machine.** Let $m$ be a mode of the machine and $C$
its final counter stack ($A$ for the flip mode, $D$ for the vertex-cover mode). Let $n, c$ be
natural numbers, $u$ a symbol of the alphabet of $C$, and $S$ stack contents in which the stack
$B$ holds $U^n$ ($n$ copies of the unit symbol $U$) and $C$ holds $u^c$. Then for every Boolean
local state $v$ there are a local state $v'$ and stack contents $S'$ such that the machine of
mode $m$ runs in exactly $n + c + 3$ steps from label $\mathsf{outB}$ with local state $v$ and
stacks $S$ to label $\mathsf{done}$ with local state $v'$ and stacks $S'$, and the output stack
$O$ of $S'$ holds, from the top, $c$ copies of $\mathrm{true}$, then $\mathrm{false}$, then $n$
copies of $\mathrm{true}$, then the contents of $O$ in $S$. -/
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

/-- **Output phase of the KG-map machine.** Let $m$ be a mode, $r$ a list of bits and $n$ and
$c$ natural numbers. Consider a configuration of the KG-map machine $M_m$ at the label output
pair bits, with any internal bit, in which stack $Y$ holds the symbols $\mathrm{val}(b)$ for the
bits $b$ of $r$ in reverse order (the last bit of $r$ on top), stack $B$ holds $n$ copies of the
unit symbol, the counter of $m$ ($A$ for flip, $D$ for vc) holds $c$ copies of some symbol, and
the output stack $O$ is empty. Then in exactly $|r| + n + c + 4$ steps $M_m$ reaches the halting
label with $O$ equal, top first, to the encoding of the instance with numbers $c$ and $n$ and
pair bits $\beta_m(r)$: $c$ trues, a false, $n$ trues, a false, then $\beta_m(r)$, where
$\beta_m$ negates every bit for flip and leaves the bits unchanged for vc. -/
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

/-- **Correctness and running time of the KG-map machine.** Let $m$ be a mode and $x$ a list of
bits, and let $F_m$ be the clique-to-independent-set map on bit strings for flip and the
independent-set-to-vertex-cover map for vc. From any configuration of the KG-map machine $M_m$
at its start label, with any internal bit, in which stack $X$ holds the input symbols
$\mathrm{bit}(b)$ for the bits $b$ of $x$, top first, and every other stack is empty, $M_m$
reaches the halting label in at most $3(|x| + 1)$ steps with the output stack $O$ equal to
$F_m(x)$, top first. -/
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
