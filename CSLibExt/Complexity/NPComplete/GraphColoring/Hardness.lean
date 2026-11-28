/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import CSLibExt.Computability.Complexity.Karp.ColorComplete
public import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import CSLibExt.Computability.Complexity.Host

/-!
# GRAPH COLORING is NP-hard

SAT reduces to GRAPH COLORING in polynomial time, by composing the SAT to 3-COLOR reduction
`Cslib.Complexity.Karp.reduceCol` with an edge-gadget transducer.

The 3-COLOR instances that `reduceCol` produces may list an edge more than once, so they are not
well formed GRAPH COLORING instances. The transducer replaces every edge `(u, v)` by six edges
on three fresh vertices `c, c + 1, c + 2`: the triangle `u, c, c + 1`, the edges from `c + 2` to
`c` and `c + 1`, and the edge `(c + 2, v)`. Every new edge has a fresh endpoint, so the new edge
list has no repeated or reversed entries and no loops, and since `c + 2` must take the color of
`u` in every 3-coloring, a loop-free graph is 3-colorable exactly when its replacement is
(`Hardness.colorable_target_iff`). The output is the canonical bitstring encoding of the
replacement graph with `K = 3`.

The transducer is an explicit `TM2` machine (`Transducer.prog`) that parses the unary graph
encoding, keeps the next fresh vertex as a unary counter, and writes binary numbers with the
existing unary-to-binary converter `PolynomialEncoding.UnaryNat`. Its exact behavior on every bit
string is the function `Transducer.convF` (`Transducer.start_run`), within `200000 (n + 1)^2`
steps, and `Host.isPolyTime_reduction` turns this into `Transducer.isPolyTime_convF`.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH COLORING
(chromatic number); R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Hardness

open Cslib.Complexity.Karp

/-- The six edges that replace an edge `(u, v)`, using the fresh vertices `c`, `c + 1` and
`c + 2`: a triangle `u, c, c + 1`, a vertex `c + 2` joined to `c` and `c + 1` (so in a
3-coloring it gets the color of `u`), and the edge `(c + 2, v)`. -/
def gadget (u v c : ℕ) : List (ℕ × ℕ) :=
  [(u, c), (u, c + 1), (c, c + 1), (c + 2, c), (c + 2, c + 1), (c + 2, v)]

/-- The gadgets of an edge list, with fresh vertices allocated from `c` on, three per edge. -/
def gad : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | c, (u, v) :: es => gadget u v c ++ gad (c + 3) es

/-- The GRAPH COLORING instance produced from a graph `(n, es)`: `n + 3 |es|` vertices, the
gadget edges, and `K = 3`. -/
def target (n : ℕ) (es : List (ℕ × ℕ)) : GraphColoringInstance :=
  (n + 3 * es.length, gad n es, 3)

/-- Structural invariant of the gadget list: no repeated entry, every pair has a fresh endpoint,
both endpoints are allocated and distinct, and no reversed pair occurs. -/
theorem gad_good (n : ℕ) :
    ∀ (es : List (ℕ × ℕ)) (c : ℕ), n ≤ c → (∀ e ∈ es, e.1 < n ∧ e.2 < n) →
      (gad c es).Nodup ∧ ∀ e ∈ gad c es, (c ≤ e.1 ∨ c ≤ e.2) ∧
        e.1 < c + 3 * es.length ∧ e.2 < c + 3 * es.length ∧ e.1 ≠ e.2 ∧
          (e.2, e.1) ∉ gad c es
  | [], c, _, _ => by simp [gad]
  | (u, v) :: es, c, hc, hb => by
    have huv := hb (u, v) (by simp)
    simp only at huv
    obtain ⟨ihn, ihm⟩ := gad_good n es (c + 3) (by omega)
      (fun e he => hb e (List.mem_cons_of_mem _ he))
    have tail_big : ∀ e ∈ gad (c + 3) es, c + 3 ≤ e.1 ∨ c + 3 ≤ e.2 :=
      fun e he => (ihm e he).1
    refine ⟨?_, fun e he => ?_⟩
    · rw [gad, List.nodup_append]
      refine ⟨?_, ihn, fun a ha b hb' hab => ?_⟩
      · simp only [gadget, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          Prod.mk.injEq, not_or, List.nodup_nil, not_false_eq_true, and_true]
        omega
      · subst hab
        have := tail_big a hb'
        simp only [gadget, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at this <;> omega
    · rw [gad, List.mem_append] at he
      simp only [List.length_cons]
      rcases he with he | he
      · simp only [gadget, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
          refine ⟨by omega, by omega, by omega, by omega, fun hr => ?_⟩ <;>
          rw [gad, List.mem_append] at hr <;>
          rcases hr with hr | hr <;>
          first
          | (simp only [gadget, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr;
             omega)
          | (have := tail_big _ hr; dsimp only at this; omega)
      · obtain ⟨h1, h2, h3, h4, h5⟩ := ihm e he
        refine ⟨by omega, by omega, by omega, h4, fun hr => ?_⟩
        rw [gad, List.mem_append] at hr
        rcases hr with hr | hr
        · simp only [gadget, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with hr | hr | hr | hr | hr | hr <;>
            simp only [Prod.ext_iff] at hr <;> omega
        · exact h5 hr

/-- The produced instance is well formed whenever the source edges are in range. -/
theorem wellFormed_target {n : ℕ} {es : List (ℕ × ℕ)} (hb : ∀ e ∈ es, e.1 < n ∧ e.2 < n) :
    WellFormed (target n es) := by
  obtain ⟨hn, hm⟩ := gad_good n es n le_rfl hb
  exact ⟨hn, fun e he => by
    obtain ⟨-, h1, h2, h3, h4⟩ := hm e he
    exact ⟨h1, h2, h3, h4⟩⟩

/-- The second color different from `k`. -/
def other₁ (k : Fin 3) : Fin 3 := k + 1

/-- The third color different from `k`. -/
def other₂ (k : Fin 3) : Fin 3 := k + 2

/-- Extend a coloring of the old vertices to the fresh gadget vertices. -/
def ext (f : ℕ → Fin 3) : ℕ → List (ℕ × ℕ) → ℕ → Fin 3
  | _, [] => f
  | c, (u, _) :: es => fun x =>
      if x = c then other₁ (f u) else if x = c + 1 then other₂ (f u)
      else if x = c + 2 then f u else ext f (c + 3) es x

theorem ext_old (f : ℕ → Fin 3) :
    ∀ (es : List (ℕ × ℕ)) (c x : ℕ), x < c → ext f c es x = f x
  | [], _, _, _ => rfl
  | (u, v) :: es, c, x, hx => by
    simp only [ext, show ¬ x = c by omega, show ¬ x = c + 1 by omega,
      show ¬ x = c + 2 by omega, ite_false]
    exact ext_old f es (c + 3) x (by omega)

private theorem fin3_forced : ∀ a b x y : Fin 3, a ≠ b → x ≠ a → x ≠ b → y ≠ a → y ≠ b →
    x = y := by decide

private theorem ext_proper (f : ℕ → Fin 3) (n : ℕ) :
    ∀ (es : List (ℕ × ℕ)) (c : ℕ), n ≤ c → (∀ e ∈ es, e.1 < n ∧ e.2 < n) →
      ColProper f es → ColProper (ext f c es) (gad c es)
  | [], _, _, _, _ => by simp [ColProper, gad]
  | (u, v) :: es, c, hc, hb, hf => by
    have huv := hb (u, v) (by simp)
    simp only at huv
    have hfu : f u ≠ f v := hf (u, v) (by simp)
    have ih := ext_proper f n es (c + 3) (by omega)
      (fun e he => hb e (List.mem_cons_of_mem _ he))
      (fun e he => hf e (List.mem_cons_of_mem _ he))
    have hold : ∀ x, x < c → ext f c ((u, v) :: es) x = f x :=
      fun x hx => ext_old f _ c x hx
    have hc0 : ext f c ((u, v) :: es) c = other₁ (f u) := by simp [ext]
    have hc1 : ext f c ((u, v) :: es) (c + 1) = other₂ (f u) := by simp [ext]
    have hc2 : ext f c ((u, v) :: es) (c + 2) = f u := by simp [ext]
    have htail : ∀ x, c + 3 ≤ x →
        ext f c ((u, v) :: es) x = ext f (c + 3) es x := by
      intro x hx
      simp only [ext, show ¬ x = c by omega, show ¬ x = c + 1 by omega,
        show ¬ x = c + 2 by omega, ite_false]
    intro e he
    rw [gad, List.mem_append] at he
    rcases he with he | he
    · have k1 : ∀ k : Fin 3, k ≠ other₁ k := by decide
      have k2 : ∀ k : Fin 3, k ≠ other₂ k := by decide
      have k3 : ∀ k : Fin 3, other₁ k ≠ other₂ k := by decide
      simp only [gadget, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
        simp only [hc0, hc1, hc2, hold u (by omega), hold v (by omega)]
      · exact k1 _
      · exact k2 _
      · exact k3 _
      · exact k1 _
      · exact k2 _
      · exact hfu
    · obtain ⟨h1, -⟩ := (gad_good n es (c + 3) (by omega)
        (fun e he => hb e (List.mem_cons_of_mem _ he))).2 e he
      have := ih e he
      -- both endpoints of a later gadget edge are either old or fresh beyond `c + 2`
      have hgood := (gad_good n es (c + 3) (by omega)
        (fun e he => hb e (List.mem_cons_of_mem _ he))).2 e he
      have hpt : ∀ x, (x < n ∨ c + 3 ≤ x) →
          ext f c ((u, v) :: es) x = ext f (c + 3) es x := by
        rintro x (hx | hx)
        · rw [hold x (by omega), ext_old f es (c + 3) x (by omega)]
        · exact htail x hx
      have hend : ∀ x, x = e.1 ∨ x = e.2 → x < n ∨ c + 3 ≤ x := by
        -- endpoints of gadgets from `c + 3` on are old vertices or fresh ones
        clear hpt this
        revert e
        intro e he _ _ x hx
        exact gad_endpoints n es (c + 3) (by omega)
          (fun e he => hb e (List.mem_cons_of_mem _ he)) e he x hx
      rw [hpt _ (hend _ (Or.inl rfl)), hpt _ (hend _ (Or.inr rfl))]
      exact this
where
  gad_endpoints (n : ℕ) : ∀ (es : List (ℕ × ℕ)) (c : ℕ), n ≤ c → (∀ e ∈ es, e.1 < n ∧ e.2 < n) →
      ∀ e ∈ gad c es, ∀ x, x = e.1 ∨ x = e.2 → x < n ∨ c ≤ x
    | [], _, _, _ => by simp [gad]
    | (u, v) :: es, c, hc, hb => by
      have huv := hb (u, v) (by simp)
      simp only at huv
      intro e he x hx
      rw [gad, List.mem_append] at he
      rcases he with he | he
      · simp only [gadget, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hx <;> omega
      · have := gad_endpoints n es (c + 3) (by omega)
          (fun e he => hb e (List.mem_cons_of_mem _ he)) e he x hx
        omega

private theorem proper_of_gad (g : ℕ → Fin 3) (n : ℕ) :
    ∀ (es : List (ℕ × ℕ)) (c : ℕ), n ≤ c → (∀ e ∈ es, e.1 < n ∧ e.2 < n) →
      ColProper g (gad c es) → ColProper g es
  | [], _, _, _, _ => by simp [ColProper]
  | (u, v) :: es, c, hc, hb, hg => by
    have huv := hb (u, v) (by simp)
    simp only at huv
    have hg' : ∀ e ∈ gadget u v c, g e.1 ≠ g e.2 := fun e he =>
      hg e (by rw [gad]; exact List.mem_append_left _ he)
    have e1 := hg' (u, c) (by simp [gadget])
    have e2 := hg' (u, c + 1) (by simp [gadget])
    have e3 := hg' (c, c + 1) (by simp [gadget])
    have e4 := hg' (c + 2, c) (by simp [gadget])
    have e5 := hg' (c + 2, c + 1) (by simp [gadget])
    have e6 := hg' (c + 2, v) (by simp [gadget])
    have hw : g (c + 2) = g u := fin3_forced _ _ _ _ e3 e4 e5 e1 e2
    have ih := proper_of_gad g n es (c + 3) (by omega)
      (fun e he => hb e (List.mem_cons_of_mem _ he))
      (fun e he => hg e (by rw [gad]; exact List.mem_append_right _ he))
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · dsimp only
      rw [← hw]
      exact e6
    · exact ih e he

/-- For loop-free source graphs with edges in range, the produced graph is 3-colorable exactly
when the source graph is. -/
theorem colorable_target_iff {n : ℕ} {es : List (ℕ × ℕ)}
    (hb : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) :
    (Graph (target n es)).Colorable 3 ↔ (edgeGraph n es).Colorable 3 := by
  have hb' : ∀ e ∈ es, e.1 < n ∧ e.2 < n := fun e he => ⟨(hb e he).1, (hb e he).2.1⟩
  obtain ⟨-, hm⟩ := gad_good n es n le_rfl hb'
  have ht : ∀ e ∈ gad n es, e.1 < n + 3 * es.length ∧ e.2 < n + 3 * es.length ∧ e.1 ≠ e.2 :=
    fun e he => ⟨(hm e he).2.1, (hm e he).2.2.1, (hm e he).2.2.2.1⟩
  change (edgeGraph (n + 3 * es.length) (gad n es)).Colorable 3 ↔ _
  rw [colorable_iff_exists_colProper ht, colorable_iff_exists_colProper hb]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, proper_of_gad g n es n le_rfl hb' hg⟩
  · rintro ⟨f, hf⟩
    exact ⟨ext f n es, ext_proper f n es n le_rfl hb' hf⟩

/-- Membership of the produced instance in GRAPH COLORING. -/
theorem graphColoringDec_target {n : ℕ} {es : List (ℕ × ℕ)}
    (hb : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) :
    graphColoringDec (BitstringEncoding.bitEncode (target n es)) = col3Dec (encodeE n es) := by
  have hb' : ∀ e ∈ es, e.1 < n ∧ e.2 < n := fun e he => ⟨(hb e he).1, (hb e he).2.1⟩
  apply Bool.eq_iff_iff.mpr
  rw [col3Dec_encodeE_eq_true]
  simp only [graphColoringDec, BitstringEncoding.bitDecode_bitEncode, decide_eq_true_eq]
  change WellFormed (target n es) ∧ (Graph (target n es)).Colorable 3 ↔ _
  rw [colorable_target_iff hb]
  exact ⟨fun h => ⟨hb', h.2⟩, fun h => ⟨wellFormed_target hb', h.2⟩⟩

/-- Every output of the SAT to 3-COLOR reduction is the encoding of a loop-free graph whose edges
are in range. -/
theorem reduceCol_range (x : List Bool) :
    ∃ n es, reduceCol x = encodeE n es ∧ ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2 := by
  unfold reduceCol
  split
  · rename_i φ _
    refine ⟨_, _, rfl, fun e he => ?_⟩
    exact (colGood_colSt φ).em_lt e (List.mem_reverse.1 he)
  · exact ⟨_, _, rfl, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Hardness

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Transducer

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Cslib.Complexity Cslib.Complexity.Karp
open Cslib.Complexity.PolynomialEncoding

/-- The transducer's own stacks, all over `Bool`: input, vertex counter, the two endpoints of the
current edge in unary, a copy buffer, the reversed output accumulator, a payload buffer and a
garbage stack. -/
inductive Own | inp | cnt | uu | vv | tmp | acc | pay | gb
  deriving DecidableEq

instance : Fintype Own where
  elems := ⟨↑[Own.inp, .cnt, .uu, .vv, .tmp, .acc, .pay, .gb], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Stacks: the unary-to-binary converter's workspace and the transducer's own stacks. -/
inductive K | ss (k : EmitSS.K) | own (o : Own)
  deriving DecidableEq

noncomputable instance : Fintype K := Fintype.ofEquiv (EmitSS.K ⊕ Own)
  { toFun := fun | .inl k => .ss k | .inr o => .own o
    invFun := fun | .ss k => .inl k | .own o => .inr o
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun x => by cases x <;> rfl }

@[reducible] def Γ : K → Type
  | .ss k => EmitSS.Γ k
  | .own _ => Bool

instance instFintypeΓ : ∀ k : K, Fintype (Γ k)
  | .ss k => by cases k <;> infer_instance
  | .own _ => inferInstanceAs (Fintype Bool)

/-- Where a number written at a call site comes from. -/
inductive Src | c | u | v
  deriving DecidableEq

def Src.stack : Src → Own
  | .c => .cnt
  | .u => .uu
  | .v => .vv

/-- The thirteen call sites of the converter: per gadget pair, first the second component (raw),
then the first component (framed); the last site writes the vertex count. -/
def src (j : Fin 13) : Src :=
  match j.val with
  | 1 | 3 => .u
  | 10 => .v
  | _ => .c

/-- Offset added to the vertex counter at a call site. -/
def offs (j : Fin 13) : ℕ :=
  match j.val with
  | 2 | 4 | 8 => 1
  | 7 | 9 | 11 => 2
  | _ => 0

/-- Whether a call site writes a framed number. -/
def framed (j : Fin 13) : Bool := j.val % 2 == 1 || j.val == 12

/-- Labels. -/
inductive Lab
  | rdN | popN | top | rdU | popU | rdV | popV
  | cp1 (j : Fin 13) | cp2 (j : Fin 13) | off (j : Fin 13) | un (j : Fin 13) (l : UnaryNat.Lab)
  | fr (k : Fin 6) | clU | clV | inc | f1 | f2 | f3 | f4 | done
  deriving DecidableEq

/-- Label after a call site. -/
def next (j : Fin 13) : Lab :=
  if h : j.val = 12 then .done
  else if j.val % 2 = 1 then .fr ⟨j.val / 2, by have := j.isLt; omega⟩
  else .cp1 ⟨j.val + 1, by have := j.isLt; omega⟩

/-- Label after framing a pair. -/
def nextFr (k : Fin 6) : Lab :=
  if k.val = 5 then .clU else .cp1 ⟨2 * k.val + 2, by have := k.isLt; omega⟩

def unLabel (j : Fin 13) (l : UnaryNat.Lab) : Lab :=
  if l = .done then next j else .un j l

def emb : SEmb EmitSS.Γ Γ where
  e := K.ss
  inj _ _ h := K.ss.inj h
  ι _ := Equiv.refl _

/-- Leading ones are bits, a zero ends the block. -/
def dOne (b : Bool) : Option Bool := if b then some true else none

def prog : Lab → TM2.Stmt Γ Lab Bool
  | .rdN => moveB (.own .inp) (.own .cnt) dOne (fun _ => true) .rdN .popN
  | .popN => .pop (.own .inp) (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .top) (.goto fun _ => .done)
  | .top => .peek (.own .inp) (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .rdU) (.goto fun _ => .f1)
  | .rdU => moveB (.own .inp) (.own .uu) dOne (fun _ => true) .rdU .popU
  | .popU => .pop (.own .inp) (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .rdV) (.goto fun _ => .done)
  | .rdV => moveB (.own .inp) (.own .vv) dOne (fun _ => true) .rdV .popV
  | .popV => .pop (.own .inp) (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .cp1 0) (.goto fun _ => .done)
  | .cp1 j => moveB (.own (src j).stack) (.own .tmp) some id (.cp1 j) (.cp2 j)
  | .cp2 j => splitB (.own .tmp) (.own (src j).stack) (.ss .A) some id (fun _ => EmitSS.U)
      (.cp2 j) (.off j)
  | .off j => emitR (.ss .A) (cnt EmitSS.U (offs j)) (.un j (.emit .hv))
  | .un j l => mapS emb (unLabel j) (UnaryNat.prog (framed j) l)
  | .fr k => emitFrame (.ss .O) (.own .acc) some id (.fr k) (nextFr k)
  | .clU => moveB (.own .uu) (.own .gb) some id .clU .clV
  | .clV => moveB (.own .vv) (.own .gb) some id .clV .inc
  | .inc => .push (.own .cnt) (fun _ => true) <| .push (.own .cnt) (fun _ => true) <|
      .push (.own .cnt) (fun _ => true) <| .goto fun _ => .top
  | .f1 => emitR (.ss .O) (Computability.encodeNat 3) .f2
  | .f2 => moveB (.own .acc) (.own .pay) some id .f2 .f3
  | .f3 => emitFrame (.own .pay) (.own .acc) some id .f3 .f4
  | .f4 => moveB (.own .acc) (.ss .O) some id .f4 (.cp1 12)
  | .done => .halt

theorem unLabel_of_ne {j : Fin 13} {l : UnaryNat.Lab} (h : l ≠ .done) :
    unLabel j l = .un j l := by
  simp [unLabel, h]

theorem prog_un (j : Fin 13) (l : UnaryNat.Lab) :
    prog (.un j l) = mapS emb (unLabel j) (UnaryNat.prog (framed j) l) := rfl

theorem unaryNat_done (b : Bool) : UnaryNat.prog b .done = .halt := rfl

theorem embeds (j : Fin 13) : Embeds emb (unLabel j) (UnaryNat.prog (framed j)) prog := by
  intro l
  by_cases h : l = .done
  · subst h
    exact Or.inr (unaryNat_done _)
  · rw [unLabel_of_ne h]
    exact Or.inl (prog_un j l)

/-- The value a source stack holds. -/
def Src.val : Src → ℕ → ℕ → ℕ → ℕ
  | .c, a, _, _ => a
  | .u, _, a, _ => a
  | .v, _, _, a => a

/-- The configurations the transducer passes through between primitives. -/
def cfg (x : List Bool) (c u v : ℕ) (o acc pay g : List Bool) : ∀ k, List (Γ k)
  | .ss .O => o
  | .ss _ => []
  | .own .inp => x
  | .own .cnt => List.replicate c true
  | .own .uu => List.replicate u true
  | .own .vv => List.replicate v true
  | .own .tmp => []
  | .own .acc => acc
  | .own .pay => pay
  | .own .gb => g

theorem cfg_src (s : Src) (x : List Bool) (c u v : ℕ) (o acc pay g : List Bool) :
    cfg x c u v o acc pay g (.own s.stack) = List.replicate (s.val c u v) true := by
  cases s <;> rfl

/-- The number written at call site `j`. -/
def siteVal (j : Fin 13) (c u v : ℕ) : ℕ := (src j).val c u v + offs j

/-- The bits written at call site `j` above the current output. -/
def siteOut (j : Fin 13) (c u v : ℕ) : List Bool :=
  if framed j then delimit (Computability.encodeNat (siteVal j c u v))
  else Computability.encodeNat (siteVal j c u v)

theorem cfg_ext {S : ∀ k, List (Γ k)} {x : List Bool} {c u v : ℕ} {o acc pay g : List Bool}
    (hss : ∀ k, k ≠ EmitSS.K.O → S (.ss k) = []) (hO : S (.ss .O) = o)
    (hi : S (.own .inp) = x) (hc : S (.own .cnt) = List.replicate c true)
    (hu : S (.own .uu) = List.replicate u true) (hv : S (.own .vv) = List.replicate v true)
    (ht : S (.own .tmp) = []) (ha : S (.own .acc) = acc) (hp : S (.own .pay) = pay)
    (hg : S (.own .gb) = g) : S = cfg x c u v o acc pay g := by
  funext k
  rcases k with k | o
  · by_cases hk : k = .O
    · subst hk; exact hO
    · rw [hss k hk]; cases k <;> first | rfl | exact absurd rfl hk
  · cases o <;> assumption

theorem cfg_ss_ne (x : List Bool) (c u v : ℕ) (o acc pay g : List Bool) (k : EmitSS.K)
    (hk : k ≠ .O) : cfg x c u v o acc pay g (.ss k) = [] := by
  cases k <;> first | rfl | exact absurd rfl hk

/-- One call site: copy the source count into the converter, add the offset, and convert. -/
theorem site_run (j : Fin 13) (x : List Bool) (c u v : ℕ) (o acc g : List Bool) (w : Bool) :
    ∃ w', RunLe prog (720 * siteVal j c u v + 400)
      ⟨some (.cp1 j), w, cfg x c u v o acc [] g⟩
      ⟨some (next j), w', cfg x c u v (siteOut j c u v ++ o) acc [] g⟩ := by
  set s := (src j).val c u v with hs
  have hsrc : (src j).stack ≠ Own.tmp := by cases src j <;> decide
  -- copy the source onto the buffer
  obtain ⟨w₁, S₁, r₁, h1a, h1b, h1f⟩ := moveB_run (M := prog) (self := Lab.cp1 j)
    (next := .cp2 j) (a := K.own (src j).stack) (b := .own .tmp) (d := some) (g := id) rfl
    (by simp [hsrc]) (List.replicate s true) (List.replicate s true) [] w
    (cfg x c u v o acc [] g) (by rw [cfg_src]; simp [hs]) (by simp [IsBitBlock]) rfl
  -- copy it back and into the converter's counter
  obtain ⟨S₂, r₂, h2a, h2b, h2c, h2f⟩ := splitB_run (M := prog) (self := Lab.cp2 j)
    (next := .off j) (a := K.own .tmp) (b := .own (src j).stack) (c := .ss .A) (d := some)
    (gb := id) (gc := fun _ => EmitSS.U) rfl (by simp [Ne.symm hsrc]) (by simp) (by simp)
    id (fun _ => rfl) (List.replicate s true) [] w₁ S₁ rfl (by simpa [cfg] using h1b)
  have r₃ := emitR_run (M := prog) (self := Lab.off j) (next := .un j (.emit .hv))
    (k := K.ss .A) (ys := cnt EmitSS.U (offs j)) rfl false S₂
  set S₃ := update S₂ (K.ss .A) (cnt EmitSS.U (offs j) ++ S₂ (K.ss .A)) with hS₃
  have hA3 : S₃ (.ss .A) = cnt EmitSS.U (siteVal j c u v) := by
    rw [hS₃, update_self, h2c, h1f _ (by simp) (by simp)]
    simp only [cfg, List.map_replicate, List.reverse_replicate, List.append_nil, cnt,
      List.replicate_append_replicate, siteVal]
    congr 1
    omega
  have hss3 : ∀ k, k ≠ EmitSS.K.A → S₃ (.ss k) = cfg x c u v o acc [] g (.ss k) := by
    intro k hk
    rw [hS₃, update_of_ne (by simpa using hk), h2f _ (by simp) (by simp) (by simpa using hk),
      h1f _ (by simp) (by simp)]
  have hown3 : ∀ q, S₃ (.own q) = cfg x c u v o acc [] g (.own q) := by
    intro q
    rw [hS₃, update_of_ne (by simp)]
    by_cases hq : q = Own.tmp
    · subst hq; rw [h2a]; rfl
    by_cases hq' : q = (src j).stack
    · subst hq'; rw [h2b, h1a, cfg_src]; simp [hs]
    · rw [h2f _ (by simpa using hq) (by simpa using hq') (by simp),
        h1f _ (by simpa using hq') (by simpa using hq)]
  -- the embedded converter
  let Si : ∀ k, List (EmitSS.Γ k) := fun k => S₃ (.ss k)
  have hag : Agree emb Si S₃ := fun k => by change S₃ (.ss k) = (S₃ (.ss k)).map id; simp
  have hstart : unLabel j (.emit .hv) = .un j (.emit .hv) := unLabel_of_ne (by simp)
  have hdone : unLabel j .done = next j := by simp [unLabel]
  have finish : ∀ (w₂ : Bool) (U : ∀ k, List (EmitSS.Γ k)) (B : ℕ),
      RunLe (UnaryNat.prog (framed j)) B ⟨some (.emit .hv), false, Si⟩
        ⟨some .done, w₂, U⟩ →
      U .O = siteOut j c u v ++ o → (∀ k, k ≠ EmitSS.K.O → U k = []) →
      B ≤ 710 * siteVal j c u v + 306 →
      ∃ w', RunLe prog (720 * siteVal j c u v + 400)
        ⟨some (.cp1 j), w, cfg x c u v o acc [] g⟩
        ⟨some (next j), w', cfg x c u v (siteOut j c u v ++ o) acc [] g⟩ := by
    intro w₂ U B hr hUO hU hB
    obtain ⟨T, hT, hTa, hTf⟩ := runLe_embed (unLabel j) (embeds j) hr hag
    rw [hstart, hdone] at hT
    have hTss : ∀ k, T (.ss k) = U k := fun k => by
      have := hTa k; change T (.ss k) = (U k).map id at this; simpa using this
    have hTeq : T = cfg x c u v (siteOut j c u v ++ o) acc [] g := by
      apply cfg_ext
      · intro k hk; rw [hTss, hU k hk]
      · rw [hTss, hUO]
      all_goals first
        | (rw [hTf _ (fun k => by simp [emb])]; exact hown3 _)
    subst hTeq
    refine ⟨w₂, ((((r₁.trans r₂).trans r₃).le le_rfl).trans hT).mono ?_⟩
    have : s ≤ siteVal j c u v := by simp [siteVal, hs]
    simp only [List.length_replicate]
    omega
  cases hf : framed j
  · obtain ⟨w₂, U, hr, hUO, hUA, hUH, hUT, hUX, hUf⟩ := UnaryNat.run_raw (siteVal j c u v) o
      false Si hA3 ((hss3 .H (by decide)).trans rfl)
      ((hss3 .T (by decide)).trans rfl) ((hss3 .O (by decide)).trans rfl)
      ((hss3 .X (by decide)).trans rfl)
    rw [hf] at finish
    refine finish w₂ U _ hr (by simp [hUO, siteOut, hf]) (fun k hk => ?_) le_rfl
    by_cases hkA : k = .A; · subst hkA; exact hUA
    by_cases hkH : k = .H; · subst hkH; exact hUH
    by_cases hkT : k = .T; · subst hkT; exact hUT
    by_cases hkX : k = .X; · subst hkX; exact hUX
    rw [hUf k hkA hkH hkT hk hkX]
    exact (hss3 k hkA).trans (by cases k <;> first | rfl | exact absurd rfl hk)
  · obtain ⟨U, hr, hUO, hUA, hUH, hUT, hUf⟩ := UnaryNat.run_framed (siteVal j c u v) o
      false Si hA3 ((hss3 .H (by decide)).trans rfl)
      ((hss3 .T (by decide)).trans rfl) ((hss3 .O (by decide)).trans rfl)
    rw [hf] at finish
    refine finish false U _ hr (by simp [hUO, siteOut, hf]) (fun k hk => ?_) (by omega)
    by_cases hkA : k = .A; · subst hkA; exact hUA
    by_cases hkH : k = .H; · subst hkH; exact hUH
    by_cases hkT : k = .T; · subst hkT; exact hUT
    rw [hUf k hkA hkH hkT hk]
    exact (hss3 k hkA).trans (by cases k <;> first | rfl | exact absurd rfl hk)

theorem next_even (k : Fin 6) :
    next ⟨2 * k.val, by omega⟩ = .cp1 ⟨2 * k.val + 1, by omega⟩ := by
  have := k.isLt
  simp only [next]
  split_ifs <;> first | omega | rfl

theorem next_odd (k : Fin 6) : next ⟨2 * k.val + 1, by omega⟩ = .fr k := by
  have := k.isLt
  simp only [next]
  split_ifs <;> first | omega | (congr 1; ext; simp only; omega)

/-- One gadget pair: write its second component raw, then its first component framed, and frame
the pair onto the reversed accumulator. -/
theorem pair_run (k : Fin 6) (x : List Bool) (c u v : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w', RunLe prog (720 * siteVal ⟨2 * k.val, by omega⟩ c u v +
        720 * siteVal ⟨2 * k.val + 1, by omega⟩ c u v + 801 +
        (siteOut ⟨2 * k.val + 1, by omega⟩ c u v ++ siteOut ⟨2 * k.val, by omega⟩ c u v).length)
      ⟨some (.cp1 ⟨2 * k.val, by omega⟩), w, cfg x c u v [] acc [] g⟩
      ⟨some (nextFr k), w', cfg x c u v []
        ((delimit (siteOut ⟨2 * k.val + 1, by omega⟩ c u v ++
          siteOut ⟨2 * k.val, by omega⟩ c u v)).reverse ++ acc) [] g⟩ := by
  obtain ⟨w₁, r₁⟩ := site_run ⟨2 * k.val, by omega⟩ x c u v [] acc g w
  rw [next_even] at r₁
  obtain ⟨w₂, r₂⟩ := site_run ⟨2 * k.val + 1, by omega⟩ x c u v
    (siteOut ⟨2 * k.val, by omega⟩ c u v ++ []) acc g w₁
  rw [next_odd] at r₂
  set P := siteOut ⟨2 * k.val + 1, by omega⟩ c u v ++ siteOut ⟨2 * k.val, by omega⟩ c u v
  obtain ⟨S, r₃, h3a, h3b, h3f⟩ := emitFrame_run (M := prog) (self := Lab.fr k)
    (next := nextFr k) (a := K.ss .O) (b := .own .acc) (d := some) (g := id) rfl (by simp)
    id (fun _ => rfl) P [] w₂ (cfg x c u v (siteOut ⟨2 * k.val + 1, by omega⟩ c u v ++
      (siteOut ⟨2 * k.val, by omega⟩ c u v ++ [])) acc [] g) rfl (by simp [cfg, P])
  have hS : S = cfg x c u v [] ((delimit P).reverse ++ acc) [] g := by
    apply cfg_ext
    · intro k hk
      rw [h3f _ (by simpa using hk) (by simp)]
      exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk
    · exact h3a
    all_goals first
      | (rw [h3f _ (by simp) (by simp)]; rfl)
      | (rw [h3b]; simp [cfg])
  subst hS
  refine ⟨false, ((r₁.trans r₂).trans (r₃.le le_rfl)).mono ?_⟩
  omega

theorem siteVal_le (j : Fin 13) (c u v : ℕ) : siteVal j c u v ≤ c + u + v + 2 := by
  have h1 : offs j ≤ 2 := by unfold offs; split <;> omega
  have h2 : (src j).val c u v ≤ c + u + v := by cases src j <;> simp [Src.val] <;> omega
  unfold siteVal
  omega

theorem siteOut_length_le (j : Fin 13) (c u v : ℕ) :
    (siteOut j c u v).length ≤ 2 * siteVal j c u v + 1 := by
  have h := EmitSS.encodeNat_length_le (siteVal j c u v)
  unfold siteOut
  split
  · simp only [length_delimit]; omega
  · omega

theorem pair_run' (k : Fin 6) (x : List Bool) (c u v : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w', RunLe prog (1450 * (c + u + v + 2) + 810)
      ⟨some (.cp1 ⟨2 * k.val, by omega⟩), w, cfg x c u v [] acc [] g⟩
      ⟨some (nextFr k), w', cfg x c u v []
        ((delimit (siteOut ⟨2 * k.val + 1, by omega⟩ c u v ++
          siteOut ⟨2 * k.val, by omega⟩ c u v)).reverse ++ acc) [] g⟩ := by
  obtain ⟨w', r⟩ := pair_run k x c u v acc g w
  refine ⟨w', r.mono ?_⟩
  have h1 := siteVal_le ⟨2 * k.val, by omega⟩ c u v
  have h2 := siteVal_le ⟨2 * k.val + 1, by omega⟩ c u v
  have h3 := siteOut_length_le ⟨2 * k.val, by omega⟩ c u v
  have h4 := siteOut_length_le ⟨2 * k.val + 1, by omega⟩ c u v
  simp only [List.length_append]
  omega

/-- The bits of one encoded edge `(p, q)` inside the framed edge list. -/
def pairBits (p q : ℕ) : List Bool :=
  delimit (delimit (Computability.encodeNat p) ++ Computability.encodeNat q)

/-- The bits of the six gadget edges for an edge `(u, v)` with fresh vertices from `c`. -/
def gadBits (u v c : ℕ) : List Bool :=
  pairBits u c ++ pairBits u (c + 1) ++ pairBits c (c + 1) ++ pairBits (c + 2) c ++
    pairBits (c + 2) (c + 1) ++ pairBits (c + 2) v

/-- The six gadget pairs of one edge. -/
theorem pairs_run (x : List Bool) (c u v : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w', RunLe prog (6 * (1450 * (c + u + v + 2) + 810))
      ⟨some (.cp1 0), w, cfg x c u v [] acc [] g⟩
      ⟨some .clU, w', cfg x c u v [] ((gadBits u v c).reverse ++ acc) [] g⟩ := by
  obtain ⟨w₀, r₀⟩ := pair_run' 0 x c u v acc g w
  obtain ⟨w₁, r₁⟩ := pair_run' 1 x c u v _ g w₀
  obtain ⟨w₂, r₂⟩ := pair_run' 2 x c u v _ g w₁
  obtain ⟨w₃, r₃⟩ := pair_run' 3 x c u v _ g w₂
  obtain ⟨w₄, r₄⟩ := pair_run' 4 x c u v _ g w₃
  obtain ⟨w₅, r₅⟩ := pair_run' 5 x c u v _ g w₄
  have r := ((((r₀.trans r₁).trans r₂).trans r₃).trans r₄).trans r₅
  have hout : (delimit (siteOut ⟨2 * (5 : Fin 6).val + 1, by omega⟩ c u v ++
        siteOut ⟨2 * (5 : Fin 6).val, by omega⟩ c u v)).reverse ++
      ((delimit (siteOut ⟨2 * (4 : Fin 6).val + 1, by omega⟩ c u v ++
        siteOut ⟨2 * (4 : Fin 6).val, by omega⟩ c u v)).reverse ++
      ((delimit (siteOut ⟨2 * (3 : Fin 6).val + 1, by omega⟩ c u v ++
        siteOut ⟨2 * (3 : Fin 6).val, by omega⟩ c u v)).reverse ++
      ((delimit (siteOut ⟨2 * (2 : Fin 6).val + 1, by omega⟩ c u v ++
        siteOut ⟨2 * (2 : Fin 6).val, by omega⟩ c u v)).reverse ++
      ((delimit (siteOut ⟨2 * (1 : Fin 6).val + 1, by omega⟩ c u v ++
        siteOut ⟨2 * (1 : Fin 6).val, by omega⟩ c u v)).reverse ++
      ((delimit (siteOut ⟨2 * (0 : Fin 6).val + 1, by omega⟩ c u v ++
        siteOut ⟨2 * (0 : Fin 6).val, by omega⟩ c u v)).reverse ++ acc))))) =
      (gadBits u v c).reverse ++ acc := by
    simp [siteOut, siteVal, src, offs, framed, Src.val, gadBits, pairBits,
      List.reverse_append, List.append_assoc]
  rw [hout] at r
  exact ⟨w₅, r.mono (by omega)⟩

theorem cfg_update_inp (x r : List Bool) (c u v : ℕ) (o acc pay g : List Bool) :
    update (cfg x c u v o acc pay g) (.own .inp) r = cfg r c u v o acc pay g := by
  funext k
  rcases k with k | q
  · rw [update_of_ne (by simp)]; cases k <;> rfl
  · cases q <;> simp [cfg]

theorem cfg_update_cnt (x : List Bool) (c c' u v : ℕ) (o acc pay g : List Bool) :
    update (cfg x c u v o acc pay g) (.own .cnt) (List.replicate c' true) =
      cfg x c' u v o acc pay g := by
  funext k
  rcases k with k | q
  · rw [update_of_ne (by simp)]; cases k <;> rfl
  · cases q <;> simp [cfg]


theorem isBitBlock_ones (n : ℕ) :
    IsBitBlock dOne (List.replicate n true) (List.replicate n true) := by
  simp [IsBitBlock, dOne]

theorem pop_step (self yes : Lab) (hp : prog self = .pop (.own .inp) (fun _ o => o.isSome)
      (.branch id (.goto fun _ => yes) (.goto fun _ => .done)))
    (x : List Bool) (c u v : ℕ) (o acc pay g : List Bool) (w b : Bool) (rest : List Bool)
    (hx : x = b :: rest) :
    Run prog 1 ⟨some self, w, cfg x c u v o acc pay g⟩
      ⟨some yes, true, cfg rest c u v o acc pay g⟩ := by
  apply Run.single
  subst hx
  rw [← cfg_update_inp (b :: rest) rest]
  simp only [hp, TM2.stepAux]
  rw [show cfg (b :: rest) c u v o acc pay g (.own .inp) = b :: rest from rfl]
  simp

theorem pop_fail (self yes : Lab) (hp : prog self = .pop (.own .inp) (fun _ o => o.isSome)
      (.branch id (.goto fun _ => yes) (.goto fun _ => .done)))
    (c u v : ℕ) (o acc pay g : List Bool) (w : Bool) :
    Run prog 1 ⟨some self, w, cfg [] c u v o acc pay g⟩
      ⟨some .done, false, cfg [] c u v o acc pay g⟩ := by
  apply Run.single
  conv_rhs => rw [← cfg_update_inp [] []]
  simp only [hp, TM2.stepAux]
  rw [show cfg [] c u v o acc pay g (.own .inp) = [] from rfl]
  simp

theorem top_step (x : List Bool) (hx : x ≠ []) (c u v : ℕ) (o acc pay g : List Bool) (w : Bool) :
    Run prog 1 ⟨some .top, w, cfg x c u v o acc pay g⟩
      ⟨some .rdU, true, cfg x c u v o acc pay g⟩ := by
  obtain ⟨b, r, rfl⟩ := List.exists_cons_of_ne_nil hx
  exact Run.single (by simp [prog, TM2.stepAux, cfg])

theorem top_empty (c u v : ℕ) (o acc pay g : List Bool) (w : Bool) :
    Run prog 1 ⟨some .top, w, cfg [] c u v o acc pay g⟩
      ⟨some .f1, false, cfg [] c u v o acc pay g⟩ :=
  Run.single (by simp [prog, TM2.stepAux, cfg])

theorem rdU_run (n : ℕ) (rest : List Bool) (hr : EndsBitBlock dOne rest) (c : ℕ)
    (acc g : List Bool) (w : Bool) :
    ∃ w', Run prog (n + 1) ⟨some .rdU, w, cfg (List.replicate n true ++ rest) c 0 0 [] acc [] g⟩
      ⟨some .popU, w', cfg rest c n 0 [] acc [] g⟩ := by
  obtain ⟨w', S, r, ha, hb, hf⟩ := moveB_run (M := prog) (self := Lab.rdU) (next := .popU)
    (a := K.own .inp) (b := .own .uu) (d := dOne) (g := fun _ => true) rfl (by simp)
    (List.replicate n true) (List.replicate n true) rest w
    (cfg (List.replicate n true ++ rest) c 0 0 [] acc [] g) rfl (isBitBlock_ones n) hr
  have e : S = cfg rest c n 0 [] acc [] g := by
    apply cfg_ext
    all_goals first
      | (intro k hk; rw [hf _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk)
      | (simpa [cfg] using ha)
      | (simpa [cfg] using hb)
      | (rw [hf _ (by simp) (by simp)]; rfl)
  subst e
  exact ⟨w', r.of_eq (by simp)⟩

theorem rdV_run (n : ℕ) (rest : List Bool) (hr : EndsBitBlock dOne rest) (c u : ℕ)
    (acc g : List Bool) (w : Bool) :
    ∃ w', Run prog (n + 1) ⟨some .rdV, w, cfg (List.replicate n true ++ rest) c u 0 [] acc [] g⟩
      ⟨some .popV, w', cfg rest c u n [] acc [] g⟩ := by
  obtain ⟨w', S, r, ha, hb, hf⟩ := moveB_run (M := prog) (self := Lab.rdV) (next := .popV)
    (a := K.own .inp) (b := .own .vv) (d := dOne) (g := fun _ => true) rfl (by simp)
    (List.replicate n true) (List.replicate n true) rest w
    (cfg (List.replicate n true ++ rest) c u 0 [] acc [] g) rfl (isBitBlock_ones n) hr
  have e : S = cfg rest c u n [] acc [] g := by
    apply cfg_ext
    all_goals first
      | (intro k hk; rw [hf _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk)
      | (simpa [cfg] using ha)
      | (simpa [cfg] using hb)
      | (rw [hf _ (by simp) (by simp)]; rfl)
  subst e
  exact ⟨w', r.of_eq (by simp)⟩

theorem rdN_run (n : ℕ) (rest : List Bool) (hr : EndsBitBlock dOne rest) (w : Bool) :
    ∃ w', Run prog (n + 1) ⟨some .rdN, w, cfg (List.replicate n true ++ rest) 0 0 0 [] [] [] []⟩
      ⟨some .popN, w', cfg rest n 0 0 [] [] [] []⟩ := by
  obtain ⟨w', S, r, ha, hb, hf⟩ := moveB_run (M := prog) (self := Lab.rdN) (next := .popN)
    (a := K.own .inp) (b := .own .cnt) (d := dOne) (g := fun _ => true) rfl (by simp)
    (List.replicate n true) (List.replicate n true) rest w
    (cfg (List.replicate n true ++ rest) 0 0 0 [] [] [] []) rfl (isBitBlock_ones n) hr
  have e : S = cfg rest n 0 0 [] [] [] [] := by
    apply cfg_ext
    all_goals first
      | (intro k hk; rw [hf _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk)
      | (simpa [cfg] using ha)
      | (simpa [cfg] using hb)
      | (rw [hf _ (by simp) (by simp)]; rfl)
  subst e
  exact ⟨w', r.of_eq (by simp)⟩

/-- Discard the endpoints and advance the vertex counter by three. -/
theorem clean_run (x : List Bool) (c u v : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w', Run prog (u + v + 3) ⟨some .clU, w, cfg x c u v [] acc [] g⟩
      ⟨some .top, w', cfg x (c + 3) 0 0 [] acc []
        (List.replicate v true ++ (List.replicate u true ++ g))⟩ := by
  obtain ⟨w₁, S₁, r₁, h1a, h1b, h1f⟩ := moveB_run (M := prog) (self := Lab.clU) (next := .clV)
    (a := K.own .uu) (b := .own .gb) (d := some) (g := id) rfl (by simp)
    (List.replicate u true) (List.replicate u true) [] w (cfg x c u v [] acc [] g)
    (by simp [cfg]) (by simp [IsBitBlock]) rfl
  have e₁ : S₁ = cfg x c 0 v [] acc [] (List.replicate u true ++ g) := by
    apply cfg_ext
    · intro k hk; rw [h1f _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk
    · rw [h1f _ (by simp) (by simp)]; rfl
    all_goals first
      | (simpa [cfg] using h1a)
      | (simpa [cfg] using h1b)
      | (rw [h1f _ (by simp) (by simp)]; rfl)
  subst e₁
  obtain ⟨w₂, S₂, r₂, h2a, h2b, h2f⟩ := moveB_run (M := prog) (self := Lab.clV) (next := .inc)
    (a := K.own .vv) (b := .own .gb) (d := some) (g := id) rfl (by simp)
    (List.replicate v true) (List.replicate v true) [] w₁
    (cfg x c 0 v [] acc [] (List.replicate u true ++ g))
    (by simp [cfg]) (by simp [IsBitBlock]) rfl
  have e₂ : S₂ = cfg x c 0 0 [] acc [] (List.replicate v true ++ (List.replicate u true ++ g)) := by
    apply cfg_ext
    · intro k hk; rw [h2f _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk
    · rw [h2f _ (by simp) (by simp)]; rfl
    all_goals first
      | (simpa [cfg] using h2a)
      | (simpa [cfg] using h2b)
      | (rw [h2f _ (by simp) (by simp)]; rfl)
  subst e₂
  have r₃ : Run prog 1
      ⟨some .inc, w₂, cfg x c 0 0 [] acc [] (List.replicate v true ++ (List.replicate u true ++ g))⟩
      ⟨some .top, w₂, cfg x (c + 3) 0 0 [] acc []
        (List.replicate v true ++ (List.replicate u true ++ g))⟩ := by
    apply Run.single
    simp only [prog, TM2.stepAux]
    rw [show cfg x c 0 0 [] acc [] (List.replicate v true ++ (List.replicate u true ++ g))
      (.own .cnt) = List.replicate c true from rfl]
    simp only [update_idem, update_self]
    rw [show (true :: true :: true :: List.replicate c true) = List.replicate (c + 3) true by
      simp [List.replicate_succ], cfg_update_cnt]
  exact ⟨w₂, ((r₁.trans r₂).trans r₃).of_eq (by simp; omega)⟩

/-- One complete edge `(u, v)` of the input. -/
theorem edge_run (u v : ℕ) (r : List Bool) (c : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w' g', RunLe prog (8700 * (c + u + v + 2) + 4860 + 2 * u + 2 * v + 8)
      ⟨some .top, w, cfg (List.replicate u true ++ false :: (List.replicate v true ++ false :: r))
        c 0 0 [] acc [] g⟩
      ⟨some .top, w', cfg r (c + 3) 0 0 [] ((gadBits u v c).reverse ++ acc) [] g'⟩ := by
  have r₀ := top_step (List.replicate u true ++ false :: (List.replicate v true ++ false :: r))
    (by simp) c 0 0 [] acc [] g w
  obtain ⟨w₁, r₁⟩ := rdU_run u (false :: (List.replicate v true ++ false :: r)) rfl c acc g true
  have r₂ := pop_step .popU .rdV rfl (false :: (List.replicate v true ++ false :: r)) c u 0 [] acc
    [] g w₁ false _ rfl
  obtain ⟨w₃, r₃⟩ := rdV_run v (false :: r) rfl c u acc g true
  have r₄ := pop_step .popV (.cp1 0) rfl (false :: r) c u v [] acc [] g w₃ false _ rfl
  obtain ⟨w₅, r₅⟩ := pairs_run r c u v acc g true
  obtain ⟨w₆, r₆⟩ := clean_run r c u v ((gadBits u v c).reverse ++ acc) g w₅
  refine ⟨w₆, _, ((((r₀.trans r₁).trans r₂).trans r₃).trans r₄).le le_rfl |>.trans r₅ |>.trans
    (r₆.le le_rfl) |>.mono ?_⟩
  omega

theorem cfg_update_O (x : List Bool) (c u v : ℕ) (o o' acc pay g : List Bool) :
    update (cfg x c u v o acc pay g) (.ss .O) o' = cfg x c u v o' acc pay g := by
  funext k
  rcases k with k | q
  · by_cases hk : k = .O
    · subst hk; simp [cfg]
    · rw [update_of_ne (by simpa using hk)]; cases k <;> first | rfl | exact absurd rfl hk
  · rw [update_of_ne (by simp)]; cases q <;> rfl

/-- The end of the input: write `K = 3`, frame the accumulated edge list, and write the vertex
count. -/
theorem final_run (c : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w' T, RunLe prog (4 * acc.length + 720 * c + 410)
      ⟨some .top, w, cfg [] c 0 0 [] acc [] g⟩ ⟨some .done, w', T⟩ ∧
      T (.ss .O) = delimit (Computability.encodeNat c) ++ delimit acc.reverse ++
        Computability.encodeNat 3 := by
  have r₀ := top_empty c 0 0 [] acc [] g w
  have r₁ := emitR_run (M := prog) (self := Lab.f1) (next := .f2) (k := K.ss .O)
    (ys := Computability.encodeNat 3) rfl false (cfg [] c 0 0 [] acc [] g)
  rw [cfg_update_O] at r₁
  obtain ⟨w₂, S₂, r₂, h2a, h2b, h2f⟩ := moveB_run (M := prog) (self := Lab.f2) (next := .f3)
    (a := K.own .acc) (b := .own .pay) (d := some) (g := id) rfl (by simp) acc acc [] false
    (cfg [] c 0 0 (Computability.encodeNat 3 ++ []) acc [] g) (by simp [cfg])
    (by simp [IsBitBlock]) rfl
  have e₂ : S₂ = cfg [] c 0 0 (Computability.encodeNat 3) [] acc.reverse g := by
    apply cfg_ext
    all_goals first
      | (intro k hk; rw [h2f _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk)
      | (simpa [cfg] using h2a)
      | (simpa [cfg] using h2b)
      | (rw [h2f _ (by simp) (by simp)]; simp [cfg])
  subst e₂
  obtain ⟨S₃, r₃, h3a, h3b, h3f⟩ := emitFrame_run (M := prog) (self := Lab.f3) (next := .f4)
    (a := K.own .pay) (b := .own .acc) (d := some) (g := id) rfl (by simp) id (fun _ => rfl)
    acc.reverse [] w₂ (cfg [] c 0 0 (Computability.encodeNat 3) [] acc.reverse g) rfl
    (by simp [cfg])
  have e₃ : S₃ = cfg [] c 0 0 (Computability.encodeNat 3) (delimit acc.reverse).reverse [] g := by
    apply cfg_ext
    all_goals first
      | (intro k hk; rw [h3f _ (by simp) (by simp)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk)
      | (simpa [cfg] using h3a)
      | (simpa [cfg] using h3b)
      | (rw [h3f _ (by simp) (by simp)]; simp [cfg])
  subst e₃
  obtain ⟨w₄, S₄, r₄, h4a, h4b, h4f⟩ := moveB_run (M := prog) (self := Lab.f4) (next := .cp1 12)
    (a := K.own .acc) (b := .ss .O) (d := some) (g := id) rfl (by simp)
    (delimit acc.reverse).reverse (delimit acc.reverse).reverse [] false
    (cfg [] c 0 0 (Computability.encodeNat 3) (delimit acc.reverse).reverse [] g)
    (by simp [cfg]) (by simp [IsBitBlock]) rfl
  have e₄ : S₄ = cfg [] c 0 0 (delimit acc.reverse ++ Computability.encodeNat 3) [] [] g := by
    apply cfg_ext
    all_goals first
      | (intro k hk; rw [h4f _ (by simp) (by simpa using hk)]; exact cfg_ss_ne _ _ _ _ _ _ _ _ k hk)
      | (simpa [cfg] using h4a)
      | (simpa [cfg] using h4b)
      | (rw [h4f _ (by simp) (by simp)]; simp [cfg])
  subst e₄
  obtain ⟨w₅, r₅⟩ := site_run 12 [] c 0 0 (delimit acc.reverse ++ Computability.encodeNat 3)
    [] g w₄
  have hn : next 12 = .done := rfl
  rw [hn] at r₅
  refine ⟨w₅, _, ((((r₀.trans r₁).trans r₂).trans r₃).trans r₄).le le_rfl |>.trans r₅ |>.mono ?_,
    ?_⟩
  · have : siteVal 12 c 0 0 = c := rfl
    simp only [List.length_reverse, length_delimit, this]
    omega
  · have : siteOut 12 c 0 0 = delimit (Computability.encodeNat c) := rfl
    simp [cfg, this]

/-! ### The function the transducer computes -/

/-- The number of leading ones. -/
def ones (x : List Bool) : ℕ := (x.takeWhile id).length

theorem ones_split : ∀ x : List Bool, x = List.replicate (ones x) true ++ x.dropWhile id
  | [] => rfl
  | true :: t => by
    have := ones_split t
    simp only [ones, List.takeWhile_cons, id, ↓reduceIte, List.length_cons,
      List.dropWhile_cons, List.replicate_succ, List.cons_append] at this ⊢
    exact congrArg _ this
  | false :: t => by simp [ones]

theorem ends_dropWhile : ∀ x : List Bool, EndsBitBlock dOne (x.dropWhile id)
  | [] => rfl
  | true :: t => by simpa using ends_dropWhile t
  | false :: t => by simp [EndsBitBlock, dOne]

theorem dropWhile_length_le (x : List Bool) : (x.dropWhile id).length ≤ x.length :=
  (List.dropWhile_suffix _).length_le

theorem head_false {x r : List Bool} {b : Bool} (h : x.dropWhile id = b :: r) : b = false := by
  have := ends_dropWhile x
  rw [h] at this
  cases b
  · rfl
  · simp [EndsBitBlock, dOne] at this

/-- The edge loop as a function: the final vertex count and the gadget bits, or `none` when the
input ends inside an edge. -/
def edgesF (c : ℕ) (x : List Bool) : Option (ℕ × List Bool) :=
  if x = [] then some (c, []) else
  match h₁ : x.dropWhile id with
  | [] => none
  | _ :: r =>
    match h₂ : r.dropWhile id with
    | [] => none
    | _ :: t =>
      have : t.length < x.length := by
        have a := dropWhile_length_le x
        have b := dropWhile_length_le r
        rw [h₁] at a; rw [h₂] at b
        simp only [List.length_cons] at a b
        omega
      (edgesF (c + 3) t).map fun p => (p.1, gadBits (ones x) (ones r) c ++ p.2)
termination_by x.length

theorem length_split (x : List Bool) : x.length = ones x + (x.dropWhile id).length := by
  conv_lhs => rw [ones_split x]
  simp

theorem edgesF_nil {c : ℕ} : edgesF c [] = some (c, []) := by
  rw [edgesF]; simp

theorem edgesF_none₁ {c : ℕ} {x : List Bool} (hx : x ≠ []) (h₁ : x.dropWhile id = []) :
    edgesF c x = none := by
  rw [edgesF]; simp only [hx, ite_false]
  split
  · rfl
  · rename_i h; rw [h₁] at h; cases h

theorem edgesF_none₂ {c : ℕ} {x r : List Bool} {b : Bool} (hx : x ≠ [])
    (h₁ : x.dropWhile id = b :: r) (h₂ : r.dropWhile id = []) : edgesF c x = none := by
  rw [edgesF]; simp only [hx, ite_false]
  split
  · rfl
  · rename_i r' h
    rw [h₁] at h
    obtain ⟨-, rfl⟩ := List.cons.inj h
    split
    · rfl
    · rename_i h'; rw [h₂] at h'; cases h'

theorem edgesF_cons {c : ℕ} {x r t : List Bool} {b b' : Bool} (hx : x ≠ [])
    (h₁ : x.dropWhile id = b :: r) (h₂ : r.dropWhile id = b' :: t) :
    edgesF c x = (edgesF (c + 3) t).map fun p => (p.1, gadBits (ones x) (ones r) c ++ p.2) := by
  rw [edgesF]; simp only [hx, ite_false]
  split
  · rename_i h; rw [h₁] at h; cases h
  · rename_i r' h
    rw [h₁] at h
    obtain ⟨-, rfl⟩ := List.cons.inj h
    split
    · rename_i h'; rw [h₂] at h'; cases h'
    · rename_i t' h'
      rw [h₂] at h'
      obtain ⟨-, rfl⟩ := List.cons.inj h'
      rfl

/-- The output of the edge loop started with counter `c` and accumulator `acc`. -/
def loopOut (c : ℕ) (acc x : List Bool) : List Bool :=
  match edgesF c x with
  | none => []
  | some (N, be) => delimit (Computability.encodeNat N) ++ delimit (acc.reverse ++ be) ++
      Computability.encodeNat 3

/-- The transducer's function on all bit strings. -/
def convF (x : List Bool) : List Bool :=
  match x.dropWhile id with
  | [] => []
  | _ :: r => loopOut (ones x) [] r

theorem pairBits_length_le (p q : ℕ) : (pairBits p q).length ≤ 4 * p + 2 * q + 3 := by
  have hp := EmitSS.encodeNat_length_le p
  have hq := EmitSS.encodeNat_length_le q
  simp only [pairBits, length_delimit, List.length_append]
  omega

theorem gadBits_length_le (u v c : ℕ) : (gadBits u v c).length ≤ 40 * (c + u + v + 3) := by
  have := pairBits_length_le u c
  have := pairBits_length_le u (c + 1)
  have := pairBits_length_le c (c + 1)
  have := pairBits_length_le (c + 2) c
  have := pairBits_length_le (c + 2) (c + 1)
  have := pairBits_length_le (c + 2) v
  simp only [gadBits, List.length_append]
  omega

/-- The step bound of the edge loop. -/
def bnd (c L A : ℕ) : ℕ := 40000 * (c + 4 * L + 4) * (L + 1) + 4 * A + 1000

theorem bnd_step (c u v L A G : ℕ) (hG : G ≤ 40 * (c + u + v + 3)) :
    8700 * (c + u + v + 2) + 4860 + 2 * u + 2 * v + 8 + bnd (c + 3) L (G + A) ≤
      bnd c (L + u + v + 2) A := by
  unfold bnd
  have q1 : (c + 3 + 4 * L + 4) * (L + 1) ≤ (c + 4 * (L + u + v + 2) + 4) * (L + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have q2 : (c + 4 * (L + u + v + 2) + 4) * (L + u + v + 2 + 1) =
      (c + 4 * (L + u + v + 2) + 4) * (L + 1) +
        (c + 4 * (L + u + v + 2) + 4) * (u + v + 2) := by ring
  have q3 : (c + u + v + 3) * 2 ≤ (c + 4 * (L + u + v + 2) + 4) * (u + v + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : 40000 * (c + 4 * (L + u + v + 2) + 4) * (L + u + v + 2 + 1) =
      40000 * ((c + 4 * (L + u + v + 2) + 4) * (L + 1)) +
        40000 * ((c + 4 * (L + u + v + 2) + 4) * (u + v + 2)) := by
    rw [Nat.mul_assoc, q2, Nat.mul_add]
  have e0 : 40000 * (c + 3 + 4 * L + 4) * (L + 1) = 40000 * ((c + 3 + 4 * L + 4) * (L + 1)) :=
    Nat.mul_assoc _ _ _
  rw [e0, e1]
  omega

theorem loop_run (x : List Bool) (c : ℕ) (acc g : List Bool) (w : Bool) :
    ∃ w' T, RunLe prog (bnd c x.length acc.length)
      ⟨some .top, w, cfg x c 0 0 [] acc [] g⟩ ⟨some .done, w', T⟩ ∧
      T (.ss .O) = loopOut c acc x := by
  by_cases hx : x = []
  · subst hx
    obtain ⟨w', T, r, hT⟩ := final_run c acc g w
    refine ⟨w', T, r.mono ?_, ?_⟩
    · simp only [bnd, List.length_nil]; nlinarith
    · rw [hT, loopOut, edgesF_nil]; simp
  have hsplit := ones_split x
  have r₀ := top_step x hx c 0 0 [] acc [] g w
  cases h₁ : x.dropWhile id with
  | nil =>
    rw [h₁, List.append_nil] at hsplit
    obtain ⟨w₁, r₁⟩ := rdU_run (ones x) [] rfl c acc g true
    rw [List.append_nil, ← hsplit] at r₁
    have r₂ := pop_fail .popU .rdV rfl c (ones x) 0 [] acc [] g w₁
    refine ⟨false, _, ((r₀.trans r₁).trans r₂).le le_rfl |>.mono ?_, ?_⟩
    · have : ones x ≤ x.length := by rw [length_split x]; omega
      simp only [bnd]; nlinarith
    · simp [loopOut, edgesF_none₁ hx h₁, cfg]
  | cons b r =>
    have hb := head_false h₁
    subst hb
    rw [h₁] at hsplit
    have hsplit' := ones_split r
    obtain ⟨w₁, r₁⟩ := rdU_run (ones x) (false :: r) rfl c acc g true
    rw [← hsplit] at r₁
    have r₂ := pop_step .popU .rdV rfl (false :: r) c (ones x) 0 [] acc [] g w₁ false r rfl
    cases h₂ : r.dropWhile id with
    | nil =>
      rw [h₂, List.append_nil] at hsplit'
      obtain ⟨w₃, r₃⟩ := rdV_run (ones r) [] rfl c (ones x) acc g true
      rw [List.append_nil, ← hsplit'] at r₃
      have r₄ := pop_fail .popV (.cp1 0) rfl c (ones x) (ones r) [] acc [] g w₃
      refine ⟨false, _, ((((r₀.trans r₁).trans r₂).trans r₃).trans r₄).le le_rfl |>.mono ?_, ?_⟩
      · have h1 : ones x + 1 + r.length ≤ x.length := by
          rw [length_split x, h₁, List.length_cons]; omega
        have h2 : ones r ≤ r.length := by rw [length_split r]; omega
        simp only [bnd]; nlinarith
      · simp [loopOut, edgesF_none₂ hx h₁ h₂, cfg]
    | cons b' t =>
      have hb' := head_false h₂
      subst hb'
      rw [h₂] at hsplit'
      have hx' : x = List.replicate (ones x) true ++ false ::
          (List.replicate (ones r) true ++ false :: t) := by
        have h := hsplit
        rw [hsplit'] at h
        exact h
      obtain ⟨w₁, g₁, re⟩ := edge_run (ones x) (ones r) t c acc g w
      rw [← hx'] at re
      have hlt : t.length + ones x + ones r + 2 = x.length := by
        rw [length_split x, h₁, List.length_cons, length_split r, h₂, List.length_cons]; omega
      obtain ⟨w₂, T, rl, hT⟩ := loop_run t (c + 3) ((gadBits (ones x) (ones r) c).reverse ++ acc)
        g₁ w₁
      refine ⟨w₂, T, (re.trans rl).mono ?_, ?_⟩
      · have hg := gadBits_length_le (ones x) (ones r) c
        have hb := bnd_step c (ones x) (ones r) t.length acc.length _ hg
        simp only [List.length_append, List.length_reverse]
        rw [← hlt]
        convert hb using 2
      · rw [hT]
        unfold loopOut
        rw [edgesF_cons hx h₁ h₂]
        cases edgesF (c + 3) t with
        | none => rfl
        | some p => simp [List.reverse_append, List.append_assoc]
termination_by x.length
decreasing_by omega

theorem start_run (x : List Bool) :
    ∃ w' T, RunLe prog (200000 * (x.length + 1) ^ 2)
      ⟨some .rdN, false, cfg x 0 0 0 [] [] [] []⟩ ⟨some .done, w', T⟩ ∧
      T (.ss .O) = convF x := by
  obtain ⟨w₁, r₁⟩ := rdN_run (ones x) (x.dropWhile id) (ends_dropWhile x) false
  rw [← ones_split x] at r₁
  have hlen := length_split x
  cases h : x.dropWhile id with
  | nil =>
    rw [h] at r₁
    have r₂ := pop_fail .popN .top rfl (ones x) 0 0 [] [] [] [] w₁
    refine ⟨false, _, (r₁.trans r₂).le le_rfl |>.mono ?_, ?_⟩
    · rw [h] at hlen
      simp only [List.length_nil, Nat.add_zero] at hlen
      nlinarith
    · simp [convF, h, cfg]
  | cons b r =>
    rw [h] at r₁
    have r₂ := pop_step .popN .top rfl (b :: r) (ones x) 0 0 [] [] [] [] w₁ b r rfl
    obtain ⟨w₃, T, r₃, hT⟩ := loop_run r (ones x) [] [] true
    refine ⟨w₃, T, ((r₁.trans r₂).le le_rfl).trans r₃ |>.mono ?_, ?_⟩
    · rw [h, List.length_cons] at hlen
      simp only [bnd, List.length_nil]
      nlinarith
    · rw [hT]; simp [convF, h]

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.rdN, .popN, .top, .rdU, .popU, .rdV, .popV, .clU, .clV, .inc, .f1, .f2, .f3, .f4, .done] ++
    (List.finRange 13).map .cp1 ++ (List.finRange 13).map .cp2 ++ (List.finRange 13).map .off ++
    (List.finRange 6).map .fr ++
    ((List.finRange 13).flatMap fun j => (Finset.univ : Finset UnaryNat.Lab).toList.map (.un j)))
  (by intro l; cases l <;> simp)

/-- The transducer as a host component. -/
noncomputable abbrev comp : Host.Comp where
  K := K
  Γ := Γ
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

theorem init_eq (x : List Bool) :
    update (β := fun k => List (Γ k)) (fun _ => []) (K.own .inp) (x.map id) =
      cfg x 0 0 0 [] [] [] [] := by
  funext k
  rcases k with k | q
  · rw [update_of_ne (by simp)]; cases k <;> rfl
  · cases q <;> simp [cfg]

/-- **The edge-gadget transducer runs in polynomial time.** -/
theorem isPolyTime_convF : ComplexityTheory.IsPolyTime convF := by
  apply Host.isPolyTime_reduction (c := comp) (cX := K.own .inp) (cO := K.ss .O)
    (gX := id) (start := Lab.rdN) (done := Lab.done) (Equiv.refl Bool) convF
    (Polynomial.C 200000 * (Polynomial.X + 1) ^ 2) rfl
  intro x
  obtain ⟨w, T, r, hT⟩ := start_run x
  refine ⟨w, T, ?_, ?_⟩
  · rw [init_eq]
    simpa using r
  · change T (.ss .O) = (convF x).map id
    simpa using hT

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Transducer

/-! ### The reduction -/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Hardness

open Cslib.CookLevin Cslib.Complexity Cslib.Complexity.Karp MetaMathlibExt.ComplexityTheory
open MetaMathlibExt.BitstringEncoding Transducer

theorem dropWhile_unary (u : ℕ) (r : List Bool) :
    (List.replicate u true ++ false :: r).dropWhile id = false :: r := by
  induction u with
  | zero => rfl
  | succ u ih => simp [List.replicate_succ]

theorem ones_unary (u : ℕ) (r : List Bool) : ones (List.replicate u true ++ false :: r) = u := by
  induction u with
  | zero => rfl
  | succ u ih => simp [ones, List.replicate_succ]

theorem bitEncode_gadget (u v c : ℕ) :
    bitEncode (gadget u v c) = gadBits u v c := by
  change ((gadget u v c).map bitEncode |>.map delimit).flatten = _
  simp [gadget, gadBits, pairBits, List.append_assoc]
  rfl

theorem bitEncode_append (l₁ l₂ : List (ℕ × ℕ)) :
    bitEncode (l₁ ++ l₂) = bitEncode l₁ ++ bitEncode l₂ := by
  change ((l₁ ++ l₂).map bitEncode |>.map delimit).flatten =
    (l₁.map bitEncode |>.map delimit).flatten ++ (l₂.map bitEncode |>.map delimit).flatten
  simp

theorem edgesF_edgeBits :
    ∀ (es : List (ℕ × ℕ)) (c : ℕ),
      edgesF c (edgeBits es) = some (c + 3 * es.length, bitEncode (gad c es))
  | [], c => by simp [edgeBits, edgesF_nil, gad]; rfl
  | (u, v) :: es, c => by
    have hx : edgeBits ((u, v) :: es) =
        List.replicate u true ++ false :: (List.replicate v true ++ false :: edgeBits es) := by
      simp [edgeBits, List.append_assoc]
    rw [hx, edgesF_cons (by simp) (dropWhile_unary _ _) (dropWhile_unary _ _),
      edgesF_edgeBits es (c + 3), ones_unary, ones_unary]
    simp only [Option.map_some, gad, bitEncode_append, bitEncode_gadget, List.length_cons]
    congr 2
    omega

/-- On graph encodings the transducer outputs the encoded gadget instance. -/
theorem convF_encodeE (n : ℕ) (es : List (ℕ × ℕ)) :
    convF (encodeE n es) = bitEncode (target n es) := by
  rw [encodeE_eq, convF, dropWhile_unary]
  simp only [loopOut, ones_unary, edgesF_edgeBits, List.reverse_nil, List.nil_append,
    List.append_assoc]
  unfold target
  rw [show bitEncode ((n + 3 * es.length, gad n es, 3) : GraphColoringInstance) =
    delimit (bitEncode (n + 3 * es.length)) ++ (delimit (bitEncode (gad n es)) ++
      bitEncode (3 : ℕ)) from rfl]
  simp only [BinaryNatEncoding.bitEncode_nat]

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Hardness

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring

open Cslib.CookLevin Cslib.Complexity Cslib.Complexity.Karp MetaMathlibExt.ComplexityTheory
open Transducer Hardness

/-- **SAT reduces to GRAPH COLORING.** -/
theorem satDec_polyManyOneRed_graphColoringDec : PolyManyOneRed satDec graphColoringDec :=
  ⟨convF ∘ reduceCol, IsPolyTime.comp isPolyTime_reduceCol isPolyTime_convF, fun x => by
    rw [satDec_eq_col3Dec_reduceCol, Function.comp_apply]
    obtain ⟨n, es, h, hb⟩ := reduceCol_range x
    rw [h, convF_encodeE]
    exact (graphColoringDec_target hb).symm⟩

/-- **GRAPH COLORING is NP-hard.** Every decision problem in NP has a polynomial-time many-one
reduction to GRAPH COLORING.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GRAPH COLORING
(chromatic number); R. M. Karp, "Reducibility among combinatorial problems" (1972). -/
theorem graphColoring_npHard :
    ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ MetaMathlibExt.ComplexityTheory.NP →
        Cslib.CookLevin.PolyManyOneRed L graphColoringDec :=
  NPHard.of_polyManyOneRed Cslib.Complexity.CookLevin.Hardness.satDec_npHard
    satDec_polyManyOneRed_graphColoringDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoring
