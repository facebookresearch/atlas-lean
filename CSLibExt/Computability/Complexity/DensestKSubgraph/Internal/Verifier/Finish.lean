/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.KeepOrder
public import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
import MathlibExt.Computability.BinaryNatEncoding

/-! # Numeric finish checks on binary headers and physically bounded counts -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.VerifierFinish

open Turing Function MetaMathlibExt TM2Program TM2Embedding
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier (Sym)
open Computability (encodeNat)

/- Binary header words and the two counts after conversion. -/
inductive Word | n | k | m | binaryCount (vertex : Bool)
  deriving DecidableEq

instance : Fintype Word := Fintype.ofList [.n, .k, .m, .binaryCount false, .binaryCount true]
  (by intro w; cases w with | binaryCount b => cases b <;> decide | _ => decide)

/- Three comparisons: `k ≤ n`, `m ≤ edges`, `vertices ≤ k`. -/
inductive Test | bound | edges | vertices
  deriving DecidableEq

instance : Fintype Test := Fintype.ofList [.bound, .edges, .vertices]
  (by intro s; cases s <;> decide)

/- Independent scratch and ports for conversion and binary comparison. -/
inductive K | word (p : Word) | count (vertex : Bool) | code (s : EmitSS.K) | cmp (s : KeepOrder.K)
  deriving DecidableEq

instance : Fintype K where
  elems := {.count false, .count true} ∪ Finset.univ.image K.word ∪
    Finset.univ.image K.code ∪ Finset.univ.image K.cmp
  complete k := by cases k with | count b => cases b <;> simp | _ => simp

/- The counters carry one symbol per unit; all comparisons use Boolean words. -/
@[reducible] def Γ : K → Type
  | .code s => EmitSS.Γ s
  | .count _ => Sym
  | _ => Bool

/- Sequence the conversions and comparisons, ending with an explicit verdict. -/
inductive Lab | test (t : Test) (l : KeepOrder.Lab) | convert (vertex : Bool) (l : UnaryNat.Lab)
  | yes | no
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.yes, .no} ∪ Finset.univ.image (fun p : Test × KeepOrder.Lab => .test p.1 p.2) ∪
    Finset.univ.image (fun p : Bool × UnaryNat.Lab => .convert p.1 p.2)
  complete l := by cases l <;> simp

/- Assign the two operands in the direction of the respective `≤` test. -/
def operand : Test → BinaryOrder.K → Word
  | .bound, .a => .k
  | .bound, .b => .n
  | .edges, .a => .m
  | .edges, .b => .binaryCount false
  | .vertices, .a => .binaryCount true
  | .vertices, .b => .k

/- Route the comparison operand ports while leaving its scratch independent. -/
def cmpPort (t : Test) : KeepOrder.K → K
  | .word w => .word (operand t w)
  | s => .cmp s

/- Embed the reusable bit-length comparison. -/
def cmpEmb (t : Test) : SEmb (fun _ : KeepOrder.K => Bool) Γ where
  e := cmpPort t
  inj a b h := by
    rcases a with x | x | _ <;> rcases b with y | y | _ <;>
      (try cases x) <;> (try cases y) <;> cases t <;> cases h <;> rfl
  ι s := by cases s <;> exact Equiv.refl _

/- Conversion consumes a physical count and writes the corresponding binary word. -/
def codePort (b : Bool) : EmitSS.K → K
  | .A => .count b
  | .O => .word (.binaryCount b)
  | s => .code s

/- Embed the previously proved unary-counter conversion. -/
def codeEmb (b : Bool) : SEmb EmitSS.Γ Γ where
  e := codePort b
  inj x y h := by cases x <;> cases y <;> cases h <;> rfl
  ι s := by cases s <;> exact Equiv.refl _

/- The greater-than result fails a non-strict comparison. -/
def cmpNext (t : Test) (o : Ordering) : Lab := if o = .gt then .no else
  match t with
  | .bound => .convert false (.emit .hv)
  | .edges => .convert true (.emit .hv)
  | .vertices => .yes

/- The order label determines the next action. -/
def cmpLabel (t : Test) : KeepOrder.Lab → Lab
  | .done o => cmpNext t o
  | l => .test t l

/- Compare a freshly serialized count against the corresponding bound. -/
def codeLabel (b : Bool) : UnaryNat.Lab → Lab
  | .done => .test (if b then .vertices else .edges) (.copy .a)
  | l => .convert b l

/- The exact terminating threshold program. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .test t l => mapS (cmpEmb t) (cmpLabel t) (KeepOrder.prog l)
  | .convert b l => mapS (codeEmb b) (codeLabel b) (UnaryNat.prog false l)
  | .yes | .no => .halt

private theorem cmp_ok (t : Test) : Embeds (cmpEmb t) (cmpLabel t) KeepOrder.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem code_ok (b : Bool) :
    Embeds (codeEmb b) (codeLabel b) (UnaryNat.prog false) prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

/- Idle workspace interpreted as a collection of binary words and unary counters. -/
def stk (words : Word → List Bool) (cs : Bool → ℕ) : (a : K) → List (Γ a)
  | .word w => words w
  | .count b => cnt EmitSS.U (cs b)
  | _ => []

/- Before the first test, neither physical counter has been converted. -/
def words (n k m : ℕ) : Word → List Bool
  | .n => encodeNat n
  | .k => encodeNat k
  | .m => encodeNat m
  | .binaryCount _ => []

/- Initial numeric workspace. -/
abbrev st (n k m e d : ℕ) : (a : K) → List (Γ a) :=
  stk (words n k m) (fun b => if b then d else e)

private theorem test_run (p : Test) (ws : Word → List Bool) (cs : Bool → ℕ) (a b : ℕ) (v : Bool)
    (ha : ws (operand p .a) = encodeNat a) (hb : ws (operand p .b) = encodeNat b) :
    ∃ w, RunLe prog (3 * (a.size + b.size) + 5)
      ⟨some (.test p (.copy .a)), v, stk ws cs⟩
      ⟨some (cmpNext p (compare a b)), w, stk ws cs⟩ := by
  obtain ⟨w, hr⟩ := KeepOrder.run a b v
  have hg : Agree (cmpEmb p) (KeepOrder.st (encodeNat a) (encodeNat b) [] []) (stk ws cs) := by
    intro j
    cases j with
    | word q =>
      cases q with
      | a => exact ha.trans (List.map_id _).symm
      | b => exact hb.trans (List.map_id _).symm
    | work q => cases q <;> rfl
    | temp => rfl
  obtain ⟨T, h, hA, hf⟩ := runLe_embed (cmpLabel p) (cmp_ok p) hr hg
  have he : T = stk ws cs := by
    funext j
    by_cases hj : ∃ z, (cmpEmb p).e z = j
    · obtain ⟨z, rfl⟩ := hj
      exact (hA z).trans (hg z).symm
    · exact hf j (fun z hz => hj ⟨z, hz⟩)
  exact ⟨w, he ▸ h⟩

private def codeSt (a : ℕ) : (i : EmitSS.K) → List (EmitSS.Γ i)
  | .A => cnt EmitSS.U a
  | _ => []

private theorem convert_run (b : Bool) (ws : Word → List Bool) (cs : Bool → ℕ) (v : Bool)
    (ho : ws (.binaryCount b) = []) :
    ∃ w, RunLe prog (710 * cs b + 306) ⟨some (.convert b (.emit .hv)), v, stk ws cs⟩
      ⟨some (.test (if b then .vertices else .edges) (.copy .a)), w,
        stk (update ws (.binaryCount b) (encodeNat (cs b))) (update cs b 0)⟩ := by
  obtain ⟨w, S, hr, hout, ha, hh, ht, hx, hf⟩ :=
    UnaryNat.run_raw (cs b) [] v (codeSt (cs b)) rfl rfl rfl rfl rfl
  have hg : Agree (codeEmb b) (codeSt (cs b)) (stk ws cs) := by
    intro j
    cases j
    case O => exact ho
    case A => exact (List.map_id _).symm
    all_goals rfl
  obtain ⟨T, h, hA, hF⟩ := runLe_embed (codeLabel b) (code_ok b) hr hg
  have he : T = stk (update ws (.binaryCount b) (encodeNat (cs b))) (update cs b 0) := by
    funext j
    by_cases hj : ∃ z, (codeEmb b).e z = j
    · obtain ⟨z, rfl⟩ := hj
      have hz := hA z
      cases z
      case A => exact (hz.trans (List.map_id _)).trans (by rw [ha]; cases b <;> rfl)
      case O =>
        exact (hz.trans (List.map_id _)).trans (by rw [hout, List.append_nil]; cases b <;> rfl)
      case X => exact (hz.trans (List.map_id _)).trans hx
      case H => exact (hz.trans (List.map_id _)).trans hh
      case T => exact (hz.trans (List.map_id _)).trans ht
      all_goals
        exact (hz.trans (List.map_id _)).trans
          (hf _ (by decide) (by decide) (by decide) (by decide) (by decide))
    · apply (hF j (fun z hz => hj ⟨z, hz⟩)).trans
      cases j with
      | word p =>
        have hp : p ≠ .binaryCount b := fun h => hj ⟨.O, congrArg K.word h.symm⟩
        exact (update_of_ne hp _ _).symm
      | count t =>
        have hp : t ≠ b := fun h => hj ⟨.A, congrArg K.count h.symm⟩
        simp [stk, hp]
      | _ => rfl
  exact ⟨w, he ▸ h⟩

/- All thresholds are decided with a bound depending on header bit lengths and physical counts. -/
theorem run (n k m e d : ℕ) (v : Bool) :
    ∃ w S, RunLe prog (1500 * (n.size + k.size + m.size + e + d + 1))
      ⟨some (.test .bound (.copy .a)), v, st n k m e d⟩
      ⟨some (if k ≤ n ∧ m ≤ e ∧ d ≤ k then .yes else .no), w, S⟩ := by
  let ws := words n k m
  let cs := fun b : Bool => if b then d else e
  obtain ⟨w₁, r₁⟩ := test_run .bound ws cs k n v rfl rfl
  by_cases hk : k ≤ n
  swap
  · have h := Nat.compare_eq_gt.mpr (Nat.lt_of_not_ge hk)
    simp only [cmpNext, h, ↓reduceIte] at r₁
    exact ⟨w₁, _, by simpa only [hk, false_and, ite_false] using r₁.mono (by omega)⟩
  have hno : compare k n ≠ .gt := Nat.compare_ne_gt.mpr hk
  simp only [cmpNext, hno, ite_false] at r₁
  obtain ⟨w₂, r₂⟩ := convert_run false ws cs w₁ rfl
  let ws₁ := update ws (.binaryCount false) (encodeNat e)
  let cs₁ := update cs false 0
  obtain ⟨w₃, r₃⟩ := test_run .edges ws₁ cs₁ m e w₂ rfl rfl
  have he := EmitSS.encodeNat_length_le e
  rw [BinaryNatEncoding.length_encodeNat] at he
  by_cases hm : m ≤ e
  swap
  · have h := Nat.compare_eq_gt.mpr (Nat.lt_of_not_ge hm)
    simp only [cmpNext, h, ↓reduceIte] at r₃
    refine ⟨w₃, stk ws₁ cs₁, ?_⟩
    have hr := (r₁.trans r₂).trans r₃
    simp only [hm, false_and, and_false, ite_false]
    exact hr.mono (by change 3 * (k.size + n.size) + 5 + (710 * e + 306) +
      (3 * (m.size + e.size) + 5) ≤ _; omega)
  have hno₂ : compare m e ≠ .gt := Nat.compare_ne_gt.mpr hm
  simp only [cmpNext, hno₂, ite_false] at r₃
  obtain ⟨w₄, r₄⟩ := convert_run true ws₁ cs₁ w₃ rfl
  let ws₂ := update ws₁ (.binaryCount true) (encodeNat d)
  let cs₂ := update cs₁ true 0
  obtain ⟨w, r₅⟩ := test_run .vertices ws₂ cs₂ d k w₄ rfl rfl
  have hd := EmitSS.encodeNat_length_le d
  rw [BinaryNatEncoding.length_encodeNat] at hd
  have hl : cmpNext .vertices (compare d k) = (if k ≤ n ∧ m ≤ e ∧ d ≤ k then .yes else .no) := by
    by_cases hh : d ≤ k
    · simp [cmpNext, Nat.compare_ne_gt.mpr hh, hk, hm, hh]
    · simp [cmpNext, Nat.compare_eq_gt.mpr (Nat.lt_of_not_ge hh), hh]
  rw [hl] at r₅
  refine ⟨w, stk ws₂ cs₂, ((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).mono ?_⟩
  change 3 * (k.size + n.size) + 5 + (710 * e + 306) + (3 * (m.size + e.size) + 5) +
    (710 * d + 306) + (3 * (d.size + k.size) + 5) ≤ _
  omega

end Cslib.Complexity.DensestKSubgraph.Internal.VerifierFinish
