/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.FramedCNF.Block
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Computability.PartrecCode
import MathlibExt.Computability.TuringMachine.Cleanup
import MathlibExt.Computability.TuringMachine.Recursive.OfTM2

/-!
# An oracle separates NP from coNP

We construct an oracle for which the language of inputs having an oracle-positive
witness of bounded length belongs to relativized NP and its complement does not.
The oracle is built in stages. At each stage we diagonalize against a bounded verifier,
preserving at most one accepting run, and fix all answers that can affect the outcome.
-/

public section

namespace MetaMathlibExt.Complexity.KeyTheorems.OracleNPCoNPSeparation

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory MetaMathlibExt.BitstringEncoding

private abbrev Word := List Bool
private abbrev Oracle := Word → Bool
private abbrev Input := Word × List (Word × Bool)

section Verifier

open Turing MetaMathlibExt.TM2Program

private inductive Stack | input | output | scratch
  deriving DecidableEq

private instance stackFintype : Fintype Stack :=
  Fintype.ofList [.input, .output, .scratch] (by intro k; cases k <;> simp)

private inductive Label | read | restore | clean | halt
  deriving DecidableEq

private instance labelFintype : Fintype Label :=
  Fintype.ofList [.read, .restore, .clean, .halt] (by intro l; cases l <;> simp)

private abbrev projectProg : Label → TM2.Stmt (fun _ : Stack => Bool) Label Bool
  | .read => Cslib.Complexity.FramedCNF.Block.read .input .scratch some id .read .restore .clean
  | .restore => moveB .scratch .output some id .restore .clean
  | .clean => cleanS [.input] .clean .halt
  | .halt => .halt

private abbrev projectTM : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .read
  σ := Bool
  initialState := false
  m := projectProg

private def contents (input output scratch : Word) : Stack → Word
  | .input => input
  | .output => output
  | .scratch => scratch

private theorem projectRun (word suffix : Word) :
    RunLe projectTM.m (2 * word.length + suffix.length + 4)
      (initList projectTM (delimit word ++ suffix)) (haltList projectTM word) := by
  have hi : initList projectTM (delimit word ++ suffix) =
      ⟨some .read, false, contents (delimit word ++ suffix) [] []⟩ := by
    simp only [initList]
    congr 1
    funext k
    cases k <;> rfl
  have ho : haltList projectTM word = ⟨none, false, contents [] word []⟩ := by
    simp only [haltList]
    congr 1
    funext k
    cases k <;> rfl
  rw [hi, ho]
  obtain ⟨s, hread, hs₀, hs₂, hs⟩ := Cslib.Complexity.FramedCNF.Block.run_delimit
    (M := projectProg) (a := Stack.input) (b := Stack.scratch) (self := Label.read)
    (good := Label.restore) (bad := Label.clean) rfl (by decide) id (fun _ => rfl)
    word suffix false (contents (delimit word ++ suffix) [] []) (by simp [contents])
  have hs₁ : s Stack.output = [] := hs Stack.output (by decide) (by decide)
  obtain ⟨v, t, hmove, ht₂, ht₁, ht⟩ := moveB_run
    (M := projectProg) (a := Stack.scratch) (b := Stack.output)
    (self := Label.restore) (next := Label.clean) rfl (by decide)
    word.reverse word.reverse [] false s (by simpa [contents] using hs₂) rfl rfl
  have ht₀ := (ht Stack.input (by decide) (by decide)).trans hs₀
  have hclean := clean_run (M := projectProg) (ks := [Stack.input])
    (self := Label.clean) (next := Label.halt) rfl (by simp) suffix.length v t (by
      intro k hk
      obtain rfl : k = Stack.input := by simpa using hk
      simp [ht₀])
  have he : (fun k => if k ∈ [Stack.input] then [] else t k) = contents [] word [] := by
    funext k
    cases k <;> simp [contents, ht₁, ht₂, hs₁]
  rw [he] at hclean
  have hhalt : Run projectProg 1 ⟨some .halt, false, contents [] word []⟩
      ⟨none, false, contents [] word []⟩ := Run.single rfl
  exact ((hread.trans hmove).le le_rfl |>.trans hclean |>.trans (hhalt.le le_rfl)).mono
    (by simp; omega)

private theorem polyTime_project : IsPolyTime (Prod.fst : Input → Word) := by
  refine ⟨{
    tm := projectTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + Polynomial.C 3
    outputsFun := ?_ }⟩
  rintro ⟨word, hist⟩
  have run := projectRun (bitEncode word) (bitEncode hist)
  let n := Classical.choose run
  have hn := (Classical.choose_spec run).1
  have hr := (Classical.choose_spec run).2
  refine ⟨⟨n, ?_⟩, ?_⟩
  · change Run projectTM.m n
      (initList projectTM ((delimit (bitEncode word) ++ bitEncode hist).map id))
      (haltList projectTM ((bitEncode word).map id))
    simpa only [List.map_id] using hr
  · change n ≤ (Polynomial.X + Polynomial.C 3).eval
      (delimit (bitEncode word) ++ bitEncode hist).length
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, List.length_append,
      length_delimit]
    omega

private def shift (state : Bool × Bool) (bit : Bool) : Bool × Bool := (state.2, bit)

-- The final answer in a nonempty history is the penultimate bit of its encoding.
private def finalAnswer (a : Input) : Bool :=
  ((bitEncode a).foldl shift (false, false)).1

private abbrev answerTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := (Bool × Bool) × Bool
  initialState := ((false, false), false)
  m _ := .peek () (fun s b => (s.1, b.isSome)) <|
    .branch Prod.snd
      (.pop () (fun s b => (shift s.1 (b.getD false), false)) (.goto fun _ => ()))
      (.push () (fun s => s.1.1) (.load (fun _ => ((false, false), false)) .halt))

private theorem answerRun (bits : Word) (state : Bool × Bool) :
    Run answerTM.m (bits.length + 1) ⟨some (), (state, false), fun _ => bits⟩
      (haltList answerTM [(bits.foldl shift state).1]) := by
  induction bits generalizing state with
  | nil => exact Run.single rfl
  | cons b bits ih => exact Run.head rfl (ih (shift state b))

private theorem polyTime_answer : IsPolyTime finalAnswer := by
  refine ⟨{
    tm := answerTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.X + 1
    outputsFun := ?_ }⟩
  intro a
  refine ⟨⟨(bitEncode a).length + 1, ?_⟩, ?_⟩
  swap
  · change (bitEncode a).length + 1 ≤ (Polynomial.X + 1).eval (bitEncode a).length
    simp
  change Run answerTM.m _ (initList answerTM ((bitEncode a).map id))
    (haltList answerTM ([finalAnswer a].map id))
  have hi : initList answerTM (bitEncode a) =
      ⟨some (), ((false, false), false), fun _ => bitEncode a⟩ := rfl
  rw [List.map_id, List.map_id, hi]
  exact answerRun (bitEncode a) (false, false)

private theorem delimit_snoc (bits : Word) (b : Bool) :
    ∃ front : Word, delimit (bits ++ [b]) = front ++ [true, b, false] := by
  induction bits with
  | nil => exact ⟨[], rfl⟩
  | cons a bits ih =>
    obtain ⟨front, hp⟩ := ih
    exact ⟨true :: a :: front, congrArg (fun xs => true :: a :: xs) hp⟩

private theorem finalAnswer_append (word : Word) (hist : List (Word × Bool))
    (query : Word) (answer : Bool) :
    finalAnswer (word, hist ++ [(query, answer)]) = answer := by
  obtain ⟨front, hp⟩ := delimit_snoc (delimit (bitEncode query)) answer
  have hpair : bitEncode (query, answer) = delimit (bitEncode query) ++ [answer] := rfl
  change ((delimit (bitEncode word) ++
    (((hist ++ [(query, answer)]).map bitEncode).map delimit).flatten).foldl
      shift (false, false)).1 = answer
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil, hpair, hp, List.foldl_append]
  rfl

private noncomputable def diagonalLanguage (oracle : Oracle) : DecisionProblem :=
  fun x => by
    classical
    exact decide (∃ w : Word, w.length ≤ x.length + 1 ∧ oracle (bitEncode (x, w)) = true)

private theorem length_encode_bits (x : Word) : (bitEncode x).length = 3 * x.length := by
  change (((x.map fun b => ([b] : Word)).map delimit).flatten).length = 3 * x.length
  induction x with
  | nil => rfl
  | cons b x ih =>
    simpa only [List.map_cons, List.flatten_cons, List.length_append, length_delimit,
      List.length_cons, List.length_nil, ih] using (show 3 + 3 * x.length =
        3 * (x.length + 1) by omega)

private theorem length_encode_pair (x w : Word) :
    (bitEncode (x, w)).length = 6 * x.length + 1 + 3 * w.length := by
  change (delimit (bitEncode x) ++ bitEncode w).length = _
  simp only [List.length_append, length_delimit, length_encode_bits]
  omega

private theorem eval_project_answer (oracle : Oracle) (word : Word) (cap fuel : ℕ)
    (hcap : word.length ≤ cap) (hist : List (Word × Bool)) :
    evalOracle cap Prod.fst finalAnswer oracle word (fuel + 1) hist = oracle word := by
  induction fuel generalizing hist with
  | zero => simpa [evalOracle, hcap] using finalAnswer_append word hist word (oracle word)
  | succ fuel ih =>
    simpa only [evalOracle, Prod.fst, hcap, ite_true] using
      ih (hist ++ [(word, oracle word)])

private theorem diagonalLanguage_mem (oracle : Oracle) : diagonalLanguage oracle ∈
    NPWithOracle oracle := by
  refine ⟨Polynomial.X + 1, Polynomial.C 9 * Polynomial.X + Polynomial.C 4,
    Prod.fst, finalAnswer, polyTime_project, polyTime_answer, ?_⟩
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, diagonalLanguage, decide_eq_true_eq]
  refine exists_congr fun w => and_congr_right fun hw => ?_
  have hc : (bitEncode (x, w)).length ≤ 9 * x.length + 4 := by
    rw [length_encode_pair]
    omega
  rw [eval_project_answer oracle _ _ _ hc []]

end Verifier

section Enumeration

open Computability Turing MetaMathlibExt.TM2Recursive
open scoped Function

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
  primcodableArrow primcodableΛ primcodableσ

-- The coded simulation in `Recursive.OfTM2` gives a partial recursive evaluator on raw bits.
private theorem exists_partrec_evaluator {α β : Type} {ea : α → Word} {eb : β → Word}
    {f : α → β} (h : TM2Computable ea eb f) :
    ∃ g : Word →. Word, Partrec g ∧ ∀ a, eb (f a) ∈ g (ea a) := by
  let tm := h.tm
  let initC : Word → CodedCfg tm := fun l => (some tm.main, tm.initialState,
    Function.update (fun _ => []) tm.k₀ (l.map fun b => code tm tm.k₀ (h.inputAlphabet.symm b)))
  let halted : Option (CodedCfg tm) → Bool := fun o => o.elim true fun c => c.1.isNone
  let decOut : ℕ → Bool := fun c => ((decode tm tm.k₁ c).map h.outputAlphabet).getD false
  let out : Option (CodedCfg tm) → Word := fun o =>
    (o.elim [] fun c => c.2.2 tm.k₁).map decOut
  have hinit : Primrec fun l => some (initC l) := by
    refine Primrec.option_some.comp (Primrec.pair (Primrec.const _) (Primrec.pair
      (Primrec.const _) ((primrec_arrow_update tm.k₀).comp (Primrec.const _) ?_)))
    exact Primrec.list_map Primrec.id
      ((Primrec.dom_finite fun b : Bool => code tm tm.k₀ (h.inputAlphabet.symm b)).comp
        Primrec.snd).to₂
  have hhalted : Primrec halted :=
    (Primrec.option_casesOn Primrec.id (Primrec.const true)
      ((Primrec.dom_finite fun l : Option tm.Λ => l.isNone).comp
        (Primrec.fst.comp Primrec.snd)).to₂).of_eq fun o => by cases o <;> rfl
  have hdecode : Primrec decOut :=
    primrec_of_eventually_const (symList tm tm.k₁).length fun c hc => by
      simp only [decOut, decode_eq_none tm hc, decode_eq_none tm le_rfl]
  have hout : Primrec out :=
    Primrec.list_map ((Primrec.option_casesOn Primrec.id
      (Primrec.const []) ((primrec_arrow_eval tm.k₁).comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun o => by cases o <;> rfl)
      (hdecode.comp Primrec.snd).to₂
  refine ⟨_, partrec_run hinit (primrec_optStepC tm) hhalted hout, fun a => ?_⟩
  let input := (ea a).map h.inputAlphabet.symm
  let output := (eb (f a)).map h.outputAlphabet.symm
  obtain ⟨s, hs⟩ := h.outputsFun a
  change (flip bind tm.step)^[s] (some (initList tm input)) = some (haltList tm output) at hs
  have hc : enc tm (initList tm input) = initC (ea a) := by
    simp only [enc, initC, encStk_initList, input, List.map_map]
    rfl
  have hrun j := optStepC_iterate tm j (o := some (initList tm input)) (fun c hc => by
    obtain rfl := Option.mem_some_iff.mp hc
    exact relevant_initList tm input)
  simp only [Option.map_some, hc] at hrun
  change eb (f a) ∈ (Nat.rfind fun j =>
    Part.some (halted ((optStepC tm)^[j] (some (initC (ea a)))))).map _
  refine Part.mem_map_iff _ |>.mpr ⟨s, Nat.mem_rfind.mpr ⟨?_, fun {j} hj => ?_⟩, ?_⟩
  · rw [(hrun s).1, hs]
    exact Part.mem_some _
  · obtain ⟨c, he, hl⟩ := running_before_halt tm hs hj
    rw [(hrun j).1, he]
    simp only [halted, Option.map_some, Option.elim_some, enc]
    simpa using hl
  · have hrel := (hrun s).2 (haltList tm output) (by rw [hs]; rfl)
    rw [(hrun s).1, hs]
    simp only [out, Option.map_some, Option.elim_some, enc, encStk, haltList_stk_k₁, List.map_map]
    have hd : ∀ x ∈ output, (decOut ∘ code tm tm.k₁) x = h.outputAlphabet x := by
      intro x hx
      have hx' : x ∈ relevant tm tm.k₁ := hrel tm.k₁ x (by rwa [haltList_stk_k₁])
      simp [decOut, decode_code tm hx']
    rw [List.map_congr_left hd]
    simp [output, List.map_map]

private noncomputable def decodeProgram {β : Type} [MetaMathlibExt.BitstringEncoding β]
    (defaultValue : β) (code : Nat.Partrec.Code) (a : Input) : β := by
  classical
  exact ((code.eval (Encodable.encode (bitEncode a))).toOption.bind
    (fun n => (Encodable.decode (α := Word) n).bind bitDecode)).getD defaultValue

private theorem exists_program {β : Type} [MetaMathlibExt.BitstringEncoding β]
    (defaultValue : β) {f : Input → β} (h : IsPolyTime f) :
    ∃ code : Nat.Partrec.Code, decodeProgram defaultValue code = f := by
  classical
  obtain ⟨h⟩ := h
  obtain ⟨g, hg, hcorrect⟩ := exists_partrec_evaluator h.toTM2ComputableInTime.toTM2Computable
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hg
  refine ⟨code, funext fun a => ?_⟩
  have he : Encodable.encode (bitEncode (f a)) ∈ code.eval (Encodable.encode (bitEncode a)) := by
    rw [hcode]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact (Part.mem_map_iff Encodable.encode).mpr ⟨bitEncode (f a), hcorrect a, rfl⟩
  rw [decodeProgram, Part.toOption_eq_some_iff.mpr he]
  simp

end Enumeration

section Diagonalization

open Filter Asymptotics

private structure Verifier where
  fuel : Polynomial ℕ
  cap : Polynomial ℕ
  nextQuery : Input → Word
  finish : Input → Bool

private def Verifier.accepts (v : Verifier) (O : Oracle) (x : Word) : Prop :=
  ∃ w : Word, w.length ≤ v.fuel.eval x.length ∧
    evalOracle (v.cap.eval x.length) v.nextQuery v.finish O (bitEncode (x, w))
      (v.fuel.eval x.length) [] = true

private theorem exists_enumeration :
    ∃ e : ℕ → Verifier, ∀ (O : Oracle) (L : DecisionProblem), L ∈ NPWithOracle O →
      ∃ n, ∀ x, L x ↔ (e n).accepts O x := by
  let _ : Countable (Polynomial ℕ) :=
    Function.Surjective.countable
      (f := fun c : Σ n, Fin n → ℕ => Polynomial.ofFn c.1 c.2)
      (fun p => ⟨⟨p.natDegree + 1, Polynomial.toFn _ p⟩,
        Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)⟩)
  obtain ⟨codes, hc⟩ := exists_surjective_nat
    (Polynomial ℕ × Polynomial ℕ × Nat.Partrec.Code × Nat.Partrec.Code)
  refine ⟨fun n => ⟨(codes n).1, (codes n).2.1,
      decodeProgram [] (codes n).2.2.1, decodeProgram false (codes n).2.2.2⟩, ?_⟩
  intro O L hL
  obtain ⟨p, q, nextQuery, finish, hnext, hfinish, hspec⟩ := hL
  obtain ⟨nextCode, rfl⟩ := exists_program [] hnext
  obtain ⟨finalCode, rfl⟩ := exists_program false hfinish
  obtain ⟨n, hn⟩ := hc (p, q, nextCode, finalCode)
  exact ⟨n, fun x => by simpa only [Verifier.accepts, hn] using hspec x⟩

-- Record the queried words in one run. The initial history is shared by the two evaluators.
private def querySet (cap : ℕ) (nextQuery : Input → Word) (O : Oracle) (x : Word) :
    ℕ → List (Word × Bool) → Finset Word
  | 0, _ => ∅
  | fuel + 1, hist =>
    let query := nextQuery (x, hist)
    if query.length ≤ cap then
      insert query (querySet cap nextQuery O x fuel (hist ++ [(query, O query)]))
    else ∅

private theorem querySet_spec (cap : ℕ) (nextQuery : Input → Word) (finish : Input → Bool)
    (O : Oracle) (x : Word) (fuel : ℕ) (hist : List (Word × Bool)) :
    let queries := querySet cap nextQuery O x fuel hist
    queries.card ≤ fuel ∧ (∀ u ∈ queries, u.length ≤ cap) ∧
    ∀ O' : Oracle, (∀ u ∈ queries, O' u = O u) →
      evalOracle cap nextQuery finish O' x fuel hist =
        evalOracle cap nextQuery finish O x fuel hist := by
  induction fuel generalizing hist with
  | zero => simp [querySet, evalOracle]
  | succ fuel ih =>
    by_cases h : (nextQuery (x, hist)).length ≤ cap
    · simp only [querySet, evalOracle, h, ite_true]
      let u := nextQuery (x, hist)
      let rest := querySet cap nextQuery O x fuel (hist ++ [(u, O u)])
      obtain ⟨hcard, hlen, hrun⟩ := ih (hist ++ [(u, O u)])
      refine ⟨(Finset.card_insert_le _ _).trans (Nat.succ_le_succ hcard), ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact h
        · exact hlen t ht
      · intro O' hagree
        rw [hagree u (Finset.mem_insert_self u rest)]
        exact hrun O' fun t ht => hagree t (Finset.mem_insert_of_mem ht)
    · simp [querySet, evalOracle, h]

private theorem Verifier.accepts_congr (v : Verifier) (x : Word) {O O' : Oracle}
    (h : ∀ u : Word, u.length ≤ v.cap.eval x.length → O' u = O u) :
    v.accepts O' x ↔ v.accepts O x := by
  refine exists_congr fun w => and_congr_right fun _ => ?_
  obtain ⟨_, hlen, he⟩ := querySet_spec (v.cap.eval x.length) v.nextQuery v.finish O
    (bitEncode (x, w)) (v.fuel.eval x.length) []
  rw [he O' (fun u hu => h u (hlen u hu))]

private theorem compl_diagonalLanguage (O : Oracle) (x : Word) :
    (diagonalLanguage O)ᶜ x ↔
      ¬ ∃ w : Word, w.length ≤ x.length + 1 ∧ O (bitEncode (x, w)) = true := by
  classical
  change (!diagonalLanguage O x) = true ↔ _
  simp [diagonalLanguage]

private theorem compl_diagonalLanguage_congr (x : Word) {O O' : Oracle}
    (h : ∀ u : Word, u.length ≤ 9 * x.length + 4 → O' u = O u) :
    (diagonalLanguage O')ᶜ x ↔ (diagonalLanguage O)ᶜ x := by
  rw [compl_diagonalLanguage, compl_diagonalLanguage]
  refine not_congr (exists_congr fun w => and_congr_right fun hw => ?_)
  rw [h _ (by rw [length_encode_pair]; omega)]

private theorem eventually_eval_lt_pow (p : Polynomial ℕ) :
    ∀ᶠ n : ℕ in atTop, p.eval n < 2 ^ n := by
  have h : (fun n : ℕ => ((p.eval n : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add, Nat.cast_add] using hp.add hq
    | monomial k c =>
      have hk := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (r := 2) one_lt_two
      simpa only [Polynomial.eval_monomial, Nat.cast_mul, Nat.cast_pow] using
        hk.const_mul_left (c : ℝ)
  filter_upwards [h.def (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
  have hpos : 0 < (2 : ℝ) ^ n := by positivity
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hpos.le] at hn
  exact_mod_cast (show ((p.eval n : ℕ) : ℝ) < (2 : ℝ) ^ n by linarith)

private theorem exists_unqueried (x : Word) (queries : Finset Word)
    (h : queries.card < 2 ^ (x.length + 1)) :
    ∃ w : Word, w.length = x.length + 1 ∧ bitEncode (x, w) ∉ queries := by
  classical
  let encodeWitness (v : Fin (x.length + 1) → Bool) := bitEncode (x, List.ofFn v)
  have hi : Function.Injective encodeWitness := by
    intro v w hvw
    have hpair : (x, List.ofFn v) = (x, List.ofFn w) := by
      simpa only [encodeWitness, bitDecode_bitEncode, Option.some.injEq] using
        congrArg (bitDecode (α := Word × Word)) hvw
    exact List.ofFn_injective (congrArg Prod.snd hpair)
  by_contra! hall
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin (x.length + 1) → Bool))) (t := queries) encodeWitness
    (fun v _ => hall (List.ofFn v) (List.length_ofFn)) hi.injOn
  exact h.not_ge (by simpa [Fintype.card_fun] using hc)

private structure Stage where
  cutoff : ℕ
  oracle : Oracle

private def Stage.agrees (s : Stage) (O : Oracle) : Prop :=
  ∀ u : Word, u.length ≤ s.cutoff → O u = s.oracle u

private theorem diagonalStep (s : Stage) (v : Verifier) :
    ∃ t : Stage, s.cutoff ≤ t.cutoff ∧ s.agrees t.oracle ∧
      ∃ x, ∀ O : Oracle, t.agrees O →
        ¬ ((diagonalLanguage O)ᶜ x ↔ v.accepts O x) := by
  classical
  obtain ⟨n, hn, hp⟩ := ((eventually_ge_atTop (s.cutoff + 1)).and
    (eventually_eval_lt_pow v.fuel)).exists
  let x : Word := List.replicate n false
  have hx : x.length = n := List.length_replicate
  have hfresh (w : Word) : s.cutoff < (bitEncode (x, w)).length := by
    rw [length_encode_pair, hx]
    omega
  let baseline : Oracle := fun u => if u.length ≤ s.cutoff then s.oracle u else false
  have hbase : s.agrees baseline := fun u hu => by simp [baseline, hu]
  let bound := max (v.cap.eval x.length) (9 * x.length + 4)
  have hbound : s.cutoff ≤ bound := (show s.cutoff ≤ 9 * x.length + 4 by omega).trans
    (le_max_right _ _)
  suffices ∃ B : Oracle, s.agrees B ∧ ¬ ((diagonalLanguage B)ᶜ x ↔ v.accepts B x) by
    obtain ⟨B, hB, hdiag⟩ := this
    refine ⟨⟨bound, B⟩, hbound, hB, x, fun O hO => ?_⟩
    rw [compl_diagonalLanguage_congr x (fun u hu => hO u (hu.trans (le_max_right _ _))),
      v.accepts_congr x (fun u hu => hO u (hu.trans (le_max_left _ _)))]
    exact hdiag
  by_cases ha : v.accepts baseline x
  · -- Choose one accepting run and change an answer outside its queried words.
    obtain ⟨w, hw, hrun⟩ := ha
    let input := bitEncode (x, w)
    let queries := querySet (v.cap.eval x.length) v.nextQuery baseline input
      (v.fuel.eval x.length) []
    obtain ⟨hsize, _, htrace⟩ := querySet_spec (v.cap.eval x.length) v.nextQuery v.finish
      baseline input (v.fuel.eval x.length) []
    have hc : queries.card < 2 ^ (x.length + 1) := hsize.trans_lt (by
      rw [hx]
      exact hp.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    obtain ⟨w', hw', hmiss⟩ := exists_unqueried x queries hc
    let B := Function.update baseline (bitEncode (x, w')) true
    have hB : s.agrees B := by
      intro u hu
      have hne : u ≠ bitEncode (x, w') := fun he => (hfresh w').not_ge (he ▸ hu)
      exact (Function.update_of_ne hne _ _).trans (hbase u hu)
    have haccept : v.accepts B x := by
      refine ⟨w, hw, (htrace B ?_).trans hrun⟩
      intro u hu
      have hne : u ≠ bitEncode (x, w') := fun he => hmiss (he ▸ hu)
      exact Function.update_of_ne hne _ _
    refine ⟨B, hB, fun h => ?_⟩
    exact (compl_diagonalLanguage B x).mp (h.mpr haccept)
      ⟨w', hw'.le, Function.update_self _ _ _⟩
  · -- The baseline has no positive witness for the fresh input.
    refine ⟨baseline, hbase, fun h => ha (h.mp ((compl_diagonalLanguage baseline x).mpr ?_))⟩
    rintro ⟨w, _, hw⟩
    simp [baseline, (hfresh w).not_ge] at hw

private noncomputable def stages (e : ℕ → Verifier) : ℕ → Stage
  | 0 => ⟨0, fun _ => false⟩
  | n + 1 => Classical.choose (diagonalStep (stages e n) (e n))

private theorem stages_extend (e : ℕ → Verifier) {i j : ℕ} (hij : i ≤ j) :
    (stages e i).cutoff ≤ (stages e j).cutoff ∧ (stages e i).agrees (stages e j).oracle := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ j _ ih =>
    have hstep := Classical.choose_spec (diagonalStep (stages e j) (e j))
    exact ⟨ih.1.trans hstep.1, fun u hu => (hstep.2.1 u (hu.trans ih.1)).trans (ih.2 u hu)⟩

private noncomputable def limitOracle (e : ℕ → Verifier) : Oracle := fun u => by
  classical
  exact decide (∃ n, u.length ≤ (stages e n).cutoff ∧ (stages e n).oracle u = true)

private theorem stages_agree (e : ℕ → Verifier) (i : ℕ) : (stages e i).agrees (limitOracle e) := by
  classical
  intro u hu
  apply Bool.eq_iff_iff.mpr
  simp only [limitOracle, decide_eq_true_eq]
  refine ⟨?_, fun h => ⟨i, hu, h⟩⟩
  rintro ⟨j, hj, horacle⟩
  rcases le_total i j with h | h
  · rw [← (stages_extend e h).2 u hu]
    exact horacle
  · exact ((stages_extend e h).2 u hj).trans horacle

/-- **An oracle separates NP from coNP.** There is an oracle $O$, a function from bitstrings to
booleans, such that $\mathrm{NP}^O$ differs from the class $\mathrm{coNP}^O$ of decision problems
$L$ whose complement, the decision problem that accepts exactly the bitstrings that $L$ rejects,
belongs to $\mathrm{NP}^O$.

Source: T. Baker, J. Gill, and
R. Solovay, "Relativizations of the P =? NP question", SIAM Journal on
Computing 4 (1975), 431-442 (oracles separating NP from coNP); S. Arora and
B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 3
(relativization). -/
theorem oracle_np_co_np_separation :
    ∃ O : List Bool → Bool, NPWithOracle O ≠ {L | Lᶜ ∈ NPWithOracle O} := by
  obtain ⟨e, he⟩ := exists_enumeration
  let O := limitOracle e
  refine ⟨O, fun eq => ?_⟩
  have hL : (diagonalLanguage O)ᶜ ∈ NPWithOracle O := by
    have hmem := diagonalLanguage_mem O
    rw [eq] at hmem
    exact hmem
  obtain ⟨n, hn⟩ := he O (diagonalLanguage O)ᶜ hL
  obtain ⟨x, hx⟩ := (Classical.choose_spec (diagonalStep (stages e n) (e n))).2.2
  exact hx O (stages_agree e (n + 1)) (hn x)

end Diagonalization

end MetaMathlibExt.Complexity.KeyTheorems.OracleNPCoNPSeparation
