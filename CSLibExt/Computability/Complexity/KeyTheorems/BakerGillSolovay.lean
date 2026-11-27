/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.EncodingConverters
import MathlibExt.Computability.TuringMachine.Composition
import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Baker–Gill–Solovay oracles

We construct one oracle separating relativized P from NP and another collapsing the two classes.

For separation, at each stage we choose a fresh input length and run one deterministic
procedure against the oracle built so far. If it rejects, we add one unqueried witness.
If it accepts, every witness stays false. Later stages preserve this disagreement.

For collapse, a query can encode a machine and its input. A long enough query gets the
machine's acceptance value, which depends only on shorter oracle queries. To reach a long
enough query within polynomial bounds, the caller includes its current history in each query.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay

open Cslib.Complexity.Classes MetaMathlibExt.ComplexityTheory MetaMathlibExt.BitstringEncoding
open Turing Polynomial

private abbrev Bits := List Bool
private abbrev History := List (Bits × Bool)
private abbrev Input := Bits × History

private theorem encode_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (a : α)
    (b : β) : bitEncode (a, b) = delimit (bitEncode a) ++ bitEncode b := rfl

private theorem encode_list {α : Type} [BitstringEncoding α] (l : List α) :
    bitEncode l = l.flatMap (delimit ∘ bitEncode) := by
  induction l with
  | nil => rfl
  | cons a l ih => change delimit (bitEncode a) ++ bitEncode l = _; simp [ih]

private theorem length_encode_bits (x : Bits) : (bitEncode x).length = 3 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => change (true :: b :: false :: bitEncode x).length = _; simp [ih]; omega

private theorem length_encode_pair (x w : Bits) :
    (bitEncode (x, w)).length = 6 * x.length + 3 * w.length + 1 := by
  rw [encode_pair, List.length_append, length_delimit, length_encode_bits, length_encode_bits]
  omega

private theorem encode_injective {α : Type} [BitstringEncoding α] :
    Function.Injective (bitEncode : α → Bits) := fun _ _ h => by
  simpa only [bitDecode_bitEncode, Option.some.injEq] using congrArg (bitDecode (α := α)) h

private theorem eval_congr {α β : Type} (cap : ℕ)
    (next : Bits × List (Bits × α) → Bits) (final : Bits × List (Bits × α) → β)
    {O O' : Bits → α} (hO : ∀ s, s.length ≤ cap → O s = O' s)
    (x : Bits) (fuel : ℕ) (hist : List (Bits × α)) :
    evalOracle cap next final O x fuel hist = evalOracle cap next final O' x fuel hist := by
  induction fuel generalizing hist with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : (next (x, hist)).length ≤ cap
    · simp only [evalOracle, h, ite_true, hO _ h, ih]
    · simp only [evalOracle, h, ite_false]

private structure Machine where
  fuel : Polynomial ℕ
  cap : Polynomial ℕ
  next : Input → Bits
  final : Input → Bool
  next_poly : IsPolyTime next
  final_poly : IsPolyTime final

private def Machine.run (m : Machine) (O : Bits → Bool) (x z : Bits) : Bool :=
  evalOracle (m.cap.eval x.length) m.next m.final O z (m.fuel.eval x.length) []

/-! ## Countability of the oracle procedures -/

private theorem primrec_delimit : Primrec delimit := by
  refine (Primrec.list_foldr (h := fun _ (b, s) => true :: b :: s)
    Primrec.id (Primrec.const [false]) ?_).of_eq ?_
  · exact Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  · change ∀ s, s.foldr (fun b t => true :: b :: t) [false] = delimit s
    intro s
    induction s with
    | nil => rfl
    | cons a s ih => simp [delimit, ih]

private theorem primrec_encode_pair {α β : Type} [Primcodable α] [Primcodable β]
    [BitstringEncoding α] [BitstringEncoding β] (ha : Primrec (bitEncode : α → Bits))
    (hb : Primrec (bitEncode : β → Bits)) : Primrec (bitEncode : α × β → Bits) := by
  exact (Primrec.list_append.comp (primrec_delimit.comp (ha.comp Primrec.fst))
    (hb.comp Primrec.snd)).of_eq fun (a, b) => (encode_pair a b).symm

private theorem primrec_encode_list {α : Type} [Primcodable α] [BitstringEncoding α]
    (ha : Primrec (bitEncode : α → Bits)) : Primrec (bitEncode : List α → Bits) :=
  (Primrec.list_flatMap Primrec.id ((primrec_delimit.comp ha).comp Primrec.snd).to₂).of_eq
    fun l => (encode_list l).symm

private theorem primrec_encode_bool : Primrec (bitEncode : Bool → Bits) :=
  Primrec.dom_finite _

private theorem primrec_encode_input : Primrec (bitEncode : Input → Bits) :=
  primrec_encode_pair (primrec_encode_list primrec_encode_bool)
    (primrec_encode_list (primrec_encode_pair (primrec_encode_list primrec_encode_bool)
      primrec_encode_bool))

-- Adapt the coded TM2 simulation from
-- MathlibExt/Computability/TuringMachine/Recursive/OfTM2.lean to the canonical input encoding.
open TM2Recursive in
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
  primcodableArrow primcodableΛ primcodableσ in
private theorem computable_encoded {α β : Type} [Primcodable α] [BitstringEncoding α]
    [BitstringEncoding β] {f : α → β} (he : Primrec (bitEncode : α → Bits))
    (h : TM2Computable bitEncode bitEncode f) : Computable (bitEncode ∘ f) := by
  let tm := h.tm
  let initC : α → CodedCfg tm := fun a => (some tm.main, tm.initialState,
    Function.update (fun _ => []) tm.k₀
      ((bitEncode a).map fun b => code tm tm.k₀ (h.inputAlphabet.invFun b)))
  let halted : Option (CodedCfg tm) → Bool := fun o => o.elim true fun c => c.1.isNone
  let decOut : ℕ → Bool := fun c => ((decode tm tm.k₁ c).map h.outputAlphabet).getD false
  let out : Option (CodedCfg tm) → Bits := fun o => (o.elim [] fun c => c.2.2 tm.k₁).map decOut
  have hinitP : Primrec fun a => some (initC a) := by
    refine Primrec.option_some.comp (Primrec.pair (Primrec.const _) (Primrec.pair
      (Primrec.const _) ((primrec_arrow_update tm.k₀).comp (Primrec.const _) ?_)))
    exact Primrec.list_map he
      ((Primrec.dom_finite fun b : Bool => code tm tm.k₀ (h.inputAlphabet.invFun b)).comp
        Primrec.snd).to₂
  have hhaltedP : Primrec halted :=
    (Primrec.option_casesOn Primrec.id (Primrec.const true)
      ((Primrec.dom_finite fun l : Option tm.Λ => l.isNone).comp
        (Primrec.fst.comp Primrec.snd)).to₂).of_eq fun o => by cases o <;> rfl
  have hdecOutP : Primrec decOut :=
    primrec_of_eventually_const (symList tm tm.k₁).length fun _ hc => by
      simp only [decOut, decode_eq_none tm hc, decode_eq_none tm le_rfl]
  have houtP : Primrec out :=
    Primrec.list_map ((Primrec.option_casesOn Primrec.id
      (Primrec.const []) ((primrec_arrow_eval tm.k₁).comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun o => by cases o <;> rfl)
      (hdecOutP.comp Primrec.snd).to₂
  refine (partrec_run hinitP (primrec_optStepC tm) hhaltedP houtP).of_eq_tot fun a => ?_
  let input := (bitEncode a).map h.inputAlphabet.invFun
  let outL := (bitEncode (f a)).map h.outputAlphabet.invFun
  obtain ⟨s, hs⟩ := h.outputsFun a
  change (flip bind tm.step)^[s] (some (initList tm input)) = some (haltList tm outL) at hs
  have hinit : enc tm (initList tm input) = initC a := by
    simp only [enc, initC, encStk_initList, input, List.map_map]
    rfl
  have hrun : ∀ j, (optStepC tm)^[j] (some (initC a)) =
      ((flip bind tm.step)^[j] (some (initList tm input))).map (enc tm) ∧
      ∀ c ∈ (flip bind tm.step)^[j] (some (initList tm input)), Relevant tm c.stk := by
    intro j
    have := optStepC_iterate tm j (o := some (initList tm input)) fun c hc => by
      obtain rfl := Option.mem_some_iff.mp hc
      exact relevant_initList tm input
    rwa [Option.map_some, hinit] at this
  have hmem : s ∈ Nat.rfind fun k => Part.some (halted ((optStepC tm)^[k] (some (initC a)))) := by
    refine Nat.mem_rfind.mpr ⟨?_, fun {j} hj => ?_⟩
    · rw [(hrun s).1, hs]
      exact Part.mem_some _
    · obtain ⟨c, hc, hl⟩ := running_before_halt tm hs hj
      rw [(hrun j).1, hc]
      simp only [halted, Option.map_some, Option.elim_some, enc]
      simpa using hl
  refine (Part.mem_map_iff _).mpr ⟨s, hmem, ?_⟩
  have hrel := (hrun s).2 (haltList tm outL) (by rw [hs]; rfl)
  rw [(hrun s).1, hs]
  simp only [out, Option.map_some, Option.elim_some, enc, encStk, haltList_stk_k₁, List.map_map]
  have hdec : ∀ y ∈ outL, (decOut ∘ code tm tm.k₁) y = h.outputAlphabet y := fun y hy => by
    have hy' : y ∈ relevant tm tm.k₁ := hrel tm.k₁ y (by rw [haltList_stk_k₁]; exact hy)
    simp [decOut, decode_code tm hy']
  rw [List.map_congr_left hdec]
  simp [outL, List.map_map]

private theorem countable_computable {α β : Type} [Primcodable α] [Primcodable β] :
    Countable {f : α → β // Computable f} := by
  let g (f : {f : α → β // Computable f}) : {g : ℕ →. ℕ // Partrec g} :=
    ⟨fun n => Part.bind (↑(Encodable.decode (α := α) n))
      fun a => ((f.1 : α →. β) a).map Encodable.encode, Partrec.nat_iff.mpr (by
        have hf := f.2
        unfold Computable Partrec at hf
        exact hf)⟩
  apply Function.Injective.countable (f := g)
  intro f f' h
  apply Subtype.ext
  funext a
  have he := congrFun (congrArg Subtype.val h) (Encodable.encode a)
  exact Encodable.encode_injective (by simpa [g] using he)

private theorem countable_poly {β : Type} [BitstringEncoding β] :
    Countable {f : Input → β // IsPolyTime f} := by
  let := countable_computable (α := Input) (β := Bits)
  let g (f : {f : Input → β // IsPolyTime f}) : {g : Input → Bits // Computable g} :=
    ⟨bitEncode ∘ f.1, f.2.elim fun h => computable_encoded primrec_encode_input
      h.toTM2ComputableInTime.toTM2Computable⟩
  apply Function.Injective.countable (f := g)
  intro f f' h
  exact Subtype.ext (funext fun x => encode_injective (congrFun (congrArg Subtype.val h) x))

private theorem countable_machine : Countable Machine := by
  let := countable_poly (β := Bits)
  let := countable_poly (β := Bool)
  let : Countable (Polynomial ℕ) :=
    Function.Injective.countable (AddMonoidAlgebra.coeff_injective
      (R := ℕ) (M := ℕ))
  apply Function.Injective.countable (f := fun m : Machine =>
    (m.fuel, m.cap, (⟨m.next, m.next_poly⟩ : {f // IsPolyTime f}),
      (⟨m.final, m.final_poly⟩ : {f // IsPolyTime f})))
  intro m m' h
  cases m
  cases m'
  simp_all

/-! ## Queries containing the input and history -/

open TM2Program in
private def prefixTM (tag : Bits) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fun _ => pushList () tag.reverse .halt

private def query (tag : Bits) (i : Input) : Bits := tag ++ bitEncode i

open TM2Program in
private theorem query_poly (tag : Bits) : IsPolyTime (query tag) := by
  let tm := prefixTM tag
  let h : TM2ComputableInPolyTime bitEncode id (query tag) := {
    tm := tm
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := C 1
    outputsFun := fun i => by
      refine ⟨⟨1, ?_⟩, by simp⟩
      change Run tm.m 1 (initList tm (List.map id (bitEncode i)))
        (haltList tm (List.map id (query tag i)))
      erw [List.map_id, List.map_id]
      have hi : initList tm (bitEncode i) = ⟨some (), (), fun _ => bitEncode i⟩ := by congr 1
      have ho : haltList tm (query tag i) = ⟨none, (), fun _ => query tag i⟩ := by congr 1
      rw [hi, ho]
      apply Run.single
      change TM2.stepAux (pushList () tag.reverse .halt) () (fun _ => bitEncode i) =
        (⟨none, (), fun _ => query tag i⟩ : tm.Cfg)
      rw [stepAux_pushList, List.reverse_reverse]
      congr 1 }
  exact tm2ComputableInPolyTime_comp (g := id) h
    Cslib.Complexity.DenseSAT.EncodeBits.computable

private abbrev ScanState := Option Bool × Bool

private def scanBit (s : ScanState) (o : Option Bool) : ScanState :=
  (o, if o.isSome then s.1.getD false else s.2)

private def scan : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit ScanState := fun _ =>
  .pop () scanBit (.branch (fun s => s.1.isSome) (.goto fun _ => ())
    (.push () Prod.snd (.load (fun _ => (none, false)) .halt)))

private def scanTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := ScanState
  initialState := (none, false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := scan

open TM2Program in
private theorem scan_run (s : ScanState) (l : Bits) :
    Run scan (l.length + 1) ⟨some (), s, fun _ => l⟩
      ⟨none, (none, false), fun _ => [(l.foldl (fun a b => scanBit a (some b)) s).2]⟩ := by
  induction l generalizing s with
  | nil => exact Run.single rfl
  | cons b l ih =>
    change Run scan (l.length + 1 + 1) _ _
    refine Run.head ?_ (ih (scanBit s (some b)))
    have hu (xs ys : Bits) :
        Function.update (fun _ : Unit => xs) () ys = (fun _ => ys) := by
      funext k
      cases k
      exact Function.update_self _ _ _
    simp [TM2.step, scan, TM2.stepAux, scanBit, hu]

-- Every nonempty encoded history ends with the last answer followed by a false delimiter.
private def lastAnswer (i : Input) : Bool :=
  ((bitEncode i).foldl (fun a b => scanBit a (some b)) (none, false)).2

open TM2Program in
private theorem lastAnswer_poly : IsPolyTime lastAnswer := by
  refine ⟨{
    tm := scanTM
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := X + C 1
    outputsFun := fun i => ?_ }⟩
  refine ⟨⟨(bitEncode i).length + 1, ?_⟩, by simp [bitEncode]⟩
  change Run scan ((bitEncode i).length + 1)
    (initList scanTM (List.map id (bitEncode i))) (haltList scanTM [lastAnswer i])
  erw [List.map_id]
  have hi : initList scanTM (bitEncode i) = ⟨some (), (none, false), fun _ => bitEncode i⟩ := by
    congr 1
  have ho : haltList scanTM [lastAnswer i] = ⟨none, (none, false), fun _ => [lastAnswer i]⟩ := by
    congr 1
  rw [hi, ho]
  exact scan_run (none, false) (bitEncode i)

private theorem lastAnswer_append (z : Bits) (h : History) (q : Bits) (b : Bool) :
    lastAnswer (z, h ++ [(q, b)]) = b := by
  have he : bitEncode (h ++ [(q, b)]) = bitEncode h ++ delimit (bitEncode (q, b)) := by
    simp [encode_list, Function.comp_def]
  have hb : ∀ l : Bits, delimit (l ++ [b]) = (delimit l).dropLast ++ [true, b, false] := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.cons_append, delimit, ih]
      cases l <;> simp [delimit]
  unfold lastAnswer
  rw [encode_pair, he, encode_pair]
  change ((delimit (bitEncode z) ++
    (bitEncode h ++ delimit (delimit (bitEncode q) ++ [b]))).foldl
      (fun a c => scanBit a (some c)) (none, false)).2 = b
  rw [hb]
  simp [List.foldl_append, scanBit]

private instance machineNonempty : Nonempty Machine :=
  ⟨⟨0, 0, query [], lastAnswer, query_poly [], lastAnswer_poly⟩⟩


private theorem length_encode_history_append (h : History) (q : Bits) (b : Bool) :
    (bitEncode (h ++ [(q, b)])).length = (bitEncode h).length + (12 * q.length + 5) := by
  rw [encode_list, List.flatMap_append, List.length_append, ← encode_list]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Function.comp_apply,
    length_delimit, encode_pair, List.length_append, length_encode_bits]
  change _ + (2 * (2 * (3 * q.length) + 1 + 1) + 1) = _
  omega

private theorem length_query (tag z : Bits) (h : History) :
    (query tag (z, h)).length = tag.length + (6 * z.length + 1) + (bitEncode h).length := by
  simp [query, encode_pair, length_encode_bits, Nat.add_assoc, ← Nat.mul_assoc]

private theorem length_query_grows (tag z : Bits) (h : History) (q : Bits) (b : Bool) :
    q.length < (query tag (z, h ++ [(q, b)])).length := by
  rw [length_query, length_encode_history_append]
  omega

private theorem length_encode_history_le (h : History) (d : ℕ)
    (hh : ∀ qb ∈ h, (qb : Bits × Bool).1.length ≤ d) :
    (bitEncode h).length ≤ h.length * (12 * d + 5) := by
  induction h with
  | nil => simp; rfl
  | cons qb h ih =>
    have hq := hh qb (by simp)
    have ht := ih (fun qc hqc => hh qc (List.mem_cons_of_mem _ hqc))
    rw [show (qb :: h) = [qb] ++ h from rfl, encode_list, List.flatMap_append,
      List.length_append, ← encode_list, ← encode_list]
    obtain ⟨q, b⟩ := qb
    have hfirst := length_encode_history_append [] q b
    change (bitEncode ([(q, b)] : History)).length = 0 + (12 * q.length + 5) at hfirst
    change q.length ≤ d at hq
    rw [hfirst, Nat.zero_add, List.singleton_append, List.length_cons]
    change 12 * q.length + 5 + (bitEncode h).length ≤ (h.length + 1) * (12 * d + 5)
    rw [Nat.add_mul, Nat.one_mul, add_comm (h.length * (12 * d + 5))]
    exact Nat.add_le_add (by omega) ht

/-- Asking for the encoded history on each round makes the queries grow. While all the
previous queries are short, the next query fits under the stated polynomial cap. -/
private theorem query_until_large (O : Bits → Bool) (tag z : Bits) (d cap : ℕ) (b : Bool)
    (hcap : tag.length + (6 * z.length + 1) + d * (12 * d + 5) ≤ cap)
    (hO : ∀ h : History, d < (query tag (z, h)).length → O (query tag (z, h)) = b) :
    evalOracle cap (query tag) lastAnswer O z (d + 1) [] = b := by
  suffices ∀ (fuel : ℕ) (h : History),
      ((h.length ≤ d ∧ ∀ qb ∈ h, (qb : Bits × Bool).1.length ≤ d) ∧
          h.length + fuel = d + 1 ∨
        ∃ pre q, h = pre ++ [(q, b)] ∧ d < (q : Bits).length) →
      evalOracle cap (query tag) lastAnswer O z fuel h = b by
    apply this
    left
    simp
  intro fuel
  induction fuel with
  | zero =>
    rintro h (⟨⟨hh, _⟩, hn⟩ | ⟨pre, q, rfl, _⟩)
    · omega
    · exact lastAnswer_append z pre q b
  | succ fuel ih =>
    intro h hh
    let q := query tag (z, h)
    rw [evalOracle]
    change (if q.length ≤ cap then
      evalOracle cap (query tag) lastAnswer O z fuel (h ++ [(q, O q)])
      else lastAnswer (z, h)) = b
    by_cases hq : q.length ≤ cap
    · rw [ite_eq_left hq]
      apply ih
      by_cases hshort : q.length ≤ d
      · obtain ⟨⟨hlen, hall⟩, hfuel⟩ | ⟨pre, last, he, hl⟩ := hh
        · have hnext : h.length + 1 ≤ q.length := by
            rw [show q = query tag (z, h) from rfl, length_query]
            have := length_le_length_flatten_delimit (h.map (bitEncode (α := Bits × Bool)))
            have hlen' : h.length ≤ (bitEncode h).length := by
              change h.length ≤ (((h.map bitEncode).map delimit).flatten).length
              simpa only [List.length_map] using this
            omega
          left
          refine ⟨⟨by simp; omega, ?_⟩, by simp; omega⟩
          intro qb hqb
          rcases List.mem_append.mp hqb with hin | hin
          · exact hall qb hin
          · simpa using (List.mem_singleton.mp hin) ▸ hshort
        · subst h
          have := length_query_grows tag z pre last b
          exact False.elim (by dsimp [q] at hshort; omega)
      · have hlt := Nat.lt_of_not_ge hshort
        have hb := hO h hlt
        right
        exact ⟨h, q, by rw [hb], hlt⟩
    · rw [ite_eq_right hq]
      obtain ⟨⟨hlen, hall⟩, _⟩ | ⟨pre, last, rfl, _⟩ := hh
      · exfalso
        apply hq
        rw [show q = query tag (z, h) from rfl, length_query]
        exact (Nat.add_le_add_left
          ((length_encode_history_le h d hall).trans (Nat.mul_le_mul_right _ hlen)) _).trans hcap
      · exact lastAnswer_append z pre last b

private theorem run_agrees (m : Machine) {O O' : Bits → Bool} (x z : Bits)
    (h : ∀ s, s.length ≤ m.cap.eval x.length → O s = O' s) :
    m.run O x z = m.run O' x z :=
  eval_congr _ _ _ h _ _ _


/-! ## A collapsing oracle by recursion on query length -/

private abbrev Code := Bool × Machine

private noncomputable instance machineEncoding : Encodable Machine :=
  @Encodable.ofCountable Machine countable_machine


private noncomputable def tag (c : Code) : Bits :=
  delimit (List.replicate (Encodable.encode c) true)

private noncomputable def address (a : Code × Input) : Bits :=
  query (tag a.1) a.2

private theorem address_injective : Function.Injective address := by
  rintro ⟨c, i⟩ ⟨c', i'⟩ h
  have he := congrArg undelimit h
  change undelimit (delimit _ ++ bitEncode i) = undelimit (delimit _ ++ bitEncode i') at he
  rw [undelimit_delimit, undelimit_delimit] at he
  obtain ⟨hc, hi⟩ := Prod.mk.inj (Option.some.inj he)
  have hcc : c = c' := Encodable.encode_injective (by
    simpa only [List.length_replicate] using congrArg List.length hc)
  exact Prod.ext hcc (encode_injective hi)

private def payload (mode : Bool) (z : Bits) : Option Bits :=
  if mode then some z else (bitDecode (α := Bits × Bits) z).map Prod.fst

private def accepts (c : Code) (O : Bits → Bool) (x : Bits) : Prop :=
  if c.1 then
    ∃ w : Bits, w.length ≤ c.2.fuel.eval x.length ∧
      c.2.run O x (bitEncode (x, w)) = true
  else c.2.run O x x = true

private theorem accepts_congr (c : Code) {O O' : Bits → Bool} (x : Bits)
    (h : ∀ s, s.length ≤ c.2.cap.eval x.length → O s = O' s) :
    accepts c O x ↔ accepts c O' x := by
  unfold accepts
  simp only [run_agrees c.2 x _ h]

open Classical in
private noncomputable def collapse (s : Bits) : Bool :=
  let a := Function.invFun address s
  match payload a.1.1 a.2.1 with
  | none => false
  | some x =>
    if a.1.2.cap.eval x.length < s.length then
      decide (accepts a.1 (fun t => if _ht : t.length < s.length then collapse t else false) x)
    else false
termination_by s.length

open Classical in
private theorem collapse_answer (c : Code) (z : Bits) (h : History) (x : Bits)
    (hx : payload c.1 z = some x) (hlen : c.2.cap.eval x.length < (query (tag c) (z, h)).length) :
    collapse (query (tag c) (z, h)) = decide (accepts c collapse x) := by
  change collapse (address (c, (z, h))) = _
  rw [collapse]
  have hinv := Function.leftInverse_invFun address_injective (c, (z, h))
  rw [hinv]
  simp only [hx, show c.2.cap.eval x.length < (address (c, (z, h))).length from hlen, ite_true]
  apply Bool.decide_congr
  apply accepts_congr
  intro s hs
  have ht : s.length < (address (c, (z, h))).length := hs.trans_lt hlen
  rw [dite_eq_left ht]

private noncomputable def liftCap (c : Code) (tagLength : ℕ) : Polynomial ℕ :=
  C tagLength + (C 6 * (C 6 * X + C 3 * (c.2.cap + C 1) + C 1) + C 1) +
    c.2.cap * (C 12 * c.2.cap + C 5)

open Classical in
private theorem collapse_run (c : Code) (x z : Bits) (hx : payload c.1 z = some x)
    (hz : z.length ≤ 6 * x.length + 3 * (c.2.cap.eval x.length + 1) + 1) :
    evalOracle ((liftCap c (tag c).length).eval x.length) (query (tag c)) lastAnswer
      collapse z (c.2.cap.eval x.length + 1) [] = decide (accepts c collapse x) := by
  apply query_until_large
  · unfold liftCap
    simp only [eval_add, eval_mul, eval_C, eval_X]
    omega
  · intro h hh
    exact collapse_answer c z h x hx hh

private theorem collapse_equal : PWithOracle collapse = NPWithOracle collapse := by
  classical
  ext L
  constructor
  · rintro ⟨p, q, next, final, hn, hf, hL⟩
    let c : Code := (false, ⟨p, q, next, final, hn, hf⟩)
    refine ⟨q + C 1, liftCap c (tag c).length, query (tag c), lastAnswer,
      query_poly _, lastAnswer_poly, fun x => ?_⟩
    have hl (w : Bits) (hw : w.length ≤ q.eval x.length + 1) :
        evalOracle ((liftCap c (tag c).length).eval x.length) (query (tag c)) lastAnswer
          collapse (bitEncode (x, w)) (q.eval x.length + 1) [] = true ↔ L x := by
      rw [collapse_run c x _ (by simp [payload, c]) (by rw [length_encode_pair]; dsimp [c]; omega)]
      simpa [accepts, c, Machine.run] using (hL x).symm
    simp only [eval_add, eval_C]
    exact ⟨fun hx => ⟨[], by simp, (hl [] (by simp)).mpr hx⟩,
      fun ⟨w, hw, h⟩ => (hl w hw).mp h⟩
  · rintro ⟨p, q, next, final, hn, hf, hL⟩
    let c : Code := (true, ⟨p, q, next, final, hn, hf⟩)
    refine ⟨q + C 1, liftCap c (tag c).length, query (tag c), lastAnswer,
      query_poly _, lastAnswer_poly, fun x => ?_⟩
    simp only [eval_add, eval_C]
    rw [collapse_run c x x rfl (by omega)]
    simpa [accepts, c, Machine.run] using hL x


/-! ## A separating oracle by diagonalization -/

private def witnessAddress (x w : Bits) : Bits := query [] (bitEncode (x, w), [])

private theorem length_witnessAddress (x w : Bits) :
    (witnessAddress x w).length = 36 * x.length + 18 * w.length + 7 := by
  rw [witnessAddress, length_query, length_encode_pair]
  change 0 + (6 * (6 * x.length + 3 * w.length + 1) + 1) + 0 = _
  omega

private theorem witnessAddress_injective (x : Bits) : Function.Injective (witnessAddress x) := by
  intro w w' h
  change bitEncode ((bitEncode (x, w), []) : Input) =
    bitEncode ((bitEncode (x, w'), []) : Input) at h
  have hi : bitEncode (x, w) = bitEncode (x, w') :=
    congrArg (fun i : Input => i.1) (encode_injective h)
  have hp : (x, w) = (x, w') := encode_injective hi
  exact (Prod.mk.inj hp).2

open Classical in
private noncomputable def witnessLanguage (O : Bits → Bool) : DecisionProblem :=
  fun x => decide (∃ w : Bits, w.length ≤ x.length + 1 ∧ O (witnessAddress x w) = true)

private theorem witnessLanguage_mem (O : Bits → Bool) :
    witnessLanguage O ∈ NPWithOracle O := by
  refine ⟨X + C 1, C 54 * X + C 25, query [], lastAnswer, query_poly [],
    lastAnswer_poly, fun x => ?_⟩
  simp only [eval_add, eval_C, eval_X, eval_mul, witnessLanguage, decide_eq_true_eq]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  let z := bitEncode (x, w)
  let q := witnessAddress x w
  let cap := 54 * x.length + 25
  have hq : q.length ≤ cap := by
    dsimp [q, cap]
    rw [length_witnessAddress]
    omega
  have hnext : ¬ (query [] (z, [(q, O q)])).length ≤ cap := by
    have hh := length_encode_history_append [] q (O q)
    change (bitEncode ([(q, O q)] : History)).length = 0 + (12 * q.length + 5) at hh
    rw [length_query, hh]
    dsimp [q, cap]
    rw [length_witnessAddress]
    omega
  have he : evalOracle cap (query []) lastAnswer O z (x.length + 1) [] = O q := by
    change (if q.length ≤ cap then
      evalOracle cap (query []) lastAnswer O z x.length [(q, O q)]
      else lastAnswer (z, [])) = O q
    rw [ite_eq_left hq]
    generalize x.length = n
    cases n with
    | zero => exact lastAnswer_append z [] q (O q)
    | succ n =>
      rw [evalOracle, ite_eq_right hnext]
      exact lastAnswer_append z [] q (O q)
  rw [he]

private def traceQueries (cap : ℕ) (next : Input → Bits) (O : Bits → Bool) (x : Bits) :
    ℕ → History → List Bits
  | 0, _ => []
  | fuel + 1, h =>
    let q := next (x, h)
    if q.length ≤ cap then q :: traceQueries cap next O x fuel (h ++ [(q, O q)]) else []

private theorem length_traceQueries (cap : ℕ) (next : Input → Bits) (O : Bits → Bool)
    (x : Bits) (fuel : ℕ) (h : History) : (traceQueries cap next O x fuel h).length ≤ fuel := by
  induction fuel generalizing h with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    by_cases hq : (next (x, h)).length ≤ cap
    · simpa only [traceQueries, hq, ite_true, List.length_cons, Nat.succ_le_succ_iff] using
        ih (h ++ [(next (x, h), O (next (x, h)))])
    · simp [traceQueries, hq]

private theorem eval_agrees_on_trace (cap : ℕ) (next : Input → Bits) (final : Input → Bool)
    (O O' : Bits → Bool) (x : Bits) (fuel : ℕ) (h : History)
    (ha : ∀ q ∈ traceQueries cap next O x fuel h, O q = O' q) :
    evalOracle cap next final O x fuel h = evalOracle cap next final O' x fuel h := by
  induction fuel generalizing h with
  | zero => rfl
  | succ fuel ih =>
    by_cases hq : (next (x, h)).length ≤ cap
    · simp only [traceQueries, hq, ite_true, List.mem_cons] at ha
      simp only [evalOracle, hq, ite_true, ← ha _ (Or.inl rfl)]
      exact ih _ (fun q hq => ha q (Or.inr hq))
    · simp [evalOracle, hq]

open Filter Asymptotics in
private theorem eventually_eval_lt_pow (p : Polynomial ℕ) :
    ∀ᶠ n in atTop, p.eval n < 2 ^ n := by
  have h : (fun n : ℕ => ((p.eval n : ℕ) : ℝ)) =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Pi.add_apply, eval_add, Nat.cast_add] using hp.add hq
    | monomial d a =>
      simpa only [eval_monomial, Nat.cast_mul, Nat.cast_pow] using
        (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (show (1 : ℝ) < 2 by norm_num)
          ).const_mul_left (a : ℝ)
  filter_upwards [h.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
  norm_num [Real.norm_eq_abs, abs_of_nonneg ((Nat.cast_nonneg (α := ℝ) (p.eval n))),
    abs_of_nonneg (show (0 : ℝ) ≤ 2 ^ n by positivity)] at hn
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  exact_mod_cast (show ((p.eval n : ℕ) : ℝ) < (2 : ℝ) ^ n by linarith)

private structure Stage where
  cutoff : ℕ
  yes : Finset Bits
  bounded : ∀ s ∈ yes, (s : Bits).length ≤ cutoff

private def Stage.oracle (s : Stage) (q : Bits) : Bool := decide (q ∈ s.yes)

private def Stage.Extends (s t : Stage) : Prop :=
  s.cutoff ≤ t.cutoff ∧ s.yes ⊆ t.yes ∧ ∀ q, q.length ≤ s.cutoff → (q ∈ t.yes ↔ q ∈ s.yes)

private theorem Stage.Extends.refl (s : Stage) : s.Extends s :=
  ⟨le_rfl, fun _ h => h, fun _ _ => Iff.rfl⟩

private theorem Stage.Extends.trans {s t u : Stage} (hst : s.Extends t) (htu : t.Extends u) :
    s.Extends u :=
  ⟨hst.1.trans htu.1, fun _ h => htu.2.1 (hst.2.1 h),
    fun q hq => (htu.2.2 q (hq.trans hst.1)).trans (hst.2.2 q hq)⟩

private theorem diagonal_step (s : Stage) (m : Machine) :
    ∃ t : Stage, s.Extends t ∧ ∃ x,
      max (m.cap.eval x.length) (54 * x.length + 25) ≤ t.cutoff ∧
        witnessLanguage t.oracle x ≠ m.run t.oracle x x := by
  classical
  obtain ⟨n, hn, hp⟩ := ((eventually_eval_lt_pow m.fuel).and
    (Filter.eventually_gt_atTop s.cutoff)).exists
  let x : Bits := List.replicate n false
  have hx : x.length = n := List.length_replicate
  let k := max (m.cap.eval n) (54 * n + 25)
  have hk : s.cutoff ≤ k := by
    have := le_max_right (m.cap.eval n) (54 * n + 25)
    omega
  have hfresh (w : Bits) : s.cutoff < (witnessAddress x w).length := by
    rw [length_witnessAddress, hx]
    omega
  have hbound (w : Bits) (hw : w.length ≤ n + 1) : (witnessAddress x w).length ≤ k := by
    rw [length_witnessAddress, hx]
    exact (show 36 * n + 18 * w.length + 7 ≤ 54 * n + 25 by omega).trans (le_max_right _ _)
  cases hD : m.run s.oracle x x with
  | true =>
    let t : Stage := ⟨k, s.yes, fun q hq => (s.bounded q hq).trans hk⟩
    refine ⟨t, ⟨hk, fun _ h => h, fun _ _ => Iff.rfl⟩, x, by rw [hx], ?_⟩
    change witnessLanguage s.oracle x ≠ m.run s.oracle x x
    rw [hD]
    simp only [ne_eq, witnessLanguage, decide_eq_true_eq, not_exists]
    intro w hw
    exact (Nat.not_le_of_gt (hfresh w)) (s.bounded _ (by simpa [Stage.oracle] using hw.2))
  | false =>
    let T := traceQueries (m.cap.eval x.length) m.next s.oracle x (m.fuel.eval x.length) []
    let candidates := Finset.univ.image (fun w : Fin n → Bool => witnessAddress x (List.ofFn w))
    have hc : candidates.card = 2 ^ n := by
      change (Finset.univ.image (witnessAddress x ∘ (List.ofFn : (Fin n → Bool) → Bits))).card = _
      rw [Finset.card_image_of_injective _ ((witnessAddress_injective x).comp List.ofFn_injective)]
      simp
    have ht : T.toFinset.card ≤ m.fuel.eval n := by
      rw [← hx]
      exact (List.toFinset_card_le T).trans (length_traceQueries _ _ _ _ _ _)
    obtain ⟨q, hq, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show T.toFinset.card < candidates.card by rw [hc]; exact ht.trans_lt hn)
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    let q := witnessAddress x (List.ofFn w)
    have hl : q.length ≤ k := hbound _ (by simp)
    have hnew : s.cutoff < q.length := hfresh _
    let t : Stage := ⟨k, insert q s.yes, fun a ha => by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hl
      · exact (s.bounded a ha).trans hk⟩
    refine ⟨t, ⟨hk, fun _ h => Finset.mem_insert_of_mem h, fun a ha => ?_⟩, x,
      by rw [hx], ?_⟩
    · change a ∈ insert q s.yes ↔ a ∈ s.yes
      have hne : a ≠ q := fun he => (Nat.not_le_of_gt hnew) (he ▸ ha)
      simp [hne]
    have hr : m.run s.oracle x x = m.run t.oracle x x := by
      apply eval_agrees_on_trace
      intro a ha
      have hne : a ≠ q := fun he => hnot (List.mem_toFinset.mpr (by
        change q ∈ T
        rwa [← he]))
      simp [Stage.oracle, t, hne]
    rw [← hr, hD]
    have he : witnessLanguage t.oracle x = true := by
      simp only [witnessLanguage, decide_eq_true_eq]
      exact ⟨List.ofFn w, by simp [hx], by simp [q, Stage.oracle, t]⟩
    simp [he]

private theorem separation_exists : ∃ O : Bits → Bool, PWithOracle O ≠ NPWithOracle O := by
  classical
  let := countable_machine
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat Machine
  let step (n : ℕ) (s : Stage) := Classical.choose (diagonal_step s (enumerate n))
  let stage : ℕ → Stage := Nat.rec ⟨0, ∅, by simp⟩ step
  have hstep (n : ℕ) : (stage n).Extends (stage (n + 1)) ∧
      ∃ x, max ((enumerate n).cap.eval x.length) (54 * x.length + 25) ≤
        (stage (n + 1)).cutoff ∧ witnessLanguage (stage (n + 1)).oracle x ≠
          (enumerate n).run (stage (n + 1)).oracle x x :=
    Classical.choose_spec (diagonal_step (stage n) (enumerate n))
  have hext {i j : ℕ} (hij : i ≤ j) : (stage i).Extends (stage j) := by
    induction hij with
    | refl => exact Stage.Extends.refl _
    | step _ ih => exact ih.trans (hstep _).1
  let O : Bits → Bool := fun q => decide (∃ n, q ∈ (stage n).yes)
  have hO (n : ℕ) (q : Bits) (hq : q.length ≤ (stage n).cutoff) :
      O q = (stage n).oracle q := by
    apply Bool.decide_congr
    constructor
    · rintro ⟨i, hi⟩
      rcases le_total i n with hin | hni
      · exact (hext hin).2.1 hi
      · exact ((hext hni).2.2 q hq).mp hi
    · exact fun h => ⟨n, h⟩
  refine ⟨O, fun he => ?_⟩
  have hL : witnessLanguage O ∈ PWithOracle O := he ▸ witnessLanguage_mem O
  obtain ⟨p, q, next, final, hn, hf, hL⟩ := hL
  let m : Machine := ⟨p, q, next, final, hn, hf⟩
  obtain ⟨n, hn⟩ := henumerate m
  obtain ⟨x, hb, hbad⟩ := (hstep n).2
  rw [hn] at hb hbad
  have hrun : m.run O x x = m.run (stage (n + 1)).oracle x x :=
    run_agrees m x x fun a ha => hO (n + 1) _ (ha.trans ((le_max_left _ _).trans hb))
  have hwit : witnessLanguage O x = witnessLanguage (stage (n + 1)).oracle x := by
    apply Bool.decide_congr
    apply exists_congr
    intro w
    apply and_congr_right
    intro hw
    have hwlen : (witnessAddress x w).length ≤ 54 * x.length + 25 := by
      rw [length_witnessAddress]
      omega
    rw [hO (n + 1) _ (hwlen.trans ((le_max_right _ _).trans hb))]
  apply hbad
  rw [← hrun, ← hwit]
  exact Bool.eq_iff_iff.mpr (hL x)

/-- **Baker-Gill-Solovay: oracles separate and collapse P vs NP.** For an oracle $O$, a function
from bitstrings to booleans, write $\mathsf{P}^O$ and $\mathsf{NP}^O$ for the classes of decision
problems decidable in polynomial time, respectively in nondeterministic polynomial time, by
machines that may query $O$. There is an oracle $O$ such that $\mathsf{P}^O \ne \mathsf{NP}^O$,
and there is an oracle $O$ such that $\mathsf{P}^O = \mathsf{NP}^O$.

Source: T. Baker, J. Gill,
and R. Solovay, "Relativizations of the P =? NP question", SIAM Journal on Computing 4
(1975), 431-442. -/
theorem baker_gill_solovay :
    (∃ O : List Bool → Bool, PWithOracle O ≠ NPWithOracle O) ∧
      (∃ O : List Bool → Bool, PWithOracle O = NPWithOracle O) :=
  ⟨separation_exists, ⟨collapse, collapse_equal⟩⟩

end MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay
