/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.JoinKey
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.KeepOrder
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Spec
public import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
public import MathlibExt.Computability.TuringMachine.Cleanup

/-! # Finite-state operations for one marked edge -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.VerifierRow

open Turing Function MetaMathlibExt BitstringEncoding TM2Program TM2Embedding
open Cslib.Complexity.DensestKSubgraph.Internal.VerifierSpec Cslib.Complexity.SatVerifier
open Cslib.Complexity.Karp.EmitSS (U)
open Computability (encodeNat)

/- The two normalized endpoints and the vertex bound. -/
inductive Word | first | second | bound
  deriving DecidableEq

instance : Fintype Word := Fintype.ofList [.first, .second, .bound]
  (by intro a; cases a <;> decide)

/- Three comparisons establish endpoint validity and key orientation. -/
inductive Test | first | second | pair
  deriving DecidableEq

instance : Fintype Test := Fintype.ofList [.first, .second, .pair]
  (by intro a; cases a <;> decide)

/- Two endpoint queries update the vertex dictionary; one key query updates the edge dictionary. -/
inductive Job | first | second | edge
  deriving DecidableEq

instance : Fintype Job := Fintype.ofList [.first, .second, .edge]
  (by intro a; cases a <;> decide)

/- Shared workspaces for comparisons, dictionary operations and product framing. -/
inductive K
  | word (s : Word) | compare (s : KeepOrder.K) | dict (vertex : Bool) (s : Intern.K)
  | buffer | count (vertex : Bool)
  deriving DecidableEq

instance : Fintype K where
  elems := {K.buffer, .count false, .count true} ∪ Finset.univ.image K.word ∪
    Finset.univ.image K.compare ∪ Finset.univ.image (fun p : Bool × Intern.K => .dict p.1 p.2)
  complete k := by cases k with | count b => cases b <;> simp | _ => simp

/- Only physical multiplicities and tagged lookup workspace use the symbol alphabet. -/
@[reducible] def Γ : K → Type
  | .dict _ s => Intern.Γ s
  | .count _ => Sym
  | _ => Bool

/- The three calling sequences terminate in distinct success and rejection labels. -/
inductive Lab
  | cmp (t : Test) (marked : Bool) (s : KeepOrder.Lab)
  | intern (j : Job) (swap : Bool) (s : Intern.Lab)
  | bumpVertex (second swap : Bool) | bumpEdge (swap : Bool)
  | join (swap : Bool) (l : JoinKey.Lab) | clear | done | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.clear, .done, .bad} ∪ Finset.univ.image Lab.bumpEdge ∪
    Finset.univ.image (fun p : Bool × Bool => .bumpVertex p.1 p.2) ∪
    Finset.univ.image (fun p : Test × Bool × KeepOrder.Lab => .cmp p.1 p.2.1 p.2.2) ∪
    Finset.univ.image (fun p : Job × Bool × Intern.Lab => .intern p.1 p.2.1 p.2.2) ∪
    Finset.univ.image (fun p : Bool × JoinKey.Lab => .join p.1 p.2)
  complete l := by cases l <;> simp

/- Select the operands for comparison. -/
def operand : Test → BinaryOrder.K → Word
  | .first, .a | .pair, .a => .first
  | .second, .a | .pair, .b => .second
  | _, .b => .bound

/- Compare the chosen operands without moving or changing them. -/
def cmpPort (t : Test) : KeepOrder.K → K
  | .word w => .word (operand t w)
  | s => .compare s

/- The comparison scratch is disjoint from the data words. -/
def cmpEmb (t : Test) : SEmb (fun _ : KeepOrder.K => Bool) Γ where
  e := cmpPort t
  inj a b h := by
    rcases a with x | x | _ <;> rcases b with y | y | _ <;>
      (try cases x) <;> (try cases y) <;> cases t <;> cases h <;> rfl
  ι s := by cases s <;> exact Equiv.refl Bool

/- Which dictionary receives a request. -/
def vertexJob : Job → Bool
  | .edge => false
  | _ => true

/- Vertex queries read the input endpoints; edge queries use the joined key. -/
def dictPort (job : Job) : Intern.K → K
  | .query => match job with
    | .first => .word .first
    | .second => .word .second
    | .edge => .dict false .query
  | s => .dict (vertexJob job) s

/- Each request touches only its query tape and the selected dictionary. -/
def dictEmb (job : Job) : SEmb Intern.Γ Γ where
  e := dictPort job
  inj a b h := by cases job <;> cases a <;> cases b <;> cases h <;> rfl
  ι s := by cases job <;> cases s <;> exact Equiv.refl _

/- Swapping the input ports makes the edge key independent of its orientation. -/
def joinPort (swap : Bool) : JoinKey.K → K
  | .a => .word (if swap then .second else .first)
  | .b => .word (if swap then .first else .second)
  | .rev => .buffer
  | .out => .dict false .query

/- The join consumes the endpoint words after their final use. -/
def joinEmb (swap : Bool) : SEmb (fun _ : JoinKey.K => Bool) Γ where
  e := joinPort swap
  inj x y h := by cases swap <;> cases x <;> cases y <;> cases h <;> rfl
  ι s := by cases s <;> exact Equiv.refl Bool

/- Branch only on exact binary comparisons. -/
def cmpNext (t : Test) (chosen : Bool) (o : Ordering) : Lab :=
  match t with
  | .first => if o = .lt then .cmp .second chosen (.copy .a) else .bad
  | .second => if o = .lt then .cmp .pair chosen (.copy .a) else .bad
  | .pair => if o = .eq then .bad else
      if chosen then .intern .first (o == .gt) .read else .join (o == .gt) .frame

/- Retain the mark across comparisons using the finite control. -/
def cmpLabel (t : Test) (chosen : Bool) : KeepOrder.Lab → Lab
  | .done o => cmpNext t chosen o
  | l => .cmp t chosen l

/- Bump a counter only when a new distinct vertex has been inserted. -/
def dictNext (job : Job) (swap old : Bool) : Lab :=
  match job with
  | .first => if old then .intern .second swap .read else .bumpVertex false swap
  | .second => if old then .bumpEdge swap else .bumpVertex true swap
  | .edge => if old then .bad else .clear

/- Route each dictionary outcome back to its caller. -/
def dictLabel (job : Job) (swap : Bool) : Intern.Lab → Lab
  | .done old => dictNext job swap old
  | l => .intern job swap l

/- Look up the sorted key immediately after constructing its code. -/
def joinLabel (swap : Bool) : JoinKey.Lab → Lab
  | .done => .intern .edge false .read
  | l => .join swap l

/- The exact per-edge processor performed by the verifier's finite machine. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .cmp t b l => mapS (cmpEmb t) (cmpLabel t b) (KeepOrder.prog l)
  | .intern j r l => mapS (dictEmb j) (dictLabel j r) (Intern.prog l)
  | .bumpVertex second r => incr (.count true) U
      (if second then .bumpEdge r else .intern .second r .read)
  | .bumpEdge r => incr (.count false) U (.join r .frame)
  | .join r l => mapS (joinEmb r) (joinLabel r) (JoinKey.prog l)
  | .clear => cleanS [.dict false .query] .clear .done
  | .done | .bad => .halt

private theorem cmp_ok (t : Test) (b : Bool) :
    Embeds (cmpEmb t) (cmpLabel t b) KeepOrder.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem dict_ok (j : Job) (swap : Bool) :
    Embeds (dictEmb j) (dictLabel j swap) Intern.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem join_ok (swap : Bool) :
    Embeds (joinEmb swap) (joinLabel swap) JoinKey.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

/- The actual contents at a boundary between machine operations. -/
structure Snap where
  words : Word → List Bool
  edgeQuery : List Bool
  keys : Bool → List (List Bool)
  counts : Bool → ℕ

/- At a subroutine boundary all delegated scratch is empty. -/
def stk (s : Snap) : (a : K) → List (Γ a)
  | .word w => s.words w
  | .dict v j => match j with
    | .query => if v then [] else s.edgeQuery
    | .lookup l => match l with
      | .B => tblStk (Intern.ents (s.keys v))
      | _ => []
    | .temp => []
  | .count v => cnt U (s.counts v)
  | _ => []

/- Program encoding of a state just before the first comparison. -/
def snap (n : ℕ) (u v : List Bool) (seen : Seen) : Snap where
  words | .first => u | .second => v | .bound => encodeNat n
  edgeQuery := []
  keys b := if b then seen.vertices.map bitEncode else seen.edges.map bitEncode
  counts b := if b then seen.vertices.length else seen.selected

private theorem word_cmp (t : Test) (chosen : Bool) (s : Snap) (v : Bool) (a b : ℕ)
    (ha : s.words (operand t .a) = encodeNat a) (hb : s.words (operand t .b) = encodeNat b) :
    ∃ w, RunLe prog (3 * (a.size + b.size) + 5)
      ⟨some (.cmp t chosen (.copy .a)), v, stk s⟩
      ⟨some (cmpNext t chosen (compare a b)), w, stk s⟩ := by
  obtain ⟨w, hr⟩ := KeepOrder.run a b v
  have hag : Agree (cmpEmb t) (KeepOrder.st (encodeNat a) (encodeNat b) [] []) (stk s) := by
    intro j
    cases j with
    | word j =>
      cases j with
      | a => exact ha.trans (List.map_id _).symm
      | b => exact hb.trans (List.map_id _).symm
    | work j => cases j <;> rfl
    | temp => rfl
  obtain ⟨T, hrun, has, hf⟩ := runLe_embed (cmpLabel t chosen) (cmp_ok t chosen) hr hag
  have he : T = stk s := by
    funext j
    by_cases h : ∃ u, (cmpEmb t).e u = j
    · obtain ⟨u, rfl⟩ := h
      exact (has u).trans (hag u).symm
    · exact hf j (fun u hu => h ⟨u, hu⟩)
  exact ⟨w, he ▸ hrun⟩

/- The word queried by each dictionary operation. -/
def query (s : Snap) : Job → List Bool
  | .first => s.words .first
  | .second => s.words .second
  | .edge => s.edgeQuery

/- The exact length cost for a dictionary call. -/
def lookupCost (s : Snap) (j : Job) : ℕ :=
  8 * (tblStk (Intern.ents (s.keys (vertexJob j)))).length + 4 * (query s j).length + 10

private theorem key_lookup (s : Snap) (j : Job) (swap v : Bool) :
    let old := query s j ∈ s.keys (vertexJob j)
    let ks := if old then s.keys (vertexJob j) else s.keys (vertexJob j) ++ [query s j]
    ∃ w, RunLe prog (lookupCost s j) ⟨some (.intern j swap .read), v, stk s⟩
      ⟨some (dictNext j swap (decide old)), w,
        stk {s with keys := update s.keys (vertexJob j) ks}⟩ := by
  dsimp only
  let q := query s j
  let ks := s.keys (vertexJob j)
  let new := if q ∈ ks then ks else ks ++ [q]
  let s' := {s with keys := update s.keys (vertexJob j) new}
  have agree (t : Snap) (jt : Job) :
      Agree (dictEmb jt) (Intern.st (query t jt) (t.keys (vertexJob jt))) (stk t) := by
    intro i
    cases jt <;> cases i with
    | lookup l => cases l <;> exact (List.map_id _).symm
    | query | temp => exact (List.map_id _).symm
  obtain ⟨w, hr⟩ := Intern.run q ks v
  obtain ⟨T, hrun, ha, hf⟩ := runLe_embed (dictLabel j swap) (dict_ok j swap) hr (agree s j)
  have hagr : Agree (dictEmb j) (Intern.st q new) (stk s') := by
    have hq : query s' j = q := by cases j <;> rfl
    have hk : s'.keys (vertexJob j) = new := update_self ..
    rw [← hq, ← hk]
    exact agree s' j
  have he : T = stk s' := by
    funext i
    by_cases h : ∃ u, (dictEmb j).e u = i
    · obtain ⟨u, rfl⟩ := h
      exact (ha u).trans (hagr u).symm
    · have hh : stk s i = stk s' i := by
        cases i with
        | word | compare | buffer | count => rfl
        | dict v i =>
          cases i with
          | query => cases v <;> rfl
          | temp => rfl
          | lookup l =>
            cases l <;> try rfl
            have hv : v ≠ vertexJob j := by
              intro heq
              exact h ⟨.lookup .B, by dsimp [dictEmb, dictPort]; rw [heq]⟩
            change tblStk (Intern.ents (s.keys v)) = tblStk (Intern.ents (s'.keys v))
            rw [show s'.keys v = s.keys v from update_of_ne hv new s.keys]
      exact (hf i (fun u hu => h ⟨u, hu⟩)).trans hh
  exact ⟨w, he ▸ hrun⟩

private theorem word_join (s : Snap) (swap v : Bool) :
    let a := s.words (if swap then .second else .first)
    let b := s.words (if swap then .first else .second)
    ∃ w, RunLe prog (3 * a.length + 2 * b.length + 4)
      ⟨some (.join swap .frame), v, stk s⟩
      ⟨some (.intern .edge false .read), w, stk {s with
        words := fun t => if t = .bound then s.words t else [],
        edgeQuery := delimit a ++ b ++ s.edgeQuery}⟩ := by
  dsimp only
  let a := s.words (if swap then .second else .first)
  let b := s.words (if swap then .first else .second)
  obtain ⟨w, hr⟩ := JoinKey.run a b s.edgeQuery v
  obtain ⟨T, hrun, ha, hf⟩ := runLe_embed (joinLabel swap) (join_ok swap) hr (S' := stk s) (by
    intro i; cases swap <;> cases i <;> exact (List.map_id _).symm)
  let s' : Snap := {s with
    words := fun t => if t = .bound then s.words t else []
    edgeQuery := delimit a ++ b ++ s.edgeQuery}
  have he : T = stk s' := by
    funext j
    cases j with
    | word a =>
      cases a with
      | first => cases swap <;> first | exact ha .a | exact ha .b
      | second => cases swap <;> first | exact ha .a | exact ha .b
      | bound => exact hf (.word .bound) (by intro i; cases swap <;> cases i <;> decide)
    | buffer => exact ha .rev
    | count c =>
      exact hf (.count c) (by intro i; cases swap <;> cases i <;> simp [joinEmb, joinPort])
    | compare c =>
      exact hf (.compare c) (by intro i; cases swap <;> cases i <;> simp [joinEmb, joinPort])
    | dict v i =>
      by_cases hv : v = false ∧ i = .query
      · obtain ⟨rfl, rfl⟩ := hv
        exact (ha .out).trans (List.map_id _)
      · refine (hf (.dict v i) ?_).trans ?_
        · intro j; cases swap <;> cases j <;> simp_all [joinEmb, joinPort, eq_comm]
        · cases v <;> cases i <;> simp_all [stk, s']
  exact ⟨w, he ▸ hrun⟩

private theorem clear_key (s : Snap) (v : Bool) :
    RunLe prog (s.edgeQuery.length + 1) ⟨some .clear, v, stk s⟩
      ⟨some .done, Flag.tag false, stk {s with edgeQuery := []}⟩ := by
  have hc := clean_run (M := prog) (self := .clear) rfl (by decide) s.edgeQuery.length v (stk s)
    (by simp [stk])
  have h : (fun i => if i ∈ [K.dict false Intern.K.query] then [] else stk s i) =
      stk {s with edgeQuery := []} := by
    funext i
    cases i with
    | word | compare | buffer | count => rfl
    | dict v i =>
      cases v <;> cases i with
      | lookup l => cases l <;> rfl
      | query | temp => rfl
  rwa [h] at hc

/- Physical size of an initialized lookup table, including one marker per key. -/
def tableLen (ss : List (List Bool)) : ℕ := (tblStk (Intern.ents ss)).length

private theorem tableLen_cons (s : List Bool) (ss : List (List Bool)) :
    tableLen (s :: ss) = s.length + 1 + tableLen ss := by
  simp [tableLen, tblStk, Intern.ents, entToks, Nat.add_comm]

private theorem tableLen_append (xs ys : List (List Bool)) :
    tableLen (xs ++ ys) = tableLen xs + tableLen ys := by
  simp [tableLen, tblStk, Intern.ents, Nat.add_comm]

/- Physical dictionary size is bounded by the number and bit size of the keys. -/
theorem tableLen_le (ss : List (List Bool)) (B : ℕ) (h : ∀ s ∈ ss, s.length ≤ B) :
    tableLen ss ≤ ss.length * (B + 1) := by
  induction ss with
  | nil => exact Nat.zero_le _
  | cons s ss ih =>
    have hh := h s (by simp)
    have ht := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    rw [tableLen_cons, List.length_cons, Nat.succ_mul]
    omega

private theorem encode_insert (x : ℕ) (xs : List ℕ) :
    (GraphKeys.insertKey xs x).map bitEncode =
      if bitEncode x ∈ xs.map bitEncode then xs.map bitEncode
      else xs.map bitEncode ++ [bitEncode x] := by
  by_cases h : x ∈ xs
  · have ht := (GraphKeys.mem_encoded_keys x xs).2 h
    simp only [GraphKeys.insertKey, h, ht, ite_true]
  · have ht : bitEncode x ∉ xs.map bitEncode :=
      fun hh => h ((GraphKeys.mem_encoded_keys x xs).1 hh)
    simp only [GraphKeys.insertKey, h, ht, ite_false, List.map_append, List.map_singleton]

private theorem tableLen_insert (x : ℕ) (xs : List ℕ) :
    tableLen ((GraphKeys.insertKey xs x).map bitEncode) ≤
      tableLen (xs.map bitEncode) + x.size + 1 := by
  rw [encode_insert]
  by_cases h : bitEncode x ∈ xs.map bitEncode
  · simp only [h, ite_true]
    omega
  · simp only [h, ite_false, tableLen_append, tableLen_cons, BinaryNatEncoding.length_bitEncode]
    exact Nat.le_of_eq (Nat.add_assoc _ _ _).symm

private theorem count_stk (s : Snap) (t : Bool) (n : ℕ) :
    update (stk s) (K.count t) (cnt U n) = stk {s with counts := update s.counts t n} := by
  funext j
  cases j with
  | count v => cases v <;> cases t <;> rfl
  | _ => rfl

private theorem vertex_call (right swap v : Bool) (n : ℕ) (e : ℕ × ℕ) (seen : Seen) :
    let u := if right then e.2 else e.1
    let job := if right then Job.second else Job.first
    ∃ w, RunLe prog (8 * tableLen (seen.vertices.map bitEncode) + 4 * u.size + 11)
      ⟨some (.intern job swap .read), v, stk (snap n (encodeNat e.1) (encodeNat e.2) seen)⟩
      ⟨some (if right then .bumpEdge swap else .intern .second swap .read), w,
        stk (snap n (encodeNat e.1) (encodeNat e.2)
          {seen with vertices := GraphKeys.insertKey seen.vertices u})⟩ := by
  dsimp only
  let u := if right then e.2 else e.1
  let job := if right then Job.second else Job.first
  let s := snap n (encodeNat e.1) (encodeNat e.2) seen
  let vs := GraphKeys.insertKey seen.vertices u
  have hvj : vertexJob job = true := by cases right <;> rfl
  have hq : query s job = bitEncode u := by cases right <;> rfl
  have hv : s.keys true = seen.vertices.map bitEncode := rfl
  obtain ⟨w, hr⟩ := key_lookup s job swap v
  rw [lookupCost, hvj, hq, hv, BinaryNatEncoding.length_bitEncode] at hr
  change RunLe prog (8 * tableLen (seen.vertices.map bitEncode) + 4 * u.size + 10) _ _ at hr
  by_cases h : bitEncode u ∈ seen.vertices.map bitEncode
  · have hraw := (GraphKeys.mem_encoded_keys u seen.vertices).mp h
    have hv' : vs = seen.vertices := by simp [vs, GraphKeys.insertKey, hraw]
    have hn : dictNext job swap true =
        (if right then .bumpEdge swap else .intern .second swap .read) := by cases right <;> rfl
    simp only [h, decide_true, ite_true] at hr
    rw [← hv, update_eq_self, hn, hv] at hr
    change ∃ w, RunLe prog (8 * tableLen (seen.vertices.map bitEncode) + 4 * u.size + 11)
      ⟨some (.intern job swap .read), v, stk s⟩
      ⟨some (if right then .bumpEdge swap else .intern .second swap .read), w,
        stk (snap n (encodeNat e.1) (encodeNat e.2) {seen with vertices := vs})⟩
    rw [hv', show ({seen with vertices := seen.vertices} : Seen) = seen from by cases seen; rfl]
    exact ⟨w, hr.mono (Nat.le_succ _)⟩
  · have hraw : u ∉ seen.vertices := fun h' => h ((GraphKeys.mem_encoded_keys _ _).mpr h')
    have hv' : vs = seen.vertices ++ [u] := by simp [vs, GraphKeys.insertKey, hraw]
    have hn : dictNext job swap false = .bumpVertex right swap := by cases right <;> rfl
    simp only [h, decide_false, ite_false, hn] at hr
    let s' := {s with keys := update s.keys true (seen.vertices.map bitEncode ++ [bitEncode u])}
    have hincr := incr_run (M := prog) (self := .bumpVertex right swap) rfl w (stk s')
    change Run prog 1 _ ⟨some (if right then .bumpEdge swap else .intern .second swap .read),
      w, update (stk s') (K.count true) (cnt U (seen.vertices.length + 1))⟩ at hincr
    rw [count_stk] at hincr
    have hkeys : s'.keys =
        (snap n (encodeNat e.1) (encodeNat e.2) {seen with vertices := vs}).keys := by
      funext b
      cases b
      · rfl
      · change seen.vertices.map bitEncode ++ [bitEncode u] = vs.map bitEncode
        rw [hv', List.map_append, List.map_singleton]
    have hcounts : update s'.counts true (seen.vertices.length + 1) =
        (snap n (encodeNat e.1) (encodeNat e.2) {seen with vertices := vs}).counts := by
      funext b
      cases b
      · rfl
      · change seen.vertices.length + 1 = vs.length
        rw [hv', List.length_append, List.length_singleton]
    have he : ({s' with counts := update s'.counts true (seen.vertices.length + 1)} : Snap) =
        snap n (encodeNat e.1) (encodeNat e.2) {seen with vertices := vs} := by
      change Snap.mk s.words s.edgeQuery s'.keys _ =
        Snap.mk s.words s.edgeQuery
          (snap n (encodeNat e.1) (encodeNat e.2) {seen with vertices := vs}).keys
          (snap n (encodeNat e.1) (encodeNat e.2) {seen with vertices := vs}).counts
      rw [hkeys, hcounts]
    rw [he] at hincr
    exact ⟨w, hr.trans (hincr.le le_rfl)⟩

/- Strictly bounded row work before returning to the scan loop. -/
def cost (n : ℕ) (e : ℕ × ℕ) (seen : Seen) : ℕ :=
  8 * (tableLen (seen.edges.map bitEncode) + 2 * tableLen (seen.vertices.map bitEncode)) +
    100 * (n.size + e.1.size + e.2.size + 1)

private theorem join_key_code (e : ℕ × ℕ) :
    let swap := compare e.1 e.2 == .gt
    delimit (encodeNat (if swap then e.2 else e.1)) ++ encodeNat (if swap then e.1 else e.2) =
      bitEncode (GraphKeys.key e) := by
  by_cases h : e.2 < e.1
  · rw [show compare e.1 e.2 = .gt from Nat.compare_eq_gt.mpr h]
    simp only [beq_self_eq_true, ↓reduceIte, GraphKeys.key, min_eq_right h.le, max_eq_left h.le]
    rfl
  · have hn : compare e.1 e.2 ≠ .gt := fun he => h (Nat.compare_eq_gt.mp he)
    have he : (compare e.1 e.2 == .gt) = false := beq_eq_false_iff_ne.mpr hn
    rw [he]
    simp only [Bool.false_eq_true, ↓reduceIte, GraphKeys.key, min_eq_left (Nat.le_of_not_gt h),
      max_eq_right (Nat.le_of_not_gt h)]
    rfl

private theorem key_len (e : ℕ × ℕ) : (bitEncode (GraphKeys.key e)).length ≤
    2 * (e.1.size + e.2.size) + 1 := by
  have hl := BinaryNatEncoding.bitEncode_pair_nat_length_le (GraphKeys.key e)
  rcases le_total e.1 e.2 with h | h
  · simpa only [GraphKeys.key, min_eq_left h, max_eq_right h] using hl
  · simpa only [GraphKeys.key, min_eq_right h, max_eq_left h, Nat.add_comm] using hl

private theorem after_join (n : ℕ) (e : ℕ × ℕ) (seen : Seen) (v : Bool) :
    ∃ w T, RunLe prog (8 * tableLen (seen.edges.map bitEncode) + 20 * (e.1.size + e.2.size + 1))
      ⟨some (.join (compare e.1 e.2 == .gt) .frame), v,
        stk (snap n (encodeNat e.1) (encodeNat e.2) seen)⟩
      ⟨some (if GraphKeys.key e ∈ seen.edges then .bad else .done), w, T⟩ ∧
      (GraphKeys.key e ∉ seen.edges → T =
        stk (snap n [] [] {seen with edges := seen.edges ++ [GraphKeys.key e]})) := by
  let swap := compare e.1 e.2 == .gt
  let q := bitEncode (GraphKeys.key e)
  let s := snap n (encodeNat e.1) (encodeNat e.2) seen
  let t := {snap n [] [] seen with edgeQuery := q}
  obtain ⟨w₁, hr₁⟩ := word_join s swap v
  have hword (s₁ : Word) : (if s₁ = .bound then s.words s₁ else []) =
      (snap n [] [] seen).words s₁ := by cases s₁ <;> rfl
  have hjoin : ({s with
      words := fun s₁ => if s₁ = .bound then s.words s₁ else []
      edgeQuery := delimit (s.words (if swap then .second else .first)) ++
        s.words (if swap then .first else .second) ++ s.edgeQuery} : Snap) = t := by
    have hp (b : Bool) : s.words (if b then .second else .first) =
        encodeNat (if b then e.2 else e.1) := by cases b <;> rfl
    have hq (b : Bool) : s.words (if b then .first else .second) =
        encodeNat (if b then e.1 else e.2) := by cases b <;> rfl
    rw [hp, hq, show s.edgeQuery = [] from rfl, List.append_nil, join_key_code e]
    unfold t
    rw [show (fun s₁ => if s₁ = Word.bound then s.words s₁ else []) =
      (snap n [] [] seen).words from funext hword]
    rfl
  rw [hjoin] at hr₁
  have hc (b : Bool) : (s.words (if b then .second else .first)).length ≤ e.1.size + e.2.size ∧
      (s.words (if b then .first else .second)).length ≤ e.1.size + e.2.size := by
    cases b <;> simp [s, snap]
  obtain ⟨w₂, hr₂⟩ := key_lookup t .edge false w₁
  change RunLe prog (8 * tableLen (seen.edges.map bitEncode) + 4 * q.length + 10) _
      ⟨some (dictNext .edge false (decide (q ∈ seen.edges.map bitEncode))), w₂,
        stk {t with keys := update t.keys false (if q ∈ seen.edges.map bitEncode then
          seen.edges.map bitEncode else seen.edges.map bitEncode ++ [q])}⟩ at hr₂
  have heq : q ∈ seen.edges.map bitEncode ↔ GraphKeys.key e ∈ seen.edges :=
    GraphKeys.mem_encoded_keys _ _
  simp only [heq] at hr₂
  have hlen : q.length ≤ 2 * (e.1.size + e.2.size) + 1 := key_len e
  by_cases h : GraphKeys.key e ∈ seen.edges
  · simp only [h, decide_true, dictNext, ↓reduceIte] at hr₂
    refine ⟨w₂, stk {t with keys := update t.keys false (seen.edges.map bitEncode)},
      ?_, fun h' => (h' h).elim⟩
    simp only [h, ite_true]
    have hh := hc swap
    exact (hr₁.trans hr₂).mono (by omega)
  · simp only [h, decide_false, dictNext, Bool.false_eq_true, ↓reduceIte] at hr₂
    let t' := {t with keys := update t.keys false (seen.edges.map bitEncode ++ [q])}
    have ht : ({t' with edgeQuery := []} : Snap) =
        snap n [] [] {seen with edges := seen.edges ++ [GraphKeys.key e]} := by
      have hkeys : t'.keys =
          (snap n [] [] {seen with edges := seen.edges ++ [GraphKeys.key e]}).keys := by
        funext j
        cases j
        · change seen.edges.map bitEncode ++ [q] = (seen.edges ++ [GraphKeys.key e]).map bitEncode
          simp [q]
        · rfl
      simp only [t', t, snap] at hkeys ⊢
      rw [hkeys]
    have hr₃ := clear_key t' w₂
    rw [ht] at hr₃
    refine ⟨Flag.tag false,
      stk (snap n [] [] {seen with edges := seen.edges ++ [GraphKeys.key e]}), ?_, fun _ => rfl⟩
    simp only [h, ite_false]
    have hh := hc swap
    have htq : t'.edgeQuery.length = q.length := rfl
    exact ((hr₁.trans hr₂).trans hr₃).mono (by omega)

private theorem run_marks (n : ℕ) (e : ℕ × ℕ) (seen : Seen) (b swap v : Bool) :
    ∃ w, RunLe prog (16 * tableLen (seen.vertices.map bitEncode) +
        20 * (e.1.size + e.2.size + 2))
      ⟨some (if b then .intern .first swap .read else .join swap .frame), v,
        stk (snap n (encodeNat e.1) (encodeNat e.2) seen)⟩
      ⟨some (.join swap .frame), w, stk (snap n (encodeNat e.1) (encodeNat e.2)
        {seen with vertices := mark seen e b, selected := seen.selected + b.toNat})⟩ := by
  cases b with
  | false => exact ⟨v, RunLe.refl _ _⟩
  | true =>
    let seen₁ : Seen := {seen with vertices := GraphKeys.insertKey seen.vertices e.1}
    let seen₂ : Seen := {seen₁ with vertices := GraphKeys.insertKey seen₁.vertices e.2}
    obtain ⟨w₁, h₁⟩ := vertex_call false swap v n e seen
    obtain ⟨w₂, h₂⟩ := vertex_call true swap w₁ n e seen₁
    let s := snap n (encodeNat e.1) (encodeNat e.2) seen₂
    have h₃ := incr_run (M := prog) (self := .bumpEdge swap) rfl w₂ (stk s)
    change Run prog 1 _ ⟨some (.join swap .frame), w₂,
      update (stk s) (K.count false) (cnt U (seen.selected + 1))⟩ at h₃
    rw [count_stk] at h₃
    have he : ({s with counts := update s.counts false (seen.selected + 1)} : Snap) =
        snap n (encodeNat e.1) (encodeNat e.2)
          {seen with vertices := mark seen e true, selected := seen.selected + true.toNat} := by
      have hc : update s.counts false (seen.selected + 1) =
          (snap n (encodeNat e.1) (encodeNat e.2)
            {seen with vertices := seen₂.vertices, selected := seen.selected + 1}).counts := by
        funext j
        cases j <;> rfl
      change ({s with counts := update s.counts false (seen.selected + 1)} : Snap) =
        snap n (encodeNat e.1) (encodeNat e.2)
          {seen with vertices := seen₂.vertices, selected := seen.selected + 1}
      simp only [s, snap] at hc ⊢
      rw [hc]
    rw [he] at h₃
    have ht := tableLen_insert e.1 seen.vertices
    refine ⟨w₂, ((h₁.trans h₂).trans (h₃.le le_rfl)).mono ?_⟩
    simp only [seen₁, Bool.false_eq_true, ↓reduceIte]
    omega

/- The complete edge step checks both bounds, the self-loop rule and undirected uniqueness.
It restores the empty row workspace on success and updates the abstract counters exactly. -/
theorem run (n : ℕ) (e : ℕ × ℕ) (seen : Seen) (b v : Bool) :
    ∃ w T, RunLe prog (cost n e seen)
      ⟨some (.cmp .first b (.copy .a)), v, stk (snap n (encodeNat e.1) (encodeNat e.2) seen)⟩
      ⟨some (if Valid n e ∧ GraphKeys.key e ∉ seen.edges then .done else .bad), w, T⟩ ∧
      (Valid n e ∧ GraphKeys.key e ∉ seen.edges →
        T = stk (snap n [] [] (advance seen e b))) := by
  let s := snap n (encodeNat e.1) (encodeNat e.2) seen
  obtain ⟨w₁, h₁⟩ := word_cmp .first b s v e.1 n rfl rfl
  by_cases hA : e.1 < n
  swap
  · have hh : ¬ (Valid n e ∧ GraphKeys.key e ∉ seen.edges) := fun h => hA h.1.1
    refine ⟨w₁, stk s, ?_, fun h => (hh h).elim⟩
    have hn : compare e.1 n ≠ .lt := fun h => hA (Nat.compare_eq_lt.mp h)
    simp only [cmpNext, hn, ite_false] at h₁
    simpa only [hh, ite_false] using h₁.mono (by unfold cost; omega)
  rw [Nat.compare_eq_lt.mpr hA] at h₁
  obtain ⟨w₂, h₂⟩ := word_cmp .second b s w₁ e.2 n rfl rfl
  by_cases hB : e.2 < n
  swap
  · have hh : ¬ (Valid n e ∧ GraphKeys.key e ∉ seen.edges) := fun h => hB h.1.2.1
    refine ⟨w₂, stk s, ?_, fun h => (hh h).elim⟩
    have hn : compare e.2 n ≠ .lt := fun h => hB (Nat.compare_eq_lt.mp h)
    simp only [cmpNext, hn, ite_false] at h₂
    simpa only [hh, ite_false] using (h₁.trans h₂).mono (by unfold cost; omega)
  rw [Nat.compare_eq_lt.mpr hB] at h₂
  obtain ⟨w₃, h₃⟩ := word_cmp .pair b s w₂ e.1 e.2 rfl rfl
  by_cases hC : e.1 = e.2
  · have hh : ¬ (Valid n e ∧ GraphKeys.key e ∉ seen.edges) := fun h => h.1.2.2 hC
    rw [Nat.compare_eq_eq.mpr hC] at h₃
    refine ⟨w₃, stk s, ?_, fun h => (hh h).elim⟩
    simpa only [hh, ite_false, cmpNext, ↓reduceIte] using
      ((h₁.trans h₂).trans h₃).mono (by unfold cost; omega)
  have hV : Valid n e := ⟨hA, hB, hC⟩
  have hn : compare e.1 e.2 ≠ .eq := fun h => hC (Nat.compare_eq_eq.mp h)
  simp only [cmpNext, hn, ite_false] at h₃
  let seen' : Seen := {seen with vertices := mark seen e b, selected := seen.selected + b.toNat}
  obtain ⟨w₄, h₄⟩ := run_marks n e seen b (compare e.1 e.2 == .gt) w₃
  obtain ⟨w, T, h₅, hT⟩ := after_join n e seen' w₄
  have hl : (if GraphKeys.key e ∈ seen'.edges then Lab.bad else .done) =
      (if Valid n e ∧ GraphKeys.key e ∉ seen.edges then .done else .bad) := by
    dsimp only [seen']
    by_cases h : GraphKeys.key e ∈ seen.edges <;> simp [h, hV]
  rw [hl] at h₅
  refine ⟨w, T, ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).mono ?_, fun h => hT h.2⟩
  unfold cost
  dsimp only [seen']
  omega

end Cslib.Complexity.DensestKSubgraph.Internal.VerifierRow
