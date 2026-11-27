/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Comprehension

/-!
# Polynomial-time normal-form gate operations

Encode literals as words, clauses as lists of framed literals, formulas as lists
of framed clauses, and alternatives as lists of framed formulas. Binary gate
operations need at most two nested Cartesian products. A large conjunction in a
weft-one circuit has a single alternative per predecessor, so it can collect the
clauses of those alternatives with one traversal.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.NormalFormMachine

open MetaMathlibExt BitstringEncoding ComplexityTheory
open Cslib.Complexity.PolynomialEncoding.BitScan Cslib.Complexity.PolynomialEncoding.Comprehension

local notation "Word" => List Bool

/-- A sequence of self-delimiting rows. -/
def frames (xs : List Word) : Word := xs.flatMap delimit

@[simp] private theorem rows_frames (xs : List Word) : rowsOf (frames xs) = xs := rowsOf_frames xs

@[simp] private theorem frames_append (xs ys : List Word) :
    frames (xs ++ ys) = frames xs ++ frames ys := List.flatMap_append

/-- Apply a word operation to every pair of rows and frame each result. The
input to each call consists of the left row followed by the right row. -/
def cross (op : Word → Word) (w : Word) : Word :=
  (rowsOf (hd w)).flatMap fun x => (rowsOf (tl w)).flatMap fun y =>
    delimit (op (pack x y))

/-- All input traversal, calls, framing and concatenation in a Cartesian product
take polynomial time when the operation on a pair of rows does. -/
theorem polyCross {op : Word → Word} (hop : IsPolyTime op) : IsPolyTime (cross op) := by
  have hl := polyField true false
  have hr := polyField false true
  have inner := polyFlatMap hr hl (((polyPack hr hl).comp hop).comp polyDelimit)
  unfold cross
  simpa only [Function.comp_def, hd_pack, tl_pack] using polyFlatMap hl hr inner

private theorem cross_frames (op : Word → Word) (xs ys : List Word) :
    cross op (pack (frames xs) (frames ys)) =
      frames (xs.flatMap fun x => ys.map fun y => op (pack x y)) := by
  simp [cross, frames, List.flatMap_map, List.flatMap_assoc]

/-- A variable label and its polarity can be represented by an arbitrary literal word. -/
abbrev Clause := List Word

/-- The clauses of one alternative. -/
abbrev Formula := List Clause

/-- A family of alternative CNFs. -/
abbrev Family := List Formula

/-- Serialize a formula together with all its clauses. -/
def encodeFormula (p : Formula) := frames (p.map frames)

/-- Serialize a family together with all its alternatives. -/
def encodeFamily (a : Family) := frames (a.map encodeFormula)

def merge (w : Word) := hd w ++ tl w

theorem polyMerge : IsPolyTime merge :=
  polyAppend (polyField true false) (polyField false true)

/-- A nonempty outer alternative represents a CNF, with any literal representation. -/
abbrev FamilyOf (L : Type*) := List (List (List L))

/-- Clause distribution of a disjunction of formulas, before any duplicate removal. -/
def distribute {L : Type*} (p q : List (List L)) : List (List L) :=
  p.flatMap fun c => q.map (c ++ ·)

/-- Choose a branch on each side and conjoin their clauses. -/
def binaryAnd {L : Type*} (a b : FamilyOf L) : FamilyOf L := a.flatMap fun p => b.map (p ++ ·)

/-- Choose a branch on each side and distribute their disjunction over clauses. -/
def binaryOr {L : Type*} (a b : FamilyOf L) : FamilyOf L := a.flatMap fun p => b.map (distribute p)

private theorem merge_clause (c e : Clause) :
    merge (pack (frames c) (frames e)) = frames (c ++ e) := by simp [merge]

private theorem merge_formula (p q : Formula) :
    merge (pack (encodeFormula p) (encodeFormula q)) = encodeFormula (p ++ q) := by
  simp [merge, encodeFormula]

private theorem distribute_correct (p q : Formula) :
    cross merge (pack (encodeFormula p) (encodeFormula q)) = encodeFormula (distribute p q) := by
  simp [encodeFormula, cross_frames, distribute, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def, merge_clause]

private theorem and_correct (a b : Family) :
    cross merge (pack (encodeFamily a) (encodeFamily b)) = encodeFamily (binaryAnd a b) := by
  simp [encodeFamily, cross_frames, binaryAnd, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def, merge_formula]

private theorem or_correct (a b : Family) :
    cross (cross merge) (pack (encodeFamily a) (encodeFamily b)) = encodeFamily (binaryOr a b) := by
  simp [encodeFamily, cross_frames, binaryOr, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def, distribute_correct]

def manyOr (w : Word) := (rowsOf w).flatten

def manyAnd (w : Word) := delimit ((rowsOf w).flatMap hd)

theorem polyManyOr : IsPolyTime manyOr := by
  have h := polyFlatMap polyWordId (polyConst []) (polyField true false)
  have e : (fun x : Word => (rowsOf x).flatMap (fun r => hd (pack r []))) = manyOr := by
    funext x
    simp [manyOr, List.flatMap_def]
  exact e ▸ h

theorem polyManyAnd : IsPolyTime manyAnd := by
  have h := (polyFlatMap polyWordId (polyConst []) ((polyField true false).comp
    (polyField true false))).comp polyDelimit
  change IsPolyTime (fun x : Word => delimit ((rowsOf x).flatMap hd))
  simpa only [Function.comp_def, hd_pack] using h

private theorem manyOr_correct (args : List Family) :
    manyOr (frames (args.map encodeFamily)) = encodeFamily args.flatten := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    simpa only [manyOr, rows_frames, List.map_cons, List.flatten_cons, encodeFamily,
      List.map_append, frames_append, List.map_flatten] using
      congrArg (encodeFamily a ++ ·) ih

private theorem manyAnd_correct (args : List Formula) :
    manyAnd (frames (args.map fun p => encodeFamily [p])) = encodeFamily [args.flatten] := by
  have head (p : Formula) : hd (encodeFamily [p]) = encodeFormula p := by
    change hd (pack _ []) = _
    simp
  have flatten (ps : List Formula) : (ps.map encodeFormula).flatten = encodeFormula ps.flatten := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [ih, encodeFormula]
  rw [manyAnd, rows_frames, List.flatMap_def, List.map_map]
  simp only [Function.comp_def, head, flatten]
  simp [encodeFamily, frames]

/-- Evaluate a fan-in gate on a framed list of already normalized child families. -/
def combine (conjunction : Bool) (w : Word) : Word :=
  if w.isEmpty then encodeFamily (if conjunction then [[]] else [[[]]])
  else if (tl w).isEmpty then hd w
  else if (tl (tl w)).isEmpty then
    cross (if conjunction then merge else cross merge) (pack (hd w) (hd (tl w)))
  else if conjunction then manyAnd w else manyOr w

/-- The large-gate clause pool and all arity dispatch, including the zero- and
one-input cases, take polynomial time on arbitrary input words. -/
theorem polyCombine (conjunction : Bool) : IsPolyTime (combine conjunction) := by
  have hl := polyField true false
  have hr := polyField false true
  cases conjunction <;>
    apply polyIf polyEmpty (polyConst _) <;>
    apply polyIf (hr.comp polyEmpty) hl <;>
    apply polyIf ((hr.comp hr).comp polyEmpty)
  · exact (polyPack hl (hr.comp hl)).comp (polyCross (polyCross polyMerge))
  · exact polyManyOr
  · exact (polyPack hl (hr.comp hl)).comp (polyCross polyMerge)
  · exact polyManyAnd

private theorem empty_pack (a b : Word) : (pack a b).isEmpty = false := by
  cases a <;> rfl

private theorem frames_cons (a : Word) (xs : List Word) :
    frames (a :: xs) = pack a (frames xs) := rfl

private theorem frames_nil : frames [] = [] := rfl

/-- The list operations realized by `combine`. At a large conjunction the first
alternative of each child is sufficient when each child is a singleton. -/
def combineFamilies {L : Type*} (conjunction : Bool) : List (FamilyOf L) → FamilyOf L
  | [] => if conjunction then [[]] else [[[]]]
  | [a] => a
  | [a, b] => if conjunction then binaryAnd a b else binaryOr a b
  | a :: b :: c :: tail =>
      if conjunction then [((a :: b :: c :: tail).map (·.headD [])).flatten]
      else (a :: b :: c :: tail).flatten

private theorem head_family (a : Family) : hd (encodeFamily a) = encodeFormula (a.headD []) := by
  cases a with
  | nil => rfl
  | cons p a => exact hd_pack _ _

private theorem manyAnd_first (args : List Family) :
    manyAnd (frames (args.map encodeFamily)) =
      encodeFamily [((args.map (·.headD [])).flatten)] := by
  have h := manyAnd_correct (args.map (·.headD []))
  apply Eq.trans _ h
  unfold manyAnd
  simp only [rows_frames, List.flatMap_map, head_family, List.headD_cons]

/-- Decoding the machine's gate output gives exactly the list of alternatives specified by
`combineFamilies`, for any fan-in. -/
theorem combine_correct (conjunction : Bool) (xs : List Family) :
    combine conjunction (frames (xs.map encodeFamily)) =
      encodeFamily (combineFamilies conjunction xs) := by
  match xs with
  | [] => rfl
  | [a] => simp [combine, combineFamilies, frames_cons, frames_nil, empty_pack]
  | [a,b] =>
    cases conjunction <;>
      simp [combine, combineFamilies, frames_cons, frames_nil, empty_pack, and_correct, or_correct]
  | a :: b :: c :: tail =>
    have hm : (frames (((a :: b :: c :: tail) : List Family).map encodeFamily)).isEmpty = false :=
      empty_pack _ _
    have h₁ : (tl (frames (((a :: b :: c :: tail) : List Family).map encodeFamily))).isEmpty =
        false := by simp [frames_cons, empty_pack]
    have h₂ : (tl (tl (frames ((a :: b :: c :: tail).map encodeFamily)))).isEmpty = false :=
      by simp [frames_cons, empty_pack]
    unfold combine
    simp only [hm, h₁, h₂, Bool.false_eq_true, ite_false]
    cases conjunction
    · exact manyOr_correct _
    · exact manyAnd_first _

/-- A formula is satisfied when each of its clauses contains a true literal. -/
def Models {L : Type*} (truth : L → Prop) (p : List (List L)) : Prop := ∀ c ∈ p, ∃ l ∈ c, truth l

/-- A family is satisfied when it has a satisfied alternative. -/
def Satisfies {L : Type*} (truth : L → Prop) (a : FamilyOf L) : Prop := ∃ p ∈ a, Models truth p

private theorem models_distribute {L : Type*} (t : L → Prop) (p q : List (List L)) :
    Models t (distribute p q) ↔ Models t p ∨ Models t q := by
  classical
  constructor
  · intro h
    by_contra! bad
    obtain ⟨c, hc, hn⟩ : ∃ c ∈ p, ¬ ∃ l ∈ c, t l := by simpa [Models] using bad.1
    obtain ⟨e, he, hm⟩ : ∃ e ∈ q, ¬ ∃ l ∈ e, t l := by simpa [Models] using bad.2
    obtain ⟨l, hl, ht⟩ := h _ (List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨e, he, rfl⟩⟩)
    exact (List.mem_append.mp hl).elim (fun u => hn ⟨l, u, ht⟩) (fun u => hm ⟨l, u, ht⟩)
  · rintro h c hc
    obtain ⟨l, hl, hrest⟩ := List.mem_flatMap.mp hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrest
    rcases h with h | h
    · obtain ⟨x, hx, ht⟩ := h l hl
      exact ⟨x, List.mem_append_left _ hx, ht⟩
    · obtain ⟨x, hx, ht⟩ := h r hr
      exact ⟨x, List.mem_append_right _ hx, ht⟩

private theorem models_append {L : Type*} (t : L → Prop) (p q : List (List L)) :
    Models t (p ++ q) ↔ Models t p ∧ Models t q := by
  simp [Models, or_imp, forall_and]

private theorem satisfies_and {L : Type*} (t : L → Prop) (a b : FamilyOf L) :
    Satisfies t (binaryAnd a b) ↔ Satisfies t a ∧ Satisfies t b := by
  simp only [Satisfies, binaryAnd, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨p, hp, q, hq, rfl⟩, h⟩
    exact ⟨⟨p, hp, (models_append t p q).mp h |>.1⟩, ⟨q, hq, (models_append t p q).mp h |>.2⟩⟩
  · rintro ⟨⟨p, hp, h⟩, q, hq, h'⟩
    exact ⟨_, ⟨p, hp, q, hq, rfl⟩, (models_append t p q).mpr ⟨h, h'⟩⟩

private theorem satisfies_or {L : Type*} (t : L → Prop) (a b : FamilyOf L)
    (ha : a ≠ []) (hb : b ≠ []) :
    Satisfies t (binaryOr a b) ↔ Satisfies t a ∨ Satisfies t b := by
  simp only [Satisfies, binaryOr, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨p, hp, q, hq, rfl⟩, h⟩
    exact ((models_distribute t p q).mp h).imp (fun h => ⟨p, hp, h⟩) (fun h => ⟨q, hq, h⟩)
  · rintro (⟨p, hp, h⟩ | ⟨q, hq, h⟩)
    · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hb
      exact ⟨_, ⟨p, hp, q, hq, rfl⟩, (models_distribute t p q).mpr (Or.inl h)⟩
    · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ ha
      exact ⟨_, ⟨p, hp, q, hq, rfl⟩, (models_distribute t p q).mpr (Or.inr h)⟩

/-- The machine realizes conjunction or disjunction of its inputs. At a gate of fan-in
above two, the relevant weft-one invariant is that each child has one alternative. -/
theorem combine_satisfies {L : Type*} (t : L → Prop) (conjunction : Bool) (xs : List (FamilyOf L))
    (nonempty : ∀ a ∈ xs, a ≠ []) (single : 2 < xs.length → ∀ a ∈ xs, a.length = 1) :
    Satisfies t (combineFamilies conjunction xs) ↔
      (if conjunction then ∀ a ∈ xs, Satisfies t a else ∃ a ∈ xs, Satisfies t a) := by
  match xs with
  | [] => cases conjunction <;> simp [combineFamilies, Satisfies, Models]
  | [a] => cases conjunction <;> simp [combineFamilies]
  | [a,b] =>
    cases conjunction <;>
      simp [combineFamilies, satisfies_and, satisfies_or t a b
        (nonempty _ (by simp)) (nonempty _ (by simp))]
  | a :: b :: c :: tail =>
    let xs := a :: b :: c :: tail
    have elem (p) (hp : p ∈ xs) : Satisfies t p ↔ Models t (p.headD []) := by
      obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp (single (by simp) p hp)
      simp [Satisfies]
    cases conjunction with
    | false =>
      change Satisfies t xs.flatten ↔ ∃ p ∈ xs, Satisfies t p
      simp only [Satisfies, List.mem_flatten]
      grind
    | true =>
      change Satisfies t [(xs.map (·.headD [])).flatten] ↔ ∀ p ∈ xs, Satisfies t p
      have singleton (p : List (List L)) : Satisfies t [p] ↔ Models t p := by simp [Satisfies]
      rw [singleton]
      constructor
      · intro h p hp
        apply (elem p hp).mpr
        exact fun c hc => h c (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, hc⟩)
      · intro h c hc
        obtain ⟨_, helem, hclause⟩ := List.mem_flatten.mp hc
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp helem
        exact (elem p hp).mp (h p hp) c hclause

/-- Change the representation of each literal without changing any rows. -/
def mapFamily {L T : Type*} (f : L → T) (a : FamilyOf L) : FamilyOf T :=
  a.map (List.map (List.map f))

/-- Gate normalization commutes with changing how literals are represented. -/
theorem mapFamily_combine {L T : Type*} (f : L → T) (b : Bool) (args : List (FamilyOf L)) :
    mapFamily f (combineFamilies b args) = combineFamilies b (args.map (mapFamily f)) := by
  have h (q : FamilyOf L) : (mapFamily f q).headD [] = (q.headD []).map (List.map f) := by
    cases q <;> rfl
  match args with
  | [] => cases b <;> rfl
  | [a] => rfl
  | [a,c] =>
    cases b <;>
      simp [combineFamilies, binaryAnd, binaryOr, distribute, mapFamily,
        List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  | a :: c :: z :: tail =>
    let xs := a :: c :: z :: tail
    cases b with
    | false =>
      change xs.flatten.map (List.map (List.map f)) = (xs.map (mapFamily f)).flatten
      rw [List.map_flatten]; rfl
    | true =>
      change [((xs.map (·.headD [])).flatten).map (List.map f)] =
        [((xs.map (mapFamily f)).map (·.headD [])).flatten]
      simp only [List.map_flatten, List.map_map, Function.comp_def, h]

/-- An operator acting on any literal type has the same machine certificate after serialization. -/
theorem combine_encoded {L : Type*} (f : L → Word) (b : Bool) (args : List (FamilyOf L)) :
    combine b (frames (args.map (fun a => encodeFamily (mapFamily f a)))) =
      encodeFamily (mapFamily f (combineFamilies b args)) := by
  rw [mapFamily_combine]
  simpa only [List.map_map, Function.comp_def] using combine_correct b (args.map (mapFamily f))

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.NormalFormMachine
