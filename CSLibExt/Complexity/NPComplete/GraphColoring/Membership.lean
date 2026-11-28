/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import CSLibExt.Computability.Complexity.FramedCNF.Block
public import CSLibExt.Computability.Complexity.Host
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPair
public import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.TuringMachine.BitOps
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
import Mathlib.Tactic.Linarith

/-!
# GRAPH COLORING is in NP

A certificate for an instance `(n, E, K)` lists, for each edge `(u, v)` of `E` in order, the
colors `(a, b)` of its two endpoints. The check `Verification.ok` asks that there are as many
color pairs as edges, that `n = 0` or `K ≠ 0`, that every edge has distinct endpoints below `n`
and distinct colors below `K`, and that every two edges are neither equal nor reversed and give
equal endpoints equal colors. The vertex count and the bound are only compared, never unrolled,
so the certificate stays small when `n` is large and most vertices are isolated.

* `Verification.sound` and `Verification.complete`: a passing certificate gives a well-formed
  instance and a proper `K`-coloring, and a well-formed `K`-colorable instance has a passing
  certificate whose colors are below `2 |E|`.
* `Verification.graphColoringDec_iff`: GRAPH COLORING accepts `x` exactly when some witness of
  length at most `15 (|x| + 1)²` passes `Verification.gcCheck`, the check on bit strings.
* `Verification.Top.prog`: a multi-stack Turing machine that decodes the instance and the
  witness with the existing canonical decoders (`PolynomialEncoding.PairSplit`,
  `FramedCNF.NormalizeMachine`, `PolynomialEncoding.ListNatPair`) and runs the check
  phase `Verification.Check.prog`; `Verification.Top.full_run` bounds its running time.
* `Verification.graphColoringDec_mem_NP`: GRAPH COLORING is in NP.
-/

@[expose] public section

/-!
## GRAPH COLORING: a sparse certificate check

A certificate for an instance `(n, E, K)` lists, for the `j`-th edge `(u, v)` of `E`, the colors
`(a, b)` of its two endpoints. Writing `r = (u, v, a, b)` for the records, the check `ok` asks
that there are as many color pairs as edges, that `n = 0` or `K ≠ 0`, that every record has
`u, v < n`, `a, b < K`, `u ≠ v` and `a ≠ b` (`single`), and that every two records at different
positions satisfy `pairOk`: they are not the same edge, not reversed edges, and equal endpoints
get equal colors.

* `sound`: a passing certificate gives a well-formed instance and a proper `K`-coloring (a
  vertex takes the color of its first occurrence, and `0` if it is isolated).
* `complete`: a well-formed `K`-colorable instance has a passing certificate whose colors are
  the ranks of the used colors, hence below `2 |E|`.
* `graphColoringDec_iff`: GRAPH COLORING accepts `x` exactly when some witness of length at
  most `15 (|x| + 1)²` passes `gcCheck`, the check on decoded bit strings.
* `graphColoringDec_mem_NP_of_isPolyTime`: membership in NP follows from polynomial-time
  computability of `gcCheck`.
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding

/-- A record `(u, v, a, b)`: an edge and the colors of its two endpoints. -/
abbrev Rec := ℕ × ℕ × ℕ × ℕ

/-- The records of an edge list and a list of color pairs. -/
def recs (es cs : List (ℕ × ℕ)) : List Rec :=
  List.zipWith (fun e c => (e.1, e.2, c.1, c.2)) es cs

/-- The conditions on one record. -/
def single (n K : ℕ) (r : Rec) : Bool :=
  decide (r.1 < n) && decide (r.2.1 < n) && decide (r.2.2.1 < K) && decide (r.2.2.2 < K) &&
    r.1 != r.2.1 && r.2.2.1 != r.2.2.2

/-- The conditions on two records at different positions. -/
def pairOk (r s : Rec) : Bool :=
  !(r.1 == s.1 && r.2.1 == s.2.1) && !(r.1 == s.2.1 && r.2.1 == s.1) &&
    (r.1 != s.1 || r.2.2.1 == s.2.2.1) && (r.1 != s.2.1 || r.2.2.1 == s.2.2.2) &&
    (r.2.1 != s.1 || r.2.2.2 == s.2.2.1) && (r.2.1 != s.2.1 || r.2.2.2 == s.2.2.2)

/-- Every record against every later record. -/
def allPairs : List Rec → Bool
  | [] => true
  | r :: rs => rs.all (pairOk r) && allPairs rs

/-- The certificate check on decoded data. -/
def ok (n K : ℕ) (es cs : List (ℕ × ℕ)) : Bool :=
  es.length == cs.length && (n == 0 || K != 0) && (recs es cs).all (single n K) &&
    allPairs (recs es cs)

/-- The certificate check on bit strings: both decode and the decoded data pass `ok`. -/
def gcCheck (x w : List Bool) : Bool :=
  match bitDecode (α := GraphColoringInstance) x, bitDecode (α := List (ℕ × ℕ)) w with
  | some (n, es, K), some cs => ok n K es cs
  | _, _ => false

/-! ### Basic facts -/

theorem pairOk_iff (r s : Rec) : pairOk r s = true ↔
    ¬ (r.1 = s.1 ∧ r.2.1 = s.2.1) ∧ ¬ (r.1 = s.2.1 ∧ r.2.1 = s.1) ∧
      (r.1 = s.1 → r.2.2.1 = s.2.2.1) ∧ (r.1 = s.2.1 → r.2.2.1 = s.2.2.2) ∧
      (r.2.1 = s.1 → r.2.2.2 = s.2.2.1) ∧ (r.2.1 = s.2.1 → r.2.2.2 = s.2.2.2) := by
  simp only [pairOk, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_true,
    bne_iff_ne, beq_iff_eq, ne_eq, beq_eq_false_iff_ne, not_and]
  constructor
  · rintro ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩
    refine ⟨fun h h' => ?_, fun h h' => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    all_goals grind
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> grind

theorem pairOk_comm (r s : Rec) : pairOk r s = pairOk s r := by
  rw [Bool.eq_iff_iff, pairOk_iff, pairOk_iff]
  grind

theorem single_iff (n K : ℕ) (r : Rec) : single n K r = true ↔
    r.1 < n ∧ r.2.1 < n ∧ r.2.2.1 < K ∧ r.2.2.2 < K ∧ r.1 ≠ r.2.1 ∧ r.2.2.1 ≠ r.2.2.2 := by
  simp only [single, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  tauto

theorem allPairs_iff (rs : List Rec) :
    allPairs rs = true ↔ rs.Pairwise fun r s => pairOk r s = true := by
  induction rs with
  | nil => simp [allPairs]
  | cons r rs ih => simp [allPairs, ih, List.all_eq_true]

theorem pairwise_forall {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, ha, b, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hne
    · exact ha' ▸ h.1 b hb'
    · exact hb' ▸ hR _ _ (h.1 a ha')
    · exact pairwise_forall hR h.2 a ha' b hb' hne

theorem pairOk_of_mem {rs : List Rec} (h : allPairs rs = true) {r s : Rec} (hr : r ∈ rs)
    (hs : s ∈ rs) (hne : r ≠ s) : pairOk r s = true :=
  pairwise_forall (fun a b hab => by rwa [pairOk_comm]) ((allPairs_iff rs).1 h) r hr s hs hne

theorem map_recs (es cs : List (ℕ × ℕ)) (h : es.length = cs.length) :
    (recs es cs).map (fun r => (r.1, r.2.1)) = es := by
  induction es generalizing cs with
  | nil => rfl
  | cons e es ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simpa [recs, List.zipWith_cons_cons] using ih cs h

theorem mem_es {es cs : List (ℕ × ℕ)} (h : es.length = cs.length) {e : ℕ × ℕ} (he : e ∈ es) :
    ∃ r ∈ recs es cs, r.1 = e.1 ∧ r.2.1 = e.2 := by
  rw [← map_recs es cs h] at he
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
  exact ⟨r, hr, rfl, rfl⟩

/-! ### Soundness -/

/-- The color of a vertex: from its first occurrence among the records, `0` if it has none. -/
def colorOf (rs : List Rec) (v : ℕ) : ℕ :=
  match rs.find? (fun r => r.1 == v || r.2.1 == v) with
  | some r => if r.1 = v then r.2.2.1 else r.2.2.2
  | none => 0

theorem colorOf_rec {n K : ℕ} {rs : List Rec} (hs : ∀ r ∈ rs, single n K r = true)
    (hp : allPairs rs = true) {r : Rec} (hr : r ∈ rs) :
    colorOf rs r.1 = r.2.2.1 ∧ colorOf rs r.2.1 = r.2.2.2 := by
  have huv := ((single_iff n K r).1 (hs r hr)).2.2.2.2.1
  constructor
  · unfold colorOf
    cases hf : rs.find? (fun r' => r'.1 == r.1 || r'.2.1 == r.1) with
    | none =>
      have := List.find?_eq_none.1 hf r hr
      simp at this
    | some r' =>
      have hr' := List.mem_of_find?_eq_some hf
      have hq := List.find?_some hf
      simp only [Bool.or_eq_true, beq_iff_eq] at hq
      by_cases he : r' = r
      · subst he
        simp
      · have hpo := (pairOk_iff r' r).1 (pairOk_of_mem hp hr' hr he)
        dsimp only
        split_ifs with h₁
        · exact hpo.2.2.1 h₁
        · exact hpo.2.2.2.2.1 (hq.resolve_left h₁)
  · unfold colorOf
    cases hf : rs.find? (fun r' => r'.1 == r.2.1 || r'.2.1 == r.2.1) with
    | none =>
      have := List.find?_eq_none.1 hf r hr
      simp at this
    | some r' =>
      have hr' := List.mem_of_find?_eq_some hf
      have hq := List.find?_some hf
      simp only [Bool.or_eq_true, beq_iff_eq] at hq
      by_cases he : r' = r
      · subst he
        simp [huv]
      · have hpo := (pairOk_iff r' r).1 (pairOk_of_mem hp hr' hr he)
        dsimp only
        split_ifs with h₁
        · exact hpo.2.2.2.1 h₁
        · exact hpo.2.2.2.2.2 (hq.resolve_left h₁)

theorem colorOf_lt {n K : ℕ} {rs : List Rec} (hs : ∀ r ∈ rs, single n K r = true)
    (hK : 0 < K) (v : ℕ) : colorOf rs v < K := by
  unfold colorOf
  cases hf : rs.find? (fun r => r.1 == v || r.2.1 == v) with
  | none => exact hK
  | some r =>
    have h := (single_iff n K r).1 (hs r (List.mem_of_find?_eq_some hf))
    dsimp only
    split_ifs
    · exact h.2.2.1
    · exact h.2.2.2.1

theorem sound {n K : ℕ} {es cs : List (ℕ × ℕ)} (h : ok n K es cs = true) :
    WellFormed (n, es, K) ∧ GraphColoringFeasible (n, es, K) := by
  simp only [ok, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hnK⟩, hs⟩, hp⟩ := h
  have hmap := map_recs es cs hlen
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← hmap]
    exact ((allPairs_iff _).1 hp).map _ fun r s hrs hEq => by
      have := (pairOk_iff r s).1 hrs
      simp only [Prod.mk.injEq] at hEq
      exact this.1 hEq
  · intro e he
    obtain ⟨r, hr, h₁, h₂⟩ := mem_es hlen he
    obtain ⟨hu, hv, -, -, huv, -⟩ := (single_iff n K r).1 (hs r hr)
    refine ⟨h₁ ▸ hu, h₂ ▸ hv, fun h' => huv (h₁.trans (h'.trans h₂.symm)), fun hrev => ?_⟩
    obtain ⟨s, hs', g₁, g₂⟩ := mem_es hlen hrev
    have hne : r ≠ s := by
      rintro rfl
      exact huv (h₁.trans g₂.symm)
    exact ((pairOk_iff r s).1 (pairOk_of_mem hp hr hs' hne)).2.1
      ⟨h₁.trans g₂.symm, h₂.trans g₁.symm⟩
  · by_cases hn : n = 0
    · subst hn
      exact ⟨SimpleGraph.Coloring.mk (fun v => absurd v.isLt (Nat.not_lt_zero _))
        fun {v} => absurd v.isLt (Nat.not_lt_zero _)⟩
    · have hK : 0 < K := Nat.pos_of_ne_zero (hnK.resolve_left hn)
      refine ⟨SimpleGraph.Coloring.mk
        (fun v => ⟨colorOf (recs es cs) v.val, colorOf_lt hs hK _⟩) ?_⟩
      intro u v huv
      change u ≠ v ∧ ((u.val, v.val) ∈ es ∨ (v.val, u.val) ∈ es) at huv
      rw [Ne, Fin.ext_iff]
      dsimp only
      rcases huv.2 with he | he
      · obtain ⟨r, hr, h₁, h₂⟩ := mem_es hlen he
        obtain ⟨c₁, c₂⟩ := colorOf_rec hs hp hr
        have h₁ : r.1 = u := h₁
        have h₂ : r.2.1 = v := h₂
        rw [← h₁, ← h₂, c₁, c₂]
        exact ((single_iff n K r).1 (hs r hr)).2.2.2.2.2
      · obtain ⟨r, hr, h₁, h₂⟩ := mem_es hlen he
        obtain ⟨c₁, c₂⟩ := colorOf_rec hs hp hr
        have h₁ : r.1 = v := h₁
        have h₂ : r.2.1 = u := h₂
        rw [← h₁, ← h₂, c₁, c₂]
        exact Ne.symm ((single_iff n K r).1 (hs r hr)).2.2.2.2.2

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

/-!
## GRAPH COLORING: completeness of the sparse certificate and the NP characterization
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding

theorem recs_map (es : List (ℕ × ℕ)) (g : ℕ × ℕ → ℕ × ℕ) :
    recs es (es.map g) = es.map fun e => (e.1, e.2, (g e).1, (g e).2) := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [recs, List.zipWith_cons_cons] using ih

theorem complete {n K : ℕ} {es : List (ℕ × ℕ)} (hw : WellFormed (n, es, K))
    (hf : GraphColoringFeasible (n, es, K)) :
    ∃ cs : List (ℕ × ℕ), ok n K es cs = true ∧ cs.length = es.length ∧
      ∀ c ∈ cs, c.1 < 2 * es.length ∧ c.2 < 2 * es.length := by
  obtain ⟨C⟩ := hf
  obtain ⟨hnd, hwf⟩ := hw
  let col0 : ℕ → ℕ := fun v => if h : v < n then (C ⟨v, h⟩ : ℕ) else 0
  let ends : List ℕ := es.flatMap fun e => [e.1, e.2]
  let S : Finset ℕ := (ends.map col0).toFinset
  let rank : ℕ → ℕ := fun c => (S.filter (· < c)).card
  have hmem₁ : ∀ e ∈ es, col0 e.1 ∈ S := fun e he => by
    simp only [S, ends, List.mem_toFinset, List.mem_map, List.mem_flatMap]
    exact ⟨e.1, ⟨e, he, by simp⟩, rfl⟩
  have hmem₂ : ∀ e ∈ es, col0 e.2 ∈ S := fun e he => by
    simp only [S, ends, List.mem_toFinset, List.mem_map, List.mem_flatMap]
    exact ⟨e.2, ⟨e, he, by simp⟩, rfl⟩
  have hSK : S ⊆ Finset.range K := by
    intro c hc
    simp only [S, ends, List.mem_toFinset, List.mem_map, List.mem_flatMap] at hc
    obtain ⟨v, ⟨e, he, hv⟩, rfl⟩ := hc
    have hb := hwf e he
    have hvn : v < n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hb.1
      · exact hb.2.1
    simp only [col0, hvn, ↓reduceDIte, Finset.mem_range]
    exact (C ⟨v, hvn⟩).isLt
  have hSm : S.card ≤ 2 * es.length := by
    refine (List.toFinset_card_le _).trans ?_
    simp [ends, List.length_flatMap, Nat.mul_comm]
  have hrank : ∀ c ∈ S, rank c < S.card := fun c hc =>
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨c, hc, lt_irrefl c⟩)
  have hmono : ∀ c ∈ S, ∀ d ∈ S, c < d → rank c < rank d := fun c hc d hd hcd => by
    refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, hy.2.trans hcd⟩
    · have := hsub (Finset.mem_filter.2 ⟨hc, hcd⟩)
      simp at this
  have hinj : ∀ c ∈ S, ∀ d ∈ S, rank c = rank d → c = d := fun c hc d hd h => by
    rcases lt_trichotomy c d with hcd | rfl | hcd
    · exact absurd h (Nat.ne_of_lt (hmono c hc d hd hcd))
    · rfl
    · exact absurd h (Nat.ne_of_gt (hmono d hd c hc hcd))
  have hcol : ∀ e ∈ es, col0 e.1 ≠ col0 e.2 := fun e he => by
    obtain ⟨hu, hv, huv, -⟩ := hwf e he
    simp only [col0, hu, hv, ↓reduceDIte, ne_eq]
    intro h
    apply C.valid (v := ⟨e.1, hu⟩) (w := ⟨e.2, hv⟩) _ (Fin.ext h)
    change (⟨e.1, hu⟩ : Fin n) ≠ ⟨e.2, hv⟩ ∧ ((e.1, e.2) ∈ es ∨ (e.2, e.1) ∈ es)
    exact ⟨fun h' => huv (congrArg Fin.val h'), Or.inl he⟩
  let g : ℕ × ℕ → ℕ × ℕ := fun e => (rank (col0 e.1), rank (col0 e.2))
  refine ⟨es.map g, ?_, by simp, ?_⟩
  · simp only [ok, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
      List.all_eq_true, recs_map, List.length_map, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases hn : n = 0
      · exact Or.inl hn
      · refine Or.inr fun hK => ?_
        have h0 : ((C ⟨0, Nat.pos_of_ne_zero hn⟩ : Fin K) : ℕ) < K :=
          (C ⟨0, Nat.pos_of_ne_zero hn⟩).isLt
        omega
    · intro r hr
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
      obtain ⟨hu, hv, huv, -⟩ := hwf e he
      rw [single_iff]
      refine ⟨hu, hv, ?_, ?_, huv, fun h => hcol e he (hinj _ (hmem₁ e he) _ (hmem₂ e he) h)⟩
      · exact lt_of_lt_of_le (hrank _ (hmem₁ e he)) ((Finset.card_le_card hSK).trans (by simp))
      · exact lt_of_lt_of_le (hrank _ (hmem₂ e he)) ((Finset.card_le_card hSK).trans (by simp))
    · rw [allPairs_iff, List.pairwise_map]
      refine hnd.imp_of_mem fun {e e'} he he' hne => ?_
      rw [pairOk_iff]
      dsimp only
      refine ⟨fun h => hne (Prod.ext h.1 h.2), fun h => ?_, fun h => by simp only [g, h],
        fun h => by simp only [g, h], fun h => by simp only [g, h], fun h => by simp only [g, h]⟩
      have := (hwf e' he').2.2.2
      apply this
      have : (e'.2, e'.1) = e := Prod.ext h.1.symm h.2.symm
      rw [this]
      exact he
  · intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact ⟨lt_of_lt_of_le (hrank _ (hmem₁ e he)) hSm, lt_of_lt_of_le (hrank _ (hmem₂ e he)) hSm⟩

theorem encoded_pairs_length (ps : List (ℕ × ℕ)) :
    (bitEncode ps).length = (ps.map fun p => 4 * p.1.size + 2 * p.2.size + 3).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (delimit (bitEncode p) ++ bitEncode ps).length = _
    rw [List.length_append, length_delimit,
      MetaMathlibExt.BinaryNatEncoding.bitEncode_pair_nat_length, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem witness_length_le (cs : List (ℕ × ℕ)) (M : ℕ) (h : ∀ c ∈ cs, c.1 < M ∧ c.2 < M) :
    (bitEncode cs).length ≤ cs.length * (6 * M + 3) := by
  rw [encoded_pairs_length]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have h₁ : c.1.size ≤ M := Nat.size_le.2 ((h c (by simp)).1.trans (Nat.lt_two_pow_self))
    have h₂ : c.2.size ≤ M := Nat.size_le.2 ((h c (by simp)).2.trans (Nat.lt_two_pow_self))
    have := ih fun d hd => h d (by simp [hd])
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- The witness bound. -/
noncomputable def witnessBound : Polynomial ℕ := Polynomial.C 15 * (Polynomial.X + 1) ^ 2

theorem eval_witnessBound (n : ℕ) : witnessBound.eval n = 15 * (n + 1) ^ 2 := by
  simp [witnessBound]

theorem graphColoringDec_iff (x : List Bool) : graphColoringDec x = true ↔
    ∃ w : List Bool, w.length ≤ witnessBound.eval x.length ∧ gcCheck x w = true := by
  rw [eval_witnessBound]
  constructor
  · intro hx
    unfold graphColoringDec at hx
    cases hd : bitDecode (α := GraphColoringInstance) x with
    | none => rw [hd] at hx; simp at hx
    | some i =>
      obtain ⟨n, es, K⟩ := i
      rw [hd] at hx
      simp only [decide_eq_true_eq] at hx
      obtain ⟨hw, hf⟩ := hx
      obtain ⟨cs, hok, hlen, hb⟩ := complete hw hf
      have hm : es.length ≤ x.length := decoded_middle_list_length_le hd
      refine ⟨bitEncode cs, ?_, ?_⟩
      · have := witness_length_le cs (2 * es.length) hb
        rw [hlen] at this
        nlinarith
      · rw [gcCheck, hd, bitDecode_bitEncode]
        exact hok
  · rintro ⟨w, -, hc⟩
    unfold gcCheck at hc
    cases hd : bitDecode (α := GraphColoringInstance) x with
    | none => rw [hd] at hc; simp at hc
    | some i =>
      obtain ⟨n, es, K⟩ := i
      cases hw : bitDecode (α := List (ℕ × ℕ)) w with
      | none => rw [hd, hw] at hc; simp at hc
      | some cs =>
        rw [hd, hw] at hc
        unfold graphColoringDec
        rw [hd]
        simp only [decide_eq_true_eq]
        exact sound hc

theorem graphColoringDec_mem_NP_of_isPolyTime
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun q : List Bool × List Bool =>
      gcCheck q.1 q.2) :
    graphColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  ⟨witnessBound, fun q => gcCheck q.1 q.2, h, fun x => graphColoringDec_iff x⟩

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

/-!
## Bit-stack primitives for the GRAPH COLORING verifier

Statements on machines whose stacks all hold `Bool` and whose state is a `Bool`, each with a
bounded run:

* `moveAll`: move a whole stack onto another, reversed (`BitOps.moveB` with every symbol a bit).
* `mvBlk`: move one framed block `delimit q` symbol by symbol onto another stack.
* `eqHB`: compare a raw stack `p` with the payload `q` of the framed block on top of another
  stack, moving what it reads onto two scratch stacks.
* `eqRaw`: compare two raw stacks, moving what it reads onto two scratch stacks.
* `ltRaw`: least-significant-bit-first comparison `ltSer` of two raw stacks, with the running
  answer kept in the label.

The comparisons keep `reverse (scratch) ++ stack` fixed (`Keeps`), so moving the scratch stacks
back restores the compared stacks.
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

variable {K Λ : Type} [DecidableEq K] {M : Λ → TM2.Stmt (fun _ : K => Bool) Λ Bool}

/-- Stack contents of an all-`Bool` machine. -/
abbrev Stk (K : Type) := ∀ _ : K, List Bool

/-! ### Moving a whole stack -/

/-- Move all of stack `a` onto stack `b`, reversed. -/
abbrev moveAll (a b : K) (self next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ Bool :=
  moveB a b (fun x => some x) id self next

theorem moveAll_run {self next : Λ} {a b : K} (hp : M self = moveAll a b self next)
    (hab : a ≠ b) (v : Bool) (S : Stk K) :
    ∃ v', Run M ((S a).length + 1) ⟨some self, v, S⟩
      ⟨some next, v', update (update S a []) b ((S a).reverse ++ S b)⟩ := by
  obtain ⟨v', S', hr, ha, hb, hk⟩ := moveB_run (M := M) hp hab (S a) (S a) [] v S
    (by simp) (by simp [IsBitBlock]) rfl
  refine ⟨v', ?_⟩
  have : S' = update (update S a []) b ((S a).reverse ++ S b) := by
    funext k
    by_cases hkb : k = b
    · subst hkb; simpa using hb
    · by_cases hka : k = a
      · subst hka; simp [ha, hkb]
      · simp [hk k hka hkb, hka, hkb]
  exact this ▸ hr

/-! ### Moving one framed block -/

/-- Move the framed block on top of `a` onto `b`, symbol by symbol. -/
def mvBlk (a b : K) (self next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ Bool :=
  .pop a (fun _ o => o.getD false) <| .push b id <| .branch id
    (.pop a (fun _ o => o.getD false) <| .push b id <| .goto fun _ => self)
    (.goto fun _ => next)

theorem mvBlk_run {self next : Λ} {a b : K} (hp : M self = mvBlk a b self next) (hab : a ≠ b) :
    ∀ (q rest : List Bool) (v : Bool) (S : Stk K), S a = delimit q ++ rest →
      ∃ v', Run M (q.length + 1) ⟨some self, v, S⟩
        ⟨some next, v', update (update S a rest) b ((delimit q).reverse ++ S b)⟩ := by
  intro q
  induction q with
  | nil =>
    intro rest v S hS
    refine ⟨false, Run.single ?_⟩
    simp [hp, mvBlk, TM2.stepAux, hS, delimit, hab.symm]
  | cons c q ih =>
    intro rest v S hS
    let S₁ := update (update S a (delimit q ++ rest)) b (c :: true :: S b)
    obtain ⟨v', hr⟩ := ih rest c S₁ (by simp [S₁, hab])
    have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, c, S₁⟩ := by
      have : TM2.stepAux (M self) v S = ⟨some self, c, S₁⟩ := by
        simp only [hp, mvBlk, TM2.stepAux, hS, delimit, List.cons_append, update_of_ne hab,
          update_self, List.head?_cons, Option.getD_some, List.tail_cons, Bool.cond_true, S₁,
          TM2.Cfg.mk.injEq, true_and, id]
        funext k
        simp only [update_apply]
        split_ifs <;> simp_all
      simp [TM2.step, this]
    have heq : update (update S₁ a rest) b ((delimit q).reverse ++ S₁ b) =
        update (update S a rest) b ((delimit (c :: q)).reverse ++ S b) := by
      funext k
      by_cases hkb : k = b
      · subst hkb; simp [S₁, delimit]
      · by_cases hka : k = a
        · subst hka; simp [S₁, hkb]
        · simp [S₁, hka, hkb]
    exact ⟨v', heq ▸ (Run.head hstep hr).of_eq (by simp)⟩

/-! ### Comparisons with restorable scratch -/

/-- What a comparison has moved from `a` lies, reversed, on `ta`. -/
def Keeps (a ta : K) (S S' : Stk K) : Prop := (S' ta).reverse ++ S' a = (S ta).reverse ++ S a

omit [DecidableEq K] in
theorem Keeps.refl (a ta : K) (S : Stk K) : Keeps a ta S S := rfl

omit [DecidableEq K] in
theorem Keeps.trans {a ta : K} {S₁ S₂ S₃ : Stk K} (h₁ : Keeps a ta S₁ S₂)
    (h₂ : Keeps a ta S₂ S₃) : Keeps a ta S₁ S₃ := Eq.trans h₂ h₁

/-- Compare the raw stack `h` with the payload of the framed block on top of `u`. -/
def eqHB (h u sh su : K) (self eqL neL : Λ) : TM2.Stmt (fun _ : K => Bool) Λ Bool :=
  .peek u (fun _ o => o.isSome) <| .branch id
    (.pop u (fun _ o => o.getD false) <| .push su id <| .branch id
      (.pop u (fun _ o => o.getD false) <| .push su id <| .branch id
        (.peek h (fun _ o => o == some true) <| .branch id
          (.pop h (fun _ o => o.getD false) <| .push sh id <| .goto fun _ => self)
          (.goto fun _ => neL))
        (.peek h (fun _ o => o == some false) <| .branch id
          (.pop h (fun _ o => o.getD false) <| .push sh id <| .goto fun _ => self)
          (.goto fun _ => neL)))
      (.peek h (fun _ o => o.isSome) <| .branch id (.goto fun _ => neL) (.goto fun _ => eqL)))
    (.goto fun _ => neL)

/-- The conclusion of a comparison run on stacks `a`, `b` with scratch `ta`, `tb`. -/
def CmpOut (a b ta tb : K) (B : ℕ) (S S' : Stk K) : Prop :=
  Keeps a ta S S' ∧ Keeps b tb S S' ∧ (∀ k, k ≠ a → k ≠ b → k ≠ ta → k ≠ tb → S' k = S k) ∧
    (S' ta).length + (S' tb).length ≤ (S ta).length + (S tb).length + B

omit [DecidableEq K] in
theorem CmpOut.refl (a b ta tb : K) (B : ℕ) (S : Stk K) : CmpOut a b ta tb B S S :=
  ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by omega⟩

/-- `simp` with the pairwise distinctness `d₁ … d₆` of the four stacks of a comparison. -/
syntax "dsimp6" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| dsimp6 [$ts,*]) => `(tactic| simp [update_apply, d₁, d₂, d₃, d₄, d₅, d₆,
      d₁.symm, d₂.symm, d₃.symm, d₄.symm, d₅.symm, d₆.symm, $ts,*])

theorem eqHB_run {self eqL neL : Λ} {h u sh su : K} (hp : M self = eqHB h u sh su self eqL neL)
    (hd : Distinct4 h u sh su) :
    ∀ (q p rest : List Bool) (v : Bool) (S : Stk K), S u = delimit q ++ rest → S h = p →
      ∃ v' S', RunLe M (q.length + 1) ⟨some self, v, S⟩
        ⟨some (if p = q then eqL else neL), v', S'⟩ ∧
        CmpOut h u sh su (3 * q.length + 2) S S' := by
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hd
  intro q
  induction q with
  | nil =>
    intro p rest v S hu hh
    have hS : TM2.stepAux (M self) v S = ⟨some (if p = [] then eqL else neL), p ≠ [],
        fun k => if k = su then false :: S su else if k = u then rest else S k⟩ := by
      cases p
      all_goals
        dsimp6 [hp, eqHB, TM2.stepAux, hu, delimit, hh]
        funext k; dsimp6 []
    refine ⟨_, _, ⟨1, le_rfl, Run.single hS⟩, ?_, ?_, ?_, ?_⟩
    · dsimp6 [Keeps]
    · dsimp6 [Keeps, hu, delimit]
    · intro k k₁ k₂ k₃ k₄; dsimp6 [k₁, k₂, k₃, k₄]
    · dsimp6 []; omega
  | cons c q ih =>
    intro p rest v S hu hh
    have hmis : (S h).head? ≠ some c →
        ∃ v' S', RunLe M ((c :: q).length + 1) ⟨some self, v, S⟩ ⟨some neL, v', S'⟩ ∧
          CmpOut h u sh su (3 * (c :: q).length + 2) S S' := by
      intro hc
      have hc' : ((S h).head? == some c) = false := by simpa using hc
      have hS : TM2.stepAux (M self) v S = ⟨some neL, false,
          fun k => if k = su then c :: true :: S su else if k = u then delimit q ++ rest
            else S k⟩ := by
        cases c
        all_goals
          dsimp6 [hp, eqHB, TM2.stepAux, hu, delimit, hc']
          funext k; dsimp6 []; split_ifs <;> simp_all
      refine ⟨_, _, ⟨1, by simp, Run.single hS⟩, ?_, ?_, ?_, ?_⟩
      · dsimp6 [Keeps]
      · dsimp6 [Keeps, hu, delimit]
      · intro k k₁ k₂ k₃ k₄; dsimp6 [k₁, k₂, k₃, k₄]
      · dsimp6 []; omega
    rcases p with _ | ⟨b, p⟩
    · obtain ⟨v', S', hr, ho⟩ := hmis (by simp [hh])
      exact ⟨v', S', by simpa using hr, ho⟩
    · by_cases hbc : b = c
      · subst hbc
        let S₁ : Stk K := fun k => if k = sh then b :: S sh else if k = h then p else
          if k = su then b :: true :: S su else if k = u then delimit q ++ rest else S k
        obtain ⟨v', S', hr, ho⟩ := ih p rest b S₁ (by dsimp6 [S₁]) (by dsimp6 [S₁])
        have hS : TM2.stepAux (M self) v S = ⟨some self, b, S₁⟩ := by
          cases b
          all_goals
            dsimp6 [hp, eqHB, TM2.stepAux, hu, hh, delimit]
            funext k; dsimp6 [S₁]; split_ifs <;> simp_all
        have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, b, S₁⟩ := by
          simp [TM2.step, hS]
        have hif : (if b :: p = b :: q then eqL else neL) = (if p = q then eqL else neL) := by
          simp
        rw [hif]
        refine ⟨v', S', (RunLe.trans ⟨1, le_rfl, Run.head hstep (Run.zero _)⟩ hr).mono
          (by simp only [List.length_cons]; omega), ?_⟩
        obtain ⟨k₁, k₂, k₃, k₄⟩ := ho
        refine ⟨?_, ?_, ?_, ?_⟩
        · refine Eq.trans k₁ ?_
          dsimp6 [Keeps, S₁, hh]
        · refine Eq.trans k₂ ?_
          dsimp6 [Keeps, S₁, hu, delimit]
        · intro k j₁ j₂ j₃ j₄
          rw [k₃ k j₁ j₂ j₃ j₄]
          dsimp6 [S₁, j₁, j₂, j₃, j₄]
        · have : (S₁ sh).length + (S₁ su).length = (S sh).length + (S su).length + 3 := by
            dsimp6 [S₁]
            omega
          simp only [List.length_cons] at *
          omega
      · obtain ⟨v', S', hr, ho⟩ := hmis (by simp [hh, hbc])
        refine ⟨v', S', ?_, ho⟩
        have : (b :: p = c :: q) = False := by simp [hbc]
        simpa [this] using hr

/-- Compare two raw stacks. -/
def eqRaw (a b sa sb : K) (self eqL neL : Λ) : TM2.Stmt (fun _ : K => Bool) Λ Bool :=
  .peek a (fun _ o => o.isSome) <| .branch id
    (.pop a (fun _ o => o.getD false) <| .push sa id <| .branch id
      (.peek b (fun _ o => o == some true) <| .branch id
        (.pop b (fun _ o => o.getD false) <| .push sb id <| .goto fun _ => self)
        (.goto fun _ => neL))
      (.peek b (fun _ o => o == some false) <| .branch id
        (.pop b (fun _ o => o.getD false) <| .push sb id <| .goto fun _ => self)
        (.goto fun _ => neL)))
    (.peek b (fun _ o => o.isSome) <| .branch id (.goto fun _ => neL) (.goto fun _ => eqL))

theorem eqRaw_run {self eqL neL : Λ} {h u sh su : K} (hp : M self = eqRaw h u sh su self eqL neL)
    (hd : Distinct4 h u sh su) :
    ∀ (p q : List Bool) (v : Bool) (S : Stk K), S h = p → S u = q →
      ∃ v' S', RunLe M (p.length + 1) ⟨some self, v, S⟩
        ⟨some (if p = q then eqL else neL), v', S'⟩ ∧
        CmpOut h u sh su (2 * p.length + 2) S S' := by
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hd
  intro p
  induction p with
  | nil =>
    intro q v S hh hu
    have hS : TM2.stepAux (M self) v S = ⟨some (if [] = q then eqL else neL), q ≠ [], S⟩ := by
      cases q <;> dsimp6 [hp, eqRaw, TM2.stepAux, hu, hh]
    exact ⟨_, _, ⟨1, le_rfl, Run.single hS⟩, CmpOut.refl _ _ _ _ _ _⟩
  | cons c p ih =>
    intro q v S hh hu
    have hmis : (S u).head? ≠ some c →
        ∃ v' S', RunLe M ((c :: p).length + 1) ⟨some self, v, S⟩ ⟨some neL, v', S'⟩ ∧
          CmpOut h u sh su (2 * (c :: p).length + 2) S S' := by
      intro hc
      have hc' : ((S u).head? == some c) = false := by simpa using hc
      have hS : TM2.stepAux (M self) v S = ⟨some neL, false,
          fun k => if k = sh then c :: S sh else if k = h then p else S k⟩ := by
        cases c
        all_goals
          dsimp6 [hp, eqRaw, TM2.stepAux, hh, hc']
        all_goals (funext k; dsimp6 [])
      refine ⟨_, _, ⟨1, by simp, Run.single hS⟩, ?_, ?_, ?_, ?_⟩
      · dsimp6 [Keeps, hh]
      · dsimp6 [Keeps]
      · intro k k₁ k₂ k₃ k₄; dsimp6 [k₁, k₂, k₃, k₄]
      · dsimp6 []; omega
    rcases q with _ | ⟨b, q⟩
    · obtain ⟨v', S', hr, ho⟩ := hmis (by simp [hu])
      exact ⟨v', S', by simpa using hr, ho⟩
    · by_cases hbc : b = c
      · subst hbc
        let S₁ : Stk K := fun k => if k = su then b :: S su else if k = u then q else
          if k = sh then b :: S sh else if k = h then p else S k
        obtain ⟨v', S', hr, ho⟩ := ih q b S₁ (by dsimp6 [S₁]) (by dsimp6 [S₁])
        have hS : TM2.stepAux (M self) v S = ⟨some self, b, S₁⟩ := by
          cases b
          all_goals
            dsimp6 [hp, eqRaw, TM2.stepAux, hu, hh]
          all_goals (funext k; dsimp6 [S₁])
        have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, b, S₁⟩ := by
          simp [TM2.step, hS]
        have hif : (if b :: p = b :: q then eqL else neL) = (if p = q then eqL else neL) := by
          simp
        rw [hif]
        refine ⟨v', S', (RunLe.trans ⟨1, le_rfl, Run.head hstep (Run.zero _)⟩ hr).mono
          (by simp only [List.length_cons]; omega), ?_⟩
        obtain ⟨k₁, k₂, k₃, k₄⟩ := ho
        refine ⟨?_, ?_, ?_, ?_⟩
        · refine Eq.trans k₁ ?_
          dsimp6 [Keeps, S₁, hh]
        · refine Eq.trans k₂ ?_
          dsimp6 [Keeps, S₁, hu]
        · intro k j₁ j₂ j₃ j₄
          rw [k₃ k j₁ j₂ j₃ j₄]
          dsimp6 [S₁, j₁, j₂, j₃, j₄]
        · have : (S₁ sh).length + (S₁ su).length = (S sh).length + (S su).length + 2 := by
            dsimp6 [S₁]
            omega
          simp only [List.length_cons] at *
          omega
      · obtain ⟨v', S', hr, ho⟩ := hmis (by simp [hu, hbc])
        refine ⟨v', S', ?_, ho⟩
        have : (c :: p = b :: q) = False := by simp [Ne.symm hbc]
        simpa [this] using hr

/-- Least-significant-bit-first comparison: `ltSer f p q` reads `p` and `q` from their first
bits, keeping in `f` whether the part read so far of `p` is below that of `q`. -/
def ltSer : Bool → List Bool → List Bool → Bool
  | f, [], [] => f
  | _, [], _ :: _ => true
  | _, _ :: _, [] => false
  | f, x :: xs, y :: ys => ltSer (if x = y then f else y) xs ys

/-- One round of the serial comparison, with the running answer `f` in the label. -/
def ltRaw (a b sa sb : K) (self : Bool → Λ) (done : Bool → Λ) (f : Bool) :
    TM2.Stmt (fun _ : K => Bool) Λ Bool :=
  .peek a (fun _ o => o.isSome) <| .branch id
    (.peek b (fun _ o => o.isSome) <| .branch id
      (.pop a (fun _ o => o.getD false) <| .push sa id <| .branch id
        (.pop b (fun _ o => o.getD false) <| .push sb id <| .branch id
          (.goto fun _ => self f) (.goto fun _ => self false))
        (.pop b (fun _ o => o.getD false) <| .push sb id <| .branch id
          (.goto fun _ => self true) (.goto fun _ => self f)))
      (.goto fun _ => done false))
    (.peek b (fun _ o => o.isSome) <| .branch id (.goto fun _ => done true)
      (.goto fun _ => done f))

theorem ltRaw_run {self done : Bool → Λ} {h u sh su : K}
    (hp : ∀ f, M (self f) = ltRaw h u sh su self done f) (hd : Distinct4 h u sh su) :
    ∀ (p q : List Bool) (f v : Bool) (S : Stk K), S h = p → S u = q →
      ∃ v' S', RunLe M (p.length + 1) ⟨some (self f), v, S⟩
        ⟨some (done (ltSer f p q)), v', S'⟩ ∧
        CmpOut h u sh su (2 * p.length + 2) S S' := by
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hd
  intro p
  induction p with
  | nil =>
    intro q f v S hh hu
    have hS : TM2.stepAux (M (self f)) v S = ⟨some (done (ltSer f [] q)), q ≠ [], S⟩ := by
      cases q <;> dsimp6 [hp, ltRaw, TM2.stepAux, hu, hh, ltSer]
    exact ⟨_, _, ⟨1, le_rfl, Run.single hS⟩, CmpOut.refl _ _ _ _ _ _⟩
  | cons c p ih =>
    intro q f v S hh hu
    rcases q with _ | ⟨b, q⟩
    · have hS : TM2.stepAux (M (self f)) v S = ⟨some (done (ltSer f (c :: p) [])), false, S⟩ := by
        dsimp6 [hp, ltRaw, TM2.stepAux, hu, hh, ltSer]
      exact ⟨_, _, ⟨1, by simp, Run.single hS⟩, CmpOut.refl _ _ _ _ _ _⟩
    · let S₁ : Stk K := fun k => if k = su then b :: S su else if k = u then q else
          if k = sh then c :: S sh else if k = h then p else S k
      obtain ⟨v', S', hr, ho⟩ := ih q (if c = b then f else b) b S₁ (by dsimp6 [S₁])
        (by dsimp6 [S₁])
      have hS : TM2.stepAux (M (self f)) v S = ⟨some (self (if c = b then f else b)), b, S₁⟩ := by
        cases b <;> cases c
        all_goals
          dsimp6 [hp, ltRaw, TM2.stepAux, hu, hh]
        all_goals (funext k; dsimp6 [S₁])
      have hstep : TM2.step M ⟨some (self f), v, S⟩ =
          some ⟨some (self (if c = b then f else b)), b, S₁⟩ := by
        simp [TM2.step, hS]
      have hl : ltSer f (c :: p) (b :: q) = ltSer (if c = b then f else b) p q := rfl
      rw [hl]
      refine ⟨v', S', (RunLe.trans ⟨1, le_rfl, Run.head hstep (Run.zero _)⟩ hr).mono
        (by simp only [List.length_cons]; omega), ?_⟩
      obtain ⟨k₁, k₂, k₃, k₄⟩ := ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine Eq.trans k₁ ?_
        dsimp6 [Keeps, S₁, hh]
      · refine Eq.trans k₂ ?_
        dsimp6 [Keeps, S₁, hu]
      · intro k j₁ j₂ j₃ j₄
        rw [k₃ k j₁ j₂ j₃ j₄]
        dsimp6 [S₁, j₁, j₂, j₃, j₄]
      · have : (S₁ sh).length + (S₁ su).length = (S sh).length + (S su).length + 2 := by
          dsimp6 [S₁]
          omega
        simp only [List.length_cons] at *
        omega

/-- Moving the two scratch stacks back after a comparison restores the stacks. -/
theorem restore_run {r₁ r₂ next : Λ} {a b ta tb : K} (h₁ : M r₁ = moveAll ta a r₁ r₂)
    (h₂ : M r₂ = moveAll tb b r₂ next) (hd : Distinct4 a b ta tb) {B : ℕ} {S S' : Stk K}
    (ho : CmpOut a b ta tb B S S') (ha : S ta = []) (hb : S tb = []) (v : Bool) :
    ∃ v', RunLe M (B + 2) ⟨some r₁, v, S'⟩ ⟨some next, v', S⟩ := by
  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ := hd
  obtain ⟨k₁, k₂, k₃, k₄⟩ := ho
  obtain ⟨v₁, hr₁⟩ := moveAll_run h₁ d₂.symm v S'
  obtain ⟨v₂, hr₂⟩ :=
    moveAll_run h₂ d₅.symm v₁ (update (update S' ta []) a ((S' ta).reverse ++ S' a))
  have heq : update (update (update (update S' ta []) a ((S' ta).reverse ++ S' a)) tb []) b
      ((update (update S' ta []) a ((S' ta).reverse ++ S' a) tb).reverse ++
        update (update S' ta []) a ((S' ta).reverse ++ S' a) b) = S := by
    funext k
    unfold Keeps at k₁ k₂
    rw [ha] at k₁
    rw [hb] at k₂
    simp only [List.reverse_nil, List.nil_append] at k₁ k₂
    by_cases hk₁ : k = b
    · subst hk₁; dsimp6 [k₂]
    · by_cases hk₂ : k = tb
      · subst hk₂; dsimp6 [hb]
      · by_cases hk₃ : k = a
        · subst hk₃; dsimp6 [k₁]
        · by_cases hk₄ : k = ta
          · subst hk₄; dsimp6 [ha]
          · dsimp6 [hk₁, hk₂, hk₃, hk₄, k₃ k hk₃ hk₁ hk₄ hk₂]
  refine ⟨v₂, heq ▸ ((hr₁.trans hr₂).le le_rfl).mono ?_⟩
  dsimp6 []
  rw [ha, hb] at k₄
  simp at k₄
  omega

/-! ### Comparisons as tests -/

theorem ltSer_encodeNat (f : Bool) (a b : ℕ) :
    ltSer f (Computability.encodeNat a) (Computability.encodeNat b) =
      decide (a < b ∨ (a = b ∧ f = true)) := by
  induction a using Nat.strong_induction_on generalizing b f with
  | _ a ih =>
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb; cases f <;> rfl
      · rw [TM2Recursive.encodeNat_zero, TM2Recursive.encodeNat_eq_cons hb]
        simp [ltSer]; omega
    · by_cases hb : b = 0
      · subst hb
        rw [TM2Recursive.encodeNat_zero, TM2Recursive.encodeNat_eq_cons ha]
        simp [ltSer, ha]
      · rw [TM2Recursive.encodeNat_eq_cons ha, TM2Recursive.encodeNat_eq_cons hb]
        simp only [ltSer]
        rw [ih (a / 2) (by omega)]
        rw [decide_eq_decide]
        rcases Nat.mod_two_eq_zero_or_one a with h₁ | h₁ <;>
          rcases Nat.mod_two_eq_zero_or_one b with h₂ | h₂ <;> cases f <;> simp [h₁, h₂] <;>
          omega

theorem ltSer_false_encodeNat (a b : ℕ) :
    ltSer false (Computability.encodeNat a) (Computability.encodeNat b) = decide (a < b) := by
  rw [ltSer_encodeNat]; simp

theorem encodeNat_inj {a b : ℕ} : Computability.encodeNat a = Computability.encodeNat b ↔ a = b :=
  ⟨fun h => by simpa using congrArg Computability.decodeNat h, fun h => h ▸ rfl⟩

theorem ite_label {α : Type} (c : Prop) [Decidable c] (f : Bool → α) :
    (if c then f true else f false) = f (decide c) := by
  by_cases h : c <;> simp [h]

theorem eqHB_test {self : Λ} {r₁ r₂ out : Bool → Λ} {h u sh su : K}
    (hp : M self = eqHB h u sh su self (r₁ true) (r₁ false))
    (h₁ : ∀ o, M (r₁ o) = moveAll sh h (r₁ o) (r₂ o))
    (h₂ : ∀ o, M (r₂ o) = moveAll su u (r₂ o) (out o)) (hd : Distinct4 h u sh su)
    {q p rest : List Bool} {S : Stk K} (hu : S u = delimit q ++ rest) (hh : S h = p)
    (hsh : S sh = []) (hsu : S su = []) (v : Bool) :
    ∃ v', RunLe M (4 * q.length + 5) ⟨some self, v, S⟩ ⟨some (out (decide (p = q))), v', S⟩ := by
  obtain ⟨v₁, S₁, hr, ho⟩ := eqHB_run hp hd q p rest v S hu hh
  rw [ite_label (p = q) r₁] at hr
  obtain ⟨v₂, hr₂⟩ := restore_run (h₁ _) (h₂ _) hd ho hsh hsu v₁
  exact ⟨v₂, (hr.trans hr₂).mono (by omega)⟩

theorem eqRaw_test {self : Λ} {r₁ r₂ out : Bool → Λ} {h u sh su : K}
    (hp : M self = eqRaw h u sh su self (r₁ true) (r₁ false))
    (h₁ : ∀ o, M (r₁ o) = moveAll sh h (r₁ o) (r₂ o))
    (h₂ : ∀ o, M (r₂ o) = moveAll su u (r₂ o) (out o)) (hd : Distinct4 h u sh su)
    {p q : List Bool} {S : Stk K} (hh : S h = p) (hu : S u = q)
    (hsh : S sh = []) (hsu : S su = []) (v : Bool) :
    ∃ v', RunLe M (3 * p.length + 5) ⟨some self, v, S⟩ ⟨some (out (decide (p = q))), v', S⟩ := by
  obtain ⟨v₁, S₁, hr, ho⟩ := eqRaw_run hp hd p q v S hh hu
  rw [ite_label (p = q) r₁] at hr
  obtain ⟨v₂, hr₂⟩ := restore_run (h₁ _) (h₂ _) hd ho hsh hsu v₁
  exact ⟨v₂, (hr.trans hr₂).mono (by omega)⟩

theorem ltRaw_test {self r₁ r₂ out : Bool → Λ} {h u sh su : K}
    (hp : ∀ f, M (self f) = ltRaw h u sh su self r₁ f)
    (h₁ : ∀ o, M (r₁ o) = moveAll sh h (r₁ o) (r₂ o))
    (h₂ : ∀ o, M (r₂ o) = moveAll su u (r₂ o) (out o)) (hd : Distinct4 h u sh su)
    {p q : List Bool} {S : Stk K} (hh : S h = p) (hu : S u = q)
    (hsh : S sh = []) (hsu : S su = []) (v : Bool) :
    ∃ v', RunLe M (3 * p.length + 5) ⟨some (self false), v, S⟩
      ⟨some (out (ltSer false p q)), v', S⟩ := by
  obtain ⟨v₁, S₁, hr, ho⟩ := ltRaw_run hp hd p q false v S hh hu
  obtain ⟨v₂, hr₂⟩ := restore_run (h₁ _) (h₂ _) hd ho hsh hsu v₁
  exact ⟨v₂, (hr.trans hr₂).mono (by omega)⟩

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

/-!
## The check phase of the GRAPH COLORING verifier

A component on seventeen `Bool` stacks. It starts with the canonical encodings `N` of `n` and
`Kc` of `K`, and the canonical list encodings `U`, `V`, `A`, `B` of the first endpoints, second
endpoints, first colors and second colors. It checks `n = 0 ∨ K ≠ 0`, then repeatedly takes the
top record off `U, V, A, B` into the holding stacks `HU, HV, HA, HB`, tests it alone
(`single`) and against every later record (`pairOk`), moving the later records onto the
temporary stacks `TU, TV, TA, TB` and back. The comparisons use the scratch stacks `S1`, `S2`.
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

/-- The stacks. -/
inductive K | N | Kc | U | V | A | B | HU | HV | HA | HB | TU | TV | TA | TB | S1 | S2 | Z
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.N, .Kc, .U, .V, .A, .B, .HU, .HV, .HA, .HB, .TU, .TV, .TA, .TB, .S1, .S2, .Z],
    by decide⟩
  complete k := by cases k <;> decide

/-- The four fields of a record. -/
inductive F | u | v | a | b
  deriving DecidableEq

instance : Fintype F where
  elems := ⟨↑[F.u, .v, .a, .b], by decide⟩
  complete k := by cases k <;> decide

/-- The input stack of a field. -/
def src : F → K | .u => .U | .v => .V | .a => .A | .b => .B
/-- The holding stack of a field. -/
def hold : F → K | .u => .HU | .v => .HV | .a => .HA | .b => .HB
/-- The temporary stack of a field. -/
def tmp : F → K | .u => .TU | .v => .TV | .a => .TA | .b => .TB

/-- The test sites. -/
inductive Site | lu | lv | la | lb | nuv | nab
  | e1 | e2 | aa | e2' | bb | e3 | e4 | ab | e4' | ba
  deriving DecidableEq

instance : Fintype Site where
  elems := ⟨↑[Site.lu, .lv, .la, .lb, .nuv, .nab, .e1, .e2, .aa, .e2', .bb, .e3, .e4, .ab, .e4',
    .ba], by decide⟩
  complete k := by cases k <;> decide

/-- The labels of one test: the comparison loop (with the running answer of a serial
comparison) and the two restoring moves, with the outcome. -/
inductive TL | loop (f : Bool) | r1 (o : Bool) | r2 (o : Bool)
  deriving DecidableEq

instance : Fintype TL where
  elems := ⟨↑[TL.loop false, .loop true, .r1 false, .r1 true, .r2 false, .r2 true], by decide⟩
  complete k := by rcases k with (_ | _) | (_ | _) | (_ | _) <;> decide

/-- The labels. -/
inductive Lab | start | zK | oh | oh2 | oh3 | cp (i : F) | cq (i : F) | t (s : Site) (l : TL)
  | ih | ih2 | mv (i : F) | rs (i : F) | cl (i : F) | yes | no
  deriving DecidableEq

/-- Every label is named by a small sum type. -/
def labOf : (Fin 9 ⊕ F ⊕ F ⊕ (Site × TL) ⊕ F ⊕ F ⊕ F) → Lab
  | .inl i => match i with
    | 0 => .start | 1 => .zK | 2 => .oh | 3 => .oh2 | 4 => .oh3 | 5 => .ih | 6 => .ih2
    | 7 => .yes | _ => .no
  | .inr (.inl i) => .cp i
  | .inr (.inr (.inl i)) => .cq i
  | .inr (.inr (.inr (.inl p))) => .t p.1 p.2
  | .inr (.inr (.inr (.inr (.inl i)))) => .mv i
  | .inr (.inr (.inr (.inr (.inr (.inl i))))) => .rs i
  | .inr (.inr (.inr (.inr (.inr (.inr i))))) => .cl i

instance : Fintype Lab :=
  Fintype.ofSurjective labOf fun l => by
    cases l with
    | start => exact ⟨.inl 0, rfl⟩
    | zK => exact ⟨.inl 1, rfl⟩
    | oh => exact ⟨.inl 2, rfl⟩
    | oh2 => exact ⟨.inl 3, rfl⟩
    | oh3 => exact ⟨.inl 4, rfl⟩
    | ih => exact ⟨.inl 5, rfl⟩
    | ih2 => exact ⟨.inl 6, rfl⟩
    | yes => exact ⟨.inl 7, rfl⟩
    | no => exact ⟨.inl 8, rfl⟩
    | cp i => exact ⟨.inr (.inl i), rfl⟩
    | cq i => exact ⟨.inr (.inr (.inl i)), rfl⟩
    | t s l => exact ⟨.inr (.inr (.inr (.inl (s, l)))), rfl⟩
    | mv i => exact ⟨.inr (.inr (.inr (.inr (.inl i)))), rfl⟩
    | rs i => exact ⟨.inr (.inr (.inr (.inr (.inr (.inl i))))), rfl⟩
    | cl i => exact ⟨.inr (.inr (.inr (.inr (.inr (.inr i))))), rfl⟩

/-- The kind of comparison at a site. -/
inductive Kind | lt | raw | hb

/-- The kind of a site. -/
def Site.kind : Site → Kind
  | .lu | .lv | .la | .lb => .lt
  | .nuv | .nab => .raw
  | _ => .hb

/-- The first compared stack of a site (a holding stack). -/
def Site.h : Site → K
  | .lu | .nuv | .e1 | .e3 => .HU
  | .lv | .e2 | .e2' | .e4 | .e4' => .HV
  | .la | .nab | .aa | .ab => .HA
  | .lb | .bb | .ba => .HB

/-- The second compared stack of a site. -/
def Site.x : Site → K
  | .lu | .lv => .N
  | .la | .lb => .Kc
  | .nuv => .HV
  | .nab => .HB
  | .e1 | .e4 | .e4' => .U
  | .e2 | .e2' | .e3 => .V
  | .aa | .ba => .A
  | .bb | .ab => .B

/-- Where a test continues with outcome `o`. -/
def Site.out : Site → Bool → Lab
  | .lu, o => if o then .t .lv (.loop false) else .no
  | .lv, o => if o then .t .la (.loop false) else .no
  | .la, o => if o then .t .lb (.loop false) else .no
  | .lb, o => if o then .t .nuv (.loop false) else .no
  | .nuv, o => if o then .no else .t .nab (.loop false)
  | .nab, o => if o then .no else .ih
  | .e1, o => if o then .t .e2 (.loop false) else .t .e2' (.loop false)
  | .e2, o => if o then .no else .t .aa (.loop false)
  | .aa, o => if o then .t .e2' (.loop false) else .no
  | .e2', o => if o then .t .bb (.loop false) else .t .e3 (.loop false)
  | .bb, o => if o then .t .e3 (.loop false) else .no
  | .e3, o => if o then .t .e4 (.loop false) else .t .e4' (.loop false)
  | .e4, o => if o then .no else .t .ab (.loop false)
  | .ab, o => if o then .t .e4' (.loop false) else .no
  | .e4', o => if o then .t .ba (.loop false) else .mv .u
  | .ba, o => if o then .mv .u else .no

/-- The field after a field. -/
def F.next : F → Option F | .u => some .v | .v => some .a | .a => some .b | .b => none

/-- Peek at a stack: go to `ne` if it has a symbol, to `em` if it is empty. -/
def peekS (k : K) (ne em : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .peek k (fun _ o => o.isSome) <| .branch id (.goto fun _ => ne) (.goto fun _ => em)

/-- The program. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .start => peekS .N .zK .oh
  | .zK => peekS .Kc .oh .no
  | .oh => peekS .U .oh3 .oh2
  | .oh2 => peekS .A .no .yes
  | .oh3 => peekS .A (.cp .u) .no
  | .cp i => Cslib.Complexity.FramedCNF.Block.read (src i) .S1 (fun x => some x) id (.cp i)
      (.cq i) .no
  | .cq i => moveAll .S1 (hold i) (.cq i) (match i.next with
      | some j => .cp j
      | none => .t .lu (.loop false))
  | .t s (.loop f) => match s.kind with
      | .lt => ltRaw s.h s.x .S1 .S2 (fun f => .t s (.loop f)) (fun o => .t s (.r1 o)) f
      | .raw => eqRaw s.h s.x .S1 .S2 (.t s (.loop false)) (.t s (.r1 true)) (.t s (.r1 false))
      | .hb => eqHB s.h s.x .S1 .S2 (.t s (.loop false)) (.t s (.r1 true)) (.t s (.r1 false))
  | .t s (.r1 o) => moveAll .S1 s.h (.t s (.r1 o)) (.t s (.r2 o))
  | .t s (.r2 o) => moveAll .S2 s.x (.t s (.r2 o)) (s.out o)
  | .ih => peekS .U .ih2 (.rs .u)
  | .ih2 => peekS .A (.t .e1 (.loop false)) (.rs .u)
  | .mv i => mvBlk (src i) (tmp i) (.mv i) (match i.next with
      | some j => .mv j
      | none => .ih)
  | .rs i => moveAll (tmp i) (src i) (.rs i) (match i.next with
      | some j => .rs j
      | none => .cl .u)
  | .cl i => moveAll (hold i) .Z (.cl i) (match i.next with
      | some j => .cl j
      | none => .oh)
  | .yes | .no => .halt

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

/-!
## The check phase as list recursion

`checkP` is what the check-phase machine computes from the endpoint lists `us`, `vs` and the
color lists `as`, `bs`; `checkP_eq_ok` identifies it with `ok`.
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

/-- A record against all later records, stopping when the endpoints or the colors run out. -/
def innerP (r : Rec) : List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | u :: us, v :: vs, a :: as, b :: bs => pairOk r (u, v, a, b) && innerP r us vs as bs
  | _, _, _, _ => true

/-- Every record alone and against every later record; the lists must run out together. -/
def outerP (n K : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], _, [], _ => true
  | u :: us, v :: vs, a :: as, b :: bs =>
      single n K (u, v, a, b) && innerP (u, v, a, b) us vs as bs && outerP n K us vs as bs
  | _, _, _, _ => false

/-- The check phase. -/
def checkP (n K : ℕ) (us vs as bs : List ℕ) : Bool :=
  (n == 0 || K != 0) && outerP n K us vs as bs

theorem innerP_eq (r : Rec) : ∀ (es cs : List (ℕ × ℕ)),
    innerP r (es.map Prod.fst) (es.map Prod.snd) (cs.map Prod.fst) (cs.map Prod.snd) =
      (recs es cs).all (pairOk r)
  | [], _ => by cases ‹List (ℕ × ℕ)› <;> rfl
  | _ :: _, [] => rfl
  | e :: es, c :: cs => by
    simp only [List.map_cons, innerP, recs, List.zipWith_cons_cons, List.all_cons]
    rw [innerP_eq r es cs]
    rfl

theorem outerP_eq (n K : ℕ) : ∀ (es cs : List (ℕ × ℕ)),
    outerP n K (es.map Prod.fst) (es.map Prod.snd) (cs.map Prod.fst) (cs.map Prod.snd) =
      (es.length == cs.length && (recs es cs).all (single n K) && allPairs (recs es cs))
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | e :: es, c :: cs => by
    simp only [List.map_cons, outerP, recs, List.zipWith_cons_cons, List.all_cons,
      allPairs, List.length_cons]
    rw [innerP_eq, outerP_eq n K es cs]
    simp only [recs]
    cases single n K (e.1, e.2, c.1, c.2) <;>
      cases (List.zipWith (fun e c => (e.1, e.2, c.1, c.2)) es cs).all
        (pairOk (e.1, e.2, c.1, c.2)) <;> simp [Bool.and_comm]

theorem checkP_eq_ok (n K : ℕ) (es cs : List (ℕ × ℕ)) :
    checkP n K (es.map Prod.fst) (es.map Prod.snd) (cs.map Prod.fst) (cs.map Prod.snd) =
      ok n K es cs := by
  rw [checkP, outerP_eq, ok]
  cases (n == 0 || K != 0) <;> cases es.length == cs.length <;> simp

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

/-!
## Runs of the check phase: stack registers and single steps
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

/-- The contents of the stacks other than the scratch stacks `S1`, `S2` (which are empty between
tests). -/
structure Regs where
  N : List Bool
  Kc : List Bool
  U : List Bool
  V : List Bool
  A : List Bool
  B : List Bool
  HU : List Bool
  HV : List Bool
  HA : List Bool
  HB : List Bool
  TU : List Bool
  TV : List Bool
  TA : List Bool
  TB : List Bool
  Z : List Bool

/-- The stacks of a register file, with empty scratch stacks. -/
def Regs.stk (r : Regs) : Stk K
  | .N => r.N | .Kc => r.Kc | .U => r.U | .V => r.V | .A => r.A | .B => r.B
  | .HU => r.HU | .HV => r.HV | .HA => r.HA | .HB => r.HB
  | .TU => r.TU | .TV => r.TV | .TA => r.TA | .TB => r.TB | .Z => r.Z
  | .S1 => [] | .S2 => []

/-- Set one register. -/
def Regs.set (r : Regs) : K → List Bool → Regs
  | .N, x => { r with N := x } | .Kc, x => { r with Kc := x }
  | .U, x => { r with U := x } | .V, x => { r with V := x }
  | .A, x => { r with A := x } | .B, x => { r with B := x }
  | .HU, x => { r with HU := x } | .HV, x => { r with HV := x }
  | .HA, x => { r with HA := x } | .HB, x => { r with HB := x }
  | .TU, x => { r with TU := x } | .TV, x => { r with TV := x }
  | .TA, x => { r with TA := x } | .TB, x => { r with TB := x }
  | .Z, x => { r with Z := x } | .S1, _ => r | .S2, _ => r

theorem update_stk (r : Regs) (k : K) (h₁ : k ≠ .S1) (h₂ : k ≠ .S2) (x : List Bool) :
    update r.stk k x = (r.set k x).stk := by
  funext j
  cases k <;> cases j <;> first | rfl | exact absurd rfl h₁ | exact absurd rfl h₂

theorem set_stk_self (r : Regs) (k : K) (h₁ : k ≠ .S1) (h₂ : k ≠ .S2) (x : List Bool) :
    (r.set k x).stk k = x := by
  cases k <;> first | rfl | exact absurd rfl h₁ | exact absurd rfl h₂

theorem set_stk_ne (r : Regs) (k j : K) (h : j ≠ k) (x : List Bool) :
    (r.set k x).stk j = r.stk j := by
  cases k <;> cases j <;> first | rfl | exact absurd rfl h

theorem stk_S1 (r : Regs) : r.stk .S1 = [] := rfl
theorem stk_S2 (r : Regs) : r.stk .S2 = [] := rfl

/-! ### Peeks -/

theorem peek_run {l ne em : Lab} {k : K} (hp : prog l = peekS k ne em) (v : Bool) (S : Stk K) :
    Run prog 1 ⟨some l, v, S⟩ ⟨some (if S k ≠ [] then ne else em), (S k).head?.isSome, S⟩ := by
  apply Run.single
  cases h : S k <;> simp [hp, peekS, TM2.stepAux, h]

theorem peek_ne {l ne em : Lab} {k : K} (hp : prog l = peekS k ne em) (v : Bool) {S : Stk K}
    (h : S k ≠ []) : ∃ v', RunLe prog 1 ⟨some l, v, S⟩ ⟨some ne, v', S⟩ :=
  ⟨_, by
    have r := (peek_run hp v S).le le_rfl
    have e : (if S k ≠ [] then ne else em) = ne := by simp [h]
    rwa [e] at r⟩

theorem peek_em {l ne em : Lab} {k : K} (hp : prog l = peekS k ne em) (v : Bool) {S : Stk K}
    (h : S k = []) : ∃ v', RunLe prog 1 ⟨some l, v, S⟩ ⟨some em, v', S⟩ :=
  ⟨_, by
    have r := (peek_run hp v S).le le_rfl
    have e : (if S k ≠ [] then ne else em) = em := by simp [h]
    rwa [e] at r⟩

/-! ### Tests -/

theorem site_distinct (s : Site) : Distinct4 s.h s.x .S1 .S2 := by
  cases s <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem test_lt {s : Site} (hk : s.kind = .lt) {p q : List Bool} {S : Stk K}
    (hh : S s.h = p) (hx : S s.x = q) (h₁ : S .S1 = []) (h₂ : S .S2 = []) (v : Bool) :
    ∃ v', RunLe prog (3 * p.length + 5) ⟨some (.t s (.loop false)), v, S⟩
      ⟨some (s.out (ltSer false p q)), v', S⟩ :=
  ltRaw_test (M := prog) (self := fun f => .t s (.loop f)) (r₁ := fun o => .t s (.r1 o))
    (r₂ := fun o => .t s (.r2 o)) (out := s.out) (fun f => by simp [prog, hk]) (fun _ => rfl)
    (fun _ => rfl) (site_distinct s) hh hx h₁ h₂ v

theorem test_raw {s : Site} (hk : s.kind = .raw) {p q : List Bool} {S : Stk K}
    (hh : S s.h = p) (hx : S s.x = q) (h₁ : S .S1 = []) (h₂ : S .S2 = []) (v : Bool) :
    ∃ v', RunLe prog (3 * p.length + 5) ⟨some (.t s (.loop false)), v, S⟩
      ⟨some (s.out (decide (p = q))), v', S⟩ :=
  eqRaw_test (M := prog) (self := .t s (.loop false)) (r₁ := fun o => .t s (.r1 o))
    (r₂ := fun o => .t s (.r2 o)) (out := s.out) (by simp [prog, hk]) (fun _ => rfl)
    (fun _ => rfl) (site_distinct s) hh hx h₁ h₂ v

theorem test_hb {s : Site} (hk : s.kind = .hb) {p q rest : List Bool} {S : Stk K}
    (hh : S s.h = p) (hx : S s.x = delimit q ++ rest) (h₁ : S .S1 = []) (h₂ : S .S2 = [])
    (v : Bool) :
    ∃ v', RunLe prog (4 * q.length + 5) ⟨some (.t s (.loop false)), v, S⟩
      ⟨some (s.out (decide (p = q))), v', S⟩ :=
  eqHB_test (M := prog) (self := .t s (.loop false)) (r₁ := fun o => .t s (.r1 o))
    (r₂ := fun o => .t s (.r2 o)) (out := s.out) (by simp [prog, hk]) (fun _ => rfl)
    (fun _ => rfl) (site_distinct s) hx hh h₁ h₂ v

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

/-!
## Runs of the check phase: the test chains

`Reaches l B S P y n`: from label `l` the program reaches `y` if `P` and `n` otherwise, within
`B` steps, leaving the stacks `S` unchanged. The pair tests reach `mv u` exactly when `pairOk`
holds (`pair_reaches`) and the single tests reach `ih` exactly when `single` holds
(`single_reaches`).
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

local notation "e" => Computability.encodeNat

/-- From `l` the program reaches `y` if `P` and `n` otherwise, within `B` steps, with the stacks
unchanged. -/
def Reaches (l : Lab) (B : ℕ) (S : Stk K) (P : Bool) (y n : Lab) : Prop :=
  ∀ v, ∃ v', RunLe prog B ⟨some l, v, S⟩ ⟨some (cond P y n), v', S⟩

theorem Reaches.mono {l : Lab} {B B' : ℕ} {S : Stk K} {P : Bool} {y n : Lab}
    (h : Reaches l B S P y n) (hB : B ≤ B') : Reaches l B' S P y n := fun v => by
  obtain ⟨v', r⟩ := h v
  exact ⟨v', r.mono hB⟩

theorem Reaches.congr {l : Lab} {B : ℕ} {S : Stk K} {P Q : Bool} {y n : Lab}
    (h : Reaches l B S P y n) (hPQ : P = Q) : Reaches l B S Q y n := hPQ ▸ h

theorem reaches_no {S : Stk K} {y : Lab} : Reaches .no 0 S false y .no :=
  fun v => ⟨v, RunLe.refl _ _⟩

theorem reaches_yes {S : Stk K} {n : Lab} (y : Lab) : Reaches y 0 S true y n :=
  fun v => ⟨v, RunLe.refl _ _⟩

/-- A test with outcome `o` followed by the continuations for both outcomes. -/
theorem Reaches.step {l : Lab} {B C : ℕ} {S : Stk K} {o P₁ P₀ : Bool} {y n : Lab}
    {out : Bool → Lab} (ht : ∀ v, ∃ v', RunLe prog C ⟨some l, v, S⟩ ⟨some (out o), v', S⟩)
    (h₁ : Reaches (out true) B S P₁ y n) (h₀ : Reaches (out false) B S P₀ y n) :
    Reaches l (B + C) S (cond o P₁ P₀) y n := by
  intro v
  obtain ⟨v₁, r₁⟩ := ht v
  cases o
  · obtain ⟨v₂, r₂⟩ := h₀ v₁
    exact ⟨v₂, (r₁.trans r₂).mono (by omega)⟩
  · obtain ⟨v₂, r₂⟩ := h₁ v₁
    exact ⟨v₂, (r₁.trans r₂).mono (by omega)⟩

theorem hb_step {s : Site} (hk : s.kind = .hb) {x z : ℕ} {rest : List Bool} {S : Stk K}
    (hh : S s.h = e x) (hx : S s.x = delimit (e z) ++ rest) (h₁ : S .S1 = []) (h₂ : S .S2 = [])
    {Q B : ℕ} (hQ : (e z).length ≤ Q) {P₁ P₀ : Bool} {y n : Lab}
    (ht : Reaches (s.out true) B S P₁ y n) (hf : Reaches (s.out false) B S P₀ y n) :
    Reaches (.t s (.loop false)) (B + (4 * Q + 5)) S (cond (decide (x = z)) P₁ P₀) y n := by
  refine Reaches.step (fun v => ?_) ht hf
  obtain ⟨v₁, r₁⟩ := test_hb hk hh hx h₁ h₂ v
  rw [show decide (e x = e z) = decide (x = z) from by simp [encodeNat_inj]] at r₁
  exact ⟨v₁, r₁.mono (by omega)⟩

theorem lt_step {s : Site} (hk : s.kind = .lt) {x z : ℕ} {S : Stk K}
    (hh : S s.h = e x) (hx : S s.x = e z) (h₁ : S .S1 = []) (h₂ : S .S2 = [])
    {Q B : ℕ} (hQ : (e x).length ≤ Q) {P₁ P₀ : Bool} {y n : Lab}
    (ht : Reaches (s.out true) B S P₁ y n) (hf : Reaches (s.out false) B S P₀ y n) :
    Reaches (.t s (.loop false)) (B + (4 * Q + 5)) S (cond (decide (x < z)) P₁ P₀) y n := by
  refine Reaches.step (fun v => ?_) ht hf
  obtain ⟨v₁, r₁⟩ := test_lt hk hh hx h₁ h₂ v
  rw [ltSer_false_encodeNat] at r₁
  exact ⟨v₁, r₁.mono (by omega)⟩

theorem raw_step {s : Site} (hk : s.kind = .raw) {x z : ℕ} {S : Stk K}
    (hh : S s.h = e x) (hx : S s.x = e z) (h₁ : S .S1 = []) (h₂ : S .S2 = [])
    {Q B : ℕ} (hQ : (e x).length ≤ Q) {P₁ P₀ : Bool} {y n : Lab}
    (ht : Reaches (s.out true) B S P₁ y n) (hf : Reaches (s.out false) B S P₀ y n) :
    Reaches (.t s (.loop false)) (B + (4 * Q + 5)) S (cond (decide (x = z)) P₁ P₀) y n := by
  refine Reaches.step (fun v => ?_) ht hf
  obtain ⟨v₁, r₁⟩ := test_raw hk hh hx h₁ h₂ v
  rw [show decide (e x = e z) = decide (x = z) from by simp [encodeNat_inj]] at r₁
  exact ⟨v₁, r₁.mono (by omega)⟩

section Chains

variable {r : Regs} {x₁ x₂ x₃ x₄ u v a b Q : ℕ} {RU RV RA RB : List Bool}
  (hHU : r.HU = e x₁) (hHV : r.HV = e x₂) (hHA : r.HA = e x₃) (hHB : r.HB = e x₄)

include hHU hHV hHA hHB in
theorem pair_reaches (hU : r.U = delimit (e u) ++ RU) (hV : r.V = delimit (e v) ++ RV)
    (hA : r.A = delimit (e a) ++ RA) (hB : r.B = delimit (e b) ++ RB)
    (qu : (e u).length ≤ Q) (qv : (e v).length ≤ Q) (qa : (e a).length ≤ Q)
    (qb : (e b).length ≤ Q) :
    Reaches (.t .e1 (.loop false)) (10 * (4 * Q + 5)) r.stk
      (pairOk (x₁, x₂, x₃, x₄) (u, v, a, b)) (.mv .u) .no := by
  have z₁ : r.stk .S1 = [] := rfl
  have z₂ : r.stk .S2 = [] := rfl
  have yes0 : Reaches (.mv .u) 0 r.stk true (.mv .u) .no := reaches_yes _
  have no0 : Reaches .no 0 r.stk false (.mv .u) .no := reaches_no
  have Rba := hb_step (s := .ba) (B := 0) rfl hHB hA z₁ z₂ qa yes0 no0
  have Re4' := hb_step (s := .e4') (B := 1 * (4 * Q + 5)) rfl hHV hU z₁ z₂ qu
    (Rba.mono (by omega)) (yes0.mono (by omega))
  have Rab := hb_step (s := .ab) (B := 2 * (4 * Q + 5)) rfl hHA hB z₁ z₂ qb
    (Re4'.mono (by omega)) (no0.mono (by omega))
  have Re4 := hb_step (s := .e4) (B := 3 * (4 * Q + 5)) rfl hHV hU z₁ z₂ qu
    (no0.mono (by omega)) (Rab.mono (by omega))
  have Re3 := hb_step (s := .e3) (B := 4 * (4 * Q + 5)) rfl hHU hV z₁ z₂ qv
    (Re4.mono (by omega)) (Re4'.mono (by omega))
  have Rbb := hb_step (s := .bb) (B := 5 * (4 * Q + 5)) rfl hHB hB z₁ z₂ qb
    (Re3.mono (by omega)) (no0.mono (by omega))
  have Re2' := hb_step (s := .e2') (B := 6 * (4 * Q + 5)) rfl hHV hV z₁ z₂ qv
    (Rbb.mono (by omega)) (Re3.mono (by omega))
  have Raa := hb_step (s := .aa) (B := 7 * (4 * Q + 5)) rfl hHA hA z₁ z₂ qa
    (Re2'.mono (by omega)) (no0.mono (by omega))
  have Re2 := hb_step (s := .e2) (B := 8 * (4 * Q + 5)) rfl hHV hV z₁ z₂ qv
    (no0.mono (by omega)) (Raa.mono (by omega))
  have Re1 := hb_step (s := .e1) (B := 9 * (4 * Q + 5)) rfl hHU hU z₁ z₂ qu
    (Re2.mono (by omega)) (Re2'.mono (by omega))
  refine (Re1.mono (by omega)).congr ?_
  simp only [pairOk, beq_eq_decide, bne, Bool.cond_eq_ite]
  generalize decide (x₁ = u) = d₁; generalize decide (x₂ = v) = d₂
  generalize decide (x₁ = v) = d₃; generalize decide (x₂ = u) = d₄
  generalize decide (x₃ = a) = d₅; generalize decide (x₄ = b) = d₆
  generalize decide (x₃ = b) = d₇; generalize decide (x₄ = a) = d₈
  cases d₁ <;> cases d₂ <;> cases d₃ <;> cases d₄ <;> cases d₅ <;> cases d₆ <;> cases d₇ <;>
    cases d₈ <;> rfl

include hHU hHV hHA hHB in
theorem single_reaches {n K : ℕ} (hN : r.N = e n) (hK : r.Kc = e K)
    (q₁ : (e x₁).length ≤ Q) (q₂ : (e x₂).length ≤ Q) (q₃ : (e x₃).length ≤ Q)
    (q₄ : (e x₄).length ≤ Q) :
    Reaches (.t .lu (.loop false)) (6 * (4 * Q + 5)) r.stk (single n K (x₁, x₂, x₃, x₄))
      .ih .no := by
  have z₁ : r.stk .S1 = [] := rfl
  have z₂ : r.stk .S2 = [] := rfl
  have yes0 : Reaches .ih 0 r.stk true .ih .no := reaches_yes _
  have no0 : Reaches .no 0 r.stk false .ih .no := reaches_no
  have Rnab := raw_step (s := .nab) (B := 0) rfl hHA hHB z₁ z₂ q₃ no0 yes0
  have Rnuv := raw_step (s := .nuv) (B := 1 * (4 * Q + 5)) rfl hHU hHV z₁ z₂ q₁
    (no0.mono (by omega)) (Rnab.mono (by omega))
  have Rlb := lt_step (s := .lb) (B := 2 * (4 * Q + 5)) rfl hHB hK z₁ z₂ q₄
    (Rnuv.mono (by omega)) (no0.mono (by omega))
  have Rla := lt_step (s := .la) (B := 3 * (4 * Q + 5)) rfl hHA hK z₁ z₂ q₃
    (Rlb.mono (by omega)) (no0.mono (by omega))
  have Rlv := lt_step (s := .lv) (B := 4 * (4 * Q + 5)) rfl hHV hN z₁ z₂ q₂
    (Rla.mono (by omega)) (no0.mono (by omega))
  have Rlu := lt_step (s := .lu) (B := 5 * (4 * Q + 5)) rfl hHU hN z₁ z₂ q₁
    (Rlv.mono (by omega)) (no0.mono (by omega))
  refine (Rlu.mono (by omega)).congr ?_
  simp only [single, bne, beq_eq_decide, Bool.cond_eq_ite]
  generalize decide (x₁ < n) = d₁; generalize decide (x₂ < n) = d₂
  generalize decide (x₃ < K) = d₃; generalize decide (x₄ < K) = d₄
  generalize decide (x₁ = x₂) = d₅; generalize decide (x₃ = x₄) = d₆
  cases d₁ <;> cases d₂ <;> cases d₃ <;> cases d₄ <;> cases d₅ <;> cases d₆ <;> rfl

end Chains

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

/-!
## Runs of the check phase: moving records
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

local notation "e" => Computability.encodeNat

theorem RunLe.of_eq' {B : ℕ} {c d d' : TM2.Cfg (fun _ : K => Bool) Lab Bool}
    (h : RunLe prog B c d) (hd : d = d') : RunLe prog B c d' := hd ▸ h

theorem moveAll_regs {l next : Lab} {a b : K} (hp : prog l = moveAll a b l next) (hab : a ≠ b)
    (ha₁ : a ≠ .S1) (ha₂ : a ≠ .S2) (hb₁ : b ≠ .S1) (hb₂ : b ≠ .S2) (r : Regs) (v : Bool) :
    ∃ v', Run prog ((r.stk a).length + 1) ⟨some l, v, r.stk⟩
      ⟨some next, v', ((r.set a []).set b ((r.stk a).reverse ++ r.stk b)).stk⟩ := by
  obtain ⟨v', hr⟩ := moveAll_run hp hab v r.stk
  refine ⟨v', ?_⟩
  rwa [update_stk r a ha₁ ha₂, show r.stk b = (r.set a []).stk b from
    (set_stk_ne r a b (Ne.symm hab) []).symm, update_stk _ b hb₁ hb₂,
    ← show r.stk b = (r.set a []).stk b from (set_stk_ne r a b (Ne.symm hab) []).symm] at hr

theorem mvBlk_regs {l next : Lab} {a b : K} (hp : prog l = mvBlk a b l next) (hab : a ≠ b)
    (ha₁ : a ≠ .S1) (ha₂ : a ≠ .S2) (hb₁ : b ≠ .S1) (hb₂ : b ≠ .S2) (r : Regs) {q rest : List Bool}
    (hq : r.stk a = delimit q ++ rest) (v : Bool) :
    ∃ v', Run prog (q.length + 1) ⟨some l, v, r.stk⟩
      ⟨some next, v', ((r.set a rest).set b ((delimit q).reverse ++ r.stk b)).stk⟩ := by
  obtain ⟨v', hr⟩ := mvBlk_run hp hab q rest v r.stk hq
  refine ⟨v', ?_⟩
  rwa [update_stk r a ha₁ ha₂, show r.stk b = (r.set a rest).stk b from
    (set_stk_ne r a b (Ne.symm hab) rest).symm, update_stk _ b hb₁ hb₂,
    ← show r.stk b = (r.set a rest).stk b from (set_stk_ne r a b (Ne.symm hab) rest).symm] at hr

theorem read_regs {i : F} (r : Regs) {q rest : List Bool} (hq : r.stk (src i) = delimit q ++ rest)
    (v : Bool) :
    ∃ v' S', Run prog (q.length + 1) ⟨some (.cp i), v, r.stk⟩ ⟨some (.cq i), v', S'⟩ ∧
      S' = update (r.set (src i) rest).stk .S1 q.reverse := by
  have hne : src i ≠ .S1 := by cases i <;> decide
  obtain ⟨S', hr, ha, hb, hk⟩ := Cslib.Complexity.FramedCNF.Block.run_delimit
    (M := prog) (a := src i) (b := .S1) (d := fun x => some x) (g := id) (self := .cp i)
    (good := .cq i) (bad := .no) rfl hne id (fun _ => rfl) q rest v r.stk (by simpa using hq)
  refine ⟨false, S', hr, ?_⟩
  funext k
  by_cases h₁ : k = .S1
  · subst h₁; simp [hb, stk_S1]
  · by_cases h₂ : k = src i
    · subst h₂
      rw [ha, update_of_ne h₁, set_stk_self _ _ hne (by cases i <;> decide)]
    · rw [hk k h₂ h₁, update_of_ne h₁, set_stk_ne _ _ _ h₂]

theorem src_ne (i : F) : src i ≠ .S1 ∧ src i ≠ .S2 := by cases i <;> decide
theorem hold_ne (i : F) : hold i ≠ .S1 ∧ hold i ≠ .S2 ∧ hold i ≠ src i ∧ hold i ≠ .Z := by
  cases i <;> decide
theorem tmp_ne (i : F) : tmp i ≠ .S1 ∧ tmp i ≠ .S2 ∧ tmp i ≠ src i := by cases i <;> decide

/-- The label after copying field `i`. -/
def cpNext (i : F) : Lab := match i.next with
  | some j => .cp j
  | none => .t .lu (.loop false)

theorem copy_one (i : F) (r : Regs) {q rest : List Bool} (hq : r.stk (src i) = delimit q ++ rest)
    (v : Bool) :
    ∃ v', RunLe prog (2 * q.length + 3) ⟨some (.cp i), v, r.stk⟩
      ⟨some (cpNext i), v', ((r.set (src i) rest).set (hold i) (q ++ r.stk (hold i))).stk⟩ := by
  obtain ⟨v₁, S', r₁, hS'⟩ := read_regs r hq v
  obtain ⟨hs₁, hs₂⟩ := src_ne i
  obtain ⟨hh₁, hh₂, hh₃, -⟩ := hold_ne i
  obtain ⟨v₂, r₂⟩ := moveAll_run (M := prog) (self := .cq i) (next := cpNext i) (a := .S1)
    (b := hold i) rfl (Ne.symm hh₁) v₁ S'
  subst hS'
  have hl : (update (r.set (src i) rest).stk K.S1 q.reverse K.S1).length = q.length := by simp
  refine ⟨v₂, RunLe.of_eq' ((r₁.trans r₂).le (by rw [hl]; omega)) ?_⟩
  congr 1
  funext k
  by_cases k₁ : k = hold i
  · subst k₁
    simp [update_of_ne hh₁, set_stk_self _ _ hh₁ hh₂, set_stk_ne _ _ _ hh₃]
  · rw [update_of_ne k₁]
    by_cases k₂ : k = .S1
    · subst k₂; rw [update_self]; rfl
    · rw [update_of_ne k₂, update_of_ne k₂, set_stk_ne _ _ _ k₁]

theorem copy_all (r : Regs) {pu pv pa pb RU RV RA RB : List Bool}
    (hU : r.U = delimit pu ++ RU) (hV : r.V = delimit pv ++ RV) (hA : r.A = delimit pa ++ RA)
    (hB : r.B = delimit pb ++ RB) (v : Bool) :
    ∃ v', RunLe prog (2 * (pu.length + pv.length + pa.length + pb.length) + 12)
      ⟨some (.cp .u), v, r.stk⟩ ⟨some (.t .lu (.loop false)), v',
        { r with
            U := RU, V := RV, A := RA, B := RB, HU := pu ++ r.HU, HV := pv ++ r.HV
            HA := pa ++ r.HA, HB := pb ++ r.HB }.stk⟩ := by
  let r₁ := (r.set .U RU).set .HU (pu ++ r.HU)
  let r₂ := (r₁.set .V RV).set .HV (pv ++ r.HV)
  let r₃ := (r₂.set .A RA).set .HA (pa ++ r.HA)
  obtain ⟨v₁, h₁⟩ := copy_one .u r (q := pu) (rest := RU) hU v
  obtain ⟨v₂, h₂⟩ := copy_one .v r₁ (q := pv) (rest := RV) hV v₁
  obtain ⟨v₃, h₃⟩ := copy_one .a r₂ (q := pa) (rest := RA) hA v₂
  obtain ⟨v₄, h₄⟩ := copy_one .b r₃ (q := pb) (rest := RB) hB v₃
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  exact ⟨v₄, h.mono (by omega)⟩

/-- The label after moving field `i`. -/
def mvNext (i : F) : Lab := match i.next with
  | some j => .mv j
  | none => .ih

theorem mv_one (i : F) (r : Regs) {q rest : List Bool} (hq : r.stk (src i) = delimit q ++ rest)
    (v : Bool) :
    ∃ v', RunLe prog (q.length + 1) ⟨some (.mv i), v, r.stk⟩
      ⟨some (mvNext i), v', ((r.set (src i) rest).set (tmp i)
        ((delimit q).reverse ++ r.stk (tmp i))).stk⟩ := by
  obtain ⟨hs₁, hs₂⟩ := src_ne i
  obtain ⟨ht₁, ht₂, ht₃⟩ := tmp_ne i
  obtain ⟨v', h⟩ := mvBlk_regs (l := .mv i) (next := mvNext i) rfl (Ne.symm ht₃) hs₁ hs₂ ht₁ ht₂
    r hq v
  exact ⟨v', h.le le_rfl⟩

theorem mv_all (r : Regs) {pu pv pa pb RU RV RA RB : List Bool}
    (hU : r.U = delimit pu ++ RU) (hV : r.V = delimit pv ++ RV) (hA : r.A = delimit pa ++ RA)
    (hB : r.B = delimit pb ++ RB) (v : Bool) :
    ∃ v', RunLe prog (pu.length + pv.length + pa.length + pb.length + 4)
      ⟨some (.mv .u), v, r.stk⟩ ⟨some .ih, v',
        { r with
            U := RU, V := RV, A := RA, B := RB
            TU := (delimit pu).reverse ++ r.TU, TV := (delimit pv).reverse ++ r.TV
            TA := (delimit pa).reverse ++ r.TA, TB := (delimit pb).reverse ++ r.TB }.stk⟩ := by
  let r₁ := (r.set .U RU).set .TU ((delimit pu).reverse ++ r.TU)
  let r₂ := (r₁.set .V RV).set .TV ((delimit pv).reverse ++ r.TV)
  let r₃ := (r₂.set .A RA).set .TA ((delimit pa).reverse ++ r.TA)
  obtain ⟨v₁, h₁⟩ := mv_one .u r (q := pu) (rest := RU) hU v
  obtain ⟨v₂, h₂⟩ := mv_one .v r₁ (q := pv) (rest := RV) hV v₁
  obtain ⟨v₃, h₃⟩ := mv_one .a r₂ (q := pa) (rest := RA) hA v₂
  obtain ⟨v₄, h₄⟩ := mv_one .b r₃ (q := pb) (rest := RB) hB v₃
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  exact ⟨v₄, h.mono (by omega)⟩

/-- The label after restoring field `i`. -/
def rsNext (i : F) : Lab := match i.next with
  | some j => .rs j
  | none => .cl .u

/-- The label after clearing field `i`. -/
def clNext (i : F) : Lab := match i.next with
  | some j => .cl j
  | none => .oh

theorem rs_one (i : F) (r : Regs) (v : Bool) :
    ∃ v', RunLe prog ((r.stk (tmp i)).length + 1) ⟨some (.rs i), v, r.stk⟩
      ⟨some (rsNext i), v', ((r.set (tmp i) []).set (src i)
        ((r.stk (tmp i)).reverse ++ r.stk (src i))).stk⟩ := by
  obtain ⟨hs₁, hs₂⟩ := src_ne i
  obtain ⟨ht₁, ht₂, ht₃⟩ := tmp_ne i
  obtain ⟨v', h⟩ := moveAll_regs (l := .rs i) (next := rsNext i) rfl ht₃ ht₁ ht₂ hs₁ hs₂ r v
  exact ⟨v', h.le le_rfl⟩

theorem cl_one (i : F) (r : Regs) (v : Bool) :
    ∃ v', RunLe prog ((r.stk (hold i)).length + 1) ⟨some (.cl i), v, r.stk⟩
      ⟨some (clNext i), v', ((r.set (hold i) []).set .Z
        ((r.stk (hold i)).reverse ++ r.Z)).stk⟩ := by
  obtain ⟨hh₁, hh₂, -, hh₄⟩ := hold_ne i
  obtain ⟨v', h⟩ := moveAll_regs (l := .cl i) (next := clNext i) rfl hh₄ hh₁ hh₂ (by decide)
    (by decide) r v
  exact ⟨v', h.le le_rfl⟩

/-- The registers after restoring the inputs and clearing the holding stacks. -/
def restoreRegs (r : Regs) : Regs :=
  ⟨r.N, r.Kc, r.TU.reverse ++ r.U, r.TV.reverse ++ r.V, r.TA.reverse ++ r.A,
    r.TB.reverse ++ r.B, [], [], [], [], [], [], [], [],
    r.HB.reverse ++ (r.HA.reverse ++ (r.HV.reverse ++ (r.HU.reverse ++ r.Z)))⟩

theorem stk_eq_of {X Y : Regs} (h : X = Y) : X.stk = Y.stk := h ▸ rfl

theorem restore_all (r : Regs) (v : Bool) :
    ∃ v', RunLe prog (r.TU.length + r.TV.length + r.TA.length + r.TB.length + r.HU.length +
        r.HV.length + r.HA.length + r.HB.length + 8) ⟨some (.rs .u), v, r.stk⟩
        ⟨some .oh, v', (restoreRegs r).stk⟩ := by
  obtain ⟨N, Kc, U, V, A, B, HU, HV, HA, HB, TU, TV, TA, TB, Z⟩ := r
  obtain ⟨v₁, h₁⟩ := rs_one .u ⟨N, Kc, U, V, A, B, HU, HV, HA, HB, TU, TV, TA, TB, Z⟩ v
  obtain ⟨v₂, h₂⟩ := rs_one .v
    ⟨N, Kc, TU.reverse ++ U, V, A, B, HU, HV, HA, HB, [], TV, TA, TB, Z⟩ v₁
  obtain ⟨v₃, h₃⟩ := rs_one .a
    ⟨N, Kc, TU.reverse ++ U, TV.reverse ++ V, A, B, HU, HV, HA, HB, [], [], TA, TB, Z⟩ v₂
  obtain ⟨v₄, h₄⟩ := rs_one .b ⟨N, Kc, TU.reverse ++ U, TV.reverse ++ V, TA.reverse ++ A, B,
    HU, HV, HA, HB, [], [], [], TB, Z⟩ v₃
  obtain ⟨v₅, h₅⟩ := cl_one .u ⟨N, Kc, TU.reverse ++ U, TV.reverse ++ V, TA.reverse ++ A,
    TB.reverse ++ B, HU, HV, HA, HB, [], [], [], [], Z⟩ v₄
  obtain ⟨v₆, h₆⟩ := cl_one .v ⟨N, Kc, TU.reverse ++ U, TV.reverse ++ V, TA.reverse ++ A,
    TB.reverse ++ B, [], HV, HA, HB, [], [], [], [], HU.reverse ++ Z⟩ v₅
  obtain ⟨v₇, h₇⟩ := cl_one .a ⟨N, Kc, TU.reverse ++ U, TV.reverse ++ V, TA.reverse ++ A,
    TB.reverse ++ B, [], [], HA, HB, [], [], [], [], HV.reverse ++ (HU.reverse ++ Z)⟩ v₆
  obtain ⟨v₈, h₈⟩ := cl_one .b ⟨N, Kc, TU.reverse ++ U, TV.reverse ++ V, TA.reverse ++ A,
    TB.reverse ++ B, [], [], [], HB, [], [], [], [], HA.reverse ++ (HV.reverse ++ (HU.reverse ++
    Z))⟩ v₇
  have h := (((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈)
  refine ⟨v₈, h.mono (le_of_eq ?_)⟩
  simp only [Regs.stk, tmp, hold]
  omega

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

/-!
## Runs of the check phase: the inner loop
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

local notation "e" => Computability.encodeNat

theorem be_cons (u : ℕ) (us : List ℕ) : bitEncode (u :: us) = delimit (e u) ++ bitEncode us := rfl
theorem be_nil : bitEncode ([] : List ℕ) = [] := rfl

theorem delimit_ne_nil (l : List Bool) : delimit l ≠ [] := by
  cases l <;> simp [delimit]

theorem be_ne_nil {us : List ℕ} (h : us ≠ []) : bitEncode us ≠ [] := by
  obtain ⟨u, us, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [be_cons, delimit_ne_nil]

theorem inner_run (N Kc HU HV HA HB Z : List Bool) (x₁ x₂ x₃ x₄ Q : ℕ) (hHU : HU = e x₁)
    (hHV : HV = e x₂) (hHA : HA = e x₃) (hHB : HB = e x₄) :
    ∀ (us vs as bs : List ℕ) (TU TV TA TB : List Bool), us.length = vs.length →
      as.length = bs.length → (∀ y ∈ us ++ vs ++ as ++ bs, (e y).length ≤ Q) → ∀ v,
      ∃ v' S', RunLe prog (us.length * (44 * Q + 56) + 2)
        ⟨some .ih, v, (⟨N, Kc, bitEncode us, bitEncode vs, bitEncode as, bitEncode bs,
          HU, HV, HA, HB, TU, TV, TA, TB, Z⟩ : Regs).stk⟩
        ⟨some (cond (innerP (x₁, x₂, x₃, x₄) us vs as bs) (.rs .u) .no), v', S'⟩ ∧
        (innerP (x₁, x₂, x₃, x₄) us vs as bs = true → ∃ U' V' A' B' TU' TV' TA' TB',
          S' = (⟨N, Kc, U', V', A', B', HU, HV, HA, HB, TU', TV', TA', TB', Z⟩ : Regs).stk ∧
          TU'.reverse ++ U' = TU.reverse ++ bitEncode us ∧
          TV'.reverse ++ V' = TV.reverse ++ bitEncode vs ∧
          TA'.reverse ++ A' = TA.reverse ++ bitEncode as ∧
          TB'.reverse ++ B' = TB.reverse ++ bitEncode bs) := by
  intro us
  induction us with
  | nil =>
    intro vs as bs TU TV TA TB _ _ _ v
    obtain ⟨v', r⟩ := peek_em (l := .ih) (k := .U) (ne := .ih2) (em := .rs .u) rfl v
      (S := (⟨N, Kc, bitEncode ([] : List ℕ), bitEncode vs, bitEncode as, bitEncode bs,
          HU, HV, HA, HB, TU, TV, TA, TB, Z⟩ : Regs).stk) rfl
    exact ⟨v', _, r.mono (by omega), fun _ => ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl⟩⟩
  | cons u us ih =>
    intro vs as bs TU TV TA TB hl₁ hl₂ hq v
    obtain ⟨v₀, vs, rfl⟩ : ∃ v₀ vs', vs = v₀ :: vs' := by
      cases vs with
      | nil => simp at hl₁
      | cons v₀ vs' => exact ⟨v₀, vs', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl₁
    obtain ⟨v₁, r₁⟩ := peek_ne (l := .ih) (k := .U) (ne := .ih2) (em := .rs .u) rfl v
      (S := (⟨N, Kc, bitEncode (u :: us), bitEncode (v₀ :: vs), bitEncode as, bitEncode bs,
          HU, HV, HA, HB, TU, TV, TA, TB, Z⟩ : Regs).stk) (be_ne_nil (List.cons_ne_nil u us))
    rcases as with _ | ⟨a, as⟩
    · have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl₂.symm)
      subst hbs
      obtain ⟨v₂, r₂⟩ := peek_em (l := .ih2) (k := .A) (ne := .t .e1 (.loop false))
        (em := .rs .u) rfl v₁ (S := (⟨N, Kc, bitEncode (u :: us), bitEncode (v₀ :: vs),
          bitEncode ([] : List ℕ), bitEncode ([] : List ℕ), HU, HV, HA, HB, TU, TV, TA, TB,
          Z⟩ : Regs).stk) rfl
      exact ⟨v₂, _, (r₁.trans r₂).mono (Nat.le_add_left 2 _),
        fun _ => ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => simp at hl₂
        | cons b bs' => exact ⟨b, bs', rfl⟩
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl₂
      let R₀ : Regs := ⟨N, Kc, bitEncode (u :: us), bitEncode (v₀ :: vs), bitEncode (a :: as),
        bitEncode (b :: bs), HU, HV, HA, HB, TU, TV, TA, TB, Z⟩
      obtain ⟨v₂, r₂⟩ := peek_ne (l := .ih2) (k := .A) (ne := .t .e1 (.loop false))
        (em := .rs .u) rfl v₁ (S := R₀.stk) (be_ne_nil (List.cons_ne_nil a as))
      have hQ : ∀ y, y = u ∨ y = v₀ ∨ y = a ∨ y = b → (e y).length ≤ Q := by
        intro y hy
        apply hq
        simp only [List.mem_append, List.mem_cons]
        tauto
      obtain ⟨v₃, r₃⟩ := pair_reaches (r := R₀) (x₁ := x₁) (x₂ := x₂) (x₃ := x₃) (x₄ := x₄)
        hHU hHV hHA hHB (be_cons u us) (be_cons v₀ vs) (be_cons a as) (be_cons b bs)
        (hQ u (by simp)) (hQ v₀ (by simp)) (hQ a (by simp)) (hQ b (by simp)) v₂
      have hin : innerP (x₁, x₂, x₃, x₄) (u :: us) (v₀ :: vs) (a :: as) (b :: bs) =
          (pairOk (x₁, x₂, x₃, x₄) (u, v₀, a, b) && innerP (x₁, x₂, x₃, x₄) us vs as bs) := rfl
      cases hpo : pairOk (x₁, x₂, x₃, x₄) (u, v₀, a, b)
      · rw [hpo] at r₃
        rw [hin, hpo]
        refine ⟨v₃, _, ((r₁.trans r₂).trans r₃).mono ?_, fun h => by simp at h⟩
        have : (us.length + 1) * (44 * Q + 56) = us.length * (44 * Q + 56) + (44 * Q + 56) := by
            rw [Nat.add_mul, Nat.one_mul]
        simp only [List.length_cons]
        omega
      · rw [hpo] at r₃
        obtain ⟨v₄, r₄⟩ := mv_all R₀ (pu := e u) (pv := e v₀) (pa := e a) (pb := e b)
          (RU := bitEncode us) (RV := bitEncode vs) (RA := bitEncode as) (RB := bitEncode bs)
          (be_cons u us) (be_cons v₀ vs) (be_cons a as) (be_cons b bs) v₃
        have hq' : ∀ y ∈ us ++ vs ++ as ++ bs, (e y).length ≤ Q := by
          intro y hy
          apply hq
          simp only [List.mem_append, List.mem_cons] at hy ⊢
          tauto
        obtain ⟨v₅, S', r₅, hS'⟩ := ih vs as bs ((delimit (e u)).reverse ++ TU)
          ((delimit (e v₀)).reverse ++ TV) ((delimit (e a)).reverse ++ TA)
          ((delimit (e b)).reverse ++ TB) hl₁ hl₂ hq' v₄
        rw [hin, hpo, Bool.true_and]
        refine ⟨v₅, S', (((r₁.trans r₂).trans r₃).trans (r₄.trans r₅)).mono ?_, fun h => ?_⟩
        · have : (us.length + 1) * (44 * Q + 56) = us.length * (44 * Q + 56) + (44 * Q + 56) := by
            rw [Nat.add_mul, Nat.one_mul]
          have := hQ u (by simp); have := hQ v₀ (by simp)
          have := hQ a (by simp); have := hQ b (by simp)
          simp only [List.length_cons]
          omega
        · obtain ⟨U', V', A', B', TU', TV', TA', TB', h₀, h₁, h₂, h₃, h₄⟩ := hS' h
          refine ⟨U', V', A', B', TU', TV', TA', TB', h₀, ?_, ?_, ?_, ?_⟩
          · rw [h₁]; simp [be_cons]
          · rw [h₂]; simp [be_cons]
          · rw [h₃]; simp [be_cons]
          · rw [h₄]; simp [be_cons]

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

/-!
## Runs of the check phase: the outer loop and the whole phase
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.BitstringEncoding

local notation "e" => Computability.encodeNat

/-- The total length of the four list stacks. -/
def wt (us vs as bs : List ℕ) : ℕ :=
  (bitEncode us).length + (bitEncode vs).length + (bitEncode as).length + (bitEncode bs).length

theorem length_le_be (us : List ℕ) : us.length ≤ (bitEncode us).length := by
  induction us with
  | nil => simp [be_nil]
  | cons u us ih => simp [be_cons]; omega

theorem outer_run (n K Q L : ℕ) (hQL : Q ≤ L) :
    ∀ (us vs as bs : List ℕ) (Z : List Bool), us.length = vs.length → as.length = bs.length →
      (∀ y ∈ us ++ vs ++ as ++ bs, (e y).length ≤ Q) → wt us vs as bs ≤ L → ∀ v,
      ∃ v' S', RunLe prog ((us.length + 1) * (200 * (L + 1) * (L + 1)))
        ⟨some .oh, v, (⟨e n, e K, bitEncode us, bitEncode vs, bitEncode as, bitEncode bs,
          [], [], [], [], [], [], [], [], Z⟩ : Regs).stk⟩
        ⟨some (cond (outerP n K us vs as bs) .yes .no), v', S'⟩ := by
  have hP : 0 < 200 * (L + 1) * (L + 1) := by positivity
  intro us
  induction us with
  | nil =>
    intro vs as bs Z _ hl₂ _ _ v
    obtain ⟨v₁, r₁⟩ := peek_em (l := .oh) (k := .U) (ne := .oh3) (em := .oh2) rfl v
      (S := (⟨e n, e K, bitEncode ([] : List ℕ), bitEncode vs, bitEncode as, bitEncode bs,
          [], [], [], [], [], [], [], [], Z⟩ : Regs).stk) rfl
    rcases as with _ | ⟨a, as⟩
    · obtain ⟨v₂, r₂⟩ := peek_em (l := .oh2) (k := .A) (ne := .no) (em := .yes) rfl v₁
        (S := (⟨e n, e K, bitEncode ([] : List ℕ), bitEncode vs, bitEncode ([] : List ℕ),
          bitEncode bs, [], [], [], [], [], [], [], [], Z⟩ : Regs).stk) rfl
      exact ⟨v₂, _, (r₁.trans r₂).mono (by simp only [List.length_nil]; nlinarith)⟩
    · obtain ⟨v₂, r₂⟩ := peek_ne (l := .oh2) (k := .A) (ne := .no) (em := .yes) rfl v₁
        (S := (⟨e n, e K, bitEncode ([] : List ℕ), bitEncode vs, bitEncode (a :: as),
          bitEncode bs, [], [], [], [], [], [], [], [], Z⟩ : Regs).stk)
        (be_ne_nil (List.cons_ne_nil a as))
      exact ⟨v₂, _, (r₁.trans r₂).mono (by simp only [List.length_nil]; nlinarith)⟩
  | cons u us ih =>
    intro vs as bs Z hl₁ hl₂ hq hw v
    obtain ⟨v₀, vs, rfl⟩ : ∃ v₀ vs', vs = v₀ :: vs' := by
      cases vs with
      | nil => simp at hl₁
      | cons v₀ vs' => exact ⟨v₀, vs', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl₁
    obtain ⟨v₁, r₁⟩ := peek_ne (l := .oh) (k := .U) (ne := .oh3) (em := .oh2) rfl v
      (S := (⟨e n, e K, bitEncode (u :: us), bitEncode (v₀ :: vs), bitEncode as, bitEncode bs,
          [], [], [], [], [], [], [], [], Z⟩ : Regs).stk) (be_ne_nil (List.cons_ne_nil u us))
    rcases as with _ | ⟨a, as⟩
    · obtain ⟨v₂, r₂⟩ := peek_em (l := .oh3) (k := .A) (ne := .cp .u) (em := .no) rfl v₁
        (S := (⟨e n, e K, bitEncode (u :: us), bitEncode (v₀ :: vs), bitEncode ([] : List ℕ),
          bitEncode bs, [], [], [], [], [], [], [], [], Z⟩ : Regs).stk) rfl
      exact ⟨v₂, _, (r₁.trans r₂).mono (by simp; nlinarith)⟩
    · obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => simp at hl₂
        | cons b bs' => exact ⟨b, bs', rfl⟩
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl₂
      let R₀ : Regs := ⟨e n, e K, bitEncode (u :: us), bitEncode (v₀ :: vs), bitEncode (a :: as),
        bitEncode (b :: bs), [], [], [], [], [], [], [], [], Z⟩
      obtain ⟨v₂, r₂⟩ := peek_ne (l := .oh3) (k := .A) (ne := .cp .u) (em := .no) rfl v₁
        (S := R₀.stk) (be_ne_nil (List.cons_ne_nil a as))
      have hQ : ∀ y, y = u ∨ y = v₀ ∨ y = a ∨ y = b → (e y).length ≤ Q := by
        intro y hy
        apply hq
        simp only [List.mem_append, List.mem_cons]
        tauto
      have hq' : ∀ y ∈ us ++ vs ++ as ++ bs, (e y).length ≤ Q := by
        intro y hy
        apply hq
        simp only [List.mem_append, List.mem_cons] at hy ⊢
        tauto
      have qu := hQ u (by simp); have qv := hQ v₀ (by simp)
      have qa := hQ a (by simp); have qb := hQ b (by simp)
      obtain ⟨v₃, r₃⟩ := copy_all R₀ (pu := e u) (pv := e v₀) (pa := e a) (pb := e b)
        (RU := bitEncode us) (RV := bitEncode vs) (RA := bitEncode as) (RB := bitEncode bs)
        (be_cons u us) (be_cons v₀ vs) (be_cons a as) (be_cons b bs) v₂
      obtain ⟨v₄, r₄⟩ := single_reaches (x₁ := u) (x₂ := v₀) (x₃ := a) (x₄ := b) (Q := Q)
        (r := { R₀ with
          U := bitEncode us, V := bitEncode vs, A := bitEncode as, B := bitEncode bs
          HU := e u ++ R₀.HU, HV := e v₀ ++ R₀.HV, HA := e a ++ R₀.HA, HB := e b ++ R₀.HB })
        (List.append_nil _) (List.append_nil _) (List.append_nil _) (List.append_nil _)
        (n := n) (K := K) rfl rfl qu qv qa qb v₃
      have hwt : wt (u :: us) (v₀ :: vs) (a :: as) (b :: bs) =
          wt us vs as bs + (2 * (e u).length + 1) + (2 * (e v₀).length + 1) +
            (2 * (e a).length + 1) + (2 * (e b).length + 1) := by
        simp [wt, be_cons]; omega
      have hml : us.length ≤ L := by
        have := length_le_be us
        simp only [wt] at hwt hw
        omega
      have hout : outerP n K (u :: us) (v₀ :: vs) (a :: as) (b :: bs) =
          (single n K (u, v₀, a, b) && innerP (u, v₀, a, b) us vs as bs &&
            outerP n K us vs as bs) := rfl
      have hPa : us.length * (44 * Q + 56) ≤ L * (44 * L + 56) :=
        Nat.mul_le_mul hml (by omega)
      have hsplit : (us.length + 1 + 1) * (200 * (L + 1) * (L + 1)) =
          (us.length + 1) * (200 * (L + 1) * (L + 1)) + 200 * (L + 1) * (L + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hbig : L * (44 * L + 56) + 37 * L + 100 ≤ 200 * (L + 1) * (L + 1) := by nlinarith
      cases hs : single n K (u, v₀, a, b)
      · rw [hs] at r₄
        rw [hout, hs]
        refine ⟨v₄, _, (((r₁.trans r₂).trans r₃).trans r₄).mono ?_⟩
        simp only [List.length_cons]
        nlinarith
      · rw [hs] at r₄
        obtain ⟨v₅, S', r₅, hS'⟩ := inner_run (e n) (e K) (e u ++ []) (e v₀ ++ []) (e a ++ [])
          (e b ++ []) Z u v₀ a b Q (List.append_nil _) (List.append_nil _) (List.append_nil _)
          (List.append_nil _) us vs as bs [] [] [] [] hl₁ hl₂ hq' v₄
        cases hi : innerP (u, v₀, a, b) us vs as bs
        · rw [hi] at r₅
          rw [hout, hs, hi]
          refine ⟨v₅, _, ((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).mono ?_⟩
          simp only [List.length_cons]
          nlinarith
        · rw [hi] at r₅
          obtain ⟨U', V', A', B', TU', TV', TA', TB', h₀, h₁, h₂, h₃, h₄⟩ := hS' hi
          subst h₀
          simp only [List.reverse_nil, List.nil_append] at h₁ h₂ h₃ h₄
          obtain ⟨v₆, r₆⟩ := restore_all ⟨e n, e K, U', V', A', B', e u ++ [], e v₀ ++ [],
            e a ++ [], e b ++ [], TU', TV', TA', TB', Z⟩ v₅
          have hR : restoreRegs ⟨e n, e K, U', V', A', B', e u ++ [], e v₀ ++ [],
              e a ++ [], e b ++ [], TU', TV', TA', TB', Z⟩ = ⟨e n, e K, bitEncode us,
              bitEncode vs, bitEncode as, bitEncode bs, [], [], [], [], [], [], [], [],
              (e b ++ []).reverse ++ ((e a ++ []).reverse ++ ((e v₀ ++ []).reverse ++
                ((e u ++ []).reverse ++ Z)))⟩ := by
            simp only [restoreRegs, h₁, h₂, h₃, h₄]
          rw [hR] at r₆
          obtain ⟨v₇, S'', r₇⟩ :=
            ih vs as bs _ hl₁ hl₂ hq' (by simp only [wt] at hwt hw ⊢; omega) v₆
          rw [hout, hs, hi, Bool.true_and, Bool.true_and]
          refine ⟨v₇, S'', (((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans
            (r₆.trans r₇)).mono ?_⟩
          have l₁ := congrArg List.length h₁; have l₂ := congrArg List.length h₂
          have l₃ := congrArg List.length h₃; have l₄ := congrArg List.length h₄
          simp only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero,
            List.length_cons] at l₁ l₂ l₃ l₄ ⊢
          simp only [wt] at hwt hw
          nlinarith

theorem enc_le_be {y : ℕ} {us : List ℕ} (h : y ∈ us) : (e y).length ≤ (bitEncode us).length := by
  induction us with
  | nil => simp at h
  | cons u us ih =>
    rw [be_cons, List.length_append, length_delimit]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem encodeNat_eq_nil_iff (n : ℕ) : e n = [] ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [TM2Recursive.encodeNat_eq_cons hn] at h
    simp at h
  · rintro rfl; rfl

/-- The initial registers of the check phase. -/
def initRegs (n K : ℕ) (us vs as bs : List ℕ) : Regs :=
  ⟨e n, e K, bitEncode us, bitEncode vs, bitEncode as, bitEncode bs,
    [], [], [], [], [], [], [], [], []⟩

/-- The step bound of the check phase. -/
def checkBound (W : ℕ) : ℕ := (W + 1) * (200 * (W + 1) * (W + 1)) + 2

theorem check_run (n K : ℕ) (us vs as bs : List ℕ) (hl₁ : us.length = vs.length)
    (hl₂ : as.length = bs.length) (v : Bool) :
    ∃ v' S', RunLe prog (checkBound (wt us vs as bs)) ⟨some .start, v,
      (initRegs n K us vs as bs).stk⟩ ⟨some (cond (checkP n K us vs as bs) .yes .no), v', S'⟩ := by
  set W := wt us vs as bs with hW
  have hq : ∀ y ∈ us ++ vs ++ as ++ bs, (e y).length ≤ W := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with ((hy | hy) | hy) | hy
    · have := enc_le_be hy; simp only [hW, wt]; omega
    · have := enc_le_be hy; simp only [hW, wt]; omega
    · have := enc_le_be hy; simp only [hW, wt]; omega
    · have := enc_le_be hy; simp only [hW, wt]; omega
  have hml : us.length ≤ W := by have := length_le_be us; simp only [hW, wt]; omega
  have ro := outer_run n K W W le_rfl us vs as bs [] hl₁ hl₂ hq le_rfl
  have hmono : (us.length + 1) * (200 * (W + 1) * (W + 1)) ≤
      (W + 1) * (200 * (W + 1) * (W + 1)) := Nat.mul_le_mul_right _ (by omega)
  unfold checkP
  by_cases hn : n = 0
  · subst hn
    obtain ⟨v₂, r₁⟩ := peek_em (l := .start) (k := .N) (ne := .zK) (em := .oh) rfl v
      (S := (initRegs 0 K us vs as bs).stk) rfl
    obtain ⟨v₃, S₃, r₂⟩ := ro v₂
    refine ⟨v₃, S₃, (r₁.trans r₂).mono ?_⟩
    · simp only [checkBound]; omega
  · obtain ⟨v₂, r₁⟩ := peek_ne (l := .start) (k := .N) (ne := .zK) (em := .oh) rfl v
      (S := (initRegs n K us vs as bs).stk) (fun h => hn ((encodeNat_eq_nil_iff n).1 h))
    by_cases hK : K = 0
    · subst hK
      obtain ⟨v₃, r₂⟩ := peek_em (l := .zK) (k := .Kc) (ne := .oh) (em := .no) rfl v₂
        (S := (initRegs n 0 us vs as bs).stk) rfl
      have hc : (n == 0 || 0 != 0) = false := by simp [hn]
      rw [hc, Bool.false_and]
      refine ⟨v₃, _, (r₁.trans r₂).mono ?_⟩
      · simp only [checkBound]; omega
    · obtain ⟨v₃, r₂⟩ := peek_ne (l := .zK) (k := .Kc) (ne := .oh) (em := .no) rfl v₂
        (S := (initRegs n K us vs as bs).stk) (fun h => hK ((encodeNat_eq_nil_iff K).1 h))
      obtain ⟨v₄, S₄, r₃⟩ := ro v₃
      have hc : (n == 0 || K != 0) = true := by simp [hK]
      rw [hc, Bool.true_and]
      refine ⟨v₄, S₄, ((r₁.trans r₂).trans r₃).mono ?_⟩
      · simp only [checkBound]; omega

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Check

/-!
## The GRAPH COLORING verifier machine

The verifier component decodes `x` (the canonical encoding of `n × E × K`) with the existing
pair splitter, Nat normalizer and Nat-pair list projector, decodes the witness `w` (a list of
color pairs) with the projector, and runs the check phase `Check.prog` on the canonical results.
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Top

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF

/-- The stacks: the raw input and witness, the two raw first fields, the splitter scratch, the
normalizer buffer, the projector accumulators and workspace, and the check-phase stacks. -/
inductive TK | X | W | P1 | P2 | SC | BF | LA (b : Bool) | NP (k : NatPair.K) | C (k : Check.K)
  deriving DecidableEq

/-- Every stack is named by a small sum type. -/
def tkOf : (Fin 6 ⊕ Bool ⊕ NatPair.K ⊕ Check.K) → TK
  | .inl i => match i with | 0 => .X | 1 => .W | 2 => .P1 | 3 => .P2 | 4 => .SC | _ => .BF
  | .inr (.inl b) => .LA b
  | .inr (.inr (.inl k)) => .NP k
  | .inr (.inr (.inr k)) => .C k

instance : Fintype TK :=
  Fintype.ofSurjective tkOf fun k => by
    cases k with
    | X => exact ⟨.inl 0, rfl⟩
    | W => exact ⟨.inl 1, rfl⟩
    | P1 => exact ⟨.inl 2, rfl⟩
    | P2 => exact ⟨.inl 3, rfl⟩
    | SC => exact ⟨.inl 4, rfl⟩
    | BF => exact ⟨.inl 5, rfl⟩
    | LA b => exact ⟨.inr (.inl b), rfl⟩
    | NP k => exact ⟨.inr (.inr (.inl k)), rfl⟩
    | C k => exact ⟨.inr (.inr (.inr k)), rfl⟩

/-- The labels: the six decoding phases, the check phase, and the outcomes. -/
inductive TL | s1 (l : PairSplit.Lab) | n1 (l : NormalizeMachine.Lab) | s2 (l : PairSplit.Lab)
  | it (l : ListNatPair.Lab) | n2 (l : NormalizeMachine.Lab) | wi (l : ListNatPair.Lab)
  | ck (l : Check.Lab) | yes | no
  deriving DecidableEq

/-- Every label is named by a small sum type. -/
def tlOf : (PairSplit.Lab ⊕ NormalizeMachine.Lab ⊕ PairSplit.Lab ⊕ ListNatPair.Lab ⊕
    NormalizeMachine.Lab ⊕ ListNatPair.Lab ⊕ Check.Lab ⊕ Bool) → TL
  | .inl l => .s1 l
  | .inr (.inl l) => .n1 l
  | .inr (.inr (.inl l)) => .s2 l
  | .inr (.inr (.inr (.inl l))) => .it l
  | .inr (.inr (.inr (.inr (.inl l)))) => .n2 l
  | .inr (.inr (.inr (.inr (.inr (.inl l))))) => .wi l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))) => .ck l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr b)))))) => if b then .yes else .no

instance : Fintype TL :=
  Fintype.ofSurjective tlOf fun l => by
    cases l with
    | s1 l => exact ⟨.inl l, rfl⟩
    | n1 l => exact ⟨.inr (.inl l), rfl⟩
    | s2 l => exact ⟨.inr (.inr (.inl l)), rfl⟩
    | it l => exact ⟨.inr (.inr (.inr (.inl l))), rfl⟩
    | n2 l => exact ⟨.inr (.inr (.inr (.inr (.inl l)))), rfl⟩
    | wi l => exact ⟨.inr (.inr (.inr (.inr (.inr (.inl l))))), rfl⟩
    | ck l => exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))), rfl⟩
    | yes => exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr true)))))), rfl⟩
    | no => exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr false)))))), rfl⟩

/-! ### Embeddings -/

/-- The first split reads `X` into `P1`. -/
def s1E : SEmb (fun _ : PairSplit.K => Bool) (fun _ : TK => Bool) where
  e | .input => .X | .left => .P1 | .scratch => .SC
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The second split reads `X` into `P2`. -/
def s2E : SEmb (fun _ : PairSplit.K => Bool) (fun _ : TK => Bool) where
  e | .input => .X | .left => .P2 | .scratch => .SC
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The first normalization turns `P1` into `N`. -/
def n1E : SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : TK => Bool) where
  e | .input => .P1 | .buffer => .BF | .output => .C .N
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The second normalization turns the rest of `X` into `Kc`. -/
def n2E : SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : TK => Bool) where
  e | .input => .X | .buffer => .BF | .output => .C .Kc
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The edge projection turns `P2` into `U` and `V`. -/
def itE : SEmb (fun _ : ListNatPair.K => Bool) (fun _ : TK => Bool) where
  e | .input => .P2 | .acc b => .LA b | .output false => .C .U | .output true => .C .V
    | .pair k => .NP k
  inj a b h := by
    rcases a with _ | a | a | a <;> rcases b with _ | b | b | b <;>
      (try cases a) <;> (try cases b) <;> simp_all
  ι _ := Equiv.refl Bool

/-- The color projection turns `W` into `A` and `B`. -/
def wiE : SEmb (fun _ : ListNatPair.K => Bool) (fun _ : TK => Bool) where
  e | .input => .W | .acc b => .LA b | .output false => .C .A | .output true => .C .B
    | .pair k => .NP k
  inj a b h := by
    rcases a with _ | a | a | a <;> rcases b with _ | b | b | b <;>
      (try cases a) <;> (try cases b) <;> simp_all
  ι _ := Equiv.refl Bool

/-- The check phase runs on the `C` stacks. -/
def ckE : SEmb (fun _ : Check.K => Bool) (fun _ : TK => Bool) where
  e := TK.C
  inj _ _ h := TK.C.inj h
  ι _ := Equiv.refl Bool

/-! ### Label maps and the program -/

def s1L : PairSplit.Lab → TL | .good => .n1 (.read none) | .bad => .no | l => .s1 l
def n1L : NormalizeMachine.Lab → TL | .done => .s2 .read | l => .n1 l
def s2L : PairSplit.Lab → TL | .good => .it .loop | .bad => .no | l => .s2 l
def itL : ListNatPair.Lab → TL | .good => .n2 (.read none) | .bad => .no | l => .it l
def n2L : NormalizeMachine.Lab → TL | .done => .wi .loop | l => .n2 l
def wiL : ListNatPair.Lab → TL | .good => .ck .start | .bad => .no | l => .wi l
def ckL : Check.Lab → TL | .yes => .yes | .no => .no | l => .ck l

/-- The verifier program. -/
def prog : TL → TM2.Stmt (fun _ : TK => Bool) TL Bool
  | .s1 l => mapS s1E s1L (PairSplit.prog l)
  | .n1 l => mapS n1E n1L (NormalizeMachine.prog l)
  | .s2 l => mapS s2E s2L (PairSplit.prog l)
  | .it l => mapS itE itL (ListNatPair.prog l)
  | .n2 l => mapS n2E n2L (NormalizeMachine.prog l)
  | .wi l => mapS wiE wiL (ListNatPair.prog l)
  | .ck l => mapS ckE ckL (Check.prog l)
  | .yes | .no => .halt

theorem embeds_s1 : Embeds s1E s1L PairSplit.prog prog := by
  intro l; cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

theorem embeds_s2 : Embeds s2E s2L PairSplit.prog prog := by
  intro l; cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

theorem embeds_n1 : Embeds n1E n1L NormalizeMachine.prog prog := by
  intro l; cases l with
  | read _ | copy => exact Or.inl rfl
  | done => exact Or.inr rfl

theorem embeds_n2 : Embeds n2E n2L NormalizeMachine.prog prog := by
  intro l; cases l with
  | read _ | copy => exact Or.inl rfl
  | done => exact Or.inr rfl

theorem embeds_it : Embeds itE itL ListNatPair.prog prog := by
  intro l; cases l with
  | loop | block | back | pair _ | emit _ | finish _ => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

theorem embeds_wi : Embeds wiE wiL ListNatPair.prog prog := by
  intro l; cases l with
  | loop | block | back | pair _ | emit _ | finish _ => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

theorem embeds_ck : Embeds ckE ckL Check.prog prog := by
  intro l; cases l with
  | yes | no => exact Or.inr rfl
  | _ => exact Or.inl rfl

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Top

/-!
## Runs of the GRAPH COLORING verifier machine: the phases
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Top

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF

/-- Stack contents: raw input and witness, the two raw first fields, check-phase stacks `C`, and
empty scratch. -/
def tst (x w p₁ p₂ : List Bool) (C : Check.K → List Bool) : TK → List Bool
  | .X => x | .W => w | .P1 => p₁ | .P2 => p₂ | .C k => C k | _ => []

theorem s1_good (p r w : List Bool) (C : Check.K → List Bool) (v : Bool) :
    ∃ v', RunLe prog ((delimit p ++ r).length + 1)
      ⟨some (.s1 .read), v, tst (delimit p ++ r) w [] [] C⟩
      ⟨some (.n1 (.read none)), v', tst r w p [] C⟩ := by
  obtain ⟨v', T, hr, hf, ha⟩ := PairSplit.run_embedded s1E s1L embeds_s1 (delimit p ++ r) v
    (tst (delimit p ++ r) w [] [] C) (by intro k; cases k <;> simp [s1E, PairSplit.st, tst])
  have hu : undelimit (delimit p ++ r) = some (p, r) := undelimit_delimit p r
  have ha := ha p r hu
  rw [hu] at hr
  have he : T = tst r w p [] C := by
    funext k
    cases k with
    | X => simpa [s1E, PairSplit.st, tst] using ha .input
    | P1 => simpa [s1E, PairSplit.st, tst] using ha .left
    | SC => simpa [s1E, PairSplit.st, tst] using ha .scratch
    | _ => exact hf _ (by intro j; cases j <;> simp [s1E])
  exact ⟨v', he ▸ hr⟩

theorem s1_bad {x : List Bool} (h : undelimit x = none) (w : List Bool) (C : Check.K → List Bool)
    (v : Bool) : ∃ v' T, RunLe prog (x.length + 1) ⟨some (.s1 .read), v, tst x w [] [] C⟩
      ⟨some .no, v', T⟩ := by
  obtain ⟨v', T, hr, -, -⟩ := PairSplit.run_embedded s1E s1L embeds_s1 x v
    (tst x w [] [] C) (by intro k; cases k <;> simp [s1E, PairSplit.st, tst])
  rw [h] at hr
  exact ⟨v', T, hr⟩

theorem s2_good (p r w : List Bool) (C : Check.K → List Bool) (v : Bool) :
    ∃ v', RunLe prog ((delimit p ++ r).length + 1)
      ⟨some (.s2 .read), v, tst (delimit p ++ r) w [] [] C⟩
      ⟨some (.it .loop), v', tst r w [] p C⟩ := by
  obtain ⟨v', T, hr, hf, ha⟩ := PairSplit.run_embedded s2E s2L embeds_s2 (delimit p ++ r) v
    (tst (delimit p ++ r) w [] [] C) (by intro k; cases k <;> simp [s2E, PairSplit.st, tst])
  have hu : undelimit (delimit p ++ r) = some (p, r) := undelimit_delimit p r
  have ha := ha p r hu
  rw [hu] at hr
  have he : T = tst r w [] p C := by
    funext k
    cases k with
    | X => simpa [s2E, PairSplit.st, tst] using ha .input
    | P2 => simpa [s2E, PairSplit.st, tst] using ha .left
    | SC => simpa [s2E, PairSplit.st, tst] using ha .scratch
    | _ => exact hf _ (by intro j; cases j <;> simp [s2E])
  exact ⟨v', he ▸ hr⟩

theorem s2_bad {x : List Bool} (h : undelimit x = none) (w : List Bool) (C : Check.K → List Bool)
    (v : Bool) : ∃ v' T, RunLe prog (x.length + 1) ⟨some (.s2 .read), v, tst x w [] [] C⟩
      ⟨some .no, v', T⟩ := by
  obtain ⟨v', T, hr, -, -⟩ := PairSplit.run_embedded s2E s2L embeds_s2 x v
    (tst x w [] [] C) (by intro k; cases k <;> simp [s2E, PairSplit.st, tst])
  rw [h] at hr
  exact ⟨v', T, hr⟩

theorem n1_run (p r w : List Bool) (C : Check.K → List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * p.length + 3) ⟨some (.n1 (.read none)), v, tst r w p [] C⟩
      ⟨some (.s2 .read), v', tst r w [] [] (update C .N (normalizeNat p ++ C .N))⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame p (C .N) v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed n1L embeds_n1 hr (S' := tst r w p [] C)
    (by intro k; cases k <;> simp [n1E, NormalizeMachine.st, tst])
  have he : T = tst r w [] [] (update C .N (normalizeNat p ++ C .N)) := by
    funext k
    cases k with
    | P1 => simpa [n1E, NormalizeMachine.st, tst] using ha .input
    | BF => simpa [n1E, NormalizeMachine.st, tst] using ha .buffer
    | C k =>
      by_cases hk : k = .N
      · subst hk; simpa [n1E, NormalizeMachine.st, tst] using ha .output
      · rw [hf _ (by intro j; cases j <;> simp [n1E, Ne.symm hk])]
        simp [tst, hk]
    | _ => exact hf _ (by intro j; cases j <;> simp [n1E])
  exact ⟨v', he ▸ ht⟩

theorem n2_run (r w : List Bool) (C : Check.K → List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * r.length + 3) ⟨some (.n2 (.read none)), v, tst r w [] [] C⟩
      ⟨some (.wi .loop), v', tst [] w [] [] (update C .Kc (normalizeNat r ++ C .Kc))⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame r (C .Kc) v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed n2L embeds_n2 hr (S' := tst r w [] [] C)
    (by intro k; cases k <;> simp [n2E, NormalizeMachine.st, tst])
  have he : T = tst [] w [] [] (update C .Kc (normalizeNat r ++ C .Kc)) := by
    funext k
    cases k with
    | X => simpa [n2E, NormalizeMachine.st, tst] using ha .input
    | BF => simpa [n2E, NormalizeMachine.st, tst] using ha .buffer
    | C k =>
      by_cases hk : k = .Kc
      · subst hk; simpa [n2E, NormalizeMachine.st, tst] using ha .output
      · rw [hf _ (by intro j; cases j <;> simp [n2E, Ne.symm hk])]
        simp [tst, hk]
    | _ => exact hf _ (by intro j; cases j <;> simp [n2E])
  exact ⟨v', he ▸ ht⟩

theorem it_run (p r w : List Bool) (C : Check.K → List Bool) (hU : C .U = []) (hV : C .V = [])
    (v : Bool) : ∃ v' T, RunLe prog (16 * p.length + 3) ⟨some (.it .loop), v, tst r w [] p C⟩
      ⟨some (itL (if (bitDecode (α := List (ℕ × ℕ)) p).isSome then .good else .bad)), v', T⟩ ∧
      ∀ es : List (ℕ × ℕ), bitDecode p = some es →
        T = tst r w [] [] (update (update C .U (bitEncode (es.map Prod.fst))) .V
          (bitEncode (es.map Prod.snd))) := by
  obtain ⟨v', T, hr, hf, ha⟩ := ListNatPair.run_embedded itE itL embeds_it p v (tst r w [] p C)
    (by
      intro k
      rcases k with _ | b | b | k
      · simp [itE, ListNatPair.st, tst]
      · simp [itE, ListNatPair.st, tst]
      · cases b <;> simp [itE, ListNatPair.st, tst, hU, hV]
      · rcases k with k | _ | _ | _ <;> (try cases k) <;>
          simp [itE, ListNatPair.st, NatPair.st, tst])
  refine ⟨v', T, hr, fun es hes => ?_⟩
  have ha := ha es hes
  funext k
  cases k with
  | P2 => simpa [itE, ListNatPair.st, tst] using ha .input
  | LA b => simpa [itE, ListNatPair.st, tst] using ha (.acc b)
  | NP k =>
    have := ha (.pair k)
    rcases k with k | _ | _ | _ <;> (try cases k) <;>
      simpa [itE, ListNatPair.st, NatPair.st, PairSplit.st, tst] using this
  | C k =>
    by_cases h₁ : k = .U
    · subst h₁; simpa [itE, ListNatPair.st, tst] using ha (.output false)
    · by_cases h₂ : k = .V
      · subst h₂; simpa [itE, ListNatPair.st, tst] using ha (.output true)
      · rw [hf _ (by
          intro j
          rcases j with _ | b | b | j <;> (try cases b) <;> simp [itE, Ne.symm h₁, Ne.symm h₂])]
        simp [tst, h₁, h₂]
  | _ => exact hf _ (by intro j; rcases j with _ | b | b | j <;> (try cases b) <;> simp [itE])

theorem wi_run (w : List Bool) (C : Check.K → List Bool) (hA : C .A = []) (hB : C .B = [])
    (v : Bool) : ∃ v' T, RunLe prog (16 * w.length + 3) ⟨some (.wi .loop), v, tst [] w [] [] C⟩
      ⟨some (wiL (if (bitDecode (α := List (ℕ × ℕ)) w).isSome then .good else .bad)), v', T⟩ ∧
      ∀ cs : List (ℕ × ℕ), bitDecode w = some cs →
        T = tst [] [] [] [] (update (update C .A (bitEncode (cs.map Prod.fst))) .B
          (bitEncode (cs.map Prod.snd))) := by
  obtain ⟨v', T, hr, hf, ha⟩ := ListNatPair.run_embedded wiE wiL embeds_wi w v (tst [] w [] [] C)
    (by
      intro k
      rcases k with _ | b | b | k
      · simp [wiE, ListNatPair.st, tst]
      · simp [wiE, ListNatPair.st, tst]
      · cases b <;> simp [wiE, ListNatPair.st, tst, hA, hB]
      · rcases k with k | _ | _ | _ <;> (try cases k) <;>
          simp [wiE, ListNatPair.st, NatPair.st, tst])
  refine ⟨v', T, hr, fun cs hcs => ?_⟩
  have ha := ha cs hcs
  funext k
  cases k with
  | W => simpa [wiE, ListNatPair.st, tst] using ha .input
  | LA b => simpa [wiE, ListNatPair.st, tst] using ha (.acc b)
  | NP k =>
    have := ha (.pair k)
    rcases k with k | _ | _ | _ <;> (try cases k) <;>
      simpa [wiE, ListNatPair.st, NatPair.st, PairSplit.st, tst] using this
  | C k =>
    by_cases h₁ : k = .A
    · subst h₁; simpa [wiE, ListNatPair.st, tst] using ha (.output false)
    · by_cases h₂ : k = .B
      · subst h₂; simpa [wiE, ListNatPair.st, tst] using ha (.output true)
      · rw [hf _ (by
          intro j
          rcases j with _ | b | b | j <;> (try cases b) <;> simp [wiE, Ne.symm h₁, Ne.symm h₂])]
        simp [tst, h₁, h₂]
  | _ => exact hf _ (by intro j; rcases j with _ | b | b | j <;> (try cases b) <;> simp [wiE])

theorem ck_run (n K : ℕ) (us vs as bs : List ℕ) (hl₁ : us.length = vs.length)
    (hl₂ : as.length = bs.length) (v : Bool) :
    ∃ v' T, RunLe prog (Check.checkBound (Check.wt us vs as bs)) ⟨some (.ck .start), v,
      tst [] [] [] [] (Check.initRegs n K us vs as bs).stk⟩
      ⟨some (if checkP n K us vs as bs then .yes else .no), v', T⟩ := by
  obtain ⟨v', S', hr⟩ := Check.check_run n K us vs as bs hl₁ hl₂ v
  obtain ⟨T, ht, -, -⟩ := runLe_embed ckL embeds_ck hr
    (S' := tst [] [] [] [] (Check.initRegs n K us vs as bs).stk) (by intro k; simp [ckE, tst])
  refine ⟨v', T, ?_⟩
  cases h : checkP n K us vs as bs <;> rw [h] at ht <;> exact ht

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Top

/-!
## GRAPH COLORING is in NP

`full_run`: the verifier machine, started on `x` and `w`, reaches `yes` exactly when
`gcCheck x w`, within a polynomial number of steps. The generic verifier host turns it into
polynomial-time computability of `gcCheck` (`isPolyTime_gcCheck`), and the certificate
characterization gives `graphColoringDec_mem_NP`.
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Top

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF

theorem decode_delimit_append {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (p r : List Bool) :
    bitDecode (α := α × β) (delimit p ++ r) =
      (bitDecode (α := α) p).bind fun a => (bitDecode (α := β) r).map fun b => (a, b) := by
  change (match undelimit (delimit p ++ r) with
    | none => none
    | some (p, r) => match bitDecode (α := α) p, bitDecode (α := β) r with
      | some a, some b => some (a, b)
      | _, _ => none) = _
  rw [undelimit_delimit]
  dsimp only
  cases bitDecode (α := α) p <;> cases bitDecode (α := β) r <;> rfl

theorem decode_pair_none {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {x : List Bool} (h : undelimit x = none) : bitDecode (α := α × β) x = none := by
  change (match undelimit x with
    | none => none
    | some (p, r) => match bitDecode (α := α) p, bitDecode (α := β) r with
      | some a, some b => some (a, b)
      | _, _ => none) = _
  rw [h]

theorem decode_nat (p : List Bool) : bitDecode (α := ℕ) p = some (Computability.decodeNat p) :=
  rfl

theorem checkBound_mono {W W' : ℕ} (h : W ≤ W') : Check.checkBound W ≤ Check.checkBound W' := by
  unfold Check.checkBound
  have h1 : W + 1 ≤ W' + 1 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h1)) _

/-- The step bound of the verifier. -/
noncomputable def bound : Polynomial ℕ :=
  Polynomial.C 40 * Polynomial.X + Polynomial.C 22 +
    (Polynomial.C 4 * Polynomial.X + 1) *
      (Polynomial.C 200 * (Polynomial.C 4 * Polynomial.X + 1) * (Polynomial.C 4 * Polynomial.X + 1))

theorem eval_bound (n : ℕ) : bound.eval n = 40 * n + 20 + Check.checkBound (4 * n) := by
  simp [bound, Check.checkBound]
  ring

theorem full_run (x w : List Bool) :
    ∃ v S', RunLe prog (bound.eval (x.length + w.length))
      ⟨some (.s1 .read), false, update (update (fun _ => []) TK.X (x.map id)) TK.W (w.map id)⟩
      ⟨some (if gcCheck x w then .yes else .no), v, S'⟩ := by
  have h0 : update (update (fun _ => ([] : List Bool)) TK.X (x.map id)) TK.W (w.map id) =
      tst x w [] [] (fun _ => []) := by
    funext k; cases k <;> simp [tst]
  rw [h0, eval_bound]
  have hmono : ∀ W, W ≤ 4 * (x.length + w.length) →
      Check.checkBound W ≤ Check.checkBound (4 * (x.length + w.length)) :=
    fun W h => checkBound_mono h
  have hcb : 0 ≤ Check.checkBound (4 * (x.length + w.length)) := Nat.zero_le _
  have hno : ∀ {B : ℕ} {v : Bool} {T : TK → List Bool}, gcCheck x w = false →
      B ≤ 40 * (x.length + w.length) + 20 →
      RunLe prog B ⟨some (.s1 .read), false, tst x w [] [] (fun _ => [])⟩ ⟨some .no, v, T⟩ →
      ∃ v S', RunLe prog (40 * (x.length + w.length) + 20 +
          Check.checkBound (4 * (x.length + w.length)))
        ⟨some (.s1 .read), false, tst x w [] [] (fun _ => [])⟩
        ⟨some (if gcCheck x w then .yes else .no), v, S'⟩ := by
    intro B v T hg hB hr
    refine ⟨v, T, ?_⟩
    rw [hg]
    exact hr.mono (by omega)
  cases hux : undelimit x with
  | none =>
    obtain ⟨v₁, T, r₁⟩ := s1_bad hux w (fun _ => []) false
    exact hno (by simp [gcCheck, decode_pair_none hux]) (by omega) r₁
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).1 hux
    have hlx : x.length = 2 * p.length + 1 + r.length := by
      rw [hx, List.length_append, length_delimit]
    obtain ⟨v₁, r₁⟩ := s1_good p r w (fun _ => []) false
    rw [← hx] at r₁
    obtain ⟨v₂, r₂⟩ := n1_run p r w (fun _ => []) v₁
    cases hur : undelimit r with
    | none =>
      obtain ⟨v₃, T, r₃⟩ := s2_bad hur w _ v₂
      refine hno (by simp [gcCheck, hx, decode_delimit_append, decode_nat,
        decode_pair_none hur]) ?_ ((r₁.trans r₂).trans r₃)
      omega
    | some pr₂ =>
      obtain ⟨p₂, r₂'⟩ := pr₂
      have hr := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).1 hur
      have hlr : r.length = 2 * p₂.length + 1 + r₂'.length := by
        rw [hr, List.length_append, length_delimit]
      obtain ⟨v₃, r₃⟩ := s2_good p₂ r₂' w _ v₂
      rw [← hr] at r₃
      obtain ⟨v₄, T₄, r₄, h₄⟩ := it_run p₂ r₂' w
        (update (fun _ => ([] : List Bool)) Check.K.N (normalizeNat p ++ [])) (by simp)
        (by simp) v₃
      cases hp₂ : bitDecode (α := List (ℕ × ℕ)) p₂ with
      | none =>
        rw [hp₂] at r₄
        refine hno (by simp [gcCheck, hx, hr, decode_delimit_append, decode_nat, hp₂]) ?_
          (((r₁.trans r₂).trans r₃).trans r₄)
        omega
      | some es =>
        rw [hp₂] at r₄
        rw [h₄ es hp₂] at r₄
        obtain ⟨v₅, r₅⟩ := n2_run r₂' w _ v₄
        obtain ⟨v₆, T₆, r₆, h₆⟩ := wi_run w
          (update (update (update (update (fun _ => ([] : List Bool)) Check.K.N
            (normalizeNat p ++ [])) Check.K.U (bitEncode (es.map Prod.fst))) Check.K.V
            (bitEncode (es.map Prod.snd))) Check.K.Kc
            (normalizeNat r₂' ++ update (update (update (fun _ => ([] : List Bool))
              Check.K.N (normalizeNat p ++ [])) Check.K.U (bitEncode (es.map Prod.fst)))
              Check.K.V (bitEncode (es.map Prod.snd)) Check.K.Kc)) (by simp) (by simp) v₅
        cases hw : bitDecode (α := List (ℕ × ℕ)) w with
        | none =>
          rw [hw] at r₆
          refine hno (by simp [gcCheck, hw]) ?_
            (((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆)
          omega
        | some cs =>
          rw [hw] at r₆
          rw [h₆ cs hw] at r₆
          have hl₁ : (es.map Prod.fst).length = (es.map Prod.snd).length := by simp
          have hl₂ : (cs.map Prod.fst).length = (cs.map Prod.snd).length := by simp
          obtain ⟨v₇, T₇, r₇⟩ := ck_run (Computability.decodeNat p) (Computability.decodeNat r₂')
            (es.map Prod.fst) (es.map Prod.snd) (cs.map Prod.fst) (cs.map Prod.snd) hl₁ hl₂ v₆
          have hC : update (update (update (update (update (update (fun _ => ([] : List Bool))
              Check.K.N (normalizeNat p ++ [])) Check.K.U (bitEncode (es.map Prod.fst)))
              Check.K.V (bitEncode (es.map Prod.snd))) Check.K.Kc
              (normalizeNat r₂' ++ update (update (update (fun _ => ([] : List Bool))
                Check.K.N (normalizeNat p ++ [])) Check.K.U (bitEncode (es.map Prod.fst)))
                Check.K.V (bitEncode (es.map Prod.snd)) Check.K.Kc)) Check.K.A
              (bitEncode (cs.map Prod.fst))) Check.K.B (bitEncode (cs.map Prod.snd)) =
              (Check.initRegs (Computability.decodeNat p) (Computability.decodeNat r₂')
                (es.map Prod.fst) (es.map Prod.snd) (cs.map Prod.fst)
                (cs.map Prod.snd)).stk := by
            funext k
            cases k <;> simp [Check.initRegs, Check.Regs.stk, normalizeNat_eq_encode_decode]
          rw [hC] at r₆
          have hg : gcCheck x w = checkP (Computability.decodeNat p)
              (Computability.decodeNat r₂') (es.map Prod.fst) (es.map Prod.snd)
              (cs.map Prod.fst) (cs.map Prod.snd) := by
            rw [checkP_eq_ok]
            simp [gcCheck, hx, hr, decode_delimit_append, decode_nat, hp₂, hw]
          rw [hg]
          refine ⟨v₇, T₇, ((((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).trans
            r₇).mono ?_⟩
          have hpe := ListNatPair.projection_length_le hp₂
          have hpw := ListNatPair.projection_length_le hw
          have hwt := hmono (Check.wt (es.map Prod.fst) (es.map Prod.snd) (cs.map Prod.fst)
            (cs.map Prod.snd)) (by simp only [Check.wt]; omega)
          omega

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification.Top

/-!
## GRAPH COLORING is in NP: the host and the theorem
-/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification

/-- The verifier as a host component. -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := Top.TK
  Γ := fun _ => Bool
  finΓ := fun _ => inferInstance
  L := Top.TL
  prog := Top.prog
  ks := (Finset.univ : Finset Top.TK).toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := Finset.mem_toList.2 (Finset.mem_univ k)

/-- The certificate check is computable in polynomial time. -/
theorem isPolyTime_gcCheck :
    MetaMathlibExt.ComplexityTheory.IsPolyTime fun q : List Bool × List Bool =>
      gcCheck q.1 q.2 :=
  Cslib.Complexity.Host.isPolyTime_verifier (c := comp) (cX := Top.TK.X) (cW := Top.TK.W)
    (gX := id) (gW := id) (start := Top.TL.s1 .read) (yes := Top.TL.yes) (no := Top.TL.no)
    gcCheck Top.bound
    (by decide) (by decide) rfl rfl Top.full_run

/-- **GRAPH COLORING is in NP.** -/
theorem graphColoringDec_mem_NP : graphColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  graphColoringDec_mem_NP_of_isPolyTime isPolyTime_gcCheck

end MetaMathlibExt.Complexity.NPComplete.GraphColoring.Verification
