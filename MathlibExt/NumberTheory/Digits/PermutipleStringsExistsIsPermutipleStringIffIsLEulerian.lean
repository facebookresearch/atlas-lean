/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.PermutipleStrings
import MathlibExt.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringOfHasEulerianCircuitFromZero
import Mathlib.Data.Nat.Find

/-!
# The $L$-Eulerian criterion for permutiple strings

The existence of a permutiple string with prescribed cycle-edge multiplicities is equivalent
to the multi-image union being $L$-Eulerian. The converse direction builds an Eulerian circuit
through zero and applies `exists_isPermutipleString_of_hasEulerianCircuitFromZero`.

Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025),
Article A111 (arXiv:2505.11414).
-/

namespace MetaMathlibExt

private def EdgeWalk : ℕ → List (ℕ × ℕ) → ℕ → Prop
  | a, [], b => a = b
  | a, e :: w, b => a = e.1 ∧ EdgeWalk e.2 w b

private theorem walk_append {a b c : ℕ} {p q : List (ℕ × ℕ)}
    (hp : EdgeWalk a p b) (hq : EdgeWalk b q c) : EdgeWalk a (p ++ q) c := by
  induction p generalizing a with
  | nil =>
    have hab : a = b := hp
    subst a
    exact hq
  | cons e p ih => exact ⟨hp.1, ih hp.2⟩

private theorem walk_counts {a b : ℕ} {w : List (ℕ × ℕ)} (h : EdgeWalk a w b) (c : ℕ) :
    (w : Multiset (ℕ × ℕ)).countP (fun e => e.2 = c) + (if a = c then 1 else 0) =
      (w : Multiset (ℕ × ℕ)).countP (fun e => e.1 = c) + (if b = c then 1 else 0) := by
  induction w generalizing a with
  | nil => simp only [EdgeWalk] at h; simp [h]
  | cons e w ih =>
    obtain ⟨rfl, hw⟩ := h
    have hi := ih hw
    simp only [Multiset.coe_countP, List.countP_cons, decide_eq_true_eq] at hi ⊢
    split_ifs at hi ⊢ <;> omega

private theorem longest_walk (D : Multiset (ℕ × ℕ)) (a : ℕ) :
    ∃ w b, EdgeWalk a w b ∧ (w : Multiset (ℕ × ℕ)) ≤ D ∧
      ∀ w' b', EdgeWalk a w' b' → (w' : Multiset (ℕ × ℕ)) ≤ D → w'.length ≤ w.length := by
  classical
  let P (k : ℕ) := ∃ w b, EdgeWalk a w b ∧ (w : Multiset (ℕ × ℕ)) ≤ D ∧ w.length = k
  have hzero : P 0 := ⟨[], a, rfl, Multiset.zero_le _, rfl⟩
  obtain ⟨w, b, hw, hD, hlen⟩ := Nat.findGreatest_spec (Nat.zero_le D.card) hzero
  refine ⟨w, b, hw, hD, ?_⟩
  intro w' b' hw' hD'
  rw [hlen]
  apply Nat.le_findGreatest
  · simpa only [Multiset.coe_card] using Multiset.card_le_card hD'
  · exact ⟨w', b', hw', hD', rfl⟩

private theorem longest_walk_closed (D : Multiset (ℕ × ℕ))
    (hbal : ∀ c, D.countP (fun e => e.2 = c) = D.countP (fun e => e.1 = c))
    {a b : ℕ} {w : List (ℕ × ℕ)} (hw : EdgeWalk a w b) (hD : (w : Multiset (ℕ × ℕ)) ≤ D)
    (hmax : ∀ w' b', EdgeWalk a w' b' → (w' : Multiset (ℕ × ℕ)) ≤ D →
      w'.length ≤ w.length) : a = b := by
  have hstop : (D - (w : Multiset (ℕ × ℕ))).countP (fun e => e.1 = b) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro e he heq
    have hle : ((w ++ [e] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) ≤ D := by
      change (w : Multiset (ℕ × ℕ)) + {e} ≤ D
      simpa only [add_comm] using (le_tsub_iff_right hD).mp (Multiset.singleton_le.mpr he)
    have hlen := hmax (w ++ [e]) e.2 (walk_append hw ⟨heq.symm, rfl⟩) hle
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  have hout : (w : Multiset (ℕ × ℕ)).countP (fun e => e.1 = b) =
      D.countP (fun e => e.1 = b) := by
    rw [Multiset.countP_sub hD] at hstop
    have hle := Multiset.countP_le_of_le (fun e : ℕ × ℕ => e.1 = b) hD
    omega
  have hcount := walk_counts hw b
  have hin := Multiset.countP_le_of_le (fun e : ℕ × ℕ => e.2 = b) hD
  rw [hout, ← hbal b] at hcount
  by_contra hab
  simp only [hab, ↓reduceIte, add_zero] at hcount
  omega

private theorem walk_split {a b v : ℕ} {w : List (ℕ × ℕ)} (hw : EdgeWalk a w b)
    (hv : ∃ e ∈ w, e.1 = v ∨ e.2 = v) :
    ∃ p q, w = p ++ q ∧ EdgeWalk a p v ∧ EdgeWalk v q b := by
  induction w generalizing a with
  | nil => simp at hv
  | cons e w ih =>
    obtain ⟨rfl, hw⟩ := hw
    obtain ⟨f, hf, hv⟩ := hv
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases hv with hv | hv
      · exact ⟨[], f :: w, rfl, hv, ⟨hv.symm, hw⟩⟩
      · exact ⟨[f], w, rfl, ⟨rfl, hv⟩, hv ▸ hw⟩
    · obtain ⟨p, q, hpq, hp, hq⟩ := ih hw ⟨f, hf, hv⟩
      exact ⟨e :: p, q, by simp [hpq], ⟨rfl, hp⟩, hq⟩

private theorem walk_reaches (D : Multiset (ℕ × ℕ)) {a b : ℕ} {w : List (ℕ × ℕ)}
    (hw : EdgeWalk a w b) (hD : ∀ e ∈ w, e ∈ D) :
    Relation.ReflTransGen (fun x y => (x, y) ∈ D) a b := by
  induction w generalizing a with
  | nil => exact hw ▸ Relation.ReflTransGen.refl
  | cons e w ih =>
    obtain ⟨rfl, hw⟩ := hw
    exact (ih hw (fun f hf => hD f (List.mem_cons_of_mem e hf))).head
      (hD e (List.mem_cons_self))

private theorem walk_isLEulerian {w : List (ℕ × ℕ)} (hw : EdgeWalk 0 w 0) (hne : w ≠ []) :
    IsLEulerian (w : Multiset (ℕ × ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · cases w with
    | nil => exact (hne rfl).elim
    | cons e w => exact ⟨e, List.mem_cons_self, Or.inl hw.1.symm⟩
  · intro u v hu hv
    obtain ⟨p, q, hpq, hp, hq⟩ := walk_split hw hu
    obtain ⟨r, s, hrs, hr, hs⟩ := walk_split hw hv
    exact (walk_reaches _ hq (fun e he => by simp [hpq, he])).trans
      (walk_reaches _ hr (fun e he => by simp [hrs, he]))
  · intro c
    exact Nat.add_right_cancel (walk_counts hw c)

private theorem euler_walk (D : Multiset (ℕ × ℕ)) (h : IsLEulerian D) :
    ∃ w, w ≠ [] ∧ (w : Multiset (ℕ × ℕ)) = D ∧ EdgeWalk 0 w 0 := by
  classical
  obtain ⟨w, b, hw, hD, hmax⟩ := longest_walk D 0
  have hb := longest_walk_closed D h.2.2 hw hD hmax
  subst b
  have heq : (w : Multiset (ℕ × ℕ)) = D := by
    by_contra hne
    let R := D - (w : Multiset (ℕ × ℕ))
    have hpart : (w : Multiset (ℕ × ℕ)) + R = D := add_tsub_cancel_of_le hD
    have hR : R ≠ 0 := by
      intro hz
      exact hne (by simpa only [hz, add_zero] using hpart)
    have hbal : ∀ c, R.countP (fun e => e.2 = c) = R.countP (fun e => e.1 = c) := by
      intro c
      have hc := walk_counts hw c
      have hc' := Nat.add_right_cancel hc
      simp only [R, Multiset.countP_sub hD, h.2.2 c, hc']
    let V (v : ℕ) := v = 0 ∨ ∃ e ∈ w, e.1 = v ∨ e.2 = v
    have hhit : ∃ v, V v ∧ ∃ e ∈ R, e.1 = v := by
      by_contra hno
      push Not at hno
      have step {x y : ℕ} (hx : V x) (hxy : (x, y) ∈ D) : V y := by
        rw [← hpart] at hxy
        rcases Multiset.mem_add.mp hxy with he | he
        · exact Or.inr ⟨(x, y), he, Or.inr rfl⟩
        · exact (hno x hx (x, y) he rfl).elim
      obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hR
      have heD := Multiset.mem_of_le (Multiset.sub_le_self D _) he
      have hp := h.2.1 0 e.1 h.1 ⟨e, heD, Or.inl rfl⟩
      have hv : V e.1 := by
        generalize e.1 = z at hp ⊢
        induction hp with
        | refl => exact Or.inl rfl
        | tail hp hxy ih => exact step ih hxy
      exact hno e.1 hv e he rfl
    obtain ⟨v, hv, e, he, heq⟩ := hhit
    obtain ⟨p, q, hpq, hp, hq⟩ :
        ∃ p q, w = p ++ q ∧ EdgeWalk 0 p v ∧ EdgeWalk v q 0 := by
      rcases hv with rfl | hv
      · exact ⟨[], w, rfl, rfl, hw⟩
      · exact walk_split hw hv
    obtain ⟨u, c, hu, hU, hmaxU⟩ := longest_walk R v
    have hc := longest_walk_closed R hbal hu hU hmaxU
    subst c
    have hpos : 0 < u.length := by
      have hl := hmaxU [e] e.2 ⟨heq.symm, rfl⟩ (Multiset.singleton_le.mpr he)
      simpa only [List.length_singleton, Nat.succ_le_iff] using hl
    have hle : ((p ++ u ++ q : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) ≤ D := by
      have hsum := add_le_add_left hU (w : Multiset (ℕ × ℕ))
      rw [← hpart, hpq]
      simp only [← Multiset.coe_add]
      simpa only [← Multiset.coe_add, hpq, add_assoc, add_comm, add_left_comm] using hsum
    have hl := hmax (p ++ u ++ q) 0 (walk_append (walk_append hp hu) hq) hle
    simp only [hpq, List.length_append] at hl
    omega
  refine ⟨w, ?_, heq, hw⟩
  intro hnil
  obtain ⟨e, he, _⟩ := h.1
  simp [← heq, hnil] at he

private theorem run_walk (n b : ℕ) (hn : 1 < n) (hnb : n < b) {a c : ℕ}
    {s : List (ℕ × ℕ)} (h : IsHoeySloaneRun n b a s c) :
    EdgeWalk a (s.map (hoeySloaneTransition n b)) c := by
  induction s generalizing a with
  | nil => exact h
  | cons e s ih =>
    obtain ⟨d, hd, hs⟩ := h
    have ht := isHoeySloaneStep_hoeySloaneTransition n b hn hnb e hd.2.2.1
    obtain ⟨ha, hb⟩ := isHoeySloaneStep_unique n b hnb.le hd ht
    exact ⟨ha, by simpa only [← hb] using ih hs⟩

/-- A nonempty edge walk from `a` to `c` is a chain of adjacent edges whose last edge ends
at `c`. -/
private theorem walk_chain {a c : ℕ} (e : ℕ × ℕ) (w : List (ℕ × ℕ))
    (h : EdgeWalk a (e :: w) c) :
    (e :: w).IsChain (fun x y => x.2 = y.1) ∧ (e :: w).getLast?.map Prod.snd = some c := by
  induction w generalizing a e with
  | nil =>
    have hc : e.2 = c := h.2
    exact ⟨.singleton e, by simp [hc]⟩
  | cons f w ih =>
    obtain ⟨hchain, hlast⟩ := ih f h.2
    exact ⟨.cons_cons h.2.1 hchain, by simpa [List.getLast?_cons_cons] using hlast⟩

@[expose] public section

/-- **$L$-Eulerian criterion for permutiple strings.** Let $1 < n < b$ and let $I$ be a
multiset of cycles of the $(n, b)$-mother graph, with multiset union of cycle edges $C_I$
and multi-image union $\Delta_I$. Then $\Delta_I$ is $L$-Eulerian if and only if there is
an $(n, b)$-permutiple string $s$ whose multiset of entries is $C_I$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Corollary 2 (`integers-2025-A111-cor-2`). -/
public theorem exists_isPermutipleString_iff_isLEulerian (n b : ℕ) (hn : 1 < n) (hnb : n < b)
    (cs : Multiset (List ℕ)) (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs) :
    (∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = cycleUnion cs ∧ IsPermutipleString n b s) ↔
      IsLEulerian (multiImageUnion n b cs)
    := by
  constructor
  · rintro ⟨s, hs, hp⟩
    have hne : s ≠ [] := by
      obtain ⟨_, k, d, σ, _, rfl⟩ := hp
      intro hn
      have hlen := congrArg List.length hn
      simp only [List.length_ofFn, List.length_nil] at hlen
      omega
    have hwalk := run_walk n b hn hnb hp.1
    have hEuler := walk_isLEulerian hwalk (fun hempty => hne (List.eq_nil_of_map_eq_nil hempty))
    simpa only [← Multiset.map_coe, hs, multiImageUnion] using hEuler
  · intro h
    obtain ⟨w, hne, hw, hwalk⟩ := euler_walk (multiImageUnion n b cs) h
    obtain ⟨e, w, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨hchain, hlast⟩ := walk_chain e w hwalk
    exact exists_isPermutipleString_of_hasEulerianCircuitFromZero n b hn hnb cs hcs
      ⟨e :: w, hne, hw, hchain, by simpa using hwalk.1.symm, hlast⟩

end

end MetaMathlibExt
