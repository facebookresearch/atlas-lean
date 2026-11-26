/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.PermutipleStrings
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination

/-!
# The $L$-Eulerian criterion for permutiple strings

The existence of a permutiple string with prescribed cycle-edge multiplicities is equivalent
to the multi-image union being $L$-Eulerian.

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

private theorem walk_run (n b : ℕ) (hn : 1 < n) (hnb : n < b) {a c : ℕ}
    {s : List (ℕ × ℕ)} (h : EdgeWalk a (s.map (hoeySloaneTransition n b)) c)
    (hedge : ∀ e ∈ s, IsMotherGraphEdge n b e.1 e.2) : IsHoeySloaneRun n b a s c := by
  induction s generalizing a with
  | nil => exact h
  | cons e s ih =>
    obtain ⟨rfl, hs⟩ := h
    exact ⟨_, isHoeySloaneStep_hoeySloaneTransition n b hn hnb e
      (hedge e List.mem_cons_self), ih hs (fun f hf => hedge f (List.mem_cons_of_mem e hf))⟩

private theorem cycleUnion_projections (cs : Multiset (List ℕ)) :
    (cycleUnion cs).map Prod.fst = (cycleUnion cs).map Prod.snd := by
  induction cs using Multiset.induction_on with
  | empty => simp [cycleUnion]
  | @cons vs cs ih =>
    have hv : (cycleEdges vs : Multiset (ℕ × ℕ)).map Prod.fst =
        (cycleEdges vs : Multiset (ℕ × ℕ)).map Prod.snd := by
      simp only [cycleEdges, Multiset.map_coe,
        List.map_fst_zip (by simp : vs.length ≤ (vs.rotate 1).length),
        List.map_snd_zip (by simp : (vs.rotate 1).length ≤ vs.length)]
      exact Quot.sound (List.rotate_perm vs 1).symm
    simpa only [cycleUnion, Multiset.cons_bind, Multiset.map_add, hv] using
      congrArg ((cycleEdges vs : Multiset (ℕ × ℕ)).map Prod.snd + ·) ih

private theorem exists_digit_permutation {m : ℕ} (f g : Fin m → ℕ)
    (h : (List.ofFn f : Multiset ℕ) = (List.ofFn g : Multiset ℕ)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ j, f (σ j) = g j := by
  classical
  have hcard (c : ℕ) : Fintype.card {j // g j = c} = Fintype.card {j // f j = c} := by
    have hc := congrArg (Multiset.countP (fun x => x = c)) h
    simpa only [Multiset.coe_countP, List.countP_ofFn, decide_eq_true_eq,
      Fintype.card_subtype] using hc.symm
  let e (c : ℕ) : {j // g j = c} ≃ {j // f j = c} :=
    Fintype.equivOfCardEq (hcard c)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private theorem run_value (n b : ℕ) {m : ℕ} (f : Fin m → ℕ × ℕ) {a c : ℕ}
    (h : IsHoeySloaneRun n b a (List.ofFn f) c) :
    (∑ j, (f j).1 * (b : ℤ) ^ (j : ℕ)) + (b : ℤ) ^ m * c =
      n * (∑ j, (f j).2 * (b : ℤ) ^ (j : ℕ)) + a := by
  induction m generalizing a with
  | zero =>
    have hac : a = c := by simpa only [List.ofFn_zero, IsHoeySloaneRun] using h
    simp [hac]
  | succ m ih =>
    rw [List.ofFn_succ] at h
    obtain ⟨d, hd, hs⟩ := h
    have hi := ih (fun j => f j.succ) hs
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      pow_succ, ← mul_assoc, ← Finset.sum_mul]
    linear_combination (b : ℤ) * hi + hd.2.2.2

private theorem string_of_run (n b : ℕ) {s : List (ℕ × ℕ)} (hne : s ≠ [])
    (hrun : IsHoeySloaneRun n b 0 s 0)
    (hedge : ∀ e ∈ s, IsMotherGraphEdge n b e.1 e.2)
    (hproj : (s : Multiset (ℕ × ℕ)).map Prod.fst = (s : Multiset (ℕ × ℕ)).map Prod.snd) :
    IsPermutipleString n b s := by
  cases s with
  | nil => exact (hne rfl).elim
  | cons e s =>
    let f : Fin (s.length + 1) → ℕ × ℕ := (e :: s).get
    let d : Fin (s.length + 1) → ℕ := fun j => (f j).1
    let g : Fin (s.length + 1) → ℕ := fun j => (f j).2
    have hf : List.ofFn f = e :: s := List.ofFn_get _
    have hdg : (List.ofFn d : Multiset ℕ) = (List.ofFn g : Multiset ℕ) := by
      simpa only [← hf, Multiset.map_coe, List.map_ofFn, Function.comp_def] using hproj
    obtain ⟨σ, hσ⟩ := exists_digit_permutation d g hdg
    refine ⟨hrun, s.length, d, σ, ⟨?_, ?_⟩, ?_⟩
    · intro j
      exact (hedge (f j) (List.get_mem _ _)).1
    · have hv := run_value n b f (by simpa only [hf] using hrun)
      have hvalue : (∑ j, (d j : ℤ) * (b : ℤ) ^ (j : ℕ)) =
          n * (∑ j, (d (σ j) : ℤ) * (b : ℤ) ^ (j : ℕ)) := by
        simpa only [Nat.cast_zero, mul_zero, add_zero, hσ] using hv
      exact_mod_cast hvalue
    · rw [← hf]
      apply congrArg List.ofFn
      funext j
      rw [hσ]

private theorem cycleUnion_edges (n b : ℕ) (cs : Multiset (List ℕ))
    (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs) {e : ℕ × ℕ}
    (he : e ∈ cycleUnion cs) : IsMotherGraphEdge n b e.1 e.2 := by
  obtain ⟨vs, hvs, he⟩ := Multiset.mem_bind.mp he
  exact (hcs vs hvs).2.2 e he

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
    classical
    obtain ⟨w, hne, hw, hwalk⟩ := euler_walk (multiImageUnion n b cs) h
    let C := cycleUnion cs
    have hp : w.Perm (C.toList.map (hoeySloaneTransition n b)) := by
      apply Multiset.coe_eq_coe.mp
      rw [← Multiset.map_coe, Multiset.coe_toList]
      exact hw
    have hlift := congrFun (congrFun (List.eq_map_comp_perm (hoeySloaneTransition n b)) w)
      C.toList
    obtain ⟨s, hws, hperm⟩ := hlift.mpr hp
    have hs : (s : Multiset (ℕ × ℕ)) = cycleUnion cs := by
      simpa only [Multiset.coe_toList, C] using (Multiset.coe_eq_coe.mpr hperm)
    have hedge : ∀ e ∈ s, IsMotherGraphEdge n b e.1 e.2 := by
      intro e he
      exact cycleUnion_edges n b cs hcs (by simpa only [← hs, Multiset.mem_coe] using he)
    refine ⟨s, hs, string_of_run n b ?_ (walk_run n b hn hnb ?_ hedge) hedge ?_⟩
    · intro hnil
      simp only [hnil, List.map_nil] at hws
      exact hne hws
    · simpa only [hws] using hwalk
    · rw [hs]
      exact cycleUnion_projections cs

end

end MetaMathlibExt
