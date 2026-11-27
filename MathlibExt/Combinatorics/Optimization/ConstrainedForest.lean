/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The primal–dual method for constrained forest problems

M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest
problems", *SIAM J. Comput.* 24(2) (1995), 296–317.

A *requirement function* `f : 2^V → {0, 1}` asks for at least one edge across every cut `δ(S)`
with `f(S) = 1`. Goemans and Williamson call `f` *proper* when it is symmetric
(`f(S) = f(V \ S)`) and disjoint sets with `f = 0` have a union with `f = 0` (p. 296); they also
assume `f(V) = 0` (p. 297). Spanning trees, `s`-`t` paths, Steiner trees and `T`-joins
(Table 1, p. 297), and generalized Steiner trees (Steiner forests; text of p. 297) are proper
constrained forest problems.

Their Theorem 2.4 shows that the primal–dual algorithm returns a feasible forest of cost at most
`(2 - 2/|A|)` times the value of a feasible dual solution, `A = {v : f({v}) = 1}`; hence the
ratio between the optimal values of the integer program (IP) and its linear relaxation (LP) is
at most `2 - 2/|A|` (p. 297). The main theorem proves this integrality-gap consequence,
which is weaker than Theorem 2.4 (it says nothing about the algorithm or its running time).
-/

open Finset

namespace MathlibExt.Combinatorics.Optimization.ConstrainedForest

@[expose] public section

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **Edges of a cut.** `δ(S)`: the edges of `G` with exactly one endpoint in `S` (Goemans and
Williamson, *SIAM J. Comput.* 24(2) (1995), §1). -/
noncomputable def cutEdges (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ u ∈ S, ∃ v ∉ S, e = s(u, v)

/-- **Proper requirement function.** `f : 2^V → {0, 1}` is proper when `f(S) = f(V \ S)` for all
`S`, and `f(A) = f(B) = 0` for disjoint `A`, `B` implies `f(A ∪ B) = 0` (Goemans and Williamson,
*SIAM J. Comput.* 24(2) (1995), §1, properties (i) and (ii), p. 296). -/
def IsProper (f : Finset V → Bool) : Prop :=
  (∀ S, f Sᶜ = f S) ∧
    ∀ A B, Disjoint A B → f A = false → f B = false → f (A ∪ B) = false

/-- **Steiner forest requirement.** For demand pairs `(s_i, t_i)`, `f(S) = 1` exactly when `S`
separates some pair; its minimal feasible forests are the Steiner forests (generalized Steiner
trees) of Goemans and Williamson, *SIAM J. Comput.* 24(2) (1995), §1, p. 297. -/
def steinerForestRequirement (demands : List (V × V)) (S : Finset V) : Bool :=
  demands.any fun d => decide (d.1 ∈ S) != decide (d.2 ∈ S)

end

variable {V : Type*} [Fintype V] [DecidableEq V]

-- The map sends each original vertex to the label of its current block.
private def preimage (p : V → V) (S : Finset V) : Finset V :=
  univ.filter fun v => p v ∈ S

@[simp] private theorem mem_preimage {p : V → V} {S : Finset V} {v : V} :
    v ∈ preimage p S ↔ p v ∈ S := by
  simp [preimage]

private theorem proper_preimage {f : Finset V → Bool} (hf : IsProper f) (p : V → V) :
    IsProper (f ∘ preimage p) := by
  constructor
  · intro S
    have heq : preimage p Sᶜ = (preimage p S)ᶜ := by ext; simp
    simpa only [Function.comp_apply, heq] using hf.1 (preimage p S)
  · intro A B hAB hA hB
    have hdisj : Disjoint (preimage p A) (preimage p B) := by
      rw [disjoint_left] at hAB ⊢
      intro v hv hw
      exact hAB (mem_preimage.mp hv) (mem_preimage.mp hw)
    have heq : preimage p (A ∪ B) = preimage p A ∪ preimage p B := by ext; simp
    simpa only [Function.comp_apply, heq] using hf.2 _ _ hdisj hA hB

private theorem false_of_singletons {f : Finset V → Bool} (hf : IsProper f)
    (h0 : f ∅ = false) {S : Finset V} (hS : ∀ v ∈ S, f {v} = false) : f S = false := by
  induction S using Finset.induction_on with
  | empty => exact h0
  | @insert v S hv ih =>
    rw [← singleton_union]
    exact hf.2 _ _ (by simpa using hv) (hS v (mem_insert_self _ _))
      (ih fun w hw => hS w (mem_insert_of_mem hw))

open Classical in
private theorem pair_mem_cutEdges {G : SimpleGraph V} {S : Finset V} {u v : V} :
    s(u, v) ∈ cutEdges G S ↔
      s(u, v) ∈ G.edgeFinset ∧ ((u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) := by
  rw [cutEdges, mem_filter]
  constructor
  · rintro ⟨he, a, ha, b, hb, huv⟩
    rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨he, Or.inl ⟨ha, hb⟩⟩
    · exact ⟨he, Or.inr ⟨ha, hb⟩⟩
  · rintro ⟨he, h | h⟩
    · exact ⟨he, u, h.1, v, h.2, rfl⟩
    · exact ⟨he, v, h.1, u, h.2, Sym2.eq_swap⟩

private noncomputable def crossing (G : SimpleGraph V) (p : V → V) (S : Finset V) :
    Finset (Sym2 V) :=
  cutEdges G (preimage p S)

open Classical in
private theorem pair_mem_crossing {G : SimpleGraph V} {p : V → V} {S : Finset V} {u v : V} :
    s(u, v) ∈ crossing G p S ↔
      s(u, v) ∈ G.edgeFinset ∧ ((p u ∈ S ∧ p v ∉ S) ∨ (p v ∈ S ∧ p u ∉ S)) := by
  simp only [crossing, pair_mem_cutEdges, mem_preimage]

private abbrev Feasible (G : SimpleGraph V) (p : V → V) (f : Finset V → Bool)
    (F : Finset (Sym2 V)) : Prop :=
  ∀ S, f (preimage p S) = true → (F ∩ crossing G p S).Nonempty

private def active (p : V → V) (f : Finset V → Bool) : Finset V :=
  univ.filter fun v => f (preimage p {v}) = true

private theorem active_empty_feasible {G : SimpleGraph V} {p : V → V}
    {f : Finset V → Bool} (hf : IsProper f) (hV : f univ = false)
    (hactive : active p f = ∅) : Feasible G p f ∅ := by
  intro S hS
  have h0 : f (preimage p ∅) = false := by
    have heq : preimage p ∅ = univᶜ := by ext; simp
    rw [heq, hf.1, hV]
  have hfalse := false_of_singletons (proper_preimage hf p) h0 (S := S) (by
    intro v _
    have hv : v ∉ active p f := by simp [hactive]
    simpa [active] using hv)
  simp [Function.comp_apply, hS] at hfalse

private def merge (a b : V) (v : V) : V :=
  if v = b then a else v

private theorem active_merge_card_le (p : V → V) {a b : V} (hab : a ≠ b)
    {f : Finset V → Bool} (hf : IsProper f) (hV : f univ = false) :
    (active (merge a b ∘ p) f).card ≤ (active p f).card := by
  have hsub : active (merge a b ∘ p) f ⊆ (active p f).image (merge a b) := by
    intro v hv
    have hv : f (preimage (merge a b ∘ p) {v}) = true := (mem_filter.mp hv).2
    by_cases h : v = a
    · subst v
      have heq : preimage (merge a b ∘ p) {a} = preimage p {a} ∪ preimage p {b} := by
        ext w
        simp only [mem_preimage, mem_singleton, Function.comp_apply, mem_union]
        by_cases hw : p w = b <;> simp [merge, hw]
      have hd : Disjoint (preimage p {a}) (preimage p {b}) := by
        rw [disjoint_left]
        simp only [mem_preimage, mem_singleton]
        grind
      rw [heq] at hv
      by_cases ha : f (preimage p {a}) = true
      · exact mem_image.mpr ⟨a, by simp [active, ha], by simp [merge, hab]⟩
      · by_cases hb : f (preimage p {b}) = true
        · exact mem_image.mpr ⟨b, by simp [active, hb], by simp [merge]⟩
        · have hfalse := hf.2 _ _ hd (by simpa using ha) (by simpa using hb)
          simp [hv] at hfalse
    · have hnb : v ≠ b := by
        rintro rfl
        have heq : preimage (merge a v ∘ p) {v} = univᶜ := by
          ext w
          simp only [mem_preimage, mem_singleton, Function.comp_apply, compl_univ, notMem_empty,
            iff_false]
          by_cases hw : p w = v <;> simp [merge, hw, Ne.symm h]
        rw [heq, hf.1, hV] at hv
        contradiction
      have heq : preimage (merge a b ∘ p) {v} = preimage p {v} := by
        ext w
        simp only [mem_preimage, mem_singleton, Function.comp_apply]
        by_cases hw : p w = b <;> simp [merge, hw, Ne.symm h, Ne.symm hnb]
      rw [heq] at hv
      exact mem_image.mpr ⟨v, by simp [active, hv], by simp [merge, hnb]⟩
  exact (card_le_card hsub).trans card_image_le

private theorem exists_minimal {G : SimpleGraph V} {p : V → V} {f : Finset V → Bool}
    {H : Finset (Sym2 V)} (hH : Feasible G p f H) :
    ∃ F ⊆ H, Feasible G p f F ∧ ∀ e ∈ F, ¬ Feasible G p f (F.erase e) := by
  classical
  let candidates := H.powerset.filter (Feasible G p f)
  have hne : candidates.Nonempty := ⟨H, mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hH⟩⟩
  obtain ⟨F, hF, hmin⟩ := candidates.exists_min_image Finset.card hne
  have hF' : F ⊆ H ∧ Feasible G p f F := by simpa [candidates] using hF
  refine ⟨F, hF'.1, hF'.2, fun e he hFe => ?_⟩
  have hmem : F.erase e ∈ candidates :=
    mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset e F).trans hF'.1), hFe⟩
  exact (not_le_of_gt (card_erase_lt_of_mem he)) (hmin _ hmem)

private theorem inactive_ne_one {G : SimpleGraph V} {p : V → V} {f : Finset V → Bool}
    (hf : IsProper f) {F : Finset (Sym2 V)} (hF : Feasible G p f F)
    (hmin : ∀ e ∈ F, ¬ Feasible G p f (F.erase e)) {b : V} (hb : b ∉ active p f) :
    (F ∩ crossing G p {b}).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨e, he⟩ := card_eq_one.mp hcard
  have heb : e ∈ F ∩ crossing G p {b} := by simp [he]
  obtain ⟨heF, heb⟩ := mem_inter.mp heb
  have hbad := hmin e heF
  unfold Feasible at hbad
  push Not at hbad
  obtain ⟨S, hS, hS'⟩ := hbad
  have hunique : ∀ e' ∈ F, e' ∈ crossing G p S → e' = e := by
    intro e' he'F he'S
    by_contra hne
    exact (not_nonempty_iff_eq_empty.mpr hS') ⟨e', mem_inter.mpr ⟨mem_erase.mpr ⟨hne, he'F⟩, he'S⟩⟩
  have heS : e ∈ crossing G p S := by
    obtain ⟨e', he'⟩ := hF S hS
    obtain ⟨he'F, he'S⟩ := mem_inter.mp he'
    exact hunique e' he'F he'S ▸ he'S
  obtain ⟨T, hbT, hT, heT, hTonly⟩ : ∃ T, b ∈ T ∧ f (preimage p T) = true ∧
      e ∈ crossing G p T ∧ ∀ e' ∈ F, e' ∈ crossing G p T → e' = e := by
    by_cases hbS : b ∈ S
    · exact ⟨S, hbS, hS, heS, hunique⟩
    · have heq : crossing G p Sᶜ = crossing G p S := by
        ext e'
        induction e' using Sym2.inductionOn with
        | _ u v =>
          simp only [pair_mem_crossing, mem_compl, not_not]
          tauto
      have hcompl := (proper_preimage hf p).1 S
      change f (preimage p Sᶜ) = f (preimage p S) at hcompl
      exact ⟨Sᶜ, by simpa using hbS, hcompl.trans hS, heq.symm ▸ ⟨heS, hunique⟩⟩
  -- Removing the inactive block from the cut leaves no edge crossing it.
  have hno : ¬ (F ∩ crossing G p (T.erase b)).Nonempty := by
    rintro ⟨e', he'⟩
    obtain ⟨he'F, he'T⟩ := mem_inter.mp he'
    by_cases heq : e' = e
    · subst e'
      induction e using Sym2.inductionOn with
      | _ u v =>
        simp only [pair_mem_crossing, mem_singleton, mem_erase] at heb heT he'T
        grind
    · have hn1 : e' ∉ crossing G p {b} := by
        intro he'b
        have : e' ∈ F ∩ crossing G p {b} := mem_inter.mpr ⟨he'F, he'b⟩
        exact heq (by simpa [he] using this)
      have hn2 : e' ∉ crossing G p T := fun he'T => heq (hTonly e' he'F he'T)
      induction e' using Sym2.inductionOn with
      | _ u v =>
        simp only [pair_mem_crossing, mem_singleton, mem_erase] at hn1 hn2 he'T
        tauto
  have herase : f (preimage p (T.erase b)) = false := by
    by_contra hn
    exact hno (hF _ (by simpa using hn))
  have hbfalse : f (preimage p {b}) = false := by simpa [active] using hb
  have hd : Disjoint (T.erase b) ({b} : Finset V) := by simp
  have hunion : T.erase b ∪ {b} = T := by ext v; by_cases h : v = b <;> simp_all
  have := (proper_preimage hf p).2 _ _ hd herase hbfalse
  change f (preimage p (T.erase b ∪ {b})) = false at this
  rw [hunion, hT] at this
  contradiction

private noncomputable def edgesAmong (p : V → V) (F : Finset (Sym2 V)) (T : Finset V) :
    Finset (Sym2 V) :=
  open Classical in F.filter fun e => ∀ v ∈ e, p v ∈ T

-- Every nonempty set of blocks spans at most one fewer edge than its size.
private abbrev RankBound (p : V → V) (F : Finset (Sym2 V)) : Prop :=
  ∀ T : Finset V, T.Nonempty → (edgesAmong p F T).card + 1 ≤ T.card

private theorem rank_mono {p : V → V} {F H : Finset (Sym2 V)} (h : F ⊆ H)
    (hH : RankBound p H) : RankBound p F := by
  intro T hT
  exact (Nat.add_le_add_right (card_le_card (filter_subset_filter _ h)) 1).trans (hH T hT)

omit [Fintype V] in
private theorem image_merge_erase {a b : V} {T : Finset V} (ha : a ∈ T) (hab : a ≠ b) :
    T.image (merge a b) = T.erase b := by
  ext v
  simp only [mem_image, mem_erase, merge]
  constructor
  · rintro ⟨w, hw, rfl⟩
    by_cases h : w = b <;> simp [h, ha, hab, hw]
  · rintro ⟨hv, hvT⟩
    exact ⟨v, hvT, ite_eq_right hv⟩

private theorem rank_insert_merge (p : V → V) {u v : V} (huv : p u ≠ p v)
    {F : Finset (Sym2 V)} (hF : RankBound (merge (p u) (p v) ∘ p) F) :
    RankBound p (insert s(u, v) F) := by
  classical
  let a := p u
  let b := p v
  let q := merge a b ∘ p
  intro T hT
  have himage : (T.image (merge a b)).Nonempty := hT.image _
  have hsub : edgesAmong p F T ⊆ edgesAmong q F (T.image (merge a b)) := by
    intro e he
    obtain ⟨heF, heT⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨heF, fun w hw => mem_image_of_mem _ (heT w hw)⟩
  have hcount := (Nat.add_le_add_right (card_le_card hsub) 1).trans (hF _ himage)
  by_cases h : a ∈ T ∧ b ∈ T
  · rw [image_merge_erase h.1 huv, card_erase_of_mem h.2] at hcount
    have heq : edgesAmong p (insert s(u, v) F) T = insert s(u, v) (edgesAmong p F T) := by
      ext e
      simp only [edgesAmong, mem_filter, mem_insert]
      have hp : ∀ w ∈ s(u, v), p w ∈ T := Sym2.forall_mem_pair.mpr h
      grind
    rw [heq]
    have := card_insert_le (s(u, v)) (edgesAmong p F T)
    omega
  · have heq : edgesAmong p (insert s(u, v) F) T = edgesAmong p F T := by
      ext e
      simp only [edgesAmong, mem_filter, mem_insert]
      have hp : ¬ ∀ w ∈ s(u, v), p w ∈ T := fun ht =>
        h ⟨ht u (by simp), ht v (by simp)⟩
      grind
    rw [heq]
    exact hcount.trans card_image_le

private theorem rank_no_loop {p : V → V} {F : Finset (Sym2 V)} (hF : RankBound p F)
    {u v : V} (he : s(u, v) ∈ F) : p u ≠ p v := by
  classical
  intro heq
  have hr := hF {p u} (singleton_nonempty _)
  have hmem : s(u, v) ∈ edgesAmong p F {p u} := by
    simp [edgesAmong, he, heq]
  have hpos : 0 < (edgesAmong p F {p u}).card := card_pos.mpr ⟨_, hmem⟩
  rw [card_singleton] at hr
  omega

open Classical in
private theorem feasible_insert_merge {G : SimpleGraph V} (p : V → V) {u v : V}
    (he : s(u, v) ∈ G.edgeFinset) {f : Finset V → Bool} {F : Finset (Sym2 V)}
    (hF : Feasible G (merge (p u) (p v) ∘ p) f F) :
    Feasible G p f (insert s(u, v) F) := by
  intro S hS
  by_cases h : s(u, v) ∈ crossing G p S
  · exact ⟨_, mem_inter.mpr ⟨mem_insert_self _ _, h⟩⟩
  · have hsame : p u ∈ S ↔ p v ∈ S := by
      simp only [pair_mem_crossing, he, true_and] at h
      tauto
    have heq : preimage (merge (p u) (p v) ∘ p) S = preimage p S := by
      ext w
      simp only [mem_preimage, Function.comp_apply]
      by_cases hw : p w = p v <;> simp [merge, hw, hsame]
    obtain ⟨e, he⟩ := hF S (heq.symm ▸ hS)
    obtain ⟨heF, heS⟩ := mem_inter.mp he
    exact ⟨e, mem_inter.mpr ⟨mem_insert_of_mem heF, by simpa only [crossing, heq] using heS⟩⟩

open Classical in
private noncomputable def multiplicity (G : SimpleGraph V) (p : V → V) (A : Finset V)
    (e : Sym2 V) : ℝ :=
  ((A.filter fun a => e ∈ crossing G p {a}).card : ℝ)

private theorem multiplicity_nonneg (G : SimpleGraph V) (p : V → V) (A : Finset V)
    (e : Sym2 V) : 0 ≤ multiplicity G p A e := by
  unfold multiplicity
  positivity

private theorem sum_multiplicity_mul (G : SimpleGraph V) (p : V → V) (A : Finset V)
    (F : Finset (Sym2 V)) (w : Sym2 V → ℝ) :
    ∑ e ∈ F, multiplicity G p A e * w e =
      ∑ a ∈ A, ∑ e ∈ F ∩ crossing G p {a}, w e := by
  classical
  calc
    _ = ∑ e ∈ F, ∑ a ∈ A, if e ∈ crossing G p {a} then w e else 0 := by
      apply sum_congr rfl
      intro e _
      rw [← sum_filter, sum_const, nsmul_eq_mul, multiplicity]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [← sum_filter]
      congr 1

open Classical in
private theorem sum_multiplicity_ge (G : SimpleGraph V) (p : V → V)
    (f : Finset V → Bool) (x : Sym2 V → ℝ)
    (hx : ∀ S, f S = true → 1 ≤ ∑ e ∈ cutEdges G S, x e) :
    ((active p f).card : ℝ) ≤ ∑ e ∈ G.edgeFinset, multiplicity G p (active p f) e * x e := by
  rw [sum_multiplicity_mul]
  conv_lhs => rw [← mul_one ((active p f).card : ℝ), ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro a ha
  have hsub : crossing G p {a} ⊆ G.edgeFinset := filter_subset _ _
  rw [inter_eq_right.mpr hsub]
  exact hx _ (mem_filter.mp ha).2

private theorem factor_nonneg (m : ℕ) : 0 ≤ 2 - 2 / (m : ℝ) := by
  cases m with
  | zero => simp
  | succ m =>
    have hm : (1 : ℝ) ≤ (m.succ : ℝ) := by exact_mod_cast m.succ_pos
    have hdiv : (2 : ℝ) / (m.succ : ℝ) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

open Classical in
private theorem sum_multiplicity_le {G : SimpleGraph V} {p : V → V} {f : Finset V → Bool}
    (hf : IsProper f) {F : Finset (Sym2 V)} (hsub : F ⊆ G.edgeFinset)
    (hF : Feasible G p f F) (hmin : ∀ e ∈ F, ¬ Feasible G p f (F.erase e))
    (hrank : RankBound p F) {m : ℕ} (hm : (active p f).card ≤ m) :
    ∑ e ∈ F, multiplicity G p (active p f) e ≤
      (2 - 2 / (m : ℝ)) * ((active p f).card : ℝ) := by
  by_cases h : F = ∅
  · subst F
    simpa using mul_nonneg (factor_nonneg m) (Nat.cast_nonneg (α := ℝ) (active p f).card)
  let degree (a : V) := (F ∩ crossing G p {a}).card
  let U : Finset V := univ.filter fun a => (F ∩ crossing G p {a}).Nonempty
  have hdegree {a} : a ∈ U ↔ 0 < degree a := by simp [U, degree, card_pos]
  have hend {e} (he : e ∈ F) : ∀ v ∈ e, p v ∈ U := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hne := rank_no_loop hrank he
      have hu : s(u, v) ∈ crossing G p {p u} := by
        simp [pair_mem_crossing, hsub he, Ne.symm hne]
      have hv : s(u, v) ∈ crossing G p {p v} := by
        simp [pair_mem_crossing, hsub he, hne]
      rw [Sym2.forall_mem_pair]
      exact ⟨hdegree.mpr (card_pos.mpr ⟨_, mem_inter.mpr ⟨he, hu⟩⟩),
        hdegree.mpr (card_pos.mpr ⟨_, mem_inter.mpr ⟨he, hv⟩⟩)⟩
  have hU : U.Nonempty := by
    obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr h
    induction e using Sym2.inductionOn with
    | _ u v => exact ⟨p u, hend he u (by simp)⟩
  have hFU : edgesAmong p F U = F := by
    exact filter_eq_self.mpr fun _ he => hend he
  have hcard : F.card + 1 ≤ U.card := by simpa only [hFU] using hrank U hU
  have hdouble : ∑ a ∈ U, (degree a : ℝ) = 2 * (F.card : ℝ) := by
    have hswap := sum_multiplicity_mul G p U F (fun _ => 1)
    simp only [mul_one, sum_const, nsmul_eq_mul] at hswap
    change (∑ e ∈ F, multiplicity G p U e) = ∑ a ∈ U, (degree a : ℝ) at hswap
    rw [← hswap]
    rw [show ∑ e ∈ F, multiplicity G p U e = ∑ _e ∈ F, (2 : ℝ) from ?_, sum_const,
      nsmul_eq_mul, mul_comm]
    apply sum_congr rfl
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hne := rank_no_loop hrank he
      have heq : (U.filter fun a => s(u, v) ∈ crossing G p {a}) = {p u, p v} := by
        ext a
        have hu := hend he u (by simp)
        have hv := hend he v (by simp)
        simp only [mem_filter, pair_mem_crossing, hsub he, true_and, mem_singleton, mem_insert]
        grind
      rw [multiplicity, heq]
      simp [hne]
  let A := active p f
  have hsplit : ∑ a ∈ U, (degree a : ℝ) =
      (∑ a ∈ U ∩ A, (degree a : ℝ)) + ∑ a ∈ U \ A, (degree a : ℝ) := by
    have hdis : Disjoint (U ∩ A) (U \ A) := by simp [disjoint_left]; grind
    rw [← sum_union hdis]
    congr 1
    ext a
    simp
  have hactive : ∑ e ∈ F, multiplicity G p A e = ∑ a ∈ U ∩ A, (degree a : ℝ) := by
    have hs := sum_multiplicity_mul G p A F (fun _ => 1)
    simp only [mul_one, sum_const, nsmul_eq_mul] at hs
    change (∑ e ∈ F, multiplicity G p A e) = ∑ a ∈ A, (degree a : ℝ) at hs
    rw [hs]
    symm
    apply sum_subset inter_subset_right
    intro a _ ha
    have h0 : degree a = 0 := by
      have : a ∉ U := by grind
      have := mt hdegree.mpr this
      omega
    simp [h0]
  have hinactive : 2 * ((U \ A).card : ℝ) ≤ ∑ a ∈ U \ A, (degree a : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro a ha
    obtain ⟨hu, hi⟩ := mem_sdiff.mp ha
    have hp := hdegree.mp hu
    have hn := inactive_ne_one hf hF hmin hi
    have : 2 ≤ degree a := by change degree a ≠ 1 at hn; omega
    exact_mod_cast this
  have hparts : ((U ∩ A).card : ℝ) + ((U \ A).card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast (card_inter_add_card_sdiff U A)
  have hcount : ((U ∩ A).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast card_le_card inter_subset_right
  have hcard' : (F.card : ℝ) + 1 ≤ (U.card : ℝ) := by exact_mod_cast hcard
  have hratio : (2 / (m : ℝ)) * (A.card : ℝ) ≤ 2 := by
    cases m with
    | zero => simp
    | succ m =>
      have hm' : (A.card : ℝ) ≤ (m.succ : ℝ) := by exact_mod_cast hm
      calc
        _ ≤ (2 / (m.succ : ℝ)) * (m.succ : ℝ) :=
          mul_le_mul_of_nonneg_left hm' (by positivity)
        _ = 2 := div_mul_cancel₀ _ (by positivity)
  -- Each incident inactive block accounts for at least two of the total degrees.
  rw [hactive]
  linarith

open Classical in
private theorem edge_of_multiplicity_pos {G : SimpleGraph V} {p : V → V} {A : Finset V}
    {e : Sym2 V} (he : 0 < multiplicity G p A e) :
    ∃ a ∈ A, e ∈ crossing G p {a} := by
  unfold multiplicity at he
  exact nonempty_def.mp (card_pos.mp (by exact_mod_cast he)) |>.imp fun a ha => mem_filter.mp ha

open Classical in
private theorem growth (G : SimpleGraph V) (f : Finset V → Bool) (hf : IsProper f)
    (hV : f univ = false) (x : Sym2 V → ℝ) (hx0 : ∀ e, 0 ≤ x e)
    (hx : ∀ S, f S = true → 1 ≤ ∑ e ∈ cutEdges G S, x e)
    (m : ℕ) (p : V → V) (hm : (active p f).card ≤ m)
    (c : Sym2 V → ℝ) (hc : ∀ e, 0 ≤ c e) :
    ∃ F ⊆ G.edgeFinset, Feasible G p f F ∧ RankBound p F ∧
      ∑ e ∈ F, c e ≤ (2 - 2 / (m : ℝ)) * ∑ e ∈ G.edgeFinset, c e * x e := by
  generalize hn : (univ.image p).card = n
  induction n using Nat.strong_induction_on generalizing p c with
  | ind n ih =>
    by_cases hA : active p f = ∅
    · refine ⟨∅, empty_subset _, active_empty_feasible hf hV hA, ?_, ?_⟩
      · intro T hT
        simpa [edgesAmong] using card_pos.mpr hT
      · simpa using mul_nonneg (factor_nonneg m) (sum_nonneg fun e _ => mul_nonneg (hc e) (hx0 e))
    let A := active p f
    let k := multiplicity G p A
    let β : ℝ := 2 - 2 / (m : ℝ)
    let candidates := G.edgeFinset.filter fun e => 0 < k e
    have hne : candidates.Nonempty := by
      obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hA
      have ha' := hx _ (mem_filter.mp ha).2
      have hcut : (crossing G p {a}).Nonempty := by
        change 1 ≤ ∑ e ∈ crossing G p {a}, x e at ha'
        by_contra! h
        rw [h, sum_empty] at ha'
        exact (by norm_num : ¬ (1 : ℝ) ≤ 0) ha'
      obtain ⟨e, he⟩ := hcut
      have heG : e ∈ G.edgeFinset := filter_subset _ _ he
      have hp : 0 < (A.filter fun a => e ∈ crossing G p {a}).card :=
        card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, he⟩⟩
      refine ⟨e, mem_filter.mpr ⟨heG, ?_⟩⟩
      change (0 : ℝ) < ((A.filter fun a => e ∈ crossing G p {a}).card : ℝ)
      exact_mod_cast hp
    have hmin : ∃ u v : V, s(u, v) ∈ candidates ∧
        ∀ e' ∈ candidates, c s(u, v) / k s(u, v) ≤ c e' / k e' :=
      Sym2.exists.mp (candidates.exists_min_image (fun e => c e / k e) hne)
    obtain ⟨u, v, he, hminimum⟩ := hmin
    let e := s(u, v)
    have heG : e ∈ G.edgeFinset := (mem_filter.mp he).1
    have hepos : 0 < k e := (mem_filter.mp he).2
    have hp : p u ≠ p v := by
      obtain ⟨a, _, ha⟩ := edge_of_multiplicity_pos hepos
      rw [pair_mem_crossing] at ha
      intro h
      simp [h] at ha
    let q := merge (p u) (p v) ∘ p
    -- Grow every active cut by the same amount until the first edge becomes tight.
    let t := c e / k e
    have ht : 0 ≤ t := div_nonneg (hc e) hepos.le
    let d (e' : Sym2 V) := c e' - t * k e'
    have hd : ∀ e', 0 ≤ d e' := by
      intro e'
      have hk : 0 ≤ k e' := multiplicity_nonneg G p A e'
      by_cases h : 0 < k e'
      · obtain ⟨a, _, ha⟩ := edge_of_multiplicity_pos h
        have he'G : e' ∈ G.edgeFinset := filter_subset _ _ ha
        have hle := hminimum e' (mem_filter.mpr ⟨he'G, h⟩)
        exact sub_nonneg.mpr ((le_div_iff₀ h).mp hle)
      · have hk0 : k e' = 0 := le_antisymm (not_lt.mp h) hk
        simpa [d, hk0] using hc e'
    have hde : d e = 0 := by
      dsimp only [d, t]
      rw [div_mul_cancel₀ _ hepos.ne', sub_self]
    have himage : univ.image q = (univ.image p).erase (p v) := by
      rw [show q = merge (p u) (p v) ∘ p from rfl, ← image_image]
      exact image_merge_erase (mem_image_of_mem _ (mem_univ u)) hp
    have hn' : (univ.image q).card < n := by
      rw [himage, ← hn]
      exact card_erase_lt_of_mem (mem_image_of_mem _ (mem_univ v))
    have hmq : (active q f).card ≤ m := (active_merge_card_le p hp hf hV).trans hm
    obtain ⟨H, hHG, hH, hrH, hcostH⟩ := ih _ hn' q hmq d hd rfl
    -- Lift the contracted solution with the tight edge, then discard redundant edges.
    obtain ⟨F, hFH, hF, hminF⟩ := exists_minimal (feasible_insert_merge p heG hH)
    have hFG : F ⊆ G.edgeFinset := hFH.trans (insert_subset heG hHG)
    have hrF : RankBound p F := rank_mono hFH (rank_insert_merge p hp hrH)
    have hcharge := sum_multiplicity_le hf hFG hF hminF hrF hm
    have hlp := sum_multiplicity_ge G p f x hx
    have hprice : ∑ e' ∈ F, d e' ≤ ∑ e' ∈ H, d e' := by
      calc
        _ ≤ ∑ e' ∈ insert e H, d e' := sum_le_sum_of_subset_of_nonneg hFH fun e' _ _ => hd e'
        _ = _ := by
          by_cases h : e ∈ H
          · simp [h]
          · simp [sum_insert h, hde]
    have hprimal :
        ∑ e' ∈ G.edgeFinset, d e' * x e' + t * (A.card : ℝ) ≤
          ∑ e' ∈ G.edgeFinset, c e' * x e' := by
      have heq : ∑ e' ∈ G.edgeFinset, d e' * x e' =
          (∑ e' ∈ G.edgeFinset, c e' * x e') - t * ∑ e' ∈ G.edgeFinset, k e' * x e' := by
        simp only [d, sub_mul, mul_assoc, sum_sub_distrib, mul_sum]
      rw [heq]
      change (A.card : ℝ) ≤ ∑ e' ∈ G.edgeFinset, k e' * x e' at hlp
      linarith [mul_le_mul_of_nonneg_left hlp ht]
    refine ⟨F, hFG, hF, hrF, ?_⟩
    calc
      ∑ e' ∈ F, c e' = (∑ e' ∈ F, d e') + t * ∑ e' ∈ F, k e' := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun e' _ => (sub_add_cancel (c e') (t * k e')).symm
      _ ≤ β * (∑ e' ∈ G.edgeFinset, d e' * x e') + t * (β * (A.card : ℝ)) :=
        add_le_add (hprice.trans hcostH) (mul_le_mul_of_nonneg_left hcharge ht)
      _ = β * ((∑ e' ∈ G.edgeFinset, d e' * x e') + t * (A.card : ℝ)) := by
        rw [mul_add, mul_left_comm t]
      _ ≤ β * ∑ e' ∈ G.edgeFinset, c e' * x e' :=
        mul_le_mul_of_nonneg_left hprimal (factor_nonneg m)

@[expose] public section

open Classical in
/-- **Goemans–Williamson integrality gap for proper constrained forest problems.** Let `G` be a
finite simple graph with nonnegative edge costs `c`, and `f` a proper requirement function with
`f(V) = 0`; put `A = {v : f({v}) = 1}`. For every feasible solution `x ≥ 0` of the linear
relaxation (`x(δ(S)) ≥ 1` whenever `f(S) = 1`) there is a set of edges `F` meeting every cut
`δ(S)` with `f(S) = 1` whose cost is at most `(2 - 2/|A|) ∑_e c_e x_e` (Goemans and Williamson,
*SIAM J. Comput.* 24(2) (1995), Theorem 2.4 and the remark on p. 297 that the ratio between the
optimal values of (IP) and (LP) is at most `2 - 2/|A|`). When `|A| = 0`, Lean's `2 / 0 = 0`
makes the factor `2`; then `f ≡ 0` and `F = ∅` works. -/
theorem exists_forest_cost_le_of_lp_feasible (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e, 0 ≤ c e) (f : Finset V → Bool) (hf : IsProper f) (hV : f univ = false)
    (x : Sym2 V → ℝ) (hx0 : ∀ e, 0 ≤ x e)
    (hx : ∀ S, f S = true → 1 ≤ ∑ e ∈ cutEdges G S, x e) :
    ∃ F ⊆ G.edgeFinset, (∀ S, f S = true → (F ∩ cutEdges G S).Nonempty) ∧
      ∑ e ∈ F, c e ≤
        (2 - 2 / ((univ.filter fun v => f {v} = true).card : ℝ)) *
          ∑ e ∈ G.edgeFinset, c e * x e := by
  have hp : ∀ S : Finset V, preimage id S = S := by intros; ext; simp
  obtain ⟨F, hFG, hF, _, hcost⟩ := growth G f hf hV x hx0 hx (active id f).card id le_rfl c hc
  exact ⟨F, hFG, fun S hS => by simpa only [crossing, hp] using hF S (by rwa [hp]), by
    simpa only [active, hp] using hcost⟩

end

end MathlibExt.Combinatorics.Optimization.ConstrainedForest
