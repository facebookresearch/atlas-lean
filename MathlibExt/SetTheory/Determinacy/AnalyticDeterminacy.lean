/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.GaleStewart
public import MathlibExt.SetTheory.Cardinal.LargeCardinal.Measurable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Martin's analytic determinacy theorem

This file proves Martin's theorem (1970): if a measurable cardinal exists, every analytic (`Σ¹₁`)
subset of Baire space is determined
(`MathlibExt.SetTheory.DeterminacyWanted.determined_of_analyticSet_of_isMeasurable`).

## Proof

The proof is Martin's auxiliary game argument. Write the analytic set as the range of a
continuous map `f : ℕ^ℕ → ℕ^ℕ`. A finite sequence `l` is *alive* at a play `x` if some `y`
extending `l` has `f y` agreeing with `x` on the first `|l|` moves. The alive sequences form a
tree, with an infinite branch exactly when `x` lies in the range of `f`. Finite sequences are
ordered by the Kleene–Brouwer order: a proper extension is smaller, and otherwise the first
difference decides. On a tree with no infinite branch this order is well-founded.

The measurable cardinal gives a set `I` with a nonprincipal ultrafilter `U` closed under
countable intersections, and a well-founded order on `I` whose final segments lie in `U`. In
the auxiliary game the moves are pairs in `ℕ × I`. With its `i`-th move player II also assigns
an element of `I` to the `i`-th finite sequence, and II wins if the assignment is strictly
increasing, for the Kleene–Brouwer order, on the sequences alive at the play of first
coordinates. This payoff is closed, so the auxiliary game is determined by the Gale–Stewart
theorem (`MathlibExt.SetTheory.Determinacy.determined_of_isOpen`).

* If II wins the auxiliary game, II wins the original game by playing the first coordinates of
  the winning strategy: along an infinite branch the assigned elements would descend forever.
* If I wins the auxiliary game, I plays in the original game the move that the auxiliary
  strategy gives for `U`-almost all assignments, for the iterated product of `U` taken along the
  Kleene–Brouwer order of the alive sequences seen so far. If a resulting play were outside the
  analytic set, its tree would have no infinite branch, and a transfinite recursion along the
  Kleene–Brouwer order, choosing each value in countably many sets of `U`, would build an
  assignment for which the auxiliary play follows I's winning strategy and is won by II.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace MathlibExt.SetTheory.DeterminacyWanted

open MathlibExt.SetTheory.Determinacy

universe u

/-! ### Iterated ultrafilters -/

section Large

variable {N I : Type*} [LinearOrder N] (U : Ultrafilter I)

/-- `X` is large for the iterated product of `U` over the finite set of coordinates `F`, taken
in increasing order, the other coordinates being those of `g`: if `F` is empty, `g ∈ X`;
otherwise, for `U`-almost all values at the least coordinate of `F`, `X` is large over the
remaining coordinates. -/
private def Large (F : Finset N) (g : N → I) (X : Set (N → I)) : Prop :=
  if h : F.Nonempty then
    {a | Large (F.erase (F.min' h)) (Function.update g (F.min' h) a) X} ∈ U
  else g ∈ X
termination_by F.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.min'_mem F h)

private theorem large_empty (g : N → I) (X : Set (N → I)) : Large U ∅ g X ↔ g ∈ X := by
  rw [Large]
  simp

private theorem large_insert {a : N} {F : Finset N} (ha : ∀ x ∈ F, a < x) (g : N → I)
    (X : Set (N → I)) :
    Large U (insert a F) g X ↔ {b | Large U F (Function.update g a b) X} ∈ U := by
  have hne : (insert a F).Nonempty := Finset.insert_nonempty a F
  have hmin : (insert a F).min' hne = a := by
    apply le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self a F))
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact le_rfl
    · exact (ha y hy).le
  have haF : a ∉ F := fun h => lt_irrefl a (ha a h)
  rw [Large, dite_eq_left hne, hmin, Finset.erase_insert haF]

/-- Largeness over `F` ignores the coordinates of `g` in `F`, and those outside the set `D` of
coordinates on which `X` depends. -/
private theorem large_congr {D : Set N} {X : Set (N → I)}
    (hX : ∀ g g' : N → I, (∀ t ∈ D, g t = g' t) → (g ∈ X ↔ g' ∈ X)) (F : Finset N)
    (hF : ∀ t ∈ F, t ∈ D) {g g' : N → I} (hg : ∀ t ∈ D, t ∉ F → g t = g' t) :
    Large U F g X ↔ Large U F g' X := by
  classical
  induction F using Finset.induction_on_min generalizing g g' with
  | empty =>
    rw [large_empty, large_empty]
    exact hX g g' fun t ht => hg t ht (Finset.notMem_empty t)
  | insert a F ha ih =>
    rw [large_insert U ha, large_insert U ha]
    have : {b | Large U F (Function.update g a b) X} =
        {b | Large U F (Function.update g' a b) X} := by
      ext b
      refine ih (fun t ht => hF t (Finset.mem_insert_of_mem ht)) fun t ht htF => ?_
      by_cases hta : t = a
      · subst hta
        simp
      · rw [Function.update_of_ne hta, Function.update_of_ne hta]
        exact hg t ht fun h => (Finset.mem_insert.1 h).elim hta htF
    rw [this]

/-- A countably complete ultrafilter contains a fibre of every map to `ℕ`. -/
private theorem exists_preimage_singleton_mem [CountableInterFilter (U : Filter I)]
    (c : I → ℕ) : ∃ k, c ⁻¹' {k} ∈ U := by
  by_contra h
  push Not at h
  have hall : ∀ k, (c ⁻¹' {k})ᶜ ∈ U := fun k => Ultrafilter.compl_mem_iff_notMem.2 (h k)
  have hI : (⋂ k, (c ⁻¹' {k})ᶜ) ∈ U := countable_iInter_mem.2 hall
  have hempty : (⋂ k, (c ⁻¹' {k})ᶜ) = ∅ := by
    ext a
    simp only [mem_iInter, mem_compl_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
      iff_false, not_forall, not_not]
    exact ⟨c a, rfl⟩
  rw [hempty] at hI
  exact Ultrafilter.empty_notMem hI

/-- For a countably complete ultrafilter, every map to `ℕ` is almost everywhere constant for the
iterated product over any finite set of coordinates. -/
private theorem exists_large_eq [CountableInterFilter (U : Filter I)] (F : Finset N) (g : N → I)
    (h : (N → I) → ℕ) : ∃ k, Large U F g {g' | h g' = k} := by
  classical
  induction F using Finset.induction_on_min generalizing g with
  | empty => exact ⟨h g, (large_empty U g _).2 rfl⟩
  | insert a F ha ih =>
    choose k hk using fun b => ih (Function.update g a b)
    obtain ⟨k₀, hk₀⟩ := exists_preimage_singleton_mem U k
    refine ⟨k₀, (large_insert U ha g _).2 (Filter.mem_of_superset hk₀ fun b hb => ?_)⟩
    have hb' : k b = k₀ := hb
    have := hk b
    rwa [hb'] at this

/-- **The recursion along a well-founded order.** Let `P` be a set of coordinates on which the
order of `N` is well-founded, and let `X n` be countably many sets, each depending only on the
coordinates in a finite subset `F n` of `P` and large for the iterated product of `U` over them.
Then some assignment `η`, strictly increasing on `P` for a relation `lt` whose upper sets lie in
`U`, belongs to every `X n`. It is built by recursion along `P`, choosing the value at `s` in
countably many sets of `U`, so that for each `n` the coordinates of `F n` above `s` stay large. -/
private theorem exists_strictMono_mem [Countable N] [CountableInterFilter (U : Filter I)]
    (lt : I → I → Prop) (hlt : ∀ c, {a | lt c a} ∈ U)
    (P : N → Prop) (hwf : WellFounded fun t s => P t ∧ P s ∧ t < s)
    (F : ℕ → Finset N) (hFP : ∀ n, ∀ t ∈ F n, P t) (X : ℕ → Set (N → I))
    (hX : ∀ n (g g' : N → I), (∀ t ∈ F n, g t = g' t) → (g ∈ X n ↔ g' ∈ X n))
    (hlarge : ∀ n, ∃ g, Large U (F n) g (X n)) :
    ∃ η : N → I, (∀ t s, P t → P s → t < s → lt (η t) (η s)) ∧ ∀ n, η ∈ X n := by
  classical
  have hI : Nonempty I := ⟨(U.nonempty_of_mem Filter.univ_mem).some⟩
  let a₀ : I := Classical.arbitrary I
  have hXn : ∀ n, ∀ g g' : N → I, (∀ t ∈ (↑(F n) : Set N), g t = g' t) →
      (g ∈ X n ↔ g' ∈ X n) :=
    fun n g g' h => hX n g g' fun t ht => h t (Finset.mem_coe.2 ht)
  -- The set from which the value at `s` is chosen, given the values `e` at earlier coordinates.
  let C : N → (N → I) → Set I := fun s e =>
    {a | ∀ n, Large U ((F n).filter (s ≤ ·)) e (X n) →
        Large U ((F n).filter (s < ·)) (Function.update e s a) (X n)} ∩
      {a | ∀ t, P t → t < s → lt (e t) a}
  have hC : ∀ s e, C s e ∈ U := by
    intro s e
    refine Filter.inter_mem ?_ ?_
    · have : {a | ∀ n, Large U ((F n).filter (s ≤ ·)) e (X n) →
          Large U ((F n).filter (s < ·)) (Function.update e s a) (X n)} =
          ⋂ n, {a | Large U ((F n).filter (s ≤ ·)) e (X n) →
            Large U ((F n).filter (s < ·)) (Function.update e s a) (X n)} := by
        ext a
        simp
      rw [this]
      refine countable_iInter_mem.2 fun n => ?_
      by_cases hL : Large U ((F n).filter (s ≤ ·)) e (X n)
      · by_cases hsF : s ∈ F n
        · have hins : (F n).filter (s ≤ ·) = insert s ((F n).filter (s < ·)) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hsx⟩
              rcases hsx.lt_or_eq with h | h
              · exact Or.inr ⟨hx, h⟩
              · exact Or.inl h.symm
            · rintro (rfl | ⟨hx, hsx⟩)
              · exact ⟨hsF, le_rfl⟩
              · exact ⟨hx, hsx.le⟩
          rw [hins, large_insert U (fun x hx => (Finset.mem_filter.1 hx).2)] at hL
          exact Filter.mem_of_superset hL fun a ha _ => ha
        · have heq : (F n).filter (s ≤ ·) = (F n).filter (s < ·) := by
            ext x
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hx, hsx⟩
              exact ⟨hx, hsx.lt_of_ne fun h => hsF (h ▸ hx)⟩
            · rintro ⟨hx, hsx⟩
              exact ⟨hx, hsx.le⟩
          refine Filter.mem_of_superset Filter.univ_mem fun a _ hL' => ?_
          rw [heq] at hL'
          refine (large_congr U (hXn n) _
            (fun t ht => Finset.mem_coe.2 (Finset.mem_filter.1 ht).1) fun t ht _ => ?_).1 hL'
          rw [Function.update_of_ne]
          rintro rfl
          exact hsF (Finset.mem_coe.1 ht)
      · exact Filter.mem_of_superset Filter.univ_mem fun a _ h => absurd h hL
    · have : {a | ∀ t, P t → t < s → lt (e t) a} = ⋂ t, {a | P t → t < s → lt (e t) a} := by
        ext a
        simp
      rw [this]
      refine countable_iInter_mem.2 fun t => ?_
      by_cases ht : P t ∧ t < s
      · exact Filter.mem_of_superset (hlt (e t)) fun a ha _ _ => ha
      · exact Filter.mem_of_superset Filter.univ_mem fun a _ h1 h2 => absurd ⟨h1, h2⟩ ht
  let G : ∀ s, (∀ t, (P t ∧ P s ∧ t < s) → I) → I := fun s rec =>
    (U.nonempty_of_mem (hC s fun t => if h : P t ∧ P s ∧ t < s then rec t h else a₀)).some
  let η : N → I := hwf.fix G
  let e : N → N → I := fun s t => if _h : P t ∧ P s ∧ t < s then η t else a₀
  have hη : ∀ s, η s ∈ C s (e s) := by
    intro s
    have h1 : η s = G s fun t _ => η t := hwf.fix_eq G s
    rw [h1]
    exact Set.Nonempty.some_mem _
  have he : ∀ s t, P t → P s → t < s → e s t = η t := by
    intro s t hPt hPs hts
    simp only [e]
    rw [dite_eq_left ⟨hPt, hPs, hts⟩]
  -- The invariant: once the value at `s` is chosen, the coordinates above `s` remain large.
  have hinv : ∀ s, P s → ∀ n, Large U ((F n).filter (s < ·)) η (X n) := by
    intro s
    induction s using hwf.induction with
    | _ s ih =>
    intro hPs n
    have step1 : Large U ((F n).filter (s ≤ ·)) η (X n) := by
      by_cases hB : ((F n).filter (· < s)).Nonempty
      · have htmem := Finset.max'_mem _ hB
        set t := ((F n).filter (· < s)).max' hB with ht
        obtain ⟨htF, hts⟩ := Finset.mem_filter.1 htmem
        have hPt := hFP n t htF
        have hIH := ih t ⟨hPt, hPs, hts⟩ hPt n
        have heq : (F n).filter (t < ·) = (F n).filter (s ≤ ·) := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, htx⟩
            refine ⟨hx, ?_⟩
            by_contra hxs
            push Not at hxs
            exact absurd htx (not_lt.2 (Finset.le_max' _ x (Finset.mem_filter.2 ⟨hx, hxs⟩)))
          · rintro ⟨hx, hsx⟩
            exact ⟨hx, lt_of_lt_of_le hts hsx⟩
        rwa [heq] at hIH
      · have heq : (F n).filter (s ≤ ·) = F n := by
          ext x
          simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hx
          by_contra hxs
          push Not at hxs
          exact hB ⟨x, Finset.mem_filter.2 ⟨hx, hxs⟩⟩
        rw [heq]
        obtain ⟨g, hg⟩ := hlarge n
        exact (large_congr U (hXn n) (F n) (fun t ht => Finset.mem_coe.2 ht)
          fun t ht htn => absurd (Finset.mem_coe.1 ht) htn).1 hg
    have step1' : Large U ((F n).filter (s ≤ ·)) (e s) (X n) := by
      refine (large_congr U (hXn n) _ (fun t ht => Finset.mem_coe.2 (Finset.mem_filter.1 ht).1)
        fun t ht htn => ?_).1 step1
      have hts : t < s := by
        by_contra h
        exact htn (Finset.mem_filter.2 ⟨Finset.mem_coe.1 ht, not_lt.1 h⟩)
      exact (he s t (hFP n t (Finset.mem_coe.1 ht)) hPs hts).symm
    have step2 := (hη s).1 n step1'
    refine (large_congr U (hXn n) _ (fun t ht => Finset.mem_coe.2 (Finset.mem_filter.1 ht).1)
      fun t ht htn => ?_).1 step2
    have hts : t ≤ s := by
      by_contra h
      exact htn (Finset.mem_filter.2 ⟨Finset.mem_coe.1 ht, not_le.1 h⟩)
    rcases hts.lt_or_eq with hts | rfl
    · rw [Function.update_of_ne hts.ne]
      exact he s t (hFP n t (Finset.mem_coe.1 ht)) hPs hts
    · simp
  refine ⟨η, fun t s hPt hPs hts => ?_, fun n => ?_⟩
  · have := (hη s).2 t hPt hts
    rwa [he s t hPt hPs hts] at this
  · by_cases hFn : (F n).Nonempty
    · have htmem := Finset.max'_mem _ hFn
      have hI := hinv _ (hFP n _ htmem) n
      have hempty : (F n).filter ((F n).max' hFn < ·) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
        exact fun hx => Finset.le_max' _ x hx
      rwa [hempty, large_empty] at hI
    · rw [Finset.not_nonempty_iff_eq_empty] at hFn
      obtain ⟨g, hg⟩ := hlarge n
      rw [hFn, large_empty] at hg
      exact (hX n g η fun t ht => by simp [hFn] at ht).1 hg

end Large

/-! ### The Kleene–Brouwer order -/

/-- The key of a finite sequence for the Kleene–Brouwer order: its entries in `WithTop ℕ`,
followed by `⊤`. The lexicographic order on keys is the Kleene–Brouwer order: a proper extension
is smaller, and otherwise the first difference decides. -/
private def kbKey (l : List ℕ) : List (WithTop ℕ) := l.map (↑) ++ [⊤]

private theorem kbKey_injective : Function.Injective kbKey := by
  intro l l' h
  have h' : l.map ((↑) : ℕ → WithTop ℕ) = l'.map (↑) := List.append_cancel_right h
  exact (List.map_injective_iff.2 WithTop.coe_injective) h'

private theorem kbKey_append_cons_lt (s r : List ℕ) (a : ℕ) : kbKey (s ++ a :: r) < kbKey s := by
  have h1 : kbKey (s ++ a :: r) = s.map (↑) ++ ((a : WithTop ℕ) :: (r.map (↑) ++ [⊤])) := by
    simp [kbKey]
  have h2 : kbKey s = s.map (↑) ++ [⊤] := rfl
  rw [h1, h2]
  exact List.Lex.append_left _ (List.Lex.rel (WithTop.coe_lt_top a)) _

private theorem kbKey_lt_of_lt (s r r' : List ℕ) {a b : ℕ} (h : a < b) :
    kbKey (s ++ a :: r) < kbKey (s ++ b :: r') := by
  have h1 : ∀ c (q : List ℕ), kbKey (s ++ c :: q) =
      s.map (↑) ++ ((c : WithTop ℕ) :: (q.map (↑) ++ [⊤])) := by
    intro c q
    simp [kbKey]
  rw [h1, h1]
  exact List.Lex.append_left _ (List.Lex.rel (WithTop.coe_lt_coe.2 h)) _

/-- In a tree with no infinite branch, the relation "is a child of" is well-founded. -/
private theorem wellFounded_child (T : List ℕ → Prop) (hT : ∀ l l', T (l ++ l') → T l)
    (hb : ∀ b : ℕ → ℕ, ∃ n, ¬ T (history b n)) :
    WellFounded fun t s : List ℕ => T t ∧ ∃ a, t = s ++ [a] := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  have hpre : ∀ m n, m ≤ n → f m <+: f n := by
    intro m n hmn
    induction hmn with
    | refl => exact List.prefix_refl _
    | step _ ih =>
      obtain ⟨a, ha⟩ := (hf _).2
      rw [ha]
      exact ih.trans (List.prefix_append _ _)
  have hlen : ∀ n, (f n).length = (f 0).length + n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨a, ha⟩ := (hf n).2
      rw [ha, List.length_append, ih, List.length_singleton]
      omega
  have hTf : ∀ n, T (f n) := by
    intro n
    cases n with
    | zero =>
      obtain ⟨a, ha⟩ := (hf 0).2
      exact hT _ [a] (ha ▸ (hf 0).1)
    | succ n => exact (hf n).1
  let b : ℕ → ℕ := fun k => (f (k + 1)).getD k 0
  have key : ∀ n, history b n = (f n).take n := by
    intro n
    apply List.ext_getElem
    · rw [length_history, List.length_take, hlen]
      omega
    · intro i hi _
      rw [length_history] at hi
      have hi' : i < (f (i + 1)).length := by
        rw [hlen]
        omega
      rw [List.getElem_take]
      simp only [history, List.getElem_ofFn, b]
      rw [← List.getElem_eq_getD 0]
      exact (hpre (i + 1) n (by omega)).getElem hi'
  obtain ⟨n, hn⟩ := hb b
  apply hn
  rw [key]
  exact hT _ ((f n).drop n) (by rw [List.take_append_drop]; exact hTf n)

/-- **The Kleene–Brouwer order on a well-founded tree is well-founded.** If the tree `T` (a set
of finite sequences closed under initial segments) has no infinite branch, the Kleene–Brouwer
order is well-founded on the keys of its members. The proof goes down the tree: the members
extending `s` are those extending the children `s ++ [a]`, taken in increasing order of `a`,
followed by `s` itself. -/
private theorem wellFounded_kbKey (T : List ℕ → Prop) (hT : ∀ l l', T (l ++ l') → T l)
    (hb : ∀ b : ℕ → ℕ, ∃ n, ¬ T (history b n)) :
    WellFounded fun k k' : List (WithTop ℕ) =>
      (∃ l, T l ∧ kbKey l = k) ∧ (∃ l, T l ∧ kbKey l = k') ∧ k < k' := by
  let R : List ℕ → List ℕ → Prop := fun t s => T t ∧ T s ∧ kbKey t < kbKey s
  let Rs : List ℕ → List ℕ → List ℕ → Prop := fun s t' t => s <+: t' ∧ s <+: t ∧ R t' t
  have main : ∀ s t, Acc (Rs s) t := by
    intro s
    induction s using (wellFounded_child T hT hb).induction with
    | _ s ih =>
    have ih' : ∀ a t, Acc (Rs (s ++ [a])) t := by
      intro a t
      by_cases hTa : T (s ++ [a])
      · exact ih _ ⟨hTa, a, rfl⟩ t
      · constructor
        rintro t' ⟨⟨r, rfl⟩, -, hTt', -⟩
        exact absurd (hT _ _ hTt') hTa
    have hext : ∀ a t, s ++ [a] <+: t → Acc (Rs s) t := by
      intro a
      induction a using Nat.strong_induction_on with
      | _ a iha =>
      intro t
      induction ih' a t with
      | intro t _ ihacc =>
      intro hat
      constructor
      rintro t' ⟨hst', -, hTt', hTt, hlt⟩
      obtain ⟨r', rfl⟩ := hst'
      obtain ⟨r, rfl⟩ := hat
      cases r' with
      | nil =>
        rw [List.append_nil] at hlt
        have := kbKey_append_cons_lt s r a
        rw [List.append_assoc, List.singleton_append] at hlt
        exact absurd hlt (lt_asymm this)
      | cons c r'' =>
        rcases lt_trichotomy c a with hca | rfl | hac
        · exact iha c hca _ ⟨r'', by simp⟩
        · exact ihacc _ ⟨⟨r'', by simp⟩, ⟨r, rfl⟩, hTt', hTt, hlt⟩ ⟨r'', by simp⟩
        · have := kbKey_lt_of_lt s r r'' hac
          rw [List.append_assoc, List.singleton_append] at hlt
          exact absurd hlt (lt_asymm this)
    intro t
    by_cases hst : s <+: t
    · obtain ⟨r, rfl⟩ := hst
      cases r with
      | nil =>
        constructor
        rintro t' ⟨⟨r', rfl⟩, -, -, -, hlt⟩
        cases r' with
        | nil => exact absurd hlt (lt_irrefl _)
        | cons c r'' => exact hext c _ ⟨r'', by simp⟩
      | cons a r => exact hext a _ ⟨r, by simp⟩
    · constructor
      rintro t' ⟨-, hst', -⟩
      exact absurd hst' hst
  have hR : ∀ l, Acc R l := fun l =>
    Subrelation.accessible (fun {a b} h => ⟨List.nil_prefix, List.nil_prefix, h⟩) (main [] l)
  have hkey : ∀ l, Acc (fun k k' : List (WithTop ℕ) =>
      (∃ l, T l ∧ kbKey l = k) ∧ (∃ l, T l ∧ kbKey l = k') ∧ k < k') (kbKey l) := by
    intro l
    induction hR l with
    | intro l _ ih =>
    constructor
    rintro k' ⟨⟨l', hTl', rfl⟩, ⟨l'', hTl'', hl''⟩, hlt⟩
    obtain rfl := kbKey_injective hl''
    exact ih l' ⟨hTl', hTl'', hlt⟩
  refine ⟨fun k => ⟨k, fun k' hk' => ?_⟩⟩
  obtain ⟨⟨l', -, rfl⟩, -, -⟩ := hk'
  exact hkey l'

/-! ### Plays -/

/-- In the product of discrete topologies, a set that depends only on the first `m` moves is
open. -/
private theorem isOpen_of_history {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    {P : Set (ℕ → M)} (m : ℕ) (hP : ∀ z z', history z m = history z' m → z ∈ P → z' ∈ P) :
    IsOpen P := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  refine Filter.mem_of_superset ((PiNat.isOpen_cylinder (fun _ => M) z m).mem_nhds
    (PiNat.self_mem_cylinder z m)) fun z' hz' => hP z z' ?_ hz
  rw [history_eq_history_iff]
  intro i hi
  exact (hz' i hi).symm

section Lift

variable {A B : Type*}

/-- The play of `A × B` with first coordinates `x` whose second coordinate at time `n` is
`e` of the history of `x` and of the lifted play before time `n`. -/
private def liftPlay (e : List A → List (A × B) → B) (x : ℕ → A) : ℕ → A × B
  | n => (x n, e (history x n) (List.ofFn fun i : Fin n => liftPlay e x i))
termination_by n => n
decreasing_by exact i.isLt

private theorem liftPlay_eq (e : List A → List (A × B) → B) (x : ℕ → A) (n : ℕ) :
    liftPlay e x n = (x n, e (history x n) (history (liftPlay e x) n)) := by
  rw [liftPlay]
  rfl

private theorem fst_liftPlay (e : List A → List (A × B) → B) (x : ℕ → A) :
    (fun n => (liftPlay e x n).1) = x := by
  funext n
  rw [liftPlay_eq]

private theorem history_liftPlay_congr (e : List A → List (A × B) → B) {x x' : ℕ → A}
    {n : ℕ} (h : history x n = history x' n) :
    history (liftPlay e x) n = history (liftPlay e x') n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h' := history_eq_of_le (Nat.le_succ n) h
    have hxn : x n = x' n := history_eq_history_iff.1 h n (Nat.lt_succ_self n)
    rw [history_succ, history_succ, liftPlay_eq e x n, liftPlay_eq e x' n, ih h', h', hxn]

/-- A finite history continued by a default move. -/
private def extend (a : A) (p : List A) : ℕ → A := fun k => p.getD k a

private theorem history_extend (a : A) (x : ℕ → A) {m n : ℕ} (h : n ≤ m) :
    history (extend a (history x m)) n = history x n := by
  rw [history_eq_history_iff]
  intro i hi
  simp only [extend]
  rw [List.getD_eq_getElem?_getD, getElem?_history (by omega)]
  rfl

end Lift

/-! ### The tree of an analytic set -/

section Tree

variable (f : (ℕ → ℕ) → ℕ → ℕ)

/-- The finite sequence `l` is alive at the play `x` for the map `f` if some `y` extending `l`
has `f y` agreeing with `x` on the first `|l|` moves. -/
private def Alive (x : ℕ → ℕ) (l : List ℕ) : Prop :=
  ∃ y : ℕ → ℕ, history y l.length = l ∧ history (f y) l.length = history x l.length

private theorem take_history (y : ℕ → ℕ) {m n : ℕ} (h : n ≤ m) :
    (history y m).take n = history y n := by
  apply List.ext_getElem
  · simp only [List.length_take, length_history]
    omega
  · intro i h1 h2
    simp [history]

private theorem alive_of_append {x : ℕ → ℕ} {l l' : List ℕ} (h : Alive f x (l ++ l')) :
    Alive f x l := by
  obtain ⟨y, hy, hfy⟩ := h
  have hle : l.length ≤ (l ++ l').length := by simp
  refine ⟨y, ?_, history_eq_of_le hle hfy⟩
  rw [← take_history y hle, hy]
  simp

private theorem alive_congr {x x' : ℕ → ℕ} {l : List ℕ} {n : ℕ} (hn : l.length ≤ n)
    (h : history x n = history x' n) : Alive f x l ↔ Alive f x' l := by
  simp only [Alive, history_eq_of_le hn h]

private theorem alive_history_of_mem_range {x : ℕ → ℕ} (hx : x ∈ range f) :
    ∃ b : ℕ → ℕ, ∀ n, Alive f x (history b n) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, fun n => ⟨y, by rw [length_history], rfl⟩⟩

/-- A branch of the tree of alive sequences at `x` is a preimage of `x`, by continuity. -/
private theorem mem_range_of_alive (hf : Continuous f) {x : ℕ → ℕ} {b : ℕ → ℕ}
    (hb : ∀ n, Alive f x (history b n)) : x ∈ range f := by
  choose y hy hfy using hb
  simp only [length_history] at hy hfy
  have h1 : Filter.Tendsto y Filter.atTop (nhds b) := by
    rw [tendsto_pi_nhds]
    intro k
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_gt_atTop k] with n hn
    exact history_eq_history_iff.1 (hy n) k hn
  have h2 : Filter.Tendsto (fun n => f (y n)) Filter.atTop (nhds x) := by
    rw [tendsto_pi_nhds]
    intro k
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_gt_atTop k] with n hn
    exact history_eq_history_iff.1 (hfy n) k hn
  exact ⟨b, tendsto_nhds_unique ((hf.tendsto b).comp h1) h2⟩

end Tree

/-! ### The auxiliary game -/

section Auxiliary

variable {I : Type*}

/-- The finite sequence to which player II assigns an element at move `2 * i + 1`. -/
private def node (i : ℕ) : List ℕ := Denumerable.ofNat (List ℕ) i

private theorem length_node_le (i : ℕ) : (node i).length ≤ i := by
  have := Encodable.length_le_encode (node i)
  rwa [node, Denumerable.encode_ofNat] at this

private theorem node_encode (l : List ℕ) : node (Encodable.encode l) = l :=
  Denumerable.ofNat_encode l

/-- Player II wins the auxiliary play `z`: the elements `(z (2 * i + 1)).2` assigned to the
sequences `node i` alive at the play of first coordinates increase strictly along the
Kleene–Brouwer order. -/
private def AuxWin (f : (ℕ → ℕ) → ℕ → ℕ) (lt : I → I → Prop) (z : ℕ → ℕ × I) : Prop :=
  ∀ i j, Alive f (fun n => (z n).1) (node i) → Alive f (fun n => (z n).1) (node j) →
    kbKey (node i) < kbKey (node j) → lt (z (2 * i + 1)).2 (z (2 * j + 1)).2

private theorem history_fst {z z' : ℕ → ℕ × I} {m : ℕ} (h : history z m = history z' m) :
    history (fun n => (z n).1) m = history (fun n => (z' n).1) m := by
  rw [history_eq_history_iff] at h ⊢
  intro i hi
  rw [h i hi]

/-- The auxiliary game is open for player I. -/
private theorem isOpen_auxWin_compl [TopologicalSpace I] [DiscreteTopology I]
    (f : (ℕ → ℕ) → ℕ → ℕ) (lt : I → I → Prop) :
    IsOpen {z : ℕ → ℕ × I | ¬ AuxWin f lt z} := by
  have : {z : ℕ → ℕ × I | ¬ AuxWin f lt z} = ⋃ i, ⋃ j, {z |
      Alive f (fun n => (z n).1) (node i) ∧ Alive f (fun n => (z n).1) (node j) ∧
        kbKey (node i) < kbKey (node j) ∧ ¬ lt (z (2 * i + 1)).2 (z (2 * j + 1)).2} := by
    ext z
    simp [AuxWin]
  rw [this]
  refine isOpen_iUnion fun i => isOpen_iUnion fun j =>
    isOpen_of_history (2 * i + 2 * j + 2) ?_
  rintro z z' hzz' ⟨hi, hj, hij, hlt⟩
  have h1 := history_fst hzz'
  have hzi : z (2 * i + 1) = z' (2 * i + 1) := history_eq_history_iff.1 hzz' _ (by omega)
  have hzj : z (2 * j + 1) = z' (2 * j + 1) := history_eq_history_iff.1 hzz' _ (by omega)
  refine ⟨(alive_congr f ((length_node_le i).trans (by omega)) h1).1 hi,
    (alive_congr f ((length_node_le j).trans (by omega)) h1).1 hj, hij, ?_⟩
  rwa [← hzi, ← hzj]

/-- If player II wins the auxiliary game, player II also wins the game on the range of `f`, with
the first coordinates of the auxiliary strategy. -/
private theorem iiWins_range_of_iiWins_aux (f : (ℕ → ℕ) → ℕ → ℕ) (lt : I → I → Prop)
    (hwf : WellFounded lt) (a₀ : I) (h : IIWins {z : ℕ → ℕ × I | ¬ AuxWin f lt z}) :
    IIWins (range f) := by
  obtain ⟨τs, hτs⟩ := h
  let e : List ℕ → List (ℕ × I) → I := fun p q => if p.length % 2 = 1 then (τs q).2 else a₀
  refine ⟨fun p => (τs (history (liftPlay e (extend 0 p)) p.length)).1, fun x hx hxS => ?_⟩
  set z := liftPlay e x with hz_def
  have hz : FollowsII τs z := by
    intro n hn
    have hxn : x n =
        (τs (history (liftPlay e (extend 0 (history x n))) (history x n).length)).1 := hx n hn
    rw [length_history, history_liftPlay_congr e (history_extend 0 x le_rfl)] at hxn
    rw [hz_def, liftPlay_eq]
    refine Prod.ext hxn ?_
    simp only [e, length_history, hn]
    rfl
  have hwin : AuxWin f lt z := by
    by_contra hcon
    exact hτs z hz hcon
  have hfst : (fun n => (z n).1) = x := fst_liftPlay e x
  obtain ⟨b, hb⟩ := alive_history_of_mem_range f hxS
  let i : ℕ → ℕ := fun n => Encodable.encode (history b n)
  have hdesc : ∀ n, lt (z (2 * i (n + 1) + 1)).2 (z (2 * i n + 1)).2 := by
    intro n
    apply hwin
    · rw [hfst, node_encode]
      exact hb (n + 1)
    · rw [hfst, node_encode]
      exact hb n
    · rw [node_encode, node_encode, history_succ]
      exact kbKey_append_cons_lt _ [] _
  exact (wellFounded_iff_isEmpty_descending_chain.1 hwf).false
    ⟨fun n => (z (2 * i n + 1)).2, hdesc⟩

open scoped Classical in
/-- The second coordinates with which player I lifts a history `p` of the original game to the
auxiliary game, for the strategy `σs` and the assignment `g`: those of player I come from `σs`,
and those of player II are the values of `g` at the alive sequences. -/
private def extraI (f : (ℕ → ℕ) → ℕ → ℕ) (σs : List (ℕ × I) → ℕ × I) (a₀ : I)
    (g : List (WithTop ℕ) → I) (p : List ℕ) (q : List (ℕ × I)) : I :=
  if p.length % 2 = 0 then (σs q).2
  else if Alive f (extend 0 p) (node (p.length / 2)) then g (kbKey (node (p.length / 2)))
  else a₀

/-- The move of the auxiliary strategy `σs` after the history `p`, lifted with the
assignment `g`. -/
private def respI (f : (ℕ → ℕ) → ℕ → ℕ) (σs : List (ℕ × I) → ℕ × I) (a₀ : I)
    (p : List ℕ) (g : List (WithTop ℕ) → I) : ℕ :=
  (σs (history (liftPlay (extraI f σs a₀ g) (extend 0 p)) p.length)).1

open scoped Classical in
/-- The keys of the sequences alive at the history `p` to which player II has already assigned
an element. -/
private def nodesI (f : (ℕ → ℕ) → ℕ → ℕ) (p : List ℕ) : Finset (List (WithTop ℕ)) :=
  ((Finset.range (p.length / 2)).filter fun i => Alive f (extend 0 p) (node i)).image
    fun i => kbKey (node i)

private theorem respI_congr (f : (ℕ → ℕ) → ℕ → ℕ) (σs : List (ℕ × I) → ℕ × I) (a₀ : I)
    (p : List ℕ) {g g' : List (WithTop ℕ) → I} (h : ∀ t ∈ nodesI f p, g t = g' t) :
    respI f σs a₀ p g = respI f σs a₀ p g' := by
  have key : ∀ m ≤ p.length, history (liftPlay (extraI f σs a₀ g) (extend 0 p)) m =
      history (liftPlay (extraI f σs a₀ g') (extend 0 p)) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      rw [history_succ, history_succ, liftPlay_eq _ _ m, liftPlay_eq _ _ m, ih']
      congr 3
      rw [extraI, extraI, length_history]
      split_ifs with h1 h2
      · rfl
      · apply h
        simp only [nodesI, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
        refine ⟨m / 2, ⟨by omega, ?_⟩, rfl⟩
        exact (alive_congr f (n := m) ((length_node_le (m / 2)).trans (by omega))
          (history_extend 0 (extend 0 p) le_rfl)).1 h2
      · rfl
  simp only [respI]
  rw [key p.length le_rfl]

/-- If player I wins the auxiliary game, player I also wins the game on the range of `f`,
playing at each turn the move of the auxiliary strategy for `U`-almost all assignments. -/
private theorem iWins_range_of_iWins_aux (U : Ultrafilter I) [CountableInterFilter (U : Filter I)]
    (f : (ℕ → ℕ) → ℕ → ℕ) (hf : Continuous f) (lt : I → I → Prop)
    (hup : ∀ c, {a | lt c a} ∈ U) (a₀ : I) (h : IWins {z : ℕ → ℕ × I | ¬ AuxWin f lt z}) :
    IWins (range f) := by
  obtain ⟨σs, hσs⟩ := h
  let σ : List ℕ → ℕ := fun p =>
    Classical.choose (exists_large_eq U (nodesI f p) (fun _ => a₀) (respI f σs a₀ p))
  have hσ : ∀ p, Large U (nodesI f p) (fun _ => a₀) {g | respI f σs a₀ p g = σ p} := fun p =>
    Classical.choose_spec (exists_large_eq U (nodesI f p) (fun _ => a₀) (respI f σs a₀ p))
  refine ⟨σ, fun x hx => ?_⟩
  by_contra hxS
  have hb : ∀ b : ℕ → ℕ, ∃ n, ¬ Alive f x (history b n) := by
    intro b
    by_contra hcon
    push Not at hcon
    exact hxS (mem_range_of_alive f hf hcon)
  have hwf := wellFounded_kbKey (Alive f x) (fun l l' h => alive_of_append f h) hb
  have hFP : ∀ n, ∀ t ∈ nodesI f (history x (2 * n)), ∃ l, Alive f x l ∧ kbKey l = t := by
    intro n t ht
    simp only [nodesI, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      length_history] at ht
    obtain ⟨i, ⟨hi, hal⟩, rfl⟩ := ht
    exact ⟨node i, (alive_congr f ((length_node_le i).trans (by omega))
      (history_extend 0 x le_rfl)).1 hal, rfl⟩
  have hX : ∀ n (g g' : List (WithTop ℕ) → I),
      (∀ t ∈ nodesI f (history x (2 * n)), g t = g' t) →
      (g ∈ {g | respI f σs a₀ (history x (2 * n)) g = x (2 * n)} ↔
        g' ∈ {g | respI f σs a₀ (history x (2 * n)) g = x (2 * n)}) := by
    intro n g g' hgg'
    simp only [Set.mem_ofPred_eq, respI_congr f σs a₀ _ hgg']
  have hlarge : ∀ n, ∃ g, Large U (nodesI f (history x (2 * n))) g
      {g | respI f σs a₀ (history x (2 * n)) g = x (2 * n)} := by
    intro n
    refine ⟨fun _ => a₀, ?_⟩
    have hxn : x (2 * n) = σ (history x (2 * n)) := hx (2 * n) (by omega)
    rw [hxn]
    exact hσ _
  obtain ⟨η, hηmono, hηX⟩ := exists_strictMono_mem U lt hup _ hwf
    (fun n => nodesI f (history x (2 * n))) hFP _ hX hlarge
  set z := liftPlay (extraI f σs a₀ η) x with hz_def
  have hz : FollowsI σs z := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have h1 : respI f σs a₀ (history x (2 * m)) η = x (2 * m) := hηX m
    simp only [respI, length_history] at h1
    rw [history_liftPlay_congr _ (history_extend 0 x le_rfl)] at h1
    rw [hz_def, liftPlay_eq]
    refine Prod.ext h1.symm ?_
    simp only [extraI, length_history, hn]
    rfl
  apply hσs z hz
  intro i j hi hj hij
  have hfst : (fun n => (z n).1) = x := fst_liftPlay _ x
  rw [hfst] at hi hj
  have hzk : ∀ k, Alive f x (node k) → (z (2 * k + 1)).2 = η (kbKey (node k)) := by
    intro k hk
    rw [hz_def, liftPlay_eq]
    have h2 : (2 * k + 1) / 2 = k := by omega
    have h3 : Alive f (extend 0 (history x (2 * k + 1))) (node k) :=
      (alive_congr f ((length_node_le k).trans (by omega)) (history_extend 0 x le_rfl)).2 hk
    rw [extraI, length_history, h2, ite_eq_right (by omega), ite_eq_left h3]
  rw [hzk i hi, hzk j hj]
  exact hηmono _ _ ⟨node i, hi, rfl⟩ ⟨node j, hj, rfl⟩ hij

end Auxiliary

/-- A `κ`-complete nonprincipal ultrafilter on a set of size `κ` contains every final segment of
a well-order of minimal type on that set. -/
private theorem exists_wellFounded_upper {I : Type u} (U : Ultrafilter I) {κ : Cardinal.{u}}
    (hI : Cardinal.mk I = κ) [CardinalInterFilter (U : Filter I) κ]
    (hcof : (U : Filter I) ≤ Filter.cofinite) :
    ∃ lt : I → I → Prop, WellFounded lt ∧ ∀ c, {a | lt c a} ∈ U := by
  obtain ⟨r, wo, hr⟩ := Cardinal.exists_ord_eq I
  refine ⟨r, wo.wf, fun c => ?_⟩
  have hsmall : Cardinal.mk {a | r a c} < κ := by
    rw [← hI]
    have := Cardinal.card_typein_lt (r := r) c hr
    rw [Ordinal.card_typein] at this
    exact this
  have h1 : {a | r a c}ᶜ ∈ U := by
    have : {a | r a c}ᶜ = ⋂ a ∈ {a | r a c}, ({a}ᶜ : Set I) := by
      ext x
      simp only [mem_compl_iff, Set.mem_ofPred_eq, mem_iInter, mem_singleton_iff]
      exact ⟨fun h i hi hxi => h (hxi ▸ hi), fun h hx => h x hx rfl⟩
    rw [this]
    exact (Filter.cardinal_bInter_mem hsmall).2 fun a _ => hcof (Filter.mem_cofinite.2 (by simp))
  have h2 : ({c}ᶜ : Set I) ∈ U := hcof (Filter.mem_cofinite.2 (by simp))
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) fun a ⟨ha1, ha2⟩ => ?_
  rcases trichotomous_of r a c with h | h | h
  · exact absurd h ha1
  · exact absurd h ha2
  · exact h

/-- **Martin's analytic determinacy theorem.** If there is a measurable cardinal, every analytic
subset of Baire space `ℕ^ℕ` is determined (D. A. Martin, *Measurable cardinals and analytic
games*, Fund. Math. 66 (1970) 287–291; Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009,
Theorem 6G.7, from the partition property that a measurable cardinal has by 6G.2 and 6G.5;
Woodin, *The continuum hypothesis, Part I*, Notices AMS 48 (2001)). The measurable cardinal may
live in any universe. -/
theorem determined_of_analyticSet_of_isMeasurable {κ : Cardinal.{u}}
    (hκ : MetaMathlibExt.IsMeasurable κ) {S : Set (ℕ → ℕ)} (hS : AnalyticSet S) :
    Determined S := by
  obtain ⟨hκ0, I, hI, U, hUκ, hcof⟩ := hκ
  have : CountableInterFilter (U : Filter I) := CardinalInterFilter.toCountableInterFilter _ hκ0
  obtain ⟨lt, hwf, hup⟩ := exists_wellFounded_upper U hI hcof
  obtain ⟨a₀⟩ : Nonempty I := ⟨(U.nonempty_of_mem Filter.univ_mem).some⟩
  obtain ⟨β, tβ, hβ, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hS
  rcases isEmpty_or_nonempty β with hβe | hβne
  · refine Or.inr ⟨fun _ => 0, fun x _ hx => ?_⟩
    obtain ⟨b, -⟩ := hx
    exact hβe.false b
  · obtain ⟨h, hh, hsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective β
    have hrange : range g = range (g ∘ h) := by
      rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    rw [hrange]
    let _ : TopologicalSpace I := ⊥
    have : DiscreteTopology I := ⟨rfl⟩
    have : Nonempty I := ⟨a₀⟩
    rcases determined_of_isOpen (isOpen_auxWin_compl (g ∘ h) lt) with hI' | hII'
    · exact Or.inl (iWins_range_of_iWins_aux U (g ∘ h) (hg.comp hh) lt hup a₀ hI')
    · exact Or.inr (iiWins_range_of_iiWins_aux (g ∘ h) lt hwf a₀ hII')

end MathlibExt.SetTheory.DeterminacyWanted
