/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ogden's lemma for context-free languages
-/
module

public import CSLibExt.Computability.Languages.ContextFree.Pumping
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ogden's lemma for context-free languages

A marked word is a word over `T × Bool`; its letters with second component `true` are marked.
`Cslib.Language.IsContextFree.ogden` states Ogden's lemma: for a context-free language `L` there
is a bound `n > 0` such that every marked word whose letters form a word of `L` and which has at
least `n` marked letters splits as `u ++ v ++ x ++ y ++ z`, where `v ++ y` has a marked letter,
`v ++ x ++ y` has at most `n` marked letters, and all pumped words
`u ++ v^[i] ++ x ++ y^[i] ++ z` have their letters in `L`. Marking every letter gives the pumping
lemma.

The lemma is due to W. F. Ogden, *A helpful result for proving inherent ambiguity*, Mathematical
Systems Theory 2(3) (1968), 191–194, doi:10.1007/BF01694004; see also J. E. Hopcroft and
J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, Addison-Wesley
(1979), p. 128. The proof here was reconstructed independently along the lines of the usual
textbook argument (descend through branch points, pigeonhole on a repeated nonterminal). It uses
the semantic derivation contexts `YieldsContext` of `Pumping.lean` in place of parse trees and
needs no normal form.
* `exists_descent`: from a nonterminal whose yield has more than `R` marked letters (`R` bounds
  the production lengths), descend to the first *branch point*, a production whose output splits
  the marked letters among several symbols, and continue into the symbol with the most marked
  letters. The context of the descent has a marked letter, and the marked count drops at most by
  the factor `R`.
* `exists_window`: descend until the marked count is at most `R ^ (K + 1)`, keeping it above
  `R ^ K`, where `K` counts the nonterminals with productions.
* `ogden_of_bound`, `pumping_of_bound`: the lemma for a given grammar with the explicit bound
  `R ^ (K + 1)` (`K` the length of a list containing every nonterminal with a production), and
  with every letter marked, the pumping
  lemma with that bound; `Decidability/ContextFree.lean` uses it to decide infiniteness.
* `ogden_chain`: from there, `K` further descents visit `K + 1` nonterminals, so one repeats. The
  context between the two visits pumps; it has a marked letter, and the upper visit's yield has at
  most `R ^ (K + 1)` marked letters.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T : Type*}

/-- **Number of marked letters.** A marked word over an alphabet $T$ is a word whose letters are
pairs $(a, b)$ with $a \in T$ and $b$ a Boolean; the letter $(a, b)$ is marked when $b$ is true.
The number of marked letters of a marked word $w$ is the number of letters of $w$ that are
marked, counted with multiplicity. -/
def marks (w : List (T × Bool)) : ℕ :=
  w.countP (·.2)

@[simp]
theorem marks_nil : marks ([] : List (T × Bool)) = 0 :=
  rfl

@[simp]
theorem marks_append (u v : List (T × Bool)) : marks (u ++ v) = marks u + marks v :=
  List.countP_append

theorem marks_le_length (w : List (T × Bool)) : marks w ≤ w.length :=
  List.countP_le_length

variable {g : ContextFreeGrammar T}

private theorem YieldsH.nil_inv {w : List T} {n : ℕ} (h : YieldsH g [] w n) : w = [] := by
  cases h
  rfl

/-- A nonterminal that yields a word is the input of a production. -/
private theorem mem_image_input_of_yields {A : g.NT} {w : List T}
    (h : Yields g [Symbol.nonterminal A] w) : A ∈ g.rules.image ContextFreeRule.input := by
  generalize hα : [Symbol.nonterminal A] = α at h
  cases h with
  | nil => simp at hα
  | terminal => simp at hα
  | @nonterminal r hr _ _ _ _ _ =>
      simp only [List.cons.injEq, Symbol.nonterminal.injEq] at hα
      rw [hα.1]
      exact Finset.mem_image_of_mem _ hr

/-- A derivation forest has a piece carrying at least the average number of marked letters. -/
private theorem exists_heavy_piece {n : ℕ} :
    ∀ (α : List (Symbol T g.NT)) (x : List (T × Bool)), α ≠ [] →
      YieldsH g α (x.map Prod.fst) n →
      ∃ α₁ s α₂ l y r, α = α₁ ++ s :: α₂ ∧ x = l ++ y ++ r ∧ Yields g α₁ (l.map Prod.fst) ∧
        YieldsH g [s] (y.map Prod.fst) n ∧ Yields g α₂ (r.map Prod.fst) ∧
        marks x ≤ α.length * marks y
  | [], _, hne, _ => absurd rfl hne
  | s :: α, x, _, h => by
      obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := YieldsH.append_inv (u := [s]) (v := α) h
      obtain ⟨x₁, x₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.1 hw
      by_cases hα : α = []
      · subst hα
        have hx₂ : x₂ = [] := List.map_eq_nil_iff.1 h₂.nil_inv
        subst hx₂
        exact ⟨[], s, [], [], x₁, [], rfl, by simp, Yields.nil, h₁, Yields.nil, by simp⟩
      · obtain ⟨α₁, s', α₂, l, y, r, hα', rfl, hl, hy, hr, hle⟩ := exists_heavy_piece α x₂ hα h₂
        by_cases hcmp : marks y ≤ marks x₁
        · refine ⟨[], s, α, [], x₁, l ++ y ++ r, rfl, by simp, Yields.nil, h₁,
            Yields.of_yieldsH h₂, ?_⟩
          have := Nat.mul_le_mul_left α.length hcmp
          simp only [marks_append, List.length_cons] at hle ⊢
          rw [Nat.add_one_mul]
          omega
        · refine ⟨s :: α₁, s', α₂, x₁ ++ l, y, r, by simp [hα'], by simp [List.append_assoc], ?_,
            hy, hr, ?_⟩
          · simpa using (Yields.of_yieldsH h₁).append hl
          · simp only [marks_append, List.length_cons] at hle ⊢
            have := Nat.mul_le_mul_left α.length (Nat.le_of_lt (Nat.lt_of_not_le hcmp))
            rw [Nat.add_one_mul]
            omega

private theorem marks_le_one_of_terminal {a : T} {y : List (T × Bool)} {n : ℕ}
    (h : YieldsH g [Symbol.terminal a] (y.map Prod.fst) n) : marks y ≤ 1 := by
  generalize hw : y.map Prod.fst = w at h
  cases h with
  | terminal _ hrest =>
      have hlen := congrArg List.length hw
      rw [hrest.nil_inv] at hlen
      simp only [List.length_map, List.length_cons, List.length_nil] at hlen
      have := marks_le_length y
      omega

/-- **One descent step**: from a nonterminal whose yield has more than `R` marked letters, reach a
nonterminal below the first branch point, through a context with a marked letter, losing at most
a factor `R` of the marked letters. -/
private theorem exists_descent {R : ℕ} (hR : ∀ r ∈ g.rules, r.output.length ≤ R) :
    ∀ (H : ℕ) (A : g.NT) (x : List (T × Bool)),
      YieldsH g [Symbol.nonterminal A] (x.map Prod.fst) H → R < marks x →
      ∃ B l y r, x = l ++ y ++ r ∧ YieldsContext g A B (l.map Prod.fst) (r.map Prod.fst) ∧
        Yields g [Symbol.nonterminal B] (y.map Prod.fst) ∧ 0 < marks (l ++ r) ∧
        marks x ≤ R * marks y := by
  intro H
  induction H using Nat.strong_induction_on with
  | _ H ih =>
    intro A x h hx
    generalize hw : x.map Prod.fst = w at h
    generalize hα : [Symbol.nonterminal A] = α at h
    cases h with
    | nil => simp at hα
    | terminal => simp at hα
    | @nonterminal r hr u w₁ w₂ n₀ m₀ hout hrest =>
      simp only [List.cons.injEq, Symbol.nonterminal.injEq] at hα
      obtain ⟨rfl, rfl⟩ := hα
      rw [hrest.nil_inv, List.append_nil] at hw
      subst hw
      have hne : r.output ≠ [] := by
        intro he
        rw [he] at hout
        have hx0 : x = [] := List.map_eq_nil_iff.1 hout.nil_inv
        subst hx0
        simp at hx
      obtain ⟨α₁, s, α₂, l, y, rr, hform, rfl, hl, hy, hrr, hle⟩ := exists_heavy_piece _ x hne hout
      have hle' : marks (l ++ y ++ rr) ≤ R * marks y :=
        hle.trans (Nat.mul_le_mul_right _ (hR r hr))
      cases s with
      | terminal a =>
          exfalso
          have h1 := marks_le_one_of_terminal hy
          have := Nat.mul_le_mul_left R h1
          omega
      | nonterminal B =>
          have hctx : YieldsContext g r.input B (l.map Prod.fst) (rr.map Prod.fst) :=
            YieldsContext.of_rule hr hform hl hrr
          by_cases hpos : 0 < marks (l ++ rr)
          · exact ⟨B, l, y, rr, rfl, hctx, Yields.of_yieldsH hy, hpos, hle'⟩
          · simp only [marks_append] at hpos hx hle'
            have hlt : n₀ < max (n₀ + 1) m₀ := by omega
            obtain ⟨B', l', y', r', rfl, hctx', hyields, hpos', hle''⟩ :=
              ih n₀ hlt B y hy (by omega)
            refine ⟨B', l ++ l', y', r' ++ rr, by simp [List.append_assoc], ?_, hyields, ?_, ?_⟩
            · simpa [List.map_append] using hctx.trans hctx'
            · simp only [marks_append] at hpos' ⊢
              omega
            · simp only [marks_append] at hle'' ⊢
              omega

/-- Descend until the number of marked letters is at most `R ^ (K + 1)`, keeping it above
`R ^ K`. -/
private theorem exists_window {R : ℕ} (hR : ∀ r ∈ g.rules, r.output.length ≤ R) (K : ℕ) :
    ∀ (m : ℕ) (A : g.NT) (x : List (T × Bool)), marks x = m →
      Yields g [Symbol.nonterminal A] (x.map Prod.fst) → R ^ K < marks x →
      ∃ B l y r, x = l ++ y ++ r ∧ YieldsContext g A B (l.map Prod.fst) (r.map Prod.fst) ∧
        Yields g [Symbol.nonterminal B] (y.map Prod.fst) ∧ R ^ K < marks y ∧
        marks y ≤ R ^ (K + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A x hm h hK
    by_cases hle : marks x ≤ R ^ (K + 1)
    · exact ⟨A, [], x, [], by simp, by simpa using YieldsContext.refl (g := g) A, h, hK, hle⟩
    · obtain ⟨H, hH⟩ := YieldsH.of_yields h
      have hRle : R ≤ R ^ (K + 1) := Nat.le_self_pow (by omega) R
      obtain ⟨B, l, y, r, rfl, hctx, hy, hpos, hxy⟩ := exists_descent hR H A _ hH (by omega)
      have hK' : R ^ K < marks y := by
        have h1 : R * R ^ K < R * marks y := by
          rw [← pow_succ']
          omega
        exact Nat.lt_of_mul_lt_mul_left h1
      simp only [marks_append] at hpos hm
      obtain ⟨B', l', y', r', rfl, hctx', hy', hK'', hle'⟩ :=
        ih (marks y) (by omega) B y rfl hy hK'
      refine ⟨B', l ++ l', y', r' ++ r, by simp [List.append_assoc], ?_, hy', hK'', hle'⟩
      simpa [List.map_append] using hctx.trans hctx'

/-- A node labeled `B` above the current node (labeled `A`, yielding `x`) in a decomposition of
`w`: the context between them has a marked letter, and the yield of `B` has at most `n` marked
letters. -/
private def OgdenAncestor (g : ContextFreeGrammar T) (w : List (T × Bool)) (n : ℕ) (B A : g.NT)
    (x : List (T × Bool)) : Prop :=
  ∃ lg rg l r, w = lg ++ (l ++ x ++ r) ++ rg ∧
    YieldsContext g g.initial B (lg.map Prod.fst) (rg.map Prod.fst) ∧
    YieldsContext g B A (l.map Prod.fst) (r.map Prod.fst) ∧ 0 < marks (l ++ r) ∧
    marks (l ++ x ++ r) ≤ n

/-- The conclusion of Ogden's lemma for `w`, with pumped words derived in `g`. -/
private def OgdenSplit (g : ContextFreeGrammar T) (w : List (T × Bool)) (n : ℕ) : Prop :=
  ∃ u v x y z : List (T × Bool), w = u ++ v ++ x ++ y ++ z ∧ 0 < marks (v ++ y) ∧
    marks (v ++ x ++ y) ≤ n ∧
    ∀ i : ℕ, Yields g [Symbol.nonterminal g.initial]
      ((u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z).map Prod.fst)

/-- A repeated nonterminal pumps. -/
private theorem ogdenSplit_of_ancestor {w x : List (T × Bool)} {n : ℕ} {A : g.NT}
    (hx : Yields g [Symbol.nonterminal A] (x.map Prod.fst)) (hanc : OgdenAncestor g w n A A x) :
    OgdenSplit g w n := by
  obtain ⟨lg, rg, l, r, hw, hc₁, hc₂, hpos, hle⟩ := hanc
  refine ⟨lg, l, x, r, rg, by rw [hw]; simp [List.append_assoc], hpos, by simpa using hle,
    fun i => ?_⟩
  have := hc₁ _ (hc₂.iterate hx i)
  simpa [List.map_append, List.map_flatten, List.map_replicate, List.append_assoc] using this

/-- Descend, recording the visited nonterminals, until one repeats. -/
private theorem ogden_chain {R : ℕ} (hR : ∀ r ∈ g.rules, r.output.length ≤ R)
    (w : List (T × Bool)) (n : ℕ) :
    ∀ (k : ℕ) (vis : Finset g.NT) (A : g.NT) (x lg rg : List (T × Bool)),
      vis ⊆ g.rules.image ContextFreeRule.input →
      (g.rules.image ContextFreeRule.input).card ≤ vis.card + k → R ^ k < marks x →
      Yields g [Symbol.nonterminal A] (x.map Prod.fst) → w = lg ++ x ++ rg →
      YieldsContext g g.initial A (lg.map Prod.fst) (rg.map Prod.fst) → marks x ≤ n →
      (∀ B ∈ vis, OgdenAncestor g w n B A x) → OgdenSplit g w n := by
  intro k
  induction k with
  | zero =>
    intro vis A x lg rg hvis hcard hK hx hw hctx hn hanc
    by_cases hA : A ∈ vis
    · exact ogdenSplit_of_ancestor hx (hanc A hA)
    · exfalso
      have hsub : insert A vis ⊆ g.rules.image ContextFreeRule.input :=
        Finset.insert_subset (mem_image_input_of_yields hx) hvis
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hA] at this
      omega
  | succ k ih =>
    intro vis A x lg rg hvis hcard hK hx hw hctx hn hanc
    by_cases hA : A ∈ vis
    · exact ogdenSplit_of_ancestor hx (hanc A hA)
    · obtain ⟨H, hH⟩ := YieldsH.of_yields hx
      have hRle : R ≤ R ^ (k + 1) := Nat.le_self_pow (by omega) R
      obtain ⟨B, l, y, r, rfl, hAB, hy, hpos, hxy⟩ := exists_descent hR H A _ hH (by omega)
      have hK' : R ^ k < marks y := by
        have h1 : R * R ^ k < R * marks y := by
          rw [← pow_succ']
          omega
        exact Nat.lt_of_mul_lt_mul_left h1
      have hmy : marks y ≤ marks (l ++ y ++ r) := by simp only [marks_append]; omega
      refine ih (insert A vis) B y (lg ++ l) (r ++ rg)
        (Finset.insert_subset (mem_image_input_of_yields hx) hvis)
        (by rw [Finset.card_insert_of_notMem hA]; omega) hK' hy
        (by rw [hw]; simp [List.append_assoc])
        (by simpa [List.map_append] using hctx.trans hAB) (hmy.trans hn) ?_
      intro B' hB'
      rcases Finset.mem_insert.1 hB' with rfl | hB'
      · exact ⟨lg, rg, l, r, by rw [hw], hctx, hAB, hpos, hn⟩
      · obtain ⟨lg', rg', l', r', hw', hc₁, hc₂, hpos', hle'⟩ := hanc B' hB'
        refine ⟨lg', rg', l' ++ l, r ++ r', by rw [hw']; simp [List.append_assoc], hc₁,
          by simpa [List.map_append] using hc₂.trans hAB, ?_, ?_⟩
        · simp only [marks_append] at hpos' ⊢
          omega
        · simp only [marks_append] at hle' ⊢
          omega

/-- The productions of a grammar have bounded length. -/
private theorem exists_output_length_bound (g : ContextFreeGrammar T) :
    ∃ R, 2 ≤ R ∧ ∀ r ∈ g.rules, r.output.length ≤ R :=
  ⟨max 2 (g.rules.sup fun r => r.output.length), le_max_left _ _,
    fun _ hr => (Finset.le_sup (f := fun r => r.output.length) hr).trans (le_max_right _ _)⟩

/-- **Ogden's lemma for a grammar, with an explicit bound.** Let $g$ be a context-free grammar
over an alphabet $T$ and let $R$, $K$, $n$ be natural numbers with $R \ge 2$ such that the
right-hand side of every production of $g$ has length at most $R$, some list of at most $K$
nonterminals contains the left-hand side of every production of $g$, and $R^{K+1} \le n$. A
marked word is a word whose letters are pairs $(a, b)$ with $a \in T$ and $b$ a Boolean, the
letter being marked when $b$ is true; its underlying word is the word of first components. Then
every marked word $w$ whose underlying word lies in the language of $g$ and which has at least
$n$ marked letters can be written as $w = uvxyz$ with marked words $u, v, x, y, z$ such that $vy$
has at least one marked letter, $vxy$ has at most $n$ marked letters, and for every natural
number $i$ the underlying word of $u v^i x y^i z$ lies in the language of $g$, where $v^i$ is the
concatenation of $i$ copies of $v$. -/
theorem ogden_of_bound (g : ContextFreeGrammar T) {R K n : ℕ} (hR2 : 2 ≤ R)
    (hR : ∀ r ∈ g.rules, r.output.length ≤ R)
    (hK : ∃ l : List g.NT, l.length ≤ K ∧ ∀ r ∈ g.rules, r.input ∈ l) (hn : R ^ (K + 1) ≤ n) :
    ∀ w : List (T × Bool), w.map Prod.fst ∈ g.language → n ≤ marks w →
      ∃ u v x y z : List (T × Bool), w = u ++ v ++ x ++ y ++ z ∧ 0 < marks (v ++ y) ∧
        marks (v ++ x ++ y) ≤ n ∧
        ∀ i : ℕ, (u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++
          z).map Prod.fst ∈ g.language := by
  intro w hw hn'
  set K₀ := (g.rules.image ContextFreeRule.input).card
  have hK₀ : K₀ ≤ K := by
    obtain ⟨l, hl, hmem⟩ := hK
    refine (Finset.card_le_card fun A hA => ?_).trans ((List.toFinset_card_le l).trans hl)
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hA
    exact List.mem_toFinset.2 (hmem r hr)
  have hn₀ : R ^ (K₀ + 1) ≤ n :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hn
  have hy := mem_language_iff_yields.1 hw
  have hlt : R ^ K₀ < R ^ (K₀ + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  obtain ⟨B, l, y, r, hwB, hctx, hyB, hK', hle⟩ :=
    exists_window hR K₀ (marks w) g.initial w rfl hy (by omega)
  obtain ⟨u, v, x, y', z, hsplit, hpos, hvxy, hpump⟩ :=
    ogden_chain hR w (R ^ (K₀ + 1)) K₀ ∅ B y l r (Finset.empty_subset _) (by simp [K₀]) hK' hyB
      hwB hctx hle (by simp)
  exact ⟨u, v, x, y', z, hsplit, hpos, hvxy.trans hn₀,
    fun i => mem_language_iff_yields.2 (hpump i)⟩

/-- **The pumping lemma for a grammar, with an explicit bound.** Let $g$ be a context-free grammar
over an alphabet $T$ and let $R$, $K$, $n$ be natural numbers with $R \ge 2$ such that the
right-hand side of every production of $g$ has length at most $R$, some list of at most $K$
nonterminals contains the left-hand side of every production of $g$, and $R^{K+1} \le n$. Then
every word $w$ in the language of $g$ of length at least $n$ can be written as $w = uvxyz$ with
words $u, v, x, y, z$ over $T$ such that $vy$ is nonempty, $vxy$ has length at most $n$, and
$u v^i x y^i z$ lies in the language of $g$ for every natural number $i$, where $v^i$ is the
concatenation of $i$ copies of $v$.

It follows from Ogden's lemma with every letter marked. -/
theorem pumping_of_bound (g : ContextFreeGrammar T) {R K n : ℕ} (hR2 : 2 ≤ R)
    (hR : ∀ r ∈ g.rules, r.output.length ≤ R)
    (hK : ∃ l : List g.NT, l.length ≤ K ∧ ∀ r ∈ g.rules, r.input ∈ l) (hn : R ^ (K + 1) ≤ n) :
    ∀ w ∈ g.language, n ≤ w.length → ∃ u v x y z : List T, w = u ++ v ++ x ++ y ++ z ∧
      v ++ y ≠ [] ∧ (v ++ x ++ y).length ≤ n ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈
        g.language := by
  intro w hw hlen
  have hall : marks (w.map fun a => (a, true)) = w.length := by
    simp [marks, List.countP_map, Function.comp_def]
  obtain ⟨u, v, x, y, z, hsplit, hpos, hle, hpump⟩ :=
    ogden_of_bound g hR2 hR hK hn (w.map fun a => (a, true))
      (by simpa [List.map_map, Function.comp_def] using hw) (by omega)
  have hmarked : ∀ p ∈ v ++ x ++ y, p.2 = true := by
    intro p hp
    have hp' : p ∈ w.map fun a => (a, true) := by
      rw [hsplit]
      simp only [List.mem_append] at hp ⊢
      tauto
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hp'
    rfl
  have hlen' : marks (v ++ x ++ y) = (v ++ x ++ y).length :=
    List.countP_eq_length.2 fun p hp => by simpa using hmarked p hp
  refine ⟨u.map Prod.fst, v.map Prod.fst, x.map Prod.fst, y.map Prod.fst, z.map Prod.fst,
    ?_, ?_, ?_, fun i => by simpa [List.map_flatten, List.map_replicate] using hpump i⟩
  · simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hsplit
  · intro hvy
    rw [← List.map_append, List.map_eq_nil_iff] at hvy
    rw [hvy] at hpos
    simp at hpos
  · rw [← List.map_append, ← List.map_append, List.length_map, ← hlen']
    exact hle

/-- **Ogden's lemma.** Let $L$ be a context-free language over an alphabet $T$. A marked word is a
word whose letters are pairs $(a, b)$ with $a \in T$ and $b$ a Boolean, the letter being marked
when $b$ is true; its underlying word is the word of first components. Then there is a natural
number $n > 0$ such that every marked word $w$ whose underlying word lies in $L$ and which has at
least $n$ marked letters can be written as $w = uvxyz$ with marked words $u, v, x, y, z$ such that
$vy$ has at least one marked letter, $vxy$ has at most $n$ marked letters, and for every natural
number $i$ the underlying word of $u v^i x y^i z$ lies in $L$, where $v^i$ is the concatenation
of $i$ copies of $v$. -/
theorem IsContextFree.ogden {L : Language T} (hL : L.IsContextFree) :
    ∃ n : ℕ, 0 < n ∧ ∀ w : List (T × Bool), w.map Prod.fst ∈ L → n ≤ marks w →
      ∃ u v x y z : List (T × Bool), w = u ++ v ++ x ++ y ++ z ∧ 0 < marks (v ++ y) ∧
        marks (v ++ x ++ y) ≤ n ∧
        ∀ i : ℕ, (u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++
          z).map Prod.fst ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  obtain ⟨R, hR2, hR⟩ := exists_output_length_bound g
  exact ⟨R ^ (g.rules.card + 1), Nat.pow_pos (by omega),
    ogden_of_bound g hR2 hR ⟨g.rules.toList.map ContextFreeRule.input, by simp,
      fun r hr => List.mem_map_of_mem (Finset.mem_toList.2 hr)⟩ le_rfl⟩

end Cslib.Language
