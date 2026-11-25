/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Reduced

/-!
# The pumping lemma for context-free languages

Every context-free language satisfies the pumping property: there is a
bound `n > 0` such that every word of length at least `n` splits as
`u ++ v ++ x ++ y ++ z` with `v ++ y` nonempty, `v ++ x ++ y` of length
at most `n`, and all pumped words `u ++ v^[i] ++ x ++ y^[i] ++ z` in
the language.

The proof goes through reduced grammars (no empty or unit outputs)
and a height-indexed version `YieldsH` of derivation forests, where
the height counts nonterminal expansions along the longest path.
Descending through height-attaining children in a minimal-height
derivation, the bottom `card + 1` nonterminals on the spine (where
`card` is the number of mentioned nonterminals) contain a repetition,
whose context pumps.

## Main definitions

* `Cslib.Language.YieldsH`: derivation forests bounded by height.

## Main results

* `Cslib.Language.IsContextFree.pumping`: the pumping lemma.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*} {g : ContextFreeGrammar T}

/-- **Height-bounded derivations.** Let $g$ be a context-free grammar. For a sentential form
$\alpha$ (a list of terminals and nonterminals of $g$), a terminal word $w$ and a natural number
$n$, say that $\alpha$ yields $w$ at height $n$ when this follows from three rules: the empty form
yields the empty word at every height $n$; if $\alpha$ yields $w$ at height $n$, then for every
terminal $a$ the form $a\alpha$ yields $aw$ at height $n$; and if $A \to \beta$ is a production of
$g$, $\beta$ yields $w_1$ at height $n$ and $\alpha$ yields $w_2$ at height $m$, then $A\alpha$
yields $w_1 w_2$ at height $\max(n + 1, m)$.

Thus $n$ bounds the height of a derivation forest, the number of nonterminal expansions along
its longest path; terminals and empty forests contribute nothing. -/
inductive YieldsH (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List T → ℕ → Prop
  | nil (n : ℕ) : YieldsH g [] [] n
  | terminal (a : T) {u : List (Symbol T g.NT)} {w : List T} {n : ℕ}
      (h : YieldsH g u w n) : YieldsH g (Symbol.terminal a :: u) (a :: w) n
  | nonterminal {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
      {u : List (Symbol T g.NT)} {w₁ w₂ : List T} {n m : ℕ}
      (hout : YieldsH g r.output w₁ n) (hrest : YieldsH g u w₂ m) :
      YieldsH g (Symbol.nonterminal r.input :: u) (w₁ ++ w₂) (max (n + 1) m)

/-- **Raising the height bound of a yield.** Let $g$ be a context-free grammar. If a sentential
form $\alpha$ yields the terminal word $w$ through a derivation forest of height at most $n$,
and $n \le m$, then $\alpha$ yields $w$ through a derivation forest of height at most $m$. -/
theorem YieldsH.mono {α : List (Symbol T g.NT)} {w : List T} {n m : ℕ}
    (h : YieldsH g α w n) (hle : n ≤ m) : YieldsH g α w m := by
  induction h generalizing m with
  | nil _ => exact YieldsH.nil m
  | terminal a _ ih => exact YieldsH.terminal a (ih hle)
  | @nonterminal r hr u w₁ w₂ n₀ m₀ hout hrest ihout ihrest =>
    cases m with
    | zero =>
      have h1 : n₀ + 1 ≤ 0 := le_trans (Nat.le_max_left _ _) hle
      omega
    | succ m =>
      have hn : n₀ ≤ m := by
        have h1 : n₀ + 1 ≤ m + 1 := le_trans (Nat.le_max_left _ _) hle
        omega
      have hm : m₀ ≤ m + 1 := le_trans (Nat.le_max_right _ _) hle
      have h := YieldsH.nonterminal hr (ihout hn) (ihrest hm)
      simpa using h

/-- **Every yield has a height bound.** Let $g$ be a context-free grammar. If a sentential form
$\alpha$ yields the terminal word $w$, then there is a natural number $n$ such that $\alpha$
yields $w$ through a derivation forest of height at most $n$. -/
theorem YieldsH.of_yields {α : List (Symbol T g.NT)} {w : List T}
    (h : Yields g α w) : ∃ n, YieldsH g α w n := by
  induction h with
  | nil => exact ⟨0, YieldsH.nil 0⟩
  | terminal a _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n, YieldsH.terminal a hn⟩
  | nonterminal hr _ _ ihout ihrest =>
    obtain ⟨n, hn⟩ := ihout
    obtain ⟨m, hm⟩ := ihrest
    exact ⟨max (n + 1) m, YieldsH.nonterminal hr hn hm⟩

/-- **Height-bounded yields are yields.** Let $g$ be a context-free grammar. If a sentential
form $\alpha$ yields the terminal word $w$ through a derivation forest of height at most $n$,
then $\alpha$ yields $w$. -/
theorem Yields.of_yieldsH {α : List (Symbol T g.NT)} {w : List T} {n : ℕ}
    (h : YieldsH g α w n) : Yields g α w := by
  induction h with
  | nil _ => exact Yields.nil
  | terminal a _ ih => exact Yields.terminal a ih
  | nonterminal hr _ _ ihout ihrest =>
    exact Yields.nonterminal hr ihout ihrest

/-- **Concatenating height-bounded yields.** Let $g$ be a context-free grammar. If a sentential
form $u$ yields the terminal word $w_1$ through a derivation forest of height at most $n$, and
a sentential form $v$ yields the terminal word $w_2$ through one of height at most $m$, then the
concatenation $uv$ yields $w_1 w_2$ through a derivation forest of height at most
$\max(n, m)$. -/
theorem YieldsH.append {u v : List (Symbol T g.NT)} {w₁ w₂ : List T}
    {n m : ℕ} (hu : YieldsH g u w₁ n) (hv : YieldsH g v w₂ m) :
    YieldsH g (u ++ v) (w₁ ++ w₂) (max n m) := by
  induction hu with
  | nil _ => simpa using hv.mono (Nat.le_max_right _ _)
  | terminal a _ ih => exact YieldsH.terminal a ih
  | nonterminal hr hout _ _ ihrest =>
    simpa [Nat.max_assoc, List.append_assoc] using
      YieldsH.nonterminal hr hout ihrest

/-- **Splitting a height-bounded yield at a concatenation.** Let $g$ be a context-free grammar
and $u$, $v$ sentential forms of $g$. If the concatenation $uv$ yields the terminal word $w$
through a derivation forest of height at most $n$, then there are terminal words $w_1$, $w_2$
with $w = w_1 w_2$ such that $u$ yields $w_1$ and $v$ yields $w_2$, each through a derivation
forest of height at most $n$. -/
theorem YieldsH.append_inv {u v : List (Symbol T g.NT)} {w : List T}
    {n : ℕ} (h : YieldsH g (u ++ v) w n) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ YieldsH g u w₁ n ∧ YieldsH g v w₂ n := by
  induction u generalizing w n with
  | nil => exact ⟨[], w, rfl, YieldsH.nil n, h⟩
  | cons s u ih =>
    cases s with
    | terminal a =>
      cases h with
      | terminal _ htail =>
        obtain ⟨w₁, w₂, rfl, hu, hv⟩ := ih htail
        exact ⟨a :: w₁, w₂, rfl, YieldsH.terminal a hu, hv⟩
    | nonterminal A =>
      cases h with
      | nonterminal hr hout hrest =>
        rename_i r w₁ w₂ n₀ m₀
        obtain ⟨w₁', w₂', rfl, hu, hv⟩ := ih hrest
        exact ⟨w₁ ++ w₁', w₂', by rw [List.append_assoc],
          YieldsH.nonterminal hr hout hu, hv.mono (Nat.le_max_right _ _)⟩

/-- **Length bound for height-bounded yields.** Let $g$ be a context-free grammar and $R$ a
natural number such that every production of $g$ has an output of length at most $R$. If a
sentential form $\alpha$ yields the terminal word $w$ through a derivation forest of height at
most $n$, then $|w| \le |\alpha| \cdot \max(2, R)^n$. -/
theorem List.length_le_of_yieldsH {R : ℕ}
    (hR : ∀ r ∈ g.rules, r.output.length ≤ R) :
    ∀ {α : List (Symbol T g.NT)} {w : List T} {n : ℕ},
      YieldsH g α w n → w.length ≤ α.length * (max 2 R) ^ n := by
  intro α w n h
  induction h with
  | nil _ => simp
  | @terminal a u w₀ n₀ _ ih =>
    have hBn : 1 ≤ (max 2 R) ^ n₀ :=
      Nat.one_le_pow _ _ (by have := Nat.le_max_left 2 R; omega)
    simp only [List.length_cons]
    calc (a :: w₀).length = w₀.length + 1 := rfl
    _ ≤ u.length * (max 2 R) ^ n₀ + (max 2 R) ^ n₀ :=
        Nat.add_le_add ih hBn
    _ ≤ (u.length + 1) * (max 2 R) ^ n₀ := by rw [Nat.add_one_mul]
  | @nonterminal r hr u w₁ w₂ n₀ m₀ hout hrest ihout ihrest =>
    have hB1 : 0 < max 2 R := by have := Nat.le_max_left 2 R; omega
    have e1 : w₁.length ≤ (max 2 R) ^ max (n₀ + 1) m₀ := by
      calc w₁.length ≤ r.output.length * (max 2 R) ^ n₀ := ihout
      _ ≤ R * (max 2 R) ^ n₀ := Nat.mul_le_mul_right _ (hR r hr)
      _ ≤ (max 2 R) * (max 2 R) ^ n₀ :=
          Nat.mul_le_mul_right _ (Nat.le_max_right 2 R)
      _ = (max 2 R) ^ (n₀ + 1) := (pow_succ' _ _).symm
      _ ≤ (max 2 R) ^ max (n₀ + 1) m₀ :=
          Nat.pow_le_pow_right hB1 (Nat.le_max_left _ _)
    have e2 : w₂.length ≤ u.length * (max 2 R) ^ max (n₀ + 1) m₀ :=
      le_trans ihrest (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hB1 (Nat.le_max_right _ _)))
    rw [List.length_append, List.length_cons, Nat.add_one_mul]
    omega

/-- **Minimal-height derivation forests exist.** Let $g$ be a context-free grammar. If a
sentential form $\alpha$ yields the terminal word $w$, then there is a natural number $n$ such
that $\alpha$ yields $w$ through a derivation forest of height at most $n$, but through no
derivation forest of height at most $m$ for any $m < n$. -/
theorem exists_minimal_yieldsH {α : List (Symbol T g.NT)} {w : List T}
    (h : Yields g α w) :
    ∃ n, YieldsH g α w n ∧ ∀ m < n, ¬ YieldsH g α w m := by
  obtain ⟨n, hn⟩ := YieldsH.of_yields h
  classical
  exact ⟨Nat.find ⟨n, hn⟩, Nat.find_spec ⟨n, hn⟩,
    fun _ hm => Nat.find_min ⟨n, hn⟩ hm⟩

private theorem le_of_minimal_yieldsH {α : List (Symbol T g.NT)}
    {w : List T} {n k : ℕ} (hmin : ∀ m < n, ¬ YieldsH g α w m)
    (hk : YieldsH g α w k) : n ≤ k :=
  le_of_not_gt (fun hlt => hmin k hlt hk)

/-- A minimal-height yield over an append splits into minimal-height
yields of the parts, at heights whose maximum is the whole height. -/
private theorem exists_minimal_yieldsH_append
    {α₁ α₂ : List (Symbol T g.NT)} {w : List T} {n : ℕ}
    (h : YieldsH g (α₁ ++ α₂) w n)
    (hmin : ∀ m < n, ¬ YieldsH g (α₁ ++ α₂) w m) :
    ∃ w₁ w₂ n₁ n₂, w = w₁ ++ w₂ ∧ YieldsH g α₁ w₁ n₁ ∧
      (∀ m < n₁, ¬ YieldsH g α₁ w₁ m) ∧ YieldsH g α₂ w₂ n₂ ∧
      (∀ m < n₂, ¬ YieldsH g α₂ w₂ m) ∧ n = max n₁ n₂ := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := YieldsH.append_inv h
  obtain ⟨n₁, hn₁, hmin₁⟩ := exists_minimal_yieldsH (Yields.of_yieldsH h₁)
  obtain ⟨n₂, hn₂, hmin₂⟩ := exists_minimal_yieldsH (Yields.of_yieldsH h₂)
  have hle1 : n₁ ≤ n := le_of_minimal_yieldsH hmin₁ h₁
  have hle2 : n₂ ≤ n := le_of_minimal_yieldsH hmin₂ h₂
  have hge : n ≤ max n₁ n₂ :=
    le_of_minimal_yieldsH hmin (YieldsH.append hn₁ hn₂)
  refine ⟨w₁, w₂, n₁, n₂, rfl, hn₁, hmin₁, hn₂, hmin₂, ?_⟩
  omega

/-- In a minimal-height yield of positive height, some nonterminal in
the form attains the height with a minimal derivation of its own. -/
private theorem exists_minimal_tall {α : List (Symbol T g.NT)}
    {w : List T} {n : ℕ} (h : YieldsH g α w n)
    (hmin : ∀ m < n, ¬ YieldsH g α w m) (hn : 0 < n) :
    ∃ α₁ B α₂ l x r, α = α₁ ++ Symbol.nonterminal B :: α₂ ∧
      w = l ++ x ++ r ∧ YieldsH g α₁ l n ∧
      YieldsH g [Symbol.nonterminal B] x n ∧
      (∀ m < n, ¬ YieldsH g [Symbol.nonterminal B] x m) ∧
      YieldsH g α₂ r n := by
  induction α generalizing w n with
  | nil =>
    cases h with
    | nil _ => exact absurd (YieldsH.nil (g := g) 0) (hmin 0 hn)
  | cons s α ih =>
    obtain ⟨w₁, w₂, n₁, n₂, hw, h₁, hmin₁, h₂, hmin₂, hnmax⟩ :=
      exists_minimal_yieldsH_append (α₁ := [s]) (α₂ := α) h hmin
    have hle1 : n₁ ≤ n := by omega
    have hle2 : n₂ ≤ n := by omega
    rcases max_choice n₁ n₂ with hm | hm
    · have hn₁ : n₁ = n := by omega
      subst hn₁
      cases s with
      | terminal a =>
        exfalso
        have h0 : YieldsH g [Symbol.terminal a] w₁ 0 := by
          cases h₁ with
          | terminal _ hrest =>
            cases hrest with
            | nil _ => exact YieldsH.terminal a (YieldsH.nil 0)
        exact hmin₁ 0 hn h0
      | nonterminal B =>
        exact ⟨[], B, α, [], w₁, w₂, rfl, by simp [hw], YieldsH.nil n₁, h₁,
          hmin₁, h₂.mono hle2⟩
    · have hn₂ : n₂ = n := by omega
      subst hn₂
      obtain ⟨α₁, B, α₂, l, x, r, hform, hword, hL, hB, hBmin, hR⟩ :=
        ih h₂ hmin₂ hn
      exact ⟨s :: α₁, B, α₂, w₁ ++ l, x, r, by simp [hform],
        by simp [hw, hword, List.append_assoc],
        by simpa using YieldsH.append (h₁.mono hle1) hL, hB, hBmin, hR⟩

/-- **Derivation contexts.** Let $g$ be a context-free grammar, let $A$ and $B$ be nonterminals of
$g$, and let $l$ and $r$ be words over the terminal alphabet. Then $(l, r)$ is a derivation
context from $A$ to $B$ when, for every terminal word $w$ that the nonterminal $B$ yields in $g$,
the nonterminal $A$ yields the word $l w r$ in $g$.

This is the language-inclusion form of a one-hole derivation context; it is what pumping
iteration uses, and it holds vacuously when $B$ yields nothing. -/
def YieldsContext (g : ContextFreeGrammar T) (A B : g.NT) (l r : List T) :
    Prop :=
  ∀ w, Yields g [Symbol.nonterminal B] w →
    Yields g [Symbol.nonterminal A] (l ++ w ++ r)

theorem YieldsContext.refl (A : g.NT) : YieldsContext g A A [] [] :=
  fun _ h => by simpa using h

theorem YieldsContext.trans {A B C : g.NT} {l₁ r₁ l₂ r₂ : List T}
    (h₁ : YieldsContext g A B l₁ r₁) (h₂ : YieldsContext g B C l₂ r₂) :
    YieldsContext g A C (l₁ ++ l₂) (r₂ ++ r₁) :=
  fun _ h => by simpa [List.append_assoc] using h₁ _ (h₂ _ h)

/-- **A production gives derivation contexts.** Let $g$ be a context-free grammar and
$A \to \alpha_1 B \alpha_2$ a production of $g$, where $B$ is a nonterminal and $\alpha_1$,
$\alpha_2$ are sentential forms. If $\alpha_1$ yields the terminal word $l$ and $\alpha_2$ yields
the terminal word $r$, then for every terminal word $w$ yielded by $B$ the word $l w r$ is
yielded by $A$; that is, $(l, r)$ is a derivation context from $A$ to $B$. -/
theorem YieldsContext.of_rule {r : ContextFreeRule T g.NT}
    (hr : r ∈ g.rules) {α₁ α₂ : List (Symbol T g.NT)} {B : g.NT}
    {l rr : List T} (hα : r.output = α₁ ++ Symbol.nonterminal B :: α₂)
    (hl : Yields g α₁ l) (hrr : Yields g α₂ rr) :
    YieldsContext g r.input B l rr := by
  intro w h
  have hmid : Yields g r.output (l ++ w ++ rr) := by
    rw [hα]
    simpa [List.append_assoc] using hl.append (h.append hrr)
  exact yields_of_rule hr hmid

private theorem flatten_replicate_append (l : List T) :
    ∀ i : ℕ, (List.replicate i l).flatten ++ l =
      l ++ (List.replicate i l).flatten
  | 0 => by simp
  | (_ + 1) => by
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc,
      flatten_replicate_append l _]

/-- **Pumping through a self-context.** Let $g$ be a context-free grammar, $A$ a nonterminal and
$l$, $r$, $x$ terminal words. Suppose that for every terminal word $w$ yielded by $A$ the word
$l w r$ is also yielded by $A$, and that $A$ yields $x$. Then for every natural number $i$ the
nonterminal $A$ yields $l^i x r^i$, where $l^i$ and $r^i$ denote the concatenations of $i$
copies of $l$ and of $r$. -/
theorem YieldsContext.iterate {A : g.NT} {l r x : List T}
    (h : YieldsContext g A A l r) (hx : Yields g [Symbol.nonterminal A] x)
    (i : ℕ) :
    Yields g [Symbol.nonterminal A]
      ((List.replicate i l).flatten ++ x ++
        (List.replicate i r).flatten) := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [List.replicate_succ, List.flatten_cons, List.replicate_succ,
      List.flatten_cons, ← flatten_replicate_append r i]
    simpa [List.append_assoc] using h _ ih

/-- One descent step from a minimal-height singleton derivation: a
height-attaining nonterminal in the first production's output, with a
nonempty context (in a reduced grammar) and a minimal derivation one
level down. -/
private theorem exists_descent_of_minimal (hne : IsReduced g)
    {A : g.NT} {w : List T} {H : ℕ} (h : YieldsH g [Symbol.nonterminal A] w H)
    (hmin : ∀ m < H, ¬ YieldsH g [Symbol.nonterminal A] w m) (hH : 2 ≤ H) :
    ∃ B l x r, w = l ++ x ++ r ∧ YieldsContext g A B l r ∧
      YieldsH g [Symbol.nonterminal B] x (H - 1) ∧
      (∀ m < H - 1, ¬ YieldsH g [Symbol.nonterminal B] x m) ∧
      l ++ r ≠ [] ∧ B ∈ grammarNTs g := by
  cases h with
  | @nonterminal r hr u w₁ w₂ n₀ m₀ hout hrest =>
    cases hrest with
    | nil _ =>
      have hH1 : n₀ + 1 = max (n₀ + 1) m₀ := by
        apply le_antisymm (Nat.le_max_left _ _)
        by_contra hlt
        exact hmin _ (Nat.lt_of_not_ge hlt) (by
          simpa using YieldsH.nonterminal hr hout (YieldsH.nil (g := g) 0))
      have hout_min : ∀ m < n₀, ¬ YieldsH g r.output w₁ m := by
        intro m hm hcontra
        exact hmin _ (Nat.lt_of_lt_of_le (by omega : m + 1 < n₀ + 1)
          (Nat.le_max_left _ _)) (by
          simpa using YieldsH.nonterminal hr hcontra (YieldsH.nil (g := g) 0))
      have hn₀ : 0 < n₀ := by omega
      obtain ⟨α₁, B, α₂, l, x, rr, hform, hword, hL, hB, hBmin, hR⟩ :=
        exists_minimal_tall hout hout_min hn₀
      have hctx : YieldsContext g r.input B l rr :=
        YieldsContext.of_rule hr (α₁ := α₁) (α₂ := α₂) hform
          (Yields.of_yieldsH hL) (Yields.of_yieldsH hR)
      have hne : l ++ rr ≠ [] := by
        intro hcon
        obtain ⟨hl, hr0⟩ := List.append_eq_nil_iff.mp hcon
        have hα₁ : α₁ = [] := by
          by_contra hc
          exact Yields.ne_nil_of_forall_output_ne_nil hne.1
            (Yields.of_yieldsH hL) hc hl
        have hα₂ : α₂ = [] := by
          by_contra hc
          exact Yields.ne_nil_of_forall_output_ne_nil hne.1
            (Yields.of_yieldsH hR) hc hr0
        exact hne.2 r hr ⟨B, by simp [hform, hα₁, hα₂]⟩
      have he : n₀ = max (n₀ + 1) m₀ - 1 := by omega
      rw [he] at hB
      refine ⟨B, l, x, rr, by simpa using hword, hctx, hB,
        by intro m hm; exact hBmin m (by omega), hne, ?_⟩
      exact mem_grammarNTs_of_mem_output hr (by
        rw [hform]
        exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl)))

/-- Singleton yields have positive height. -/
private theorem one_le_of_yieldsH_singleton {A : g.NT} {w : List T}
    {n : ℕ} (h : YieldsH g [Symbol.nonterminal A] w n) : 1 ≤ n := by
  cases h with
  | nonterminal _ _ _ =>
    exact le_trans (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_max_left _ _)

/-- An internal form of the pumping conclusion for a root nonterminal,
with iterations stated as yields. -/
private def PumpSplit (S : g.NT) (W : List T) (n : ℕ) : Prop :=
  ∃ u v x y z, W = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧
    (v ++ x ++ y).length ≤ n ∧
    ∀ i, Yields g [Symbol.nonterminal S]
      (u ++ ((List.replicate i v).flatten ++ x ++
        (List.replicate i y).flatten) ++ z)

/-- An ancestor record along the current descent spine: a nonterminal
`B` above the current node `A`, its context from the root, the context
from `B` down to `A`, and a height-bounded derivation of its own yield
(the vicinity bound comes from `he`). The root data `S, W` and current
data `A, w` are fields, tied to the ambient ones by invariants in the
proofs. -/
private structure Ancestor (g : ContextFreeGrammar T) where
  S : g.NT
  W : List T
  A : g.NT
  w : List T
  B : g.NT
  U : List T
  Z : List T
  v : List T
  y : List T
  We : List T
  he : ℕ
  hYHe : YieldsH g [Symbol.nonterminal B] We he
  rootPlug : YieldsContext g S B U Z
  downPlug : YieldsContext g B A v y
  eqRoot : W = U ++ v ++ w ++ y ++ Z
  eqDown : We = v ++ w ++ y

/-- Transport an ancestor record along one descent step. -/
private def Ancestor.update {A : g.NT} {w : List T} {B' : g.NT}
    {l x r : List T} (e : Ancestor g) (hA : e.A = A) (hw0 : e.w = w)
    (hw : w = l ++ x ++ r) (hctx : YieldsContext g A B' l r) :
    Ancestor g where
  S := e.S
  W := e.W
  A := B'
  w := x
  B := e.B
  U := e.U
  Z := e.Z
  v := e.v ++ l
  y := r ++ e.y
  We := e.We
  he := e.he
  hYHe := e.hYHe
  rootPlug := e.rootPlug
  downPlug := by
    have hctx' : YieldsContext g e.A B' l r := hA.symm ▸ hctx
    exact e.downPlug.trans hctx'
  eqRoot := by
    obtain ⟨S, W, A₀, w₀, B, U, Z, v, y, We, he, hYHe, rootPlug, downPlug,
      eqRoot, eqDown⟩ := e
    change W = U ++ (v ++ l) ++ x ++ (r ++ y) ++ Z
    have hw0' : w₀ = w := hw0
    rw [eqRoot, hw0', hw]
    simp [List.append_assoc]
  eqDown := by
    obtain ⟨S, W, A₀, w₀, B, U, Z, v, y, We, he, hYHe, rootPlug, downPlug,
      eqRoot, eqDown⟩ := e
    change We = (v ++ l) ++ x ++ (r ++ y)
    have hw0' : w₀ = w := hw0
    rw [eqDown, hw0', hw]
    simp [List.append_assoc]

private theorem Ancestor.update_B {A : g.NT} {w : List T} {B' : g.NT}
    {l x r : List T} (e : Ancestor g) (hA : e.A = A) (hw0 : e.w = w)
    (hw : w = l ++ x ++ r) (hctx : YieldsContext g A B' l r) :
    (e.update hA hw0 hw hctx).B = e.B := rfl

private theorem Ancestor.update_he {A : g.NT} {w : List T} {B' : g.NT}
    {l x r : List T} (e : Ancestor g) (hA : e.A = A) (hw0 : e.w = w)
    (hw : w = l ++ x ++ r) (hctx : YieldsContext g A B' l r) :
    (e.update hA hw0 hw hctx).he = e.he := rfl

/-- Transport a whole path of ancestor records along one descent
step. -/
private def Ancestor.updateList {A : g.NT} {w : List T} {B' : g.NT}
    {l x r : List T} (hw : w = l ++ x ++ r)
    (hctx : YieldsContext g A B' l r) (path : List (Ancestor g))
    (hp : ∀ e ∈ path, e.A = A ∧ e.w = w) : List (Ancestor g) :=
  path.pmap (fun e he => e.update he.1 he.2 hw hctx) hp

private theorem Ancestor.mem_updateList {A : g.NT} {w : List T}
    {B' : g.NT} {l x r : List T} {hw : w = l ++ x ++ r}
    {hctx : YieldsContext g A B' l r} {path : List (Ancestor g)}
    {hp : ∀ e ∈ path, e.A = A ∧ e.w = w} {e' : Ancestor g}
    (h : e' ∈ Ancestor.updateList hw hctx path hp) :
    ∃ e ∈ path, ∃ (hA : e.A = A) (hw0 : e.w = w),
      e' = e.update hA hw0 hw hctx := by
  obtain ⟨e, he, hEq⟩ := List.mem_pmap.mp h
  exact ⟨e, he, _, _, hEq.symm⟩

private theorem Ancestor.length_updateList {A : g.NT} {w : List T}
    {B' : g.NT} {l x r : List T} {hw : w = l ++ x ++ r}
    {hctx : YieldsContext g A B' l r} {path : List (Ancestor g)}
    {hp : ∀ e ∈ path, e.A = A ∧ e.w = w} :
    (Ancestor.updateList hw hctx path hp).length = path.length :=
  List.length_pmap

private theorem Ancestor.map_B_updateList {A : g.NT} {w : List T}
    {B' : g.NT} {l x r : List T} {hw : w = l ++ x ++ r}
    {hctx : YieldsContext g A B' l r} {path : List (Ancestor g)}
    {hp : ∀ e ∈ path, e.A = A ∧ e.w = w} :
    (Ancestor.updateList hw hctx path hp).map Ancestor.B =
      path.map Ancestor.B := by
  rw [Ancestor.updateList, List.map_pmap, List.pmap_eq_map_attach,
    ← List.attach_map_val (f := Ancestor.B)]
  congr 1

/-- Second phase of the pumping argument: with at most `card + 1`
levels left, recording ancestors forces a repetition. -/
private theorem pump_aux_phase2 (hred : IsReduced g) {R : ℕ}
    (hR : ∀ r ∈ g.rules, r.output.length ≤ R) :
    ∀ (k : ℕ) {S A : g.NT} {W w : List T},
      YieldsH g [Symbol.nonterminal A] w k →
      (∀ m < k, ¬ YieldsH g [Symbol.nonterminal A] w m) →
      ∀ (path : List (Ancestor g)),
        (∀ e ∈ path, e.S = S ∧ e.W = W ∧ e.A = A ∧ e.w = w) →
        (∀ e ∈ path, e.B ∈ grammarNTs g) →
        (path.map Ancestor.B).Nodup →
        (∀ e ∈ path, e.v ++ e.y ≠ []) →
        (∀ e ∈ path, e.he ≤ (grammarNTs g).card + 1) →
        path.length + k = (grammarNTs g).card + 1 →
        A ∈ grammarNTs g →
        ∀ (U₀ Z₀ : List T), YieldsContext g S A U₀ Z₀ →
          W = U₀ ++ w ++ Z₀ →
          PumpSplit S W ((max 2 R) ^ ((grammarNTs g).card + 1)) := by
  intro k
  induction k with
  | zero =>
    intro S A W w hY hmin path hinv hmem hnodup hgrowth hhe hsum hA U₀ Z₀
      hplug heq
    have := one_le_of_yieldsH_singleton hY
    omega
  | succ k ih =>
    intro S A W w hY hmin path hinv hmem hnodup hgrowth hhe hsum hA U₀ Z₀
      hplug heq
    by_cases hrep : ∃ e ∈ path, e.B = A
    · obtain ⟨e, hepath, hBeq⟩ := hrep
      obtain ⟨hS, hW, hAeq, hweq⟩ := hinv e hepath
      have hroot : YieldsContext g S A e.U e.Z := by
        have h := e.rootPlug
        rwa [hS, hBeq] at h
      have hself : YieldsContext g A A e.v e.y := by
        have h := e.downPlug
        rwa [hBeq, hAeq] at h
      have hRoot : W = e.U ++ e.v ++ w ++ e.y ++ e.Z := by
        have h := e.eqRoot
        rwa [hW, hweq] at h
      have hDown : e.We = e.v ++ w ++ e.y := by
        have h := e.eqDown
        rwa [hweq] at h
      refine ⟨e.U, e.v, w, e.y, e.Z, hRoot, hgrowth e hepath, ?_, ?_⟩
      · have hb := List.length_le_of_yieldsH hR e.hYHe
        simp only [List.length_singleton, one_mul] at hb
        rw [← hDown]
        exact le_trans hb (Nat.pow_le_pow_right
          (by have := Nat.le_max_left 2 R; omega) (hhe e hepath))
      · intro i
        simpa [List.append_assoc] using
          hroot _ (hself.iterate (Yields.of_yieldsH hY) i)
    · have hrep' : ∀ e ∈ path, e.B ≠ A :=
        fun e he hBe => hrep ⟨e, he, hBe⟩
      cases k with
      | zero =>
        exfalso
        classical
        have hlen : path.length = (grammarNTs g).card := by omega
        have hsub : (A :: path.map Ancestor.B).toFinset ⊆ grammarNTs g := by
          intro x hx
          rw [List.mem_toFinset] at hx
          cases List.mem_cons.mp hx with
          | inl h => rwa [h]
          | inr h =>
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
            exact hmem e he
        have hcard := Finset.card_le_card hsub
        have hnodup' : (A :: path.map Ancestor.B).Nodup :=
          List.nodup_cons.mpr ⟨fun hmem' => by
            obtain ⟨e, he, hBe⟩ := List.mem_map.mp hmem'
            exact hrep' e he hBe, hnodup⟩
        rw [List.toFinset_card_of_nodup hnodup'] at hcard
        simp only [List.length_cons, List.length_map] at hcard
        omega
      | succ k =>
        obtain ⟨B', l, x, r, hw, hctx, hBYH, hBmin, hlr, hBmem⟩ :=
          exists_descent_of_minimal hred hY hmin (by omega)
        let entryA : Ancestor g :=
          { S := S, W := W, A := A, w := w, B := A, U := U₀, Z := Z₀,
            v := [], y := [], We := w, he := k + 2, hYHe := hY,
            rootPlug := hplug, downPlug := YieldsContext.refl A,
            eqRoot := by simpa using heq, eqDown := by simp }
        have hpAll : ∀ e ∈ entryA :: path, e.A = A ∧ e.w = w := by
          intro e he
          cases List.mem_cons.mp he with
          | inl h => rw [h]; exact ⟨rfl, rfl⟩
          | inr h =>
            exact ⟨(hinv e h).2.2.1, (hinv e h).2.2.2⟩
        refine ih hBYH hBmin
          (Ancestor.updateList hw hctx (entryA :: path) hpAll) ?_ ?_ ?_
          ?_ ?_ ?_ hBmem (U₀ ++ l) (r ++ Z₀) (hplug.trans hctx) ?_
        · intro e he
          obtain ⟨e₀, he₀, -, -, rfl⟩ := Ancestor.mem_updateList he
          cases List.mem_cons.mp he₀ with
          | inl h =>
            subst h
            exact ⟨rfl, rfl, rfl, rfl⟩
          | inr h =>
            exact ⟨(hinv e₀ h).1, (hinv e₀ h).2.1, rfl, rfl⟩
        · intro e he
          obtain ⟨e₀, he₀, -, -, rfl⟩ := Ancestor.mem_updateList he
          rw [Ancestor.update_B]
          cases List.mem_cons.mp he₀ with
          | inl h => subst h; exact hA
          | inr h => exact hmem e₀ h
        · have hAnew : A ∉ path.map Ancestor.B := by
            intro hmem'
            obtain ⟨e, he, hBe⟩ := List.mem_map.mp hmem'
            exact hrep' e he hBe
          rw [Ancestor.map_B_updateList]
          exact List.nodup_cons.mpr ⟨hAnew, hnodup⟩
        · intro e he
          obtain ⟨e₀, -, -, -, rfl⟩ := Ancestor.mem_updateList he
          intro hcon
          change (e₀.v ++ l) ++ (r ++ e₀.y) = [] at hcon
          obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp hcon
          have hl : l = [] := (List.append_eq_nil_iff.mp h1).2
          have hr0 : r = [] := (List.append_eq_nil_iff.mp h2).1
          exact hlr (by simp [hl, hr0])
        · intro e he
          obtain ⟨e₀, he₀, -, -, rfl⟩ := Ancestor.mem_updateList he
          rw [Ancestor.update_he]
          cases List.mem_cons.mp he₀ with
          | inl h =>
            subst h
            change k + 2 ≤ (grammarNTs g).card + 1
            omega
          | inr h => exact hhe e₀ h
        · rw [Ancestor.length_updateList]
          simp only [List.length_cons]
          omega
        · simp [heq, hw, List.append_assoc]

/-- First phase: descend along height-attaining children until only
`card + 1` levels remain, then switch to the ancestor argument. -/
private theorem pump_aux_phase1 (hred : IsReduced g) {R : ℕ}
    (hR : ∀ r ∈ g.rules, r.output.length ≤ R) :
    ∀ (k : ℕ) {S A : g.NT} {W w : List T},
      YieldsH g [Symbol.nonterminal A] w k →
      (∀ m < k, ¬ YieldsH g [Symbol.nonterminal A] w m) →
      A ∈ grammarNTs g →
      ∀ (U₀ Z₀ : List T), YieldsContext g S A U₀ Z₀ →
        W = U₀ ++ w ++ Z₀ →
        (grammarNTs g).card + 1 ≤ k →
        PumpSplit S W ((max 2 R) ^ ((grammarNTs g).card + 1)) := by
  intro k
  induction k with
  | zero =>
    intro S A W w hY hmin hA U₀ Z₀ hplug heq hk
    omega
  | succ k ih =>
    intro S A W w hY hmin hA U₀ Z₀ hplug heq hk
    by_cases htop : k + 1 = (grammarNTs g).card + 1
    · exact pump_aux_phase2 hred hR (k + 1) hY hmin []
        (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp only [List.length_nil, Nat.zero_add]; exact htop) hA U₀ Z₀
        hplug heq
    · obtain ⟨B', l, x, r, hw, hctx, hBYH, hBmin, -, hBmem⟩ :=
        exists_descent_of_minimal hred hY hmin (by omega)
      exact ih hBYH hBmin hBmem (U₀ ++ l) (r ++ Z₀) (hplug.trans hctx)
        (by simp [heq, hw, List.append_assoc]) (by omega)

/-- A natural-valued function is bounded on a finset. -/
private theorem exists_le_of_finset {α : Type*} (s : Finset α)
    (f : α → ℕ) : ∃ R, ∀ a ∈ s, f a ≤ R := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | insert a s _ ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨max R (f a), fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Nat.le_max_right _ _
    · exact le_trans (hR b hb) (Nat.le_max_left _ _)

/-- The outputs of a grammar have bounded length. -/
private theorem exists_output_length_le (g : ContextFreeGrammar T) :
    ∃ R, ∀ r ∈ g.rules, r.output.length ≤ R :=
  exists_le_of_finset g.rules (fun r => r.output.length)

/-- **Pumping lemma for context-free languages.** For every context-free language $L$ over an
alphabet $T$ there is a natural number $n > 0$ such that every word $w \in L$ with $|w| \ge n$
can be written as $w = uvxyz$ with words $u, v, x, y, z$ over $T$ such that $vy$ is nonempty,
$|vxy| \le n$, and $u v^i x y^i z \in L$ for every natural number $i$, where $v^i$ and $y^i$
denote the concatenations of $i$ copies of $v$ and of $y$. -/
theorem IsContextFree.pumping {L : Language T} (hL : L.IsContextFree) :
    ∃ n : ℕ, 0 < n ∧ ∀ w ∈ L, n ≤ w.length →
      ∃ u v x y z : List T, w = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧
        (v ++ x ++ y).length ≤ n ∧
        ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++
          (List.replicate i y).flatten ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  obtain ⟨g', hlang, hne, hunit⟩ := exists_reduced_grammar g
  obtain ⟨R, hR⟩ := exists_output_length_le g'
  refine ⟨(max 2 R) ^ ((grammarNTs g').card + 1), ?_, ?_⟩
  · exact Nat.pow_pos (by have := Nat.le_max_left 2 R; omega)
  · intro w hw hlen
    have hwne : w ≠ [] := by
      rintro rfl
      simp only [List.length_nil] at hlen
      have hpos : 0 < (max 2 R) ^ ((grammarNTs g').card + 1) :=
        Nat.pow_pos (by have := Nat.le_max_left 2 R; omega)
      omega
    have hw' : w ∈ g'.language := (hlang w).mpr ⟨hw, hwne⟩
    obtain ⟨k, hY, hmin⟩ :=
      exists_minimal_yieldsH (mem_language_iff_yields.mp hw')
    have hk : (grammarNTs g').card + 1 ≤ k := by
      by_contra hlt
      have hlenle : w.length ≤ (max 2 R) ^ k := by
        have hle := List.length_le_of_yieldsH (g := g') hR hY
        simpa using hle
      have hB : 0 < max 2 R := by have := Nat.le_max_left 2 R; omega
      have h1 : (max 2 R) ^ k ≤ (max 2 R) ^ (grammarNTs g').card :=
        Nat.pow_le_pow_right hB (by omega)
      have h2 : (max 2 R) ^ (grammarNTs g').card <
          (max 2 R) ^ ((grammarNTs g').card + 1) := by
        rw [pow_succ]
        have hpos : 0 < (max 2 R) ^ (grammarNTs g').card :=
          Nat.pow_pos hB
        have h3 : (max 2 R) ^ (grammarNTs g').card * 1 <
            (max 2 R) ^ (grammarNTs g').card * max 2 R :=
          (Nat.mul_lt_mul_left hpos).mpr (by
            have := Nat.le_max_left 2 R; omega)
        rwa [mul_one] at h3
      omega
    obtain ⟨u, v, x, y, z, hsplit, hvy, hvxy, hpump⟩ :=
      pump_aux_phase1 (S := g'.initial) (W := w)
        (⟨hne, hunit⟩ : IsReduced g') hR k hY hmin
        initial_mem_grammarNTs [] [] (YieldsContext.refl _) (by simp) hk
    refine ⟨u, v, x, y, z, hsplit, hvy, hvxy, fun i => ?_⟩
    have hmem := (hlang _).mp (mem_language_iff_yields.mpr (hpump i))
    simpa [List.append_assoc] using hmem.1

end Cslib.Language
