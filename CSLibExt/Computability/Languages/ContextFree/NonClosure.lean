/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Closure
public import CSLibExt.Computability.Languages.ContextFree.Pumping

/-!
# Nonclosure of context-free languages under intersection and complement

Context-free languages are not closed under intersection or complement.
The witness is `a^n b^n c^n` over a three-letter alphabet: it is the
intersection of the context-free languages `a^n b^n c^*` and
`a^* b^n c^n`, but the pumping lemma shows it is not context-free.
Complement nonclosure follows by De Morgan with closure under union.

## Main results

* `Cslib.Language.eqPowLang_isContextFree`: `a^n b^n` is context-free.
* `Cslib.Language.anbncnLang_not_isContextFree`: `a^n b^n c^n` is not.
* `Cslib.Language.exists_isContextFree_inf_not_isContextFree`: CFLs are
  not closed under intersection.
* `Cslib.Language.exists_isContextFree_compl_not_isContextFree`: CFLs
  are not closed under complement.
-/

@[expose] public section

namespace Cslib.Language

/-- Flattening copies of a singleton word gives copies of the letter. -/
private theorem flatten_replicate_singleton {α : Type*} (a : α) :
    ∀ k : ℕ, (List.replicate k [a]).flatten = List.replicate k a
  | 0 => rfl
  | (k + 1) => by
    rw [List.replicate_succ, List.flatten_cons,
      flatten_replicate_singleton a k, List.replicate_succ]
    rfl

/-- **The Kleene star of a one-letter word.** For a letter $a$ of an alphabet, a word $w$ belongs
to the Kleene star of the language $\{a\}$ whose only word is the one-letter word $a$ if and only
if $w = a^k$ for some $k \in \mathbb{N}$. -/
theorem mem_kstar_singleton {α : Type*} {a : α} {w : List α} :
    w ∈ KStar.kstar ({[a]} : Language α) ↔
      ∃ k, w = List.replicate k a := by
  constructor
  · intro hw
    obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hw
    have hflat : ∀ L : List (List α), (∀ y ∈ L, y = [a]) →
        L.flatten = List.replicate L.length a := by
      intro L hL
      induction L with
      | nil => rfl
      | cons y L ih =>
        have hy : y = [a] := hL y (List.mem_cons_self)
        have ih' := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
        rw [List.flatten_cons, hy, ih', List.length_cons,
          List.replicate_succ]
        rfl
    exact ⟨L.length, hflat L (fun y hy => hL y hy)⟩
  · rintro ⟨k, rfl⟩
    apply Language.mem_kstar.mpr
    refine ⟨List.replicate k [a], (flatten_replicate_singleton a k).symm,
      ?_⟩
    intro y hy
    have : y = [a] := (List.mem_replicate.mp hy).2
    rw [this]
    exact rfl

/-- **The language $a^n b^n$.** For letters $a$ and $b$ of an alphabet, this is the language of the
words $a^n b^n$ for $n \in \mathbb{N}$: $n$ copies of $a$ followed by $n$ copies of $b$. -/
def eqPowLang {α : Type*} (a b : α) : Language α :=
  {w | ∃ n, w = List.replicate n a ++ List.replicate n b}

/-- **The grammar $S \to aSb \mid \varepsilon$.** For letters $a$ and $b$ of an alphabet with
decidable equality, this is the context-free grammar with a single nonterminal $S$, which is its
start symbol, and the two rules $S \to aSb$ and $S \to \varepsilon$. -/
def eqPowGrammar {α : Type*} [DecidableEq α] (a b : α) :
    ContextFreeGrammar α where
  NT := Unit
  initial := ()
  rules := {⟨(), [Symbol.terminal a, Symbol.nonterminal (),
      Symbol.terminal b]⟩, ⟨(), []⟩}

private theorem mem_eqPowGrammar_rules {α : Type*} [DecidableEq α]
    (a b : α) :
    (⟨(), [Symbol.terminal a, Symbol.nonterminal (),
      Symbol.terminal b]⟩ : ContextFreeRule α Unit) ∈
        (eqPowGrammar a b).rules ∧
    (⟨(), []⟩ : ContextFreeRule α Unit) ∈ (eqPowGrammar a b).rules := by
  constructor
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **The grammar $S \to aSb \mid \varepsilon$ generates $a^n b^n$.** For letters $a$ and $b$ of an
alphabet with decidable equality, the language of the context-free grammar with a single
nonterminal $S$, its start symbol, and the two rules $S \to aSb$ and $S \to \varepsilon$ is the
language of the words $a^n b^n$ for $n \in \mathbb{N}$. -/
theorem eqPowGrammar_language {α : Type*} [DecidableEq α] (a b : α) :
    (eqPowGrammar a b).language = eqPowLang a b := by
  apply le_antisymm
  · apply language_le_of_valuation (V := fun _ => eqPowLang a b)
    intro r hr
    have hmem : r = ⟨(), [Symbol.terminal a, Symbol.nonterminal (),
        Symbol.terminal b]⟩ ∨ r = ⟨(), []⟩ := by
      rcases (@Finset.mem_insert (ContextFreeRule α (eqPowGrammar a b).NT)
        (inferInstanceAs (DecidableEq (ContextFreeRule α Unit))) _ _ _).mp
          hr with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hmem with rfl | rfl
    · intro w hw
      simp only [evalForm_cons, evalSymbol_terminal, evalForm_nil] at hw
      obtain ⟨x, rfl, y, hy, rfl⟩ := Language.mem_mul.mp hw
      obtain ⟨y₁, ⟨n, rfl⟩, y₂, hy₂, rfl⟩ := Language.mem_mul.mp hy
      obtain ⟨x₂, rfl, y₃, hy₃, rfl⟩ := Language.mem_mul.mp hy₂
      rw [Language.mem_one] at hy₃
      subst hy₃
      refine ⟨n + 1, ?_⟩
      have e1 : [a] ++ List.replicate n a = List.replicate (n + 1) a := by
        rw [List.replicate_succ]; rfl
      have e2 : List.replicate n b ++ [b] = List.replicate (n + 1) b :=
        List.replicate_succ'.symm
      calc [a] ++ ((List.replicate n a ++ List.replicate n b) ++
              ([b] ++ []))
          = ([a] ++ List.replicate n a) ++
              (List.replicate n b ++ [b]) := by
            simp only [List.append_assoc, List.append_nil]
        _ = List.replicate (n + 1) a ++ List.replicate (n + 1) b := by
            rw [e1, e2]
    · intro w hw
      simp only [evalForm_nil] at hw
      have hw0 : w = [] := hw
      exact ⟨0, by simp [hw0]⟩
  · intro w hw
    obtain ⟨n, rfl⟩ := hw
    have hy : ∀ n, Yields (eqPowGrammar a b) [Symbol.nonterminal ()]
        (List.replicate n a ++ List.replicate n b) := by
      intro n
      induction n with
      | zero =>
        simpa using yields_of_rule (mem_eqPowGrammar_rules a b).2
          Yields.nil
      | succ n ih =>
        have hform := (Yields.terminal a Yields.nil).append
          (ih.append (Yields.terminal b Yields.nil))
        have e1 : [a] ++ List.replicate n a =
            List.replicate (n + 1) a := by
          rw [List.replicate_succ]; rfl
        have e2 : List.replicate n b ++ [b] =
            List.replicate (n + 1) b := List.replicate_succ'.symm
        have eword : [a] ++ ((List.replicate n a ++
              List.replicate n b) ++ [b]) =
            List.replicate (n + 1) a ++ List.replicate (n + 1) b := by
          calc [a] ++ ((List.replicate n a ++ List.replicate n b) ++
                  [b])
              = ([a] ++ List.replicate n a) ++
                  (List.replicate n b ++ [b]) := by
                simp only [List.append_assoc]
            _ = List.replicate (n + 1) a ++ List.replicate (n + 1) b := by
                rw [e1, e2]
        rw [eword] at hform
        exact yields_of_rule (mem_eqPowGrammar_rules a b).1 hform
    exact mem_language_iff_yields.mpr (hy n)

/-- **The language $a^n b^n$ is context-free.** For any alphabet and any letters $a$ and $b$ of it,
the language of the words $a^n b^n$ for $n \in \mathbb{N}$ is context-free. -/
theorem eqPowLang_isContextFree {α : Type*} (a b : α) :
    (eqPowLang a b).IsContextFree := by
  classical
  exact ⟨eqPowGrammar a b, eqPowGrammar_language a b⟩

/-- **The language $a^n b^n c^n$.** Over the three-letter alphabet $\{a, b, c\}$ (the letters
$0, 1, 2$), this is the language of the words $a^n b^n c^n$ for $n \in \mathbb{N}$: $n$ copies of
$a$, then $n$ copies of $b$, then $n$ copies of $c$. -/
def anbncnLang : Language (Fin 3) :=
  {w | ∃ n, w = List.replicate n 0 ++ List.replicate n 1 ++
    List.replicate n 2}

private theorem fin3_cases (t : Fin 3) : t = 0 ∨ t = 1 ∨ t = 2 := by
  have h : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  exact h t

/-- Every letter occurs exactly `n` times in `a^n b^n c^n`. -/
private theorem count_anbncn_word (n : ℕ) (t : Fin 3) :
    (List.replicate n (0 : Fin 3) ++ List.replicate n 1 ++
      List.replicate n 2).count t = n := by
  rcases fin3_cases t with rfl | rfl | rfl <;>
    simp [List.count_append, List.count_replicate]

/-- The letters of `a^n b^n c^n` by position. -/
private theorem anbncn_word_get (n m : ℕ)
    (hm : m < (List.replicate n (0 : Fin 3) ++ List.replicate n 1 ++
      List.replicate n 2).length) :
    (m < n ∧ (List.replicate n (0 : Fin 3) ++ List.replicate n 1 ++
        List.replicate n 2)[m] = 0) ∨
    (n ≤ m ∧ m < 2 * n ∧ (List.replicate n (0 : Fin 3) ++
        List.replicate n 1 ++ List.replicate n 2)[m] = 1) ∨
    (2 * n ≤ m ∧ (List.replicate n (0 : Fin 3) ++ List.replicate n 1 ++
        List.replicate n 2)[m] = 2) := by
  by_cases h1 : m < n
  · refine Or.inl ⟨h1, ?_⟩
    rw [List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega), List.getElem_replicate]
  · by_cases h2 : m < 2 * n
    · refine Or.inr (Or.inl ⟨by omega, h2, ?_⟩)
      rw [List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by simp; omega),
        List.getElem_replicate]
    · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
      rw [List.getElem_append_right (by simp; omega),
        List.getElem_replicate]

/-- A factor of length at most `n` of a word whose letters by
position are `0` below `n`, `1` below `2n`, and `2` afterwards cannot
contain both `0` and `2`. -/
private theorem not_both_mem_factor_of_get {n : ℕ}
    {W u s z : List (Fin 3)} (hW : W = u ++ s ++ z)
    (hs : s.length ≤ n)
    (hget : ∀ m (hm : m < W.length),
      (m < n ∧ W[m] = 0) ∨ (n ≤ m ∧ m < 2 * n ∧ W[m] = 1) ∨
        (2 * n ≤ m ∧ W[m] = 2)) :
    ¬ ((0 : Fin 3) ∈ s ∧ (2 : Fin 3) ∈ s) := by
  rintro ⟨h0, h2⟩
  have hW' : W = u ++ (s ++ z) := by rw [hW, List.append_assoc]
  have step : ∀ {k : ℕ} (hk : k < s.length),
      s[k] = W[u.length + k]'(by rw [hW']; simp; omega) := by
    intro k hk
    calc s[k]'hk = (s ++ z)[k]'(by simp; omega) :=
          (List.getElem_append_left hk).symm
      _ = (s ++ z)[u.length + k - u.length]'(by simp; omega) := by
          congr 1
          omega
      _ = (u ++ (s ++ z))[u.length + k]'(by simp; omega) :=
          (List.getElem_append_right
            (by simp : u.length ≤ u.length + k)).symm
      _ = W[u.length + k]'(by rw [hW']; simp; omega) := by
          congr 1
          exact hW'.symm
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp h0
  rw [step hi] at hgi
  have hult : u.length < n := by
    rcases hget (u.length + i) _ with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
    · omega
    · rw [hgi] at h; exact absurd h (by decide)
    · rw [hgi] at h; exact absurd h (by decide)
  obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp h2
  rw [step hj] at hgj
  rcases hget (u.length + j) _ with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨h, -⟩
  · rw [hgj] at h; exact absurd h (by decide)
  · rw [hgj] at h; exact absurd h (by decide)
  · omega

/-- **The language $a^n b^n c^n$ is not context-free.** Over the three-letter alphabet $\{a, b, c\}$
(the letters $0, 1, 2$), the language of the words $a^n b^n c^n$ for $n \in \mathbb{N}$ is not
context-free.

Proof idea: by the pumping lemma, pumping $a^n b^n c^n$ down would keep the three letter counts
equal, so the pumped factor has equal counts of all letters, but a short factor misses $a$ or $c$,
forcing the factor to be empty. -/
theorem anbncnLang_not_isContextFree : ¬ anbncnLang.IsContextFree := by
  intro hCF
  obtain ⟨n, -, hpump⟩ := IsContextFree.pumping hCF
  obtain ⟨u, v, x, y, z, hsplit, hvy, hvxy, hi⟩ := hpump
    (List.replicate n 0 ++ List.replicate n 1 ++ List.replicate n 2)
    ⟨n, rfl⟩ (by
      simp only [List.length_append, List.length_replicate]; omega)
  have hi0 := hi 0
  simp only [List.replicate_zero, List.flatten_nil,
    List.append_nil] at hi0
  obtain ⟨m, hm⟩ := hi0
  have key : ∀ t : Fin 3, (v ++ y).count t + m = n := by
    intro t
    have e1 := count_anbncn_word n t
    have e2 : (u ++ x ++ z).count t = m := by
      rw [hm]; exact count_anbncn_word m t
    have e3 : (List.replicate n (0 : Fin 3) ++ List.replicate n 1 ++
          List.replicate n 2).count t =
        (u ++ x ++ z).count t + (v ++ y).count t := by
      rw [hsplit]
      simp only [List.count_append]
      omega
    omega
  have hcount_s : ∀ t : Fin 3, (v ++ x ++ y).count t =
      (v ++ y).count t + x.count t := by
    intro t
    simp only [List.count_append]
    omega
  have hfactor := not_both_mem_factor_of_get (n := n) (u := u)
    (s := v ++ x ++ y) (z := z)
    (W := List.replicate n 0 ++ List.replicate n 1 ++
      List.replicate n 2)
    (by rw [hsplit]; simp only [List.append_assoc]) hvxy
    (anbncn_word_get n)
  have hmiss : (v ++ y).count (0 : Fin 3) = 0 ∨
      (v ++ y).count (2 : Fin 3) = 0 := by
    by_cases h0 : (0 : Fin 3) ∈ v ++ x ++ y
    · right
      have h2 : (2 : Fin 3) ∉ v ++ x ++ y := fun h2 => hfactor ⟨h0, h2⟩
      have hc : (v ++ x ++ y).count (2 : Fin 3) = 0 :=
        List.count_eq_zero.mpr h2
      rw [hcount_s] at hc
      omega
    · left
      have hc : (v ++ x ++ y).count (0 : Fin 3) = 0 :=
        List.count_eq_zero.mpr h0
      rw [hcount_s] at hc
      omega
  have hall : ∀ t : Fin 3, (v ++ y).count t = 0 := by
    intro t
    have k0 := key 0
    have k1 := key 1
    have k2 := key 2
    have kt := key t
    rcases hmiss with h | h <;> omega
  exact hvy (List.eq_nil_iff_forall_not_mem.mpr
    (fun t => List.count_eq_zero.mp (hall t)))

/-- The language `a^n b^n c^*` is context-free. -/
private theorem anbncStar_isContextFree :
    (eqPowLang (0 : Fin 3) 1 *
      KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3))).IsContextFree :=
  IsContextFree.mul (eqPowLang_isContextFree _ _)
    (IsContextFree.kstar (IsContextFree.singleton_word _))

/-- The language `a^* b^n c^n` is context-free. -/
private theorem aStarbncn_isContextFree :
    (KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) *
      eqPowLang (1 : Fin 3) 2).IsContextFree :=
  IsContextFree.mul
    (IsContextFree.kstar (IsContextFree.singleton_word _))
    (eqPowLang_isContextFree _ _)

/-- `a^n b^n c^n` is the intersection of `a^n b^n c^*` and
`a^* b^n c^n`: comparing the three letter counts forces all block
sizes to agree. -/
private theorem inter_eq_anbncn :
    eqPowLang (0 : Fin 3) 1 *
        KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)) ⊓
      (KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) *
        eqPowLang (1 : Fin 3) 2) = anbncnLang := by
  ext w
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Language.mem_inf.mp h
    obtain ⟨w₁, hw₁, w₂, hw₂, hf1⟩ := Language.mem_mul.mp h1
    obtain ⟨n, rfl⟩ := hw₁
    obtain ⟨k, rfl⟩ := mem_kstar_singleton.mp hw₂
    obtain ⟨w₃, hw₃, w₄, hw₄, hf2⟩ := Language.mem_mul.mp h2
    obtain ⟨j, rfl⟩ := mem_kstar_singleton.mp hw₃
    obtain ⟨m, rfl⟩ := hw₄
    have ca : w.count (0 : Fin 3) = n ∧ w.count (0 : Fin 3) = j := by
      refine ⟨?_, ?_⟩
      · rw [← hf1]; simp [List.count_append, List.count_replicate]
      · rw [← hf2]; simp [List.count_append, List.count_replicate]
    have cb : w.count (1 : Fin 3) = n ∧ w.count (1 : Fin 3) = m := by
      refine ⟨?_, ?_⟩
      · rw [← hf1]; simp [List.count_append, List.count_replicate]
      · rw [← hf2]; simp [List.count_append, List.count_replicate]
    have cc : w.count (2 : Fin 3) = k ∧ w.count (2 : Fin 3) = m := by
      refine ⟨?_, ?_⟩
      · rw [← hf1]; simp [List.count_append, List.count_replicate]
      · rw [← hf2]; simp [List.count_append, List.count_replicate]
    have hkn : k = n := by omega
    exact ⟨n, by rw [← hf1, hkn]⟩
  · intro h
    obtain ⟨n, rfl⟩ := h
    apply Language.mem_inf.mpr
    constructor
    · exact Language.mem_mul.mpr
        ⟨List.replicate n 0 ++ List.replicate n 1, ⟨n, rfl⟩,
          List.replicate n 2, mem_kstar_singleton.mpr ⟨n, rfl⟩, rfl⟩
    · exact Language.mem_mul.mpr
        ⟨List.replicate n 0, mem_kstar_singleton.mpr ⟨n, rfl⟩,
          List.replicate n 1 ++ List.replicate n 2, ⟨n, rfl⟩,
          by rw [List.append_assoc]⟩

/-- **Context-free languages are not closed under intersection.** There are context-free languages
$L$ and $M$ over the three-letter alphabet $\{0, 1, 2\}$ whose intersection $L \cap M$ is not
context-free. -/
theorem exists_isContextFree_inf_not_isContextFree :
    ∃ L M : Language (Fin 3), L.IsContextFree ∧ M.IsContextFree ∧
      ¬ (L ⊓ M).IsContextFree :=
  ⟨_, _, anbncStar_isContextFree, aStarbncn_isContextFree,
    fun h => anbncnLang_not_isContextFree (inter_eq_anbncn ▸ h)⟩

/-- **Context-free languages are not closed under complement.** There is a context-free language
$L$ over the three-letter alphabet $\{0, 1, 2\}$ whose complement is not context-free.

Closure under complement and union would give closure under intersection. -/
theorem exists_isContextFree_compl_not_isContextFree :
    ∃ L : Language (Fin 3), L.IsContextFree ∧
      ¬ (Lᶜ).IsContextFree := by
  by_contra hcon
  push Not at hcon
  have hDM : ((eqPowLang (0 : Fin 3) 1 *
        KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)))ᶜ +
      (KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) *
        eqPowLang (1 : Fin 3) 2)ᶜ)ᶜ = anbncnLang := by
    rw [← inter_eq_anbncn]
    set L1 := eqPowLang (0 : Fin 3) 1 *
      KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)) with hL1
    set L2 := KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) *
      eqPowLang (1 : Fin 3) 2 with hL2
    ext w
    rw [Language.mem_inf]
    change (¬ (w ∉ L1 ∨ w ∉ L2)) ↔ (w ∈ L1 ∧ w ∈ L2)
    simp only [not_or, not_not]
  have hsum : ((eqPowLang (0 : Fin 3) 1 *
        KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)))ᶜ +
      (KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) *
        eqPowLang (1 : Fin 3) 2)ᶜ).IsContextFree :=
    IsContextFree.add (hcon _ anbncStar_isContextFree)
      (hcon _ aStarbncn_isContextFree)
  exact anbncnLang_not_isContextFree (hDM ▸ hcon _ hsum)

/-- **Intersections of context-free languages need not be context-free.** Over the three-letter
alphabet $\{0, 1, 2\}$, it is not the case that for all context-free languages $L$ and $M$ the
intersection $L \cap M$ is context-free. -/
theorem not_forall_isContextFree_inf :
    ¬ ∀ L M : Language (Fin 3), L.IsContextFree → M.IsContextFree →
      (L ⊓ M).IsContextFree := by
  intro h
  obtain ⟨L, M, hL, hM, hnot⟩ :=
    exists_isContextFree_inf_not_isContextFree
  exact hnot (h L M hL hM)

/-- **Complements of context-free languages need not be context-free.** It is not the case that
for every context-free language $L$ over the three-letter alphabet $\{0, 1, 2\}$, the complement
of $L$ is context-free. -/
theorem not_forall_isContextFree_compl :
    ¬ ∀ L : Language (Fin 3), L.IsContextFree →
      (Lᶜ).IsContextFree := by
  intro h
  obtain ⟨L, hL, hnot⟩ := exists_isContextFree_compl_not_isContextFree
  exact hnot (h L hL)

end Cslib.Language
