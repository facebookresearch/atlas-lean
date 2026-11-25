/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.TuringReducible
public import MathlibExt.Computability.RE

@[expose] public section

/-!
# The arithmetical hierarchy

The arithmetical hierarchy (Soare, *Recursively Enumerable Sets and Degrees*,
Ch. I, §4; Rogers, *Theory of Recursive Functions and Effective Computability*,
§13.4) classifies sets of natural numbers by the number of unbounded
quantifier alternations over a computable relation needed to define them:
`Σ₀ = Π₀ = Δ₀` are the computable sets, `Σₙ₊₁` adds one existential
quantifier over a `Πₙ` relation, `Πₙ₊₁` adds one universal quantifier over
a `Σₙ` relation, and `Δₙ = Σₙ ∩ Πₙ`. This file defines the hierarchy,
proves closure under computable precomposition, the interleaving inclusions
(`Σₙ ⊆ Πₙ₊₁`, `Πₙ ⊆ Σₙ₊₁`, hence `Σₙ ⊆ Σₙ₊₁` and `Πₙ ⊆ Πₙ₊₁`), and
`Σ₁ = RE`. The hard parts — strictness of the hierarchy and Post's jump
characterisation — are registered as wanted theorems in
`WantedExt/TheoryOfComputation/HierarchyStrictness.lean` and
`WantedExt/TheoryOfComputation/PostJumpCharacterisation.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

mutual
  /-- A set is in `Σₙ` when it is defined by `n` alternating quantifiers
  over a computable relation, starting with an existential quantifier.
  Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 4.1. -/
  def IsSigma : ℕ → (ℕ → Prop) → Prop
    | 0, P => ComputablePred P
    | n + 1, P => ∃ Q : ℕ → Prop, IsPi n Q ∧ ∀ x, P x ↔ ∃ y, Q (Nat.pair x y)

  /-- A set is in `Πₙ` when it is defined by `n` alternating quantifiers
  over a computable relation, starting with a universal quantifier.
  Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 4.1. -/
  def IsPi : ℕ → (ℕ → Prop) → Prop
    | 0, P => ComputablePred P
    | n + 1, P => ∃ Q : ℕ → Prop, IsSigma n Q ∧ ∀ x, P x ↔ ∀ y, Q (Nat.pair x y)
end

/-- **The class Δₙ of the arithmetical hierarchy.** Let $n$ be a natural number. A set $P$ of
natural numbers is in $\Delta_n$ when it is in both classes $\Sigma_n$ and $\Pi_n$ of the
arithmetical hierarchy.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 4.1. -/
def IsDelta (n : ℕ) (P : ℕ → Prop) : Prop :=
  IsSigma n P ∧ IsPi n P

/-- **Computable predicates are closed under computable precomposition.** If $P$ is a decidable
set of natural numbers and $g : \mathbb{N} \to \mathbb{N}$ is a computable function, then the set
$\{w \in \mathbb{N} : g(w) \in P\}$ is decidable.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Lemma 4.2. -/
theorem computablePred_comp {P : ℕ → Prop} (hP : ComputablePred P) {g : ℕ → ℕ}
    (hg : Computable g) : ComputablePred (fun w ↦ P (g w)) := by
  rw [computablePred_iff_partrec_charFun] at hP ⊢
  have h1 := Partrec.comp hP hg
  exact h1.of_eq (fun _ ↦ rfl)

/-- **The first projection of the pairing function is computable.** Let
$\langle a, b \rangle$ denote the pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$,
$\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise.
The function sending $z \in \mathbb{N}$ to the first component $a$ of the unique pair $(a, b)$
with $\langle a, b \rangle = z$ is computable.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*, §1.3. -/
theorem computable_unpair_fst : Computable (fun z : ℕ ↦ z.unpair.1) :=
  Computable.fst.comp Primrec.unpair.to_comp

/-- **The second projection of the pairing function is computable.** Let
$\langle a, b \rangle$ denote the pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$,
$\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise.
The function sending $z \in \mathbb{N}$ to the second component $b$ of the unique pair $(a, b)$
with $\langle a, b \rangle = z$ is computable.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*, §1.3. -/
theorem computable_unpair_snd : Computable (fun z : ℕ ↦ z.unpair.2) :=
  Computable.snd.comp Primrec.unpair.to_comp

/-- **The pairing function is computable.** The pairing bijection
$\langle \cdot, \cdot \rangle : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$, given by
$\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise,
is a computable function of its two arguments.

Source: Rogers, *Theory of Recursive Functions and Effective Computability*, §1.3. -/
theorem computable_pair : Computable₂ Nat.pair := by
  apply Primrec₂.to_comp
  apply Primrec₂.nat_iff.2
  apply Nat.Primrec.of_eq
    (Nat.Primrec.succ.comp (Nat.Primrec.pair Nat.Primrec.left Nat.Primrec.right))
  intro n
  simp [Nat.unpaired]

/-- **Computable predicates are closed under precomposition with pairing.** Let
$\langle a, b \rangle$ denote the pairing bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$,
$\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise.
If $Q$ is a decidable set of natural numbers, then the set of pairs
$(a, b) \in \mathbb{N} \times \mathbb{N}$ with $\langle a, b \rangle \in Q$ is decidable.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Lemma 4.2. -/
theorem computablePred_comp_prod {Q : ℕ → Prop} (hQ : ComputablePred Q) :
    ComputablePred (fun p : ℕ × ℕ ↦ Q (Nat.pair p.1 p.2)) := by
  obtain ⟨fQ, hfQ, hQeq⟩ := ComputablePred.computable_iff.1 hQ
  refine ComputablePred.computable_iff.2 ⟨fun p : ℕ × ℕ ↦ fQ (Nat.pair p.1 p.2),
    hfQ.comp computable_pair, ?_⟩
  rw [hQeq]


/-- **The hierarchy is closed under computable precomposition.** Let $n$ be a natural number
and let $g : \mathbb{N} \to \mathbb{N}$ be computable. If a set $P$ of natural numbers is in
the class $\Sigma_n$ of the arithmetical hierarchy, then so is $\{w \in \mathbb{N} : g(w) \in P\}$;
and if $P$ is in the class $\Pi_n$, then so is $\{w \in \mathbb{N} : g(w) \in P\}$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Lemma 4.2. -/
theorem comp_closure (n : ℕ) :
    (∀ P : ℕ → Prop, IsSigma n P → ∀ g : ℕ → ℕ, Computable g →
      IsSigma n (fun w ↦ P (g w))) ∧
    (∀ P : ℕ → Prop, IsPi n P → ∀ g : ℕ → ℕ, Computable g →
      IsPi n (fun w ↦ P (g w))) := by
  induction n with
  | zero =>
    exact ⟨fun _ hP _ hg ↦ computablePred_comp hP hg,
      fun _ hP _ hg ↦ computablePred_comp hP hg⟩
  | succ n ih =>
    obtain ⟨ihS, ihP⟩ := ih
    have hpair : ∀ g : ℕ → ℕ, Computable g →
        Computable (fun z : ℕ ↦ Nat.pair (g z.unpair.1) z.unpair.2) := fun g hg ↦
      Computable₂.comp computable_pair (hg.comp computable_unpair_fst)
        computable_unpair_snd
    refine ⟨?_, ?_⟩
    · intro P hP g hg
      obtain ⟨Q, hQ, hiff⟩ := hP
      refine ⟨fun z ↦ Q (Nat.pair (g z.unpair.1) z.unpair.2),
        ihP Q hQ _ (hpair g hg), fun w ↦ ?_⟩
      constructor
      · intro h
        obtain ⟨y, hy⟩ := (hiff (g w)).1 h
        exact ⟨y, by simpa [Nat.unpair_pair] using hy⟩
      · intro h
        obtain ⟨y, hy⟩ := h
        exact (hiff (g w)).2 ⟨y, by rwa [Nat.unpair_pair] at hy⟩
    · intro P hP g hg
      obtain ⟨Q, hQ, hiff⟩ := hP
      refine ⟨fun z ↦ Q (Nat.pair (g z.unpair.1) z.unpair.2),
        ihS Q hQ _ (hpair g hg), fun w ↦ ?_⟩
      constructor
      · intro h y
        simpa [Nat.unpair_pair] using (hiff (g w)).1 h y
      · intro h
        apply (hiff (g w)).2
        intro y
        simpa [Nat.unpair_pair] using h y

/-- **Every Σₙ predicate is Πₙ₊₁.** Let $\Sigma_n$ and $\Pi_n$ be the levels of the arithmetical
hierarchy of predicates on $\mathbb{N}$: $\Sigma_0 = \Pi_0$ is the class of computable predicates,
$P \in \Sigma_{n+1}$ when for some $Q \in \Pi_n$ and all $x$, $P(x)$ holds iff
$Q(\langle x, y \rangle)$ holds for some $y$, and $P \in \Pi_{n+1}$ when for some $Q \in \Sigma_n$
and all $x$, $P(x)$ holds iff $Q(\langle x, y \rangle)$ holds for all $y$; here
$\langle x, y \rangle$ is the standard pairing function of $\mathbb{N}$. Then for every $n$, every
predicate in $\Sigma_n$ is in $\Pi_{n+1}$.

The proof adds a dummy universal quantifier.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3. -/
theorem sigma_subset_pi_succ {n : ℕ} {P : ℕ → Prop} (h : IsSigma n P) :
    IsPi (n + 1) P := by
  refine ⟨fun w ↦ P w.unpair.1, (comp_closure n).1 P h _ computable_unpair_fst,
    fun x ↦ ?_⟩
  constructor
  · intro hP _
    simpa [Nat.unpair_pair] using hP
  · intro h
    simpa [Nat.unpair_pair] using h 0

/-- **Every Πₙ set is Σₙ₊₁.** For every natural number $n$, every set of natural numbers in the
class $\Pi_n$ of the arithmetical hierarchy is also in $\Sigma_{n+1}$; that is,
$\Pi_n \subseteq \Sigma_{n+1}$, by adding a dummy existential quantifier.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3. -/
theorem pi_subset_sigma_succ {n : ℕ} {P : ℕ → Prop} (h : IsPi n P) :
    IsSigma (n + 1) P := by
  refine ⟨fun w ↦ P w.unpair.1, (comp_closure n).2 P h _ computable_unpair_fst,
    fun x ↦ ?_⟩
  constructor
  · intro hP
    exact ⟨0, by simpa [Nat.unpair_pair] using hP⟩
  · intro h
    obtain ⟨y, hy⟩ := h
    simpa [Nat.unpair_pair] using hy

/-- **Monotonicity of the hierarchy.** For every natural number $n$, writing $\Sigma_n$ and $\Pi_n$
for the classes of the arithmetical hierarchy, every $\Sigma_n$ set of natural numbers is in
$\Sigma_{n+1}$ and every $\Pi_n$ set of natural numbers is in $\Pi_{n+1}$.

The two inclusions are proved together by induction on $n$: the step case of each uses the
other at the previous level.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3. -/
theorem mono_aux : ∀ n : ℕ,
    (∀ P : ℕ → Prop, IsSigma n P → IsSigma (n + 1) P) ∧
    (∀ P : ℕ → Prop, IsPi n P → IsPi (n + 1) P) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro P hP
      refine ⟨fun w ↦ P w.unpair.1, computablePred_comp hP computable_unpair_fst,
        fun x ↦ ?_⟩
      constructor
      · intro h
        exact ⟨0, by simpa [Nat.unpair_pair] using h⟩
      · intro h
        obtain ⟨y, hy⟩ := h
        simpa [Nat.unpair_pair] using hy
    · intro P hP
      refine ⟨fun w ↦ P w.unpair.1, computablePred_comp hP computable_unpair_fst,
        fun x ↦ ?_⟩
      constructor
      · intro h _
        simpa [Nat.unpair_pair] using h
      · intro h
        simpa [Nat.unpair_pair] using h 0
  | succ n ih =>
    obtain ⟨ihS, ihP⟩ := ih
    refine ⟨?_, ?_⟩
    · intro P hP
      obtain ⟨Q, hQ, hiff⟩ := hP
      exact ⟨Q, ihP Q hQ, hiff⟩
    · intro P hP
      obtain ⟨Q, hQ, hiff⟩ := hP
      exact ⟨Q, ihS Q hQ, hiff⟩

/-- **Every Σₙ predicate is Σₙ₊₁.** Let $\Sigma_n$ and $\Pi_n$ be the levels of the arithmetical
hierarchy of predicates on $\mathbb{N}$: $\Sigma_0 = \Pi_0$ is the class of computable predicates,
$P \in \Sigma_{n+1}$ when for some $Q \in \Pi_n$ and all $x$, $P(x)$ holds iff
$Q(\langle x, y \rangle)$ holds for some $y$, and $P \in \Pi_{n+1}$ when for some $Q \in \Sigma_n$
and all $x$, $P(x)$ holds iff $Q(\langle x, y \rangle)$ holds for all $y$; here
$\langle x, y \rangle$ is the standard pairing function of $\mathbb{N}$. Then for every $n$, every
predicate in $\Sigma_n$ is in $\Sigma_{n+1}$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3. -/
theorem sigma_mono {n : ℕ} {P : ℕ → Prop} (h : IsSigma n P) : IsSigma (n + 1) P :=
  (mono_aux n).1 P h

/-- **Monotonicity of the Π hierarchy.** For every natural number $n$, every set of natural
numbers in the class $\Pi_n$ of the arithmetical hierarchy is also in $\Pi_{n+1}$; that is,
$\Pi_n \subseteq \Pi_{n+1}$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3. -/
theorem pi_mono {n : ℕ} {P : ℕ → Prop} (h : IsPi n P) : IsPi (n + 1) P :=
  (mono_aux n).2 P h

/-- **Σₙ and Πₙ predicates are Δₙ₊₁.** Let $\Sigma_n$ and $\Pi_n$ be the levels of the arithmetical
hierarchy of predicates on $\mathbb{N}$: $\Sigma_0 = \Pi_0$ is the class of computable predicates,
$P \in \Sigma_{n+1}$ when for some $Q \in \Pi_n$ and all $x$, $P(x)$ holds iff
$Q(\langle x, y \rangle)$ holds for some $y$, and $P \in \Pi_{n+1}$ when for some $Q \in \Sigma_n$
and all $x$, $P(x)$ holds iff $Q(\langle x, y \rangle)$ holds for all $y$; here
$\langle x, y \rangle$ is the standard pairing function of $\mathbb{N}$. Then for every $n$, every
predicate in $\Sigma_n$ or in $\Pi_n$ is in $\Delta_{n+1}$, that is, in both $\Sigma_{n+1}$ and
$\Pi_{n+1}$.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.3. -/
theorem sigma_pi_subset_delta_succ {n : ℕ} {P : ℕ → Prop}
    (h : IsSigma n P ∨ IsPi n P) : IsDelta (n + 1) P := by
  cases h with
  | inl hS => exact ⟨sigma_mono hS, sigma_subset_pi_succ hS⟩
  | inr hP => exact ⟨pi_subset_sigma_succ hP, pi_mono hP⟩

/-- **Σ₁ is the class of recursively enumerable predicates.** A predicate $P$ on $\mathbb{N}$ is
recursively enumerable if and only if it is in $\Sigma_1$, that is, if and only if there is a
computable predicate $Q$ on $\mathbb{N}$ such that for all $x$, $P(x)$ holds iff
$Q(\langle x, y \rangle)$ holds for some $y$, where $\langle x, y \rangle$ is the standard pairing
function of $\mathbb{N}$.

This is the first level of Post's theorem.

Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 4.4 (Post). -/
theorem sigma_one_eq_re {P : ℕ → Prop} : IsSigma 1 P ↔ REPred P := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hiff⟩ := h
    have hQ' : REPred (fun p : ℕ × ℕ ↦ Q (Nat.pair p.1 p.2)) :=
      (computablePred_comp_prod hQ).to_re
    have hRE : REPred (fun x : ℕ ↦ ∃ y, Q (Nat.pair x y)) :=
      MetaMathlibExt.REPred.exists (R := fun a b ↦ Q (Nat.pair a b)) hQ'
    exact hRE.of_eq (fun x ↦ (hiff x).symm)
  · intro hP
    have hP' : Partrec (fun a : ℕ ↦ Part.assert (P a) (fun _ ↦ Part.some ())) := hP
    have hf : Partrec (fun a : ℕ ↦
        (Part.assert (P a) (fun _ ↦ Part.some ())).map (fun _ ↦ (0 : ℕ))) :=
      hP'.map (Computable.const (0 : ℕ)).to₂
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf)
    have hiff : ∀ x, P x ↔ (Nat.Partrec.Code.eval c x).Dom := fun x ↦ by
      rw [hc]
      change P x ↔ ((Part.assert (P x) (fun _ ↦ Part.some ())).map (fun _ ↦ (0 : ℕ))).Dom
      rw [Part.map_Dom]
      constructor
      · intro h
        exact Part.dom_iff_mem.2
          ⟨(), Part.mem_assert h (Part.mem_some_iff.2 rfl)⟩
      · intro hDom
        obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hDom
        obtain ⟨h, -⟩ := Part.mem_assert_iff.1 hz
        exact h
    refine ⟨fun w ↦ ((Nat.Partrec.Code.evaln w.unpair.2 c w.unpair.1).isSome = true),
      ?_, fun x ↦ ?_⟩
    · have hcomp : Computable (fun w : ℕ ↦
          (Nat.Partrec.Code.evaln w.unpair.2 c w.unpair.1).isSome) :=
        (Primrec.option_isSome.to_comp).comp
          ((Nat.Partrec.Code.primrec_evaln.to_comp).comp
            (Computable.pair
              (Computable.pair computable_unpair_snd (Computable.const c))
              computable_unpair_fst))
      exact ComputablePred.computable_iff.2
        ⟨fun w ↦ (Nat.Partrec.Code.evaln w.unpair.2 c w.unpair.1).isSome, hcomp, rfl⟩
    · constructor
      · intro h
        obtain ⟨x', hx'⟩ := Part.dom_iff_mem.1 ((hiff x).1 h)
        obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hx'
        refine ⟨k, ?_⟩
        change ((Nat.Partrec.Code.evaln (Nat.pair x k).unpair.2 c
          (Nat.pair x k).unpair.1).isSome = true)
        rw [Nat.unpair_pair]
        exact Option.isSome_iff_exists.2 ⟨x', hk⟩
      · intro h
        obtain ⟨y, hy⟩ := h
        apply (hiff x).2
        have hy' : (Nat.Partrec.Code.evaln y c x).isSome = true := by
          have h2 := hy
          rw [Nat.unpair_pair] at h2
          exact h2
        obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 hy'
        exact Part.dom_iff_mem.2 ⟨x', Nat.Partrec.Code.evaln_sound hx'⟩
end Cslib.Decidability
