/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Beklemishev's Reflection Calculus

The Reflection Calculus RC is the strictly positive fragment of Japaridze's polymodal provability
logic GLP. Its formulas are built from atoms and `⊤` by conjunction and diamonds `⟨n⟩`, one for
each natural number `n`; its theorems are sequents `A ⊢ B`. Arithmetically, `⟨n⟩` reads as
`n`-consistency (the uniform `Π_{n+1}`-reflection principle) and atoms as theories. Closed
formulas without conjunction, the *worms* `⟨n₁⟩⟨n₂⟩⋯⟨n_k⟩⊤`, ordered by `α <₀ β` iff
`β ⊢ ⟨0⟩α`, form an ordinal notation system of order type `ε₀`, the basis of Beklemishev's
provability-algebra analysis of Peano arithmetic.

This file follows L. D. Beklemishev, "Positive provability logic for uniform reflection
principles", arXiv:1304.4396v3 (2013; *Annals of Pure and Applied Logic* 165 (2014)), Section 2
(axioms 1–6) and Section 4 (Kripke models), restricted to the modalities `n ∈ ℕ` (the source also
has a modality `ω`; the restriction is its `RC_S` with `S = ℕ`).

* `Formula`, `Derives`: strictly positive formulas and the sequent calculus RC (axioms 1–6).
* `Derives.subst_left_right` (**positive replacement**, Lemma 2.2) and `Derives.substitution`
  (closure under substitution, i.e. RC is a normal positive logic).
* `IsFrame`, `Satisfies`, `Derives.sound` (**soundness**, Lemma 4.2(ii)): RC is sound for Kripke
  models whose frames are polytransitive, satisfy condition (J) and are monotone.
* `worm`, `WormLt`: worms and the order `<₀`; `WormLt.replicate_zero_one`: every worm `0⋯0` lies
  below the worm `1`; `not_wormLt_zero_zero`: `<₀` is not reflexive on the worm `0`.

Completeness for these models and the order type `ε₀` of worms are recorded in `WantedExt`.
-/

namespace Cslib
namespace Modal
namespace RC

universe u v

variable {Atom : Type u}

/-- **Strictly positive formulas.** Formulas of the Reflection Calculus, built from atoms and `⊤`
by conjunction and the diamonds `⟨n⟩`, `n ∈ ℕ` (Beklemishev, arXiv:1304.4396v3, Section 2, whose
grammar also allows a modality `ω`). -/
inductive Formula (Atom : Type u) : Type u where
  /-- An atom. -/
  | atom : Atom → Formula Atom
  /-- Truth `⊤`. -/
  | top : Formula Atom
  /-- Conjunction. -/
  | and : Formula Atom → Formula Atom → Formula Atom
  /-- The diamond `⟨n⟩`. -/
  | dia : ℕ → Formula Atom → Formula Atom

/-- **The Reflection Calculus RC.** `Derives A B` is the sequent `A ⊢ B` of RC: axioms and rules 1–5
of the system RJ together with the monotonicity axiom 6, for modalities in `ℕ` (Beklemishev,
"Positive provability logic for uniform reflection principles", arXiv:1304.4396v3, Section 2).
Axioms 4 are redundant in the presence of axiom 6, as the source notes; they are kept to follow
its list. -/
inductive Derives : Formula Atom → Formula Atom → Prop
  /-- Axiom 1: `A ⊢ A`. -/
  | refl (A : Formula Atom) : Derives A A
  /-- Axiom 1: `A ⊢ ⊤`. -/
  | top (A : Formula Atom) : Derives A .top
  /-- Rule 1 (syllogism). -/
  | trans {A B C : Formula Atom} : Derives A B → Derives B C → Derives A C
  /-- Axiom 2: `A ∧ B ⊢ A`. -/
  | and_left (A B : Formula Atom) : Derives (.and A B) A
  /-- Axiom 2: `A ∧ B ⊢ B`. -/
  | and_right (A B : Formula Atom) : Derives (.and A B) B
  /-- Rule 2: from `A ⊢ B` and `A ⊢ C` infer `A ⊢ B ∧ C`. -/
  | and_intro {A B C : Formula Atom} : Derives A B → Derives A C → Derives A (.and B C)
  /-- Rule 3: from `A ⊢ B` infer `⟨n⟩A ⊢ ⟨n⟩B`. -/
  | dia_mono (n : ℕ) {A B : Formula Atom} : Derives A B → Derives (.dia n A) (.dia n B)
  /-- Axiom 3: `⟨n⟩⟨n⟩A ⊢ ⟨n⟩A`. -/
  | dia_dia (n : ℕ) (A : Formula Atom) : Derives (.dia n (.dia n A)) (.dia n A)
  /-- Axiom 4: `⟨m⟩⟨n⟩A ⊢ ⟨n⟩A` for `m ≥ n`. -/
  | dia_dia_of_le {m n : ℕ} (h : n ≤ m) (A : Formula Atom) :
      Derives (.dia m (.dia n A)) (.dia n A)
  /-- Axiom 4: `⟨n⟩⟨m⟩A ⊢ ⟨n⟩A` for `m ≥ n`. -/
  | dia_dia_of_le' {m n : ℕ} (h : n ≤ m) (A : Formula Atom) :
      Derives (.dia n (.dia m A)) (.dia n A)
  /-- Axiom 5: `⟨m⟩A ∧ ⟨n⟩B ⊢ ⟨m⟩(A ∧ ⟨n⟩B)` for `m > n`. -/
  | dia_and {m n : ℕ} (h : n < m) (A B : Formula Atom) :
      Derives (.and (.dia m A) (.dia n B)) (.dia m (.and A (.dia n B)))
  /-- Axiom 6 (monotonicity): `⟨m⟩A ⊢ ⟨n⟩A` for `m > n`. -/
  | monotone {m n : ℕ} (h : n < m) (A : Formula Atom) : Derives (.dia m A) (.dia n A)

/-! ### Substitution -/

section Subst

variable [DecidableEq Atom]

/-- **Substitution in strictly positive formulas.** `C.subst p A` replaces every occurrence of the
atom `p` in `C` by `A`; written `C[A/p]` in the source. -/
def Formula.subst : Formula Atom → Atom → Formula Atom → Formula Atom
  | .atom q, p, A => if q = p then A else .atom q
  | .top, _, _ => .top
  | .and B C, p, A => .and (B.subst p A) (C.subst p A)
  | .dia n B, p, A => .dia n (B.subst p A)

namespace Derives

/-- **Positive replacement.** If `A ⊢ B` in RC then `C[A/p] ⊢ C[B/p]` for every strictly positive
formula `C` (Beklemishev, arXiv:1304.4396v3, Lemma 2.2). -/
theorem subst_left_right {A B : Formula Atom} (h : Derives A B) (p : Atom) (C : Formula Atom) :
    Derives (C.subst p A) (C.subst p B) := by
  induction C with
  | atom q =>
    by_cases hq : q = p
    · simpa [Formula.subst, hq] using h
    · simpa [Formula.subst, hq] using refl (.atom q)
  | top => exact refl _
  | and C D ih₁ ih₂ => exact and_intro (trans (and_left _ _) ih₁) (trans (and_right _ _) ih₂)
  | dia n C ih => exact dia_mono n ih

/-- **Closure under substitution.** If `A ⊢ B` in RC then `A[C/p] ⊢ B[C/p]`: RC is a normal
positive logic (Beklemishev, arXiv:1304.4396v3, Section 2, remark after Lemma 2.2). -/
theorem substitution {A B : Formula Atom} (h : Derives A B) (p : Atom) (C : Formula Atom) :
    Derives (A.subst p C) (B.subst p C) := by
  induction h with
  | refl => exact refl _
  | top => exact top _
  | trans _ _ ih₁ ih₂ => exact trans ih₁ ih₂
  | and_left => exact and_left _ _
  | and_right => exact and_right _ _
  | and_intro _ _ ih₁ ih₂ => exact and_intro ih₁ ih₂
  | dia_mono n _ ih => exact dia_mono n ih
  | dia_dia n A => exact dia_dia n _
  | dia_dia_of_le h A => exact dia_dia_of_le h _
  | dia_dia_of_le' h A => exact dia_dia_of_le' h _
  | dia_and h A B => exact dia_and h _ _
  | monotone h A => exact monotone h _

end Derives

end Subst

/-! ### Kripke semantics and soundness -/

/-- **RC-frame.** A family of relations `R n` on a set of worlds is an RC-frame when it is
polytransitive (`x R m y R n z` implies `x R (min m n) z`), satisfies condition (J) (`x R m y` and
`x R n z` with `m > n` imply `y R n z`) and is monotone (`R m ⊆ R n` for `n < m`) (Beklemishev,
arXiv:1304.4396v3, Section 4, definition of RJ_S- and RC_S-frames). -/
structure IsFrame {World : Type v} (R : ℕ → World → World → Prop) : Prop where
  /-- Polytransitivity. -/
  polytrans : ∀ {m n : ℕ} {x y z : World}, R m x y → R n y z → R (min m n) x z
  /-- Condition (J). -/
  condJ : ∀ {m n : ℕ} {x y z : World}, n < m → R m x y → R n x z → R n y z
  /-- Monotonicity. -/
  monotone : ∀ {m n : ℕ} {x y : World}, n < m → R m x y → R n x y

/-- **Truth of a strictly positive formula in a Kripke model.** `⊤` is true everywhere,
conjunction is pointwise and `⟨n⟩A` holds at `x` when some `y` with `x R n y` satisfies `A`
(Beklemishev, arXiv:1304.4396v3, Section 4). -/
def Satisfies {World : Type v} (R : ℕ → World → World → Prop) (V : World → Atom → Prop) :
    World → Formula Atom → Prop
  | x, .atom p => V x p
  | _, .top => True
  | x, .and A B => Satisfies R V x A ∧ Satisfies R V x B
  | x, .dia n A => ∃ y, R n x y ∧ Satisfies R V y A

/-- **Soundness of RC for RC-models.** If `A ⊢ B` is derivable in RC, then in every Kripke model on
an RC-frame, every world satisfying `A` satisfies `B` (Beklemishev, arXiv:1304.4396v3,
Lemma 4.2(ii)). -/
theorem Derives.sound {World : Type v} {R : ℕ → World → World → Prop} (hR : IsFrame R)
    (V : World → Atom → Prop) {A B : Formula Atom} (h : Derives A B) (x : World) :
    Satisfies R V x A → Satisfies R V x B := by
  induction h generalizing x with
  | refl => exact id
  | top => exact fun _ ↦ trivial
  | trans _ _ ih₁ ih₂ => exact fun hA ↦ ih₂ x (ih₁ x hA)
  | and_left => exact fun hA ↦ hA.1
  | and_right => exact fun hA ↦ hA.2
  | and_intro _ _ ih₁ ih₂ => exact fun hA ↦ ⟨ih₁ x hA, ih₂ x hA⟩
  | dia_mono n _ ih => exact fun ⟨y, hxy, hy⟩ ↦ ⟨y, hxy, ih y hy⟩
  | dia_dia n A =>
    rintro ⟨y, hxy, z, hyz, hz⟩
    exact ⟨z, by simpa using hR.polytrans hxy hyz, hz⟩
  | dia_dia_of_le h A =>
    rintro ⟨y, hxy, z, hyz, hz⟩
    exact ⟨z, by simpa [Nat.min_eq_right h] using hR.polytrans hxy hyz, hz⟩
  | dia_dia_of_le' h A =>
    rintro ⟨y, hxy, z, hyz, hz⟩
    exact ⟨z, by simpa [Nat.min_eq_left h] using hR.polytrans hxy hyz, hz⟩
  | dia_and h A B =>
    rintro ⟨⟨y, hxy, hy⟩, ⟨z, hxz, hz⟩⟩
    exact ⟨y, hxy, hy, z, hR.condJ h hxy hxz, hz⟩
  | monotone h A => exact fun ⟨y, hxy, hy⟩ ↦ ⟨y, hR.monotone h hxy, hy⟩

/-! ### Worms -/

/-- **Worm.** The closed conjunction-free formula `⟨n₁⟩⟨n₂⟩⋯⟨n_k⟩⊤` of a list `[n₁, …, n_k]` of
natural numbers (Beklemishev, "Provability algebras: an overview and current progress", slides,
2012: the words of the positive closed fragment of GLP). -/
def worm : List ℕ → Formula Atom
  | [] => .top
  | n :: l => .dia n (worm l)

/-- **The order `<₀` on worms.** `WormLt α β` holds when `β ⊢ ⟨0⟩α` in RC, i.e. `β` proves the
consistency of `α` (Beklemishev, "Provability algebras: an overview and current progress",
slides, 2012, where `α <₀ β` is defined by `GLP ⊢ β → ⟨0⟩α`). -/
def WormLt (α β : List ℕ) : Prop := Derives (worm β : Formula Atom) (.dia 0 (worm α))

/-- **The worms `0⋯0` lie below the worm `1`.** For every `k`, `⟨1⟩⊤ ⊢ ⟨0⟩⟨0⟩^k⊤`: the worm `1`
proves the consistency of every finite iterate of consistency, as `ω` exceeds every finite
ordinal (in the ordinal assignment of worms, `0^k` has value `k` and `1` has value `ω`). -/
theorem WormLt.replicate_zero_one (k : ℕ) :
    WormLt (Atom := Atom) (List.replicate k 0) [1] := by
  induction k with
  | zero => exact Derives.monotone Nat.zero_lt_one _
  | succ k ih =>
    unfold WormLt at ih ⊢
    simp only [List.replicate_succ, worm] at ih ⊢
    exact Derives.trans (Derives.and_intro (Derives.refl _) ih)
      (Derives.trans (Derives.dia_and Nat.zero_lt_one _ _)
        (Derives.trans (Derives.monotone Nat.zero_lt_one _)
          (Derives.dia_mono 0 (Derives.and_right _ _))))

/-- **Irreflexivity of `<₀` at the worm `0`.** `⟨0⟩⊤ ⊬ ⟨0⟩⟨0⟩⊤` in RC: in the two-world model with
`0 R₀ 1` and all other relations empty, an RC-frame, `⟨0⟩⊤` holds at `0` and `⟨0⟩⟨0⟩⊤` fails. -/
theorem not_wormLt_zero_zero : ¬WormLt (Atom := Atom) [0] [0] := by
  intro h
  let R : ℕ → Bool → Bool → Prop := fun n x y ↦ n = 0 ∧ x = false ∧ y = true
  have hR : IsFrame R :=
    ⟨fun ⟨_, _, hy⟩ ⟨_, hy', _⟩ ↦ absurd (hy.symm.trans hy') (by decide),
      fun hnm ⟨hm, _⟩ _ ↦ absurd hm (Nat.ne_of_gt (Nat.zero_lt_of_lt hnm)),
      fun hnm ⟨hm, _⟩ ↦ absurd hm (Nat.ne_of_gt (Nat.zero_lt_of_lt hnm))⟩
  obtain ⟨y, ⟨_, _, rfl⟩, z, ⟨_, h1, _⟩, _⟩ :=
    Derives.sound hR (fun _ _ ↦ True) h false ⟨true, ⟨rfl, rfl, rfl⟩, trivial⟩
  exact absurd h1 (by decide)

end RC
end Modal
end Cslib
