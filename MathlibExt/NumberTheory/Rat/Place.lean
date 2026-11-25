/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section

/-!
# Rational places and completed fields

Source: arXiv:2607.14033, `pq-work-rank0-sha1.tex`, lines 237--240:

> Let M_Q be the set of all inequivalent normalised absolute values on Q.
> It consists of the ordinary absolute value, along with one non-archimedean
> absolute value for each prime number l.

`M_ℚ` is formalised as `Rat.Place` and `ℚ_v` as `CompletedField v`
(`ℝ` at infinity, `ℚ_[p]` at a prime), reusing
`Rat.AbsoluteValue.real` and `Rat.AbsoluteValue.padic`.
-/

namespace Rat

/-- **Places of $\mathbb{Q}$.** The set $M_{\mathbb{Q}}$ of places of $\mathbb{Q}$, which indexes
the inequivalent normalised absolute values on $\mathbb{Q}$. It consists of one infinite place,
corresponding to the ordinary archimedean absolute value, and one finite place for each prime
number $p$, corresponding to the $p$-adic absolute value. -/
inductive Place : Type where
  | infinite : Place
  | finite : (prime : Nat.Primes) → Place
  deriving DecidableEq

namespace Place

/-- **Absolute value at a rational place.** For a place $v$ of $\mathbb{Q}$, the absolute value
$|\cdot|_v : \mathbb{Q} \to \mathbb{R}$ sends $q \in \mathbb{Q}$ to the ordinary absolute value
$|q|$ when $v$ is the infinite place. When $v$ is the finite place at a prime $p$, it sends $q$ to
the normalised $p$-adic absolute value $|q|_p$, where $|0|_p = 0$ and $|q|_p = p^{-v_p(q)}$ for
$q \neq 0$, with $v_p(q)$ the $p$-adic valuation of $q$. -/
noncomputable def absoluteValue : Place → AbsoluteValue ℚ ℝ
  | .infinite => Rat.AbsoluteValue.real
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    Rat.AbsoluteValue.padic prime.1

/-- **Bundled complete normed field.** A complete normed field bundled with its structure: a type
$K$ together with a normed field structure on $K$ for which $K$ is complete with respect to the
metric induced by the norm. It is used to package the completed fields $\mathbb{Q}_v$ of
$\mathbb{Q}$ at its places $v$. -/
structure CompletedFieldBundle where
  carrier : Type
  [normedField : NormedField carrier]
  [completeSpace : CompleteSpace carrier]

instance : CoeSort CompletedFieldBundle Type where
  coe B := B.carrier

/-- **Bundled completed field at a rational place.** To each place $v$ of $\mathbb{Q}$ this assigns
a complete normed field: the real numbers $\mathbb{R}$ with the usual absolute value when $v$ is the
infinite place, and, when $v$ is the finite place at a prime $p$, the field $\mathbb{Q}_p$ of
$p$-adic numbers with the $p$-adic norm. -/
noncomputable abbrev bundle : Place → CompletedFieldBundle
  | .infinite => ⟨ℝ⟩
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    ⟨Padic prime.1⟩

/-- **Completed field at a rational place.** For a place $v$ of $\mathbb{Q}$, the completed field
$\mathbb{Q}_v$ is the field $\mathbb{R}$ of real numbers when $v$ is the infinite place and, when
$v$ is the finite place at a prime $p$, the field $\mathbb{Q}_p$ of $p$-adic numbers.

It is a complete normed field, with the usual absolute value on $\mathbb{R}$ and the $p$-adic norm
on $\mathbb{Q}_p$. -/
noncomputable abbrev CompletedField (v : Place) : Type :=
  (bundle v : Type)

noncomputable instance (v : Place) : NormedField (CompletedField v) :=
  (bundle v).normedField

instance (v : Place) : CompleteSpace (CompletedField v) :=
  (bundle v).completeSpace

theorem completedField_infinite :
    CompletedField .infinite = ℝ :=
  rfl

theorem completedField_finite (prime : Nat.Primes) :
    letI : Fact prime.1.Prime := ⟨prime.2⟩
    CompletedField (.finite prime) = Padic prime.1 :=
  rfl

/-- **Embedding of the rationals into a completion.** For a place $v$ of $\mathbb{Q}$ with
completed field $\mathbb{Q}_v$, the canonical ring homomorphism $\mathbb{Q} \to \mathbb{Q}_v$ sends
each rational number to itself, viewed as a real number when $v$ is the infinite place and as a
$p$-adic number when $v$ is the finite place at a prime $p$. -/
noncomputable def embedding : (v : Place) → ℚ →+* CompletedField v
  | .infinite => Rat.castHom ℝ
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    Rat.castHom (Padic prime.1)

/-- **Absolute value at the infinite rational place.** For every $q \in \mathbb{Q}$, the absolute
value attached to the infinite place of $\mathbb{Q}$, evaluated at $q$, equals the ordinary absolute
value $|q|$ of $q$ viewed as a real number. -/
theorem absoluteValue_infinite_apply (q : ℚ) :
    absoluteValue .infinite q = |(q : ℝ)| := by
  simp [absoluteValue, Rat.AbsoluteValue.real]

/-- **Absolute value at a finite rational place.** For every prime $p$ and every $q \in \mathbb{Q}$,
the absolute value attached to the finite place of $\mathbb{Q}$ at $p$, evaluated at $q$, equals the
$p$-adic absolute value $|q|_p$ of $q$. Here $|0|_p = 0$, and $|q|_p = p^{-v_p(q)}$ for $q \neq 0$,
where $v_p(q)$ is the $p$-adic valuation of $q$. -/
theorem absoluteValue_finite_apply (prime : Nat.Primes) (q : ℚ) :
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    absoluteValue (.finite prime) q = Rat.AbsoluteValue.padic prime.1 q :=
  rfl

/-- **Norm of a rational in a completion.** For every place $v$ of $\mathbb{Q}$ and every
$q \in \mathbb{Q}$, the norm in the completed field $\mathbb{Q}_v$ of the image of $q$ under the
canonical embedding $\mathbb{Q} \to \mathbb{Q}_v$ equals $|q|_v$, the absolute value attached to $v$
evaluated at $q$. -/
theorem embedding_norm_eq_absoluteValue (v : Place) (q : ℚ) :
    ‖embedding v q‖ = v.absoluteValue q := by
  cases v with
  | infinite =>
    simp only [embedding, absoluteValue, Rat.AbsoluteValue.real_eq_abs]
    change |(q : ℝ)| = (↑|q| : ℝ)
    exact (Rat.cast_abs q).symm
  | finite prime =>
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    simp only [embedding, absoluteValue, Rat.AbsoluteValue.padic_eq_padicNorm]
    change ‖(q : Padic prime.1)‖ = (padicNorm prime.1 q : ℝ)
    exact Padic.eq_padicNorm q

/-- **The rationals are dense in each completion.** For every place $v$ of $\mathbb{Q}$, with
completed field $\mathbb{Q}_v$, the image of $\mathbb{Q}$ under the canonical embedding
$\mathbb{Q} \to \mathbb{Q}_v$ is dense in $\mathbb{Q}_v$. -/
theorem denseRange_embedding (v : Place) :
    DenseRange (embedding v) := by
  cases v with
  | infinite =>
    simpa [embedding] using (Rat.denseRange_cast (𝕜 := ℝ))
  | finite prime =>
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    have h := Padic.denseRange_ratCast prime.1
    simpa [embedding] using h

/-- **Every nontrivial absolute value on $\mathbb{Q}$ is equivalent to that of a place.** Let $f$
be a real-valued absolute value on $\mathbb{Q}$ that is nontrivial, that is, $f(x) \ne 1$ for some
$x \ne 0$. Then there is a place $v$ of $\mathbb{Q}$ such that $f$ is equivalent to the absolute
value $|\cdot|_v$ attached to $v$ (the ordinary absolute value at the infinite place, the
$p$-adic absolute value at the prime $p$).

Here two absolute values $f$ and $g$ on $\mathbb{Q}$ are equivalent when $f(x) \le f(y)$ holds
exactly when $g(x) \le g(y)$, for all $x, y \in \mathbb{Q}$. -/
theorem exists_place_equiv (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    ∃ v : Place, f ≈ v.absoluteValue := by
  have h := Rat.AbsoluteValue.equiv_real_or_padic f hf
  rcases h with hreal | ⟨p, ⟨hp, h⟩, _⟩
  · exact ⟨.infinite, by simpa [absoluteValue] using hreal⟩
  · exact ⟨.finite ⟨p, hp.out⟩, by
      let _ := hp
      simpa [absoluteValue] using h⟩

/-- **Ostrowski's theorem for $\mathbb{Q}$, indexed by places.** Let $f$ be a real-valued absolute
value on $\mathbb{Q}$ that is nontrivial, that is, $f(x) \ne 1$ for some $x \ne 0$. Then there is
exactly one place $v$ of $\mathbb{Q}$ such that $f$ is equivalent to the absolute value
$|\cdot|_v$ attached to $v$ (the ordinary absolute value at the infinite place, the $p$-adic
absolute value at the prime $p$).

Here two absolute values $f$ and $g$ on $\mathbb{Q}$ are equivalent when $f(x) \le f(y)$ holds
exactly when $g(x) \le g(y)$, for all $x, y \in \mathbb{Q}$. -/
theorem exists_unique_place_equiv (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    ∃! v : Place, f ≈ v.absoluteValue := by
  have hex := Rat.AbsoluteValue.equiv_real_or_padic f hf
  rcases hex with hreal | ⟨p, ⟨hp, hpadic⟩, huniq⟩
  · refine ⟨.infinite, by simpa [absoluteValue] using hreal, ?_⟩
    intro w hw
    cases w with
    | infinite => rfl
    | finite prime =>
      let _ : Fact prime.1.Prime := ⟨prime.2⟩
      have hq : f ≈ Rat.AbsoluteValue.padic prime.1 := by
        simpa [absoluteValue] using hw
      have h : Rat.AbsoluteValue.real ≈ Rat.AbsoluteValue.padic prime.1 :=
        hreal.symm.trans hq
      exact absurd h (Rat.AbsoluteValue.not_real_isEquiv_padic (p := prime.1))
  · refine ⟨.finite ⟨p, hp.out⟩, by let _ := hp; simpa [absoluteValue] using hpadic, ?_⟩
    intro w hw
    cases w with
    | infinite =>
      have hreal' : f ≈ Rat.AbsoluteValue.real := by
        simpa [absoluteValue] using hw
      let _ := hp
      have h : Rat.AbsoluteValue.real ≈ Rat.AbsoluteValue.padic p :=
        hreal'.symm.trans hpadic
      exact absurd h (Rat.AbsoluteValue.not_real_isEquiv_padic (p := p))
    | finite prime =>
      let _ : Fact prime.1.Prime := ⟨prime.2⟩
      have hq : f ≈ Rat.AbsoluteValue.padic prime.1 := by
        simpa [absoluteValue] using hw
      have hq' : ∃ _ : Fact prime.1.Prime, f ≈ Rat.AbsoluteValue.padic prime.1 :=
        ⟨inferInstance, hq⟩
      have heq : prime.1 = p := huniq prime.1 hq'
      have hprime_eq : prime = ⟨p, hp.out⟩ := Subtype.ext heq
      rw [hprime_eq]

/-- **Embedding of $\mathbb{Q}$, normed by a place, into its completion.** For a place $v$ of
$\mathbb{Q}$, the ring homomorphism from $\mathbb{Q}$, equipped with the absolute value $|\cdot|_v$
attached to $v$ as its norm, into the completed field $\mathbb{Q}_v$ given by the canonical
embedding of $\mathbb{Q}$ ($\mathbb{Q}_v = \mathbb{R}$ at the infinite place and
$\mathbb{Q}_v = \mathbb{Q}_p$ at a prime $p$). -/
noncomputable def withAbsEmbedding (v : Place) :
    WithAbs (v.absoluteValue) →+* CompletedField v :=
  (embedding v).comp (WithAbs.equiv (v.absoluteValue)).toRingHom

/-- **The embedding of $\mathbb{Q}$ into its completion at a place is an isometry.** Let $v$ be a
place of $\mathbb{Q}$, let $|\cdot|_v$ be the absolute value attached to $v$, and let
$\mathbb{Q}_v$ be the completed field at $v$. The canonical embedding of $\mathbb{Q}$, equipped
with the metric $d(x, y) = |x - y|_v$, into $\mathbb{Q}_v$ is an isometry: for all
$x, y \in \mathbb{Q}$, the distance between the images of $x$ and $y$ in $\mathbb{Q}_v$ equals
$|x - y|_v$. -/
theorem withAbsEmbedding_isometry (v : Place) :
    Isometry (withAbsEmbedding v) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change ‖embedding v x.ofAbs‖ = ‖x‖
  rw [embedding_norm_eq_absoluteValue, WithAbs.norm_eq_apply_ofAbs]

/-- **Density of the rationals with a place's absolute value in the completion.** Let $v$ be a
place of $\mathbb{Q}$, let $|\cdot|_v$ be the absolute value attached to $v$, let $\mathbb{Q}_v$ be
the completed field at $v$, and write $(\mathbb{Q}, |\cdot|_v)$ for the field $\mathbb{Q}$ equipped
with $|\cdot|_v$. The image of the canonical ring homomorphism
$(\mathbb{Q}, |\cdot|_v) \to \mathbb{Q}_v$, which sends each rational number to itself, is dense
in $\mathbb{Q}_v$. -/
theorem denseRange_withAbsEmbedding (v : Place) :
    DenseRange (withAbsEmbedding v) := by
  change Dense (Set.range ((embedding v) ∘ (WithAbs.equiv (v.absoluteValue))))
  rw [(WithAbs.equiv (v.absoluteValue)).surjective.range_comp]
  exact denseRange_embedding v

end Place

end Rat
