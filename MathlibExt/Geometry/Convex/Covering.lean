/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Translate covering of convex bodies

Source: Arman, Bondarenko and Prymak, arXiv:2404.00547v1, introduction.
The abstract defines the Hadwiger numbers universally over bodies; the displayed
minimum over bodies in the introduction is inconsistent with that definition.
-/

@[expose] public section

namespace ConvexCovering

/-- **Convex bodies in Euclidean space.** A set $K$ in the Euclidean space $\mathbb{R}^n$ is a
convex body when it is compact and convex and its interior in $\mathbb{R}^n$ is nonempty. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- **Covering by translates.** For sets $K$ and $L$ in the Euclidean space $\mathbb{R}^n$ and a
natural number $q$, $K$ is covered by $q$ translates of $L$ when there are vectors
$v_1, \dots, v_q \in \mathbb{R}^n$ with $K \subseteq \bigcup_{i=1}^{q} (v_i + L)$, where
$v + L = \{v + y : y \in L\}$. -/
def CoveredByTranslates {n : ℕ} (K L : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : Prop :=
  ∃ translations : Fin q → EuclideanSpace ℝ (Fin n),
    K ⊆ ⋃ i, (fun x ↦ translations i + x) '' L

/-- **Covering by interior translates.** A set $K$ in the Euclidean space $\mathbb{R}^n$ is covered
by $q$ interior translates, for a natural number $q$, when there are vectors
$v_1, \dots, v_q \in \mathbb{R}^n$ such that
$K \subseteq \bigcup_{i=1}^{q} (v_i + \operatorname{int} K)$, where $\operatorname{int} K$ is the
interior of $K$ in $\mathbb{R}^n$ and $v + S = \{v + y : y \in S\}$. -/
def CoveredByInteriorTranslates {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) : Prop :=
  CoveredByTranslates K (interior K) q

/-- **Uniform bound for covering convex bodies by interior translates.** For $n, q \in \mathbb{N}$,
the uniform interior translate bound holds when every convex body $K \subseteq \mathbb{R}^n$ (a
compact convex set with nonempty interior) is covered by $q$ translates of its interior
$\operatorname{int} K$, that is, $K \subseteq (v_1 + \operatorname{int} K) \cup \dots \cup
(v_q + \operatorname{int} K)$ for some $v_1, \dots, v_q \in \mathbb{R}^n$.

This is one bound $q$ for all bodies at once, not a minimum over bodies. -/
def UniformInteriorTranslateBound (n q : ℕ) : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsConvexBody K → CoveredByInteriorTranslates K q

/-- **Central symmetry about some center.** A set $K$ in the Euclidean space $\mathbb{R}^n$ is
centrally symmetric when there is a point $c \in \mathbb{R}^n$ such that for every
$x \in \mathbb{R}^n$, $x \in K$ if and only if $2c - x \in K$. -/
def IsCentrallySymmetric {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin n),
    ∀ x, x ∈ K ↔ c + c - x ∈ K

/-- **Uniform bound for covering centrally symmetric convex bodies by interior translates.** For
$n, q \in \mathbb{N}$, the uniform symmetric interior translate bound holds when every convex body
$K \subseteq \mathbb{R}^n$ (a compact convex set with nonempty interior) that is centrally
symmetric, meaning that there is $c \in \mathbb{R}^n$ such that for all $x \in \mathbb{R}^n$,
$x \in K$ if and only if $2c - x \in K$, is covered by $q$ translates of its interior, that is,
$K \subseteq (v_1 + \operatorname{int} K) \cup \dots \cup (v_q + \operatorname{int} K)$ for some
$v_1, \dots, v_q \in \mathbb{R}^n$. -/
def UniformSymmetricInteriorTranslateBound (n q : ℕ) : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsConvexBody K → IsCentrallySymmetric K → CoveredByInteriorTranslates K q

/-- **Covering by smaller positive homothets.** A set $K$ in the Euclidean space $\mathbb{R}^n$ is
covered by $q$ smaller positive homothets, for a natural number $q$, when there are real numbers
$r_1, \dots, r_q$ with $0 < r_i < 1$ for every $i$ and vectors $v_1, \dots, v_q \in \mathbb{R}^n$
such that every point of $K$ lies in $v_i + r_i K = \{v_i + r_i y : y \in K\}$ for some $i$.

The homothets are indexed by $i$, so the same homothet may occur more than once. -/
def CoveredBySmallerPositiveHomothets {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : Prop :=
  ∃ (r : Fin q → ℝ) (v : Fin q → EuclideanSpace ℝ (Fin n)),
    (∀ i, 0 < r i ∧ r i < 1) ∧
      ∀ x ∈ K, ∃ i, x ∈ (fun y ↦ v i + r i • y) '' K

/-- **Translate covering number.** For sets $K, L \subseteq \mathbb{R}^n$, the translate covering
number of $K$ by $L$ is the least natural number $q$ for which there are vectors
$v_1, \dots, v_q \in \mathbb{R}^n$ with $K \subseteq (v_1 + L) \cup \dots \cup (v_q + L)$, and it
is $\infty$ if no such $q$ exists. -/
noncomputable def translateCoveringNumber {n : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n))) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q : ℕ | CoveredByTranslates K L q})

/-- **Hadwiger covering number.** The Hadwiger covering number of dimension $n$, an element of
$\mathbb{N} \cup \{\infty\}$, is the least natural number $q$ such that every convex body $K$ in
the Euclidean space $\mathbb{R}^n$ is covered by $q$ translates of its interior
$\operatorname{int} K$, and it is $\infty$ if no such $q$ exists. -/
noncomputable def hadwigerCoveringNumber (n : ℕ) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q : ℕ | UniformInteriorTranslateBound n q})

/-- **Symmetric Hadwiger covering number.** For $n \in \mathbb{N}$, the symmetric Hadwiger
covering number in dimension $n$ is the least natural number $q$ such that every centrally
symmetric convex body $K \subseteq \mathbb{R}^n$ (a compact convex set with nonempty interior that
is symmetric about some point) is covered by $q$ translates of its interior, and it is $\infty$
if no such $q$ exists. -/
noncomputable def symmetricHadwigerCoveringNumber (n : ℕ) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) ''
    {q : ℕ | UniformSymmetricInteriorTranslateBound n q})

/-- **Pointwise form of covering by translates.** For sets $K$ and $L$ in the Euclidean space
$\mathbb{R}^n$ and a natural number $q$, $K$ is covered by $q$ translates of $L$ if and only if
there are vectors $v_1, \dots, v_q \in \mathbb{R}^n$ such that every $x \in K$ lies in
$v_i + L = \{v_i + y : y \in L\}$ for some $i$. -/
theorem coveredByTranslates_iff {n q : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n))) :
    CoveredByTranslates K L q ↔
      ∃ v : Fin q → EuclideanSpace ℝ (Fin n), ∀ x ∈ K, ∃ i, x ∈ (fun y ↦ v i + y) '' L := by
  constructor
  · rintro ⟨v, h⟩
    exact ⟨v, fun x hx ↦ Set.mem_iUnion.mp (h hx)⟩
  · rintro ⟨v, h⟩
    exact ⟨v, fun x hx ↦ Set.mem_iUnion.mpr (h x hx)⟩

/-- **Interior-translate covers unfold to translate covers.** For every set $K$ in the Euclidean
space $\mathbb{R}^n$ and every natural number $q$, $K$ has a cover by $q$ interior translates if
and only if $K$ is covered by $q$ translates of the set $L = \operatorname{int} K$, the interior
of $K$ in $\mathbb{R}^n$. -/
theorem coveredByInteriorTranslates_iff {n q : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    CoveredByInteriorTranslates K q ↔ CoveredByTranslates K (interior K) q :=
  Iff.rfl

private theorem castCount_sInf_eq_of_isLeast (P : ℕ → Prop) (q : ℕ)
    (h : IsLeast {r : ℕ | P r} q) :
    sInf ((fun r : ℕ ↦ (r : WithTop ℕ)) '' {r : ℕ | P r}) = (q : WithTop ℕ) := by
  apply IsLeast.csInf_eq
  refine ⟨⟨q, h.1, rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact WithTop.coe_le_coe.mpr (h.2 hr)

/-- **The translate covering number is the least covering count.** Let $K, L \subseteq \mathbb{R}^n$
and let $q \in \mathbb{N}$. If $q$ is the least natural number $r$ such that $K$ is covered by $r$
translates of $L$, then the translate covering number of $K$ by $L$ equals $q$. -/
theorem translateCoveringNumber_eq_of_isLeast {n q : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (h : IsLeast {r : ℕ | CoveredByTranslates K L r} q) :
    translateCoveringNumber K L = (q : WithTop ℕ) :=
  castCount_sInf_eq_of_isLeast _ q h

/-- **A least uniform bound is the Hadwiger covering number.** If $q$ is the least natural number
such that every convex body $K$ in the Euclidean space $\mathbb{R}^n$ is covered by $q$ translates
of its interior, then the Hadwiger covering number of dimension $n$ equals $q$. -/
theorem hadwigerCoveringNumber_eq_of_isLeast {n q : ℕ}
    (h : IsLeast {r : ℕ | UniformInteriorTranslateBound n r} q) :
    hadwigerCoveringNumber n = (q : WithTop ℕ) :=
  castCount_sInf_eq_of_isLeast _ q h

/-- **A least uniform bound is the symmetric Hadwiger covering number.** If $q$ is the least
natural number such that every centrally symmetric convex body $K$ in the Euclidean space
$\mathbb{R}^n$ is covered by $q$ translates of its interior, then the symmetric Hadwiger
covering number of dimension $n$ equals $q$. -/
theorem symmetricHadwigerCoveringNumber_eq_of_isLeast {n q : ℕ}
    (h : IsLeast {r : ℕ | UniformSymmetricInteriorTranslateBound n r} q) :
    symmetricHadwigerCoveringNumber n = (q : WithTop ℕ) :=
  castCount_sInf_eq_of_isLeast _ q h

end ConvexCovering
