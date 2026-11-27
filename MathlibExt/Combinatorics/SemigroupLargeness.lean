/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hindman
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.List.OfFn

/-!
# Large sets in semigroups

Notions of largeness for subsets of an arbitrary (not necessarily commutative) semigroup `S`:
piecewise syndetic sets, `J`-sets, central sets and `C`-sets, with their basic characteristic
lemmas. Ultrafilters on `S` are multiplied with Mathlib's `Ultrafilter.semigroup`, for which
`D ∈ p * q` iff `{x | {y | x * y ∈ D} ∈ q} ∈ p`. The `J`-set condition quantifies over nonempty
finite families of sequences, so over an empty semigroup every set is a `J`-set; the lemmas
about `J`-sets therefore assume `[Nonempty S]`.

The definitions follow Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary
Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (after Hindman and Strauss).
-/

namespace MetaMathlibExt

@[expose] public section

attribute [local instance] Ultrafilter.semigroup

section LargeSets

variable {S : Type*} [Semigroup S]

/-- **Piecewise syndetic subsets of a semigroup.** A set $D$ in a semigroup $S$ is piecewise
syndetic when there is a finite set $G \subseteq S$ such that for every finite set
$F \subseteq S$ there is $x \in S$ with $Fx \subseteq \bigcup_{t \in G} t^{-1} D$, where
$Fx = \{fx : f \in F\}$ and $t^{-1} D = \{s \in S : ts \in D\}$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (piecewise syndetic sets, after
Hindman--Strauss). -/
def IsMulPiecewiseSyndetic (D : Set S) : Prop :=
  ∃ G : Finset S, ∀ F : Finset S, ∃ x : S, ∀ f ∈ F, ∃ t ∈ G, t * (f * x) ∈ D

/-- **J-sets in a semigroup.** A set $D$ in a semigroup $S$ is a $J$-set when for every nonempty
finite set $F$ of sequences $f : \mathbb{N} \to S$, where $\mathbb{N} = \{0, 1, 2, \dots\}$,
there are an integer $m \ge 1$, elements $a_1, \dots, a_{m+1} \in S$ and indices
$t_1 < \dots < t_m$ in $\mathbb{N}$ such that
$a_1 f(t_1) a_2 f(t_2) \cdots a_m f(t_m) a_{m+1} \in D$ for every $f \in F$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3). -/
def IsMulJSet (D : Set S) : Prop :=
  ∀ F : Finset (ℕ → S), F.Nonempty → ∃ (m : ℕ) (a : Fin (m + 2) → S) (t : Fin (m + 1) → ℕ),
    StrictMono t ∧ ∀ f ∈ F,
      (List.ofFn fun j : Fin m => a j.succ.castSucc * f (t j.succ)).foldl (· * ·)
          (a 0 * f (t 0)) * a (Fin.last (m + 1)) ∈ D

/-- **Central sets in a semigroup.** Let $S$ be a semigroup and let $\beta S$ be the set of
ultrafilters on $S$, with the product for which $D \in pq$ exactly when
$\{x \in S : \{y \in S : xy \in D\} \in q\} \in p$. A two-sided ideal of $\beta S$ is a set
$I \subseteq \beta S$ with $rq \in I$ and $qr \in I$ for all $q \in I$ and $r \in \beta S$. A set
$D \subseteq S$ is central when some $p \in \beta S$ with $pp = p$ lies in every nonempty
two-sided ideal of $\beta S$ and has $D \in p$.

Equivalently, $D \in p$ for a minimal idempotent $p$, that is, an idempotent of the smallest
two-sided ideal $K(\beta S)$, which is itself a nonempty two-sided ideal lying in all of them.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2.1 (central sets). -/
def IsCentralSet (D : Set S) : Prop :=
  ∃ p : Ultrafilter S, p * p = p ∧
    (∀ I : Set (Ultrafilter S), I.Nonempty → (∀ q ∈ I, ∀ r, r * q ∈ I ∧ q * r ∈ I) → p ∈ I) ∧
    D ∈ p

/-- **C-sets in a semigroup.** Let $S$ be a semigroup and let $\beta S$ be the set of ultrafilters
on $S$, with the product for which $D \in pq$ exactly when
$\{x \in S : \{y \in S : xy \in D\} \in q\} \in p$. Let $J(S)$ be the set of ultrafilters on $S$
all of whose members are $J$-sets. A set $D \subseteq S$ is a $C$-set when $D \in p$ for some
$p \in J(S)$ with $pp = p$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3) (C-sets). -/
def IsCSet (D : Set S) : Prop :=
  ∃ p : Ultrafilter S, p * p = p ∧ (∀ B ∈ p, IsMulJSet B) ∧ D ∈ p

/-- **A nonempty semigroup is piecewise syndetic in itself.** If $S$ is a nonempty semigroup,
then $S$ is a piecewise syndetic subset of $S$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (piecewise syndetic sets). -/
theorem isMulPiecewiseSyndetic_univ [Nonempty S] : IsMulPiecewiseSyndetic (Set.univ : Set S) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  exact ⟨{s}, fun _ => ⟨s, fun _ _ => ⟨s, Finset.mem_singleton_self s, Set.mem_univ _⟩⟩⟩

/-- **The empty set is not piecewise syndetic in a semigroup.** In every semigroup $S$, the empty
subset of $S$ is not piecewise syndetic.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (piecewise syndetic sets). -/
theorem not_isMulPiecewiseSyndetic_empty : ¬ IsMulPiecewiseSyndetic (∅ : Set S) := by
  rintro ⟨G, hG⟩
  obtain ⟨x, -⟩ := hG ∅
  obtain ⟨y, hy⟩ := hG {x}
  obtain ⟨t, -, ht⟩ := hy x (Finset.mem_singleton_self x)
  exact ht

/-- **A nonempty semigroup is a J-set in itself.** If $S$ is a nonempty semigroup, then $S$ is a
$J$-set in $S$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3). -/
theorem isMulJSet_univ [Nonempty S] : IsMulJSet (Set.univ : Set S) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  refine fun _ _ => ⟨0, fun _ => s, fun _ => 0, fun i j hij => ?_, fun _ _ => Set.mem_univ _⟩
  have := i.isLt
  have := j.isLt
  simp only [Fin.lt_def] at hij
  omega

/-- **The empty set is not a J-set in a nonempty semigroup.** If $S$ is a nonempty semigroup, then
the empty subset of $S$ is not a $J$-set.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3). -/
theorem not_isMulJSet_empty [Nonempty S] : ¬ IsMulJSet (∅ : Set S) := by
  intro h
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨_, _, _, _, hf⟩ := h {fun _ => s} (Finset.singleton_nonempty _)
  exact hf _ (Finset.mem_singleton_self _)

/-- **The empty set is not central in a semigroup.** In every semigroup $S$, the empty subset of
$S$ is not central.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2.1 (central sets). -/
theorem not_isCentralSet_empty : ¬ IsCentralSet (∅ : Set S) := by
  rintro ⟨p, -, -, hp⟩
  exact p.empty_notMem hp

/-- **The empty set is not a C-set in a semigroup.** In every semigroup $S$, the empty subset of
$S$ is not a $C$-set.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3) (C-sets). -/
theorem not_isCSet_empty : ¬ IsCSet (∅ : Set S) := by
  rintro ⟨p, -, -, hp⟩
  exact p.empty_notMem hp

end LargeSets

end

end MetaMathlibExt
