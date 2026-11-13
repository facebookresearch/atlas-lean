/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugacy separability of five classes of groups (Kourovka Notebook Problem 2.16)

Kourovka Notebook, Archive of Solved Problems, Problem 2.16 (M. I. Kargapolov): a group `G` is
conjugacy separable if any two of its elements are conjugate in `G` if and only if their images are
conjugate in every finite homomorphic image of `G`. Is `G` conjugacy separable when (a) `G` is
polycyclic, (b) `G` is a free soluble group, (c) `G` is a group of (all) integral matrices, (d) `G`
is a finitely generated group of matrices, (e) `G` is a finitely generated metabelian group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import WantedExt.GroupTheory.FreeSolubleNormalClosureConjugacyKourovka1Problem89Wanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.ConjugacySeparableClassesKourovka2Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.16 (M. I.
Kargapolov). UnsolvedMath record UM-00700092 (`KOU-2.16`), dataset ulamai/UnsolvedMath v1.8.0.

Conjugacy separable: elements whose images are conjugate in every finite quotient `G / N` (`N`
normal of finite index, written as `g x g⁻¹ y⁻¹ ∈ N` for some `g`) are conjugate in `G`. Polycyclic:
a series `1 = G₀ ⊴ ⋯ ⊴ G_n = G` with cyclic factors, written with generators `g₀, …, g_{n-1}` whose
initial segments generate the terms. (b) is stated for free soluble groups `F_r / F_r^{(l)}` of
finite rank `r` and every derived length `l`. (c) is `GLₙ(ℤ)` for every `n`; (d) finitely generated
subgroups of `GLₙ(K)` over a field `K : Type`; (e) finitely generated groups with `derivedSeries G 2
= ⊥`. `IsConjugacySeparable` is the shared definition in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`; `FreeSolubleGroup` is that of the Kourovka 1.89
entry, reused here.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared
open MathlibExt.GroupTheory.FreeSolubleNormalClosureConjugacyKourovka1Problem89Wanted
  (FreeSolubleGroup)

/-- `G` is polycyclic: for some elements `g₀, …, g_{n-1}` of `G`, each `Gᵢ = ⟨g_j : j < i⟩` is
normal in `Gᵢ₊₁` (`i < n`) and `G_n = G`, so `1 = G₀ ⊴ G₁ ⊴ ⋯ ⊴ G_n = G` is a series with cyclic
factors `Gᵢ₊₁ / Gᵢ = ⟨Gᵢ, gᵢ⟩ / Gᵢ`. -/
def IsPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), (∀ i : ℕ, i < n →
      ((Subgroup.closure (g '' {j | j.val < i})).subgroupOf
        (Subgroup.closure (g '' {j | j.val < i + 1}))).Normal) ∧
    Subgroup.closure (Set.range g) = ⊤

/-- Kourovka 2.16(a) (M. I. Kargapolov): every polycyclic group is conjugacy separable. -/
def polycyclicConjugacySeparable : Prop :=
  ∀ (G : Type) [Group G], IsPolycyclic G → IsConjugacySeparable G

/-- Kourovka 2.16(b) (M. I. Kargapolov): every free soluble group (of finite rank `r` and derived
length `l`) is conjugacy separable. -/
def freeSolubleConjugacySeparable : Prop :=
  ∀ r l : ℕ, IsConjugacySeparable (FreeSolubleGroup r l)

/-- Kourovka 2.16(c) (M. I. Kargapolov): the group `GLₙ(ℤ)` of all integral matrices is conjugacy
separable for every `n`. -/
def integralMatrixGroupConjugacySeparable : Prop :=
  ∀ n : ℕ, IsConjugacySeparable (GL (Fin n) ℤ)

/-- Kourovka 2.16(d) (M. I. Kargapolov): every finitely generated group of matrices over a field is
conjugacy separable. -/
def finitelyGeneratedLinearConjugacySeparable : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (G : Subgroup (GL (Fin n) K)), G.FG → IsConjugacySeparable G

/-- Kourovka 2.16(e) (M. I. Kargapolov): every finitely generated metabelian group is conjugacy
separable. -/
def finitelyGeneratedMetabelianConjugacySeparable : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → derivedSeries G 2 = ⊥ → IsConjugacySeparable G

/--
Resolved true: the Kourovka Archive answers 2.16(a) "Yes" (Remeslennikov; Formanek): polycyclic
groups are conjugacy separable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 2.16 (M. I. Kargapolov); resolution: (a) V. N. Remeslennikov, Conjugacy in
polycyclic groups, Algebra and Logic 8 (1969), 404-411; E. Formanek, Conjugate separability in
polycyclic groups, J. Algebra 42 (1976), 1-10; (b) V. N. Remeslennikov and V. G. Sokolov, Some
properties of a Magnus embedding, Algebra and Logic 9 (1970), 342-349; (c), (d) V. P. Platonov and
G. V. Matveev, Dokl. Akad. Nauk BSSR 14 (1970), 777-779; V. N. Remeslennikov and V. G. Sokolov,
ibid.; V. N. Remeslennikov, Groups that are residually finite with respect to conjugacy, Siberian
Math. J. 12 (1971), 783-792; (e) M. I. Kargapolov and E. I. Timoshenko, Abstracts of the 4th
All-Union Sympos. Group Theory (1973), 86-88, Kourovka Archive, Problem 2.16: (a) Yes; (b) Yes; (c),
(d) Not always; (e) Not always, with an explicit semidirect product of ℤ[1/p]² by ℤ²,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted polycyclicConjugacySeparable_holds : polycyclicConjugacySeparable

/--
Resolved true: the Kourovka Archive answers 2.16(b) "Yes" (Remeslennikov and Sokolov): free soluble
groups are conjugacy separable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 2.16 (M. I. Kargapolov); resolution: (a) V. N. Remeslennikov, Conjugacy in
polycyclic groups, Algebra and Logic 8 (1969), 404-411; E. Formanek, Conjugate separability in
polycyclic groups, J. Algebra 42 (1976), 1-10; (b) V. N. Remeslennikov and V. G. Sokolov, Some
properties of a Magnus embedding, Algebra and Logic 9 (1970), 342-349; (c), (d) V. P. Platonov and
G. V. Matveev, Dokl. Akad. Nauk BSSR 14 (1970), 777-779; V. N. Remeslennikov and V. G. Sokolov,
ibid.; V. N. Remeslennikov, Groups that are residually finite with respect to conjugacy, Siberian
Math. J. 12 (1971), 783-792; (e) M. I. Kargapolov and E. I. Timoshenko, Abstracts of the 4th
All-Union Sympos. Group Theory (1973), 86-88, Kourovka Archive, Problem 2.16: (a) Yes; (b) Yes; (c),
(d) Not always; (e) Not always, with an explicit semidirect product of ℤ[1/p]² by ℤ²,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted freeSolubleConjugacySeparable_holds : freeSolubleConjugacySeparable

/--
Resolved false: the Kourovka Archive answers 2.16(c) "Not always" (Platonov and Matveev;
Remeslennikov and Sokolov; Remeslennikov): `GLₙ(ℤ)` is not conjugacy separable for some `n`. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.16 (M. I. Kargapolov);
resolution: (a) V. N. Remeslennikov, Conjugacy in polycyclic groups, Algebra and Logic 8 (1969),
404-411; E. Formanek, Conjugate separability in polycyclic groups, J. Algebra 42 (1976), 1-10; (b)
V. N. Remeslennikov and V. G. Sokolov, Some properties of a Magnus embedding, Algebra and Logic 9
(1970), 342-349; (c), (d) V. P. Platonov and G. V. Matveev, Dokl. Akad. Nauk BSSR 14 (1970),
777-779; V. N. Remeslennikov and V. G. Sokolov, ibid.; V. N. Remeslennikov, Groups that are
residually finite with respect to conjugacy, Siberian Math. J. 12 (1971), 783-792; (e) M. I.
Kargapolov and E. I. Timoshenko, Abstracts of the 4th All-Union Sympos. Group Theory (1973), 86-88,
Kourovka Archive, Problem 2.16: (a) Yes; (b) Yes; (c), (d) Not always; (e) Not always, with an
explicit semidirect product of ℤ[1/p]² by ℤ², https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted integralMatrixGroupConjugacySeparable_refuted :
    ¬ integralMatrixGroupConjugacySeparable

/--
Resolved false: the Kourovka Archive answers 2.16(d) "Not always" (Platonov and Matveev;
Remeslennikov and Sokolov; Remeslennikov). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 2.16 (M. I. Kargapolov); resolution: (a) V. N. Remeslennikov, Conjugacy in
polycyclic groups, Algebra and Logic 8 (1969), 404-411; E. Formanek, Conjugate separability in
polycyclic groups, J. Algebra 42 (1976), 1-10; (b) V. N. Remeslennikov and V. G. Sokolov, Some
properties of a Magnus embedding, Algebra and Logic 9 (1970), 342-349; (c), (d) V. P. Platonov and
G. V. Matveev, Dokl. Akad. Nauk BSSR 14 (1970), 777-779; V. N. Remeslennikov and V. G. Sokolov,
ibid.; V. N. Remeslennikov, Groups that are residually finite with respect to conjugacy, Siberian
Math. J. 12 (1971), 783-792; (e) M. I. Kargapolov and E. I. Timoshenko, Abstracts of the 4th
All-Union Sympos. Group Theory (1973), 86-88, Kourovka Archive, Problem 2.16: (a) Yes; (b) Yes; (c),
(d) Not always; (e) Not always, with an explicit semidirect product of ℤ[1/p]² by ℤ²,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finitelyGeneratedLinearConjugacySeparable_refuted :
    ¬ finitelyGeneratedLinearConjugacySeparable

/--
Resolved false: the Kourovka Archive answers 2.16(e) "Not always": for a prime `p`, the semidirect
product of `ℤ[1/p]²` by `ℤ²` given there has two non-conjugate elements whose images are conjugate
in every finite quotient (Kargapolov and Timoshenko). Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 2.16 (M. I. Kargapolov); resolution: (a) V. N.
Remeslennikov, Conjugacy in polycyclic groups, Algebra and Logic 8 (1969), 404-411; E. Formanek,
Conjugate separability in polycyclic groups, J. Algebra 42 (1976), 1-10; (b) V. N. Remeslennikov and
V. G. Sokolov, Some properties of a Magnus embedding, Algebra and Logic 9 (1970), 342-349; (c), (d)
V. P. Platonov and G. V. Matveev, Dokl. Akad. Nauk BSSR 14 (1970), 777-779; V. N. Remeslennikov and
V. G. Sokolov, ibid.; V. N. Remeslennikov, Groups that are residually finite with respect to
conjugacy, Siberian Math. J. 12 (1971), 783-792; (e) M. I. Kargapolov and E. I. Timoshenko,
Abstracts of the 4th All-Union Sympos. Group Theory (1973), 86-88, Kourovka Archive, Problem 2.16:
(a) Yes; (b) Yes; (c), (d) Not always; (e) Not always, with an explicit semidirect product of
ℤ[1/p]² by ℤ², https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finitelyGeneratedMetabelianConjugacySeparable_refuted :
    ¬ finitelyGeneratedMetabelianConjugacySeparable

end MathlibExt.GroupTheory.ConjugacySeparableClassesKourovka2Problem16Wanted
