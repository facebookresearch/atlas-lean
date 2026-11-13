/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Menger set of reals that is not Hurewicz (Tsaban, Milestone Problem 5.1)

B. Tsaban, Selection principles in mathematics: A milestone of open problems, Problem 5.1
(Hurewicz's problem; Just, Miller, Scheepers and Szeptycki, Problem 3; Bukovský and Haleš, Problem
1): does there exist (in ZFC) a set of reals `X` which has the Menger property `U_fin(O, O)` but not
the Hurewicz property `U_fin(O, Γ)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.MengerNotHurewiczSetOfRealsAMR134Problem0002Wanted

/-!
Source: B. Tsaban, Selection principles in mathematics: A milestone of open problems, Note di
Matematica 22 (2003/2004), arXiv:math/0312182, Problem 5.1. UnsolvedMath record UM-00800630
(`AMR-134-0002`), dataset ulamai/UnsolvedMath v1.8.0.

Sets of reals are subsets of `ℝ` with the subspace topology. An open cover of `X` is taken as a
family of open subsets of `ℝ` whose union contains `X`; every relatively open cover of `X` is the
trace of such a family. The Menger and Hurewicz properties are stated in Hurewicz's classical form,
as in Machura, Shelah and Tsaban, Trans. Amer. Math. Soc. 362 (2010), Definition 2, and Tsaban and
Zdomskyy's Section 2; for sets of reals they are the source's `U_fin(O, O)` and `U_fin(O, Γ)`.
-/

open Filter

/-- The Menger property `U_fin(O, O)` of a set of reals `X`, in Hurewicz's form: for every
sequence `(𝒰ₙ)` of families of open subsets of `ℝ` covering `X` there are finite `𝓕ₙ ⊆ 𝒰ₙ` such
that `⋃ₙ ⋃ 𝓕ₙ` covers `X`. -/
def IsMenger (X : Set ℝ) : Prop :=
  ∀ 𝒰 : ℕ → Set (Set ℝ), (∀ n, (∀ U ∈ 𝒰 n, IsOpen U) ∧ X ⊆ ⋃₀ 𝒰 n) →
    ∃ 𝓕 : ℕ → Finset (Set ℝ), (∀ n, (𝓕 n : Set (Set ℝ)) ⊆ 𝒰 n) ∧
      X ⊆ ⋃ n, ⋃₀ (𝓕 n : Set (Set ℝ))

/-- The Hurewicz property `U_fin(O, Γ)` of a set of reals `X`: for every sequence `(𝒰ₙ)` of
families of open subsets of `ℝ` covering `X` there are finite `𝓕ₙ ⊆ 𝒰ₙ` such that every point of
`X` lies in `⋃ 𝓕ₙ` for all but finitely many `n`. -/
def IsHurewicz (X : Set ℝ) : Prop :=
  ∀ 𝒰 : ℕ → Set (Set ℝ), (∀ n, (∀ U ∈ 𝒰 n, IsOpen U) ∧ X ⊆ ⋃₀ 𝒰 n) →
    ∃ 𝓕 : ℕ → Finset (Set ℝ), (∀ n, (𝓕 n : Set (Set ℝ)) ⊆ 𝒰 n) ∧
      ∀ x ∈ X, ∀ᶠ n in atTop, x ∈ ⋃₀ (𝓕 n : Set (Set ℝ))

/-- Tsaban, Milestone Problem 5.1 (Hurewicz's problem): there is a set of reals with the Menger
property but without the Hurewicz property. -/
def existsMengerNotHurewicz : Prop :=
  ∃ X : Set ℝ, IsMenger X ∧ ¬ IsHurewicz X

/--
Resolved true: in ZFC there is a set of reals with the Menger property and without the Hurewicz
property. Chaber and Pol proved it on a dichotomic basis, Tsaban and Zdomskyy constructed a concrete
example, and the problem list's Notes added in proof record the answer 'Yes'. Source: B. Tsaban,
Selection principles in mathematics: A milestone of open problems, Note di Matematica 22
(2003/2004), arXiv:math/0312182, Problem 5.1; resolution: B. Tsaban and L. Zdomskyy, Scales, fields,
and a problem of Hurewicz, J. Eur. Math. Soc. 10 (2008), 837-866, arXiv:math/0507043, Abstract and
Section 1: a theorem of Chaber and Pol gives, in ZFC, a set of reals without the Hurewicz property
all of whose finite powers have the Menger property, and Section 3 constructs a concrete set of
reals with Menger's but not Hurewicz's property; the problem list's Notes added in proof record the
answer 'Yes' for Problem 5.1, https://arxiv.org/abs/math/0507043.
-/
public theorem_wanted existsMengerNotHurewicz_holds : existsMengerNotHurewicz

end MathlibExt.Topology.MengerNotHurewiczSetOfRealsAMR134Problem0002Wanted
