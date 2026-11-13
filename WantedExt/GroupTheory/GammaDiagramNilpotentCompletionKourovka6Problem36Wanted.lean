/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# γ-diagrams that are not nilpotent-completion diagrams (Kourovka Notebook Problem 6.36)

Kourovka Notebook, Archive of Solved Problems, Problem 6.36 (Yu. I. Merzlyakov; question of J. W.
Grossman): the nilpotent-completion diagram of a group G is G/γ₁G ← G/γ₂G ← ⋯ with the natural
homomorphisms. Every nilpotent-completion diagram G₁ ← G₂ ← ⋯ is a γ-diagram: every sequence 1 → γ_s
G_(s+1) → G_(s+1) → G_s → 1 is exact. Do γ-diagrams exist that are not nilpotent-completion
diagrams?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.GammaDiagramNilpotentCompletionKourovka6Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.36 (Yu. I.
Merzlyakov; question of J. W. Grossman). UnsolvedMath record UM-00700381 (`KOU-6.36`), dataset
ulamai/UnsolvedMath v1.8.0.

Indexing from `0`: `D i = G_(i+1)` and `f i : D (i+1) →* D i`; `γ_(i+1)` is `(⊤ : Subgroup
_).lowerCentralSeries i` (so `γ₁ = ⊤`). Exactness says that `f i` is surjective and that its kernel
is `γ_(i+1)(D (i+1))`. A γ-diagram is a nilpotent-completion diagram when it is isomorphic to that
of some group `H`: isomorphisms `D i ≃* H ⧸ γ_(i+1) H` commuting with the maps, checked on cosets.
-/

/-- Kourovka 6.36 (J. W. Grossman; Yu. I. Merzlyakov): there is a `γ`-diagram
`G₁ ← G₂ ← ⋯` (surjections `G_(s+1) → G_s` with kernel `γ_s G_(s+1)`) that is not isomorphic to the
nilpotent-completion diagram `H/γ₁H ← H/γ₂H ← ⋯` of any group `H`. Indexing: `D i = G_(i+1)` and
`γ_(i+1) = (⊤ : Subgroup _).lowerCentralSeries i`. -/
def existsGammaDiagramNotNilpotentCompletion : Prop :=
  ∃ (D : ℕ → Type) (_ : ∀ i, Group (D i)) (f : ∀ i, D (i + 1) →* D i),
    (∀ i, Function.Surjective (f i)) ∧
    (∀ i, (f i).ker = (⊤ : Subgroup (D (i + 1))).lowerCentralSeries i) ∧
    ¬ ∃ (H : Type) (_ : Group H) (e : ∀ i, D i ≃* H ⧸ (⊤ : Subgroup H).lowerCentralSeries i),
        ∀ (i : ℕ) (x : H), e i (f i ((e (i + 1)).symm (QuotientGroup.mk x))) = QuotientGroup.mk x

/--
Resolved true: the Kourovka Archive answers 6.36 "Yes, such γ-diagrams exist", citing Romanovskii
(1985): some γ-diagram is not isomorphic to the nilpotent-completion diagram of any group. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.36 (Yu. I. Merzlyakov;
question of J. W. Grossman); resolution: N. S. Romanovskii, Example of a γ-diagram of groups which
is not a nilpotent completion diagram, Sibirsk. Mat. Zh. 26, no. 4 (1985), 194-195 (Russian), zbMATH
review Zbl 0603.20023: an example of a γ-diagram that is not a nilpotent-completion diagram,
answering Grossman's question; Kourovka Archive, Problem 6.36: Yes, such γ-diagrams exist
(Romanovskii), https://zbmath.org/?q=an:0603.20023.
-/
public theorem_wanted existsGammaDiagramNotNilpotentCompletion_holds :
    existsGammaDiagramNotNilpotentCompletion

end MathlibExt.GroupTheory.GammaDiagramNilpotentCompletionKourovka6Problem36Wanted
