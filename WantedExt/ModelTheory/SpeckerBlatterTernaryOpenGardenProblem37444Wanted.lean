/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Specker-Blatter theorem fails for a ternary relation (Open Problem Garden 37444)

Open Problem Garden, Blatter-Specker Theorem for ternary relations (J. A. Makowsky): for a class `C`
of finite relational structures let `f_C(n)` be the number of structures in `C` on the labelled set
`{0, …, n - 1}`. Specker and Blatter showed that for every class definable in monadic second-order
logic with unary and binary relation symbols and every `m`, `f_C(n)` is ultimately periodic modulo
`m`. Does the Blatter-Specker theorem hold for ternary relations?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Semantics
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.ModelTheory.SpeckerBlatterTernaryOpenGardenProblem37444Wanted

/-!
Source: Open Problem Garden, Blatter-Specker Theorem for ternary relations (node 37444; J. A.
Makowsky), http://www.openproblemgarden.org/op/blatter_specker_theorem_for_ternary_relations.
UnsolvedMath record UM-00003340 (`OPG-37444`), dataset ulamai/UnsolvedMath v1.8.0.

The ternary version is stated for classes defined by first-order sentences in the vocabulary of one
ternary relation symbol (Mathlib `FirstOrder.Language`, with equality). First-order definable
classes are monadic second-order definable, so the failure stated here is the failure of the theorem
for ternary relations in the strongest form, the one Fischer and Makowsky prove. `f_φ(n)` counts
relations `A ⊆ [n]³` with `([n], A) ⊨ φ` (labelled structures); ultimately periodic modulo `m` means
`f(n + p) ≡ f(n) (mod m)` for some `p ≥ 1` and all large `n`, which is equivalent to Fischer and
Makowsky's "satisfies a linear recurrence modulo `m`".
-/

open FirstOrder FirstOrder.Language

/-- The relation symbols of the vocabulary with one ternary relation symbol `R`. -/
inductive TernaryRel : ℕ → Type
  | R : TernaryRel 3

/-- The first-order language with a single ternary relation symbol and no function symbols. -/
def ternaryLanguage : Language := ⟨fun _ => Empty, TernaryRel⟩

/-- The structure on `Fin n` interpreting the ternary symbol as the relation `A ⊆ [n]³`. -/
abbrev ternaryStructure {n : ℕ} (A : Set (Fin n × Fin n × Fin n)) :
    ternaryLanguage.Structure (Fin n) where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun {_} r xs => match r with
    | .R => (xs 0, xs 1, xs 2) ∈ A

/-- `f_φ(n)`: the number of relations `A ⊆ [n]³` such that `([n], A)` satisfies the sentence `φ`,
i.e. the number of labelled structures on `{0, …, n - 1}` in the class defined by `φ`. -/
noncomputable def specCount (φ : ternaryLanguage.Sentence) (n : ℕ) : ℕ :=
  Nat.card {A : Set (Fin n × Fin n × Fin n) //
    @Sentence.Realize ternaryLanguage (Fin n) (ternaryStructure A) φ}

/-- The sequence `s` is ultimately periodic modulo `m`. -/
def UltimatelyPeriodicMod (s : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ n, N ≤ n → s (n + p) % m = s n % m

/-- The Specker-Blatter theorem for one ternary relation, restricted to first-order definable
classes: for every first-order sentence `φ` in the language of one ternary relation and every
`m ≥ 1`, the counting function `f_φ` is ultimately periodic modulo `m`. -/
def speckerBlatterTernary : Prop :=
  ∀ (φ : ternaryLanguage.Sentence) (m : ℕ), 0 < m → UltimatelyPeriodicMod (specCount φ) m

/--
Resolved false: Fischer and Makowsky constructed a first-order sentence `φ` with a single ternary
relation symbol whose counting function `f_φ(n)` is not ultimately periodic modulo some `m`, so the
Specker-Blatter theorem fails for ternary relations, already for first-order definable classes.
Source: Open Problem Garden, Blatter-Specker Theorem for ternary relations (node 37444; J. A.
Makowsky), http://www.openproblemgarden.org/op/blatter_specker_theorem_for_ternary_relations;
resolution: E. Fischer and J. A. Makowsky, Extensions and limits of the Specker-Blatter theorem, J.
Symb. Log. 89 (2024), 1284-1312, doi:10.1017/jsl.2024.17; arXiv:2206.12135, Theorem 6.3 (Ternary
Counter-Example): there is an FOL-sentence φ with only one ternary relation symbol such that Sp_φ(n)
is not an MC-sequence (MC-finite: satisfies a linear recurrence modulo m for each m); Section 12,
Theorem 12.10: such a sentence whose counting function is not ultimately periodic modulo 2;
abstract: 'The Specker-Blatter Theorem does not hold already for C with one ternary relation
definable in First Order Logic FOL. This was left open since 1983',
https://doi.org/10.1017/jsl.2024.17.
-/
public theorem_wanted speckerBlatterTernary_refuted : ¬ speckerBlatterTernary

end MathlibExt.ModelTheory.SpeckerBlatterTernaryOpenGardenProblem37444Wanted
