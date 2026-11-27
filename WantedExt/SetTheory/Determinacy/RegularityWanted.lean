/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.SetTheory.Determinacy.BaireProperty
public import MathlibExt.SetTheory.Determinacy.PerfectSet
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Regularity of sets of reals from determinacy (wanted)

Determinacy of a class of sets of reals makes its members regular: they have the perfect set
property (Davis), the property of Baire (Banach–Mazur, Oxtoby) and are measurable for every
σ-finite Borel measure (Mycielski–Świerczkowski). Davis's theorem is proved in
`MathlibExt.SetTheory.Determinacy.PerfectSet` and the property of Baire in
`MathlibExt.SetTheory.Determinacy.BaireProperty`. We record the remaining result, measurability,
for a family `Γ` of subsets of Baire space `ℕ^ℕ` that is closed under preimages by Borel maps
`ℕ^ℕ → ℕ^ℕ` and all of whose members are determined.

**Exact hypotheses.** Moschovakis (*Descriptive Set Theory*, 2nd ed., AMS 2009, 6A.12, 6A.16 and
6A.18) states these results for an adequate pointclass `Λ` closed under Borel (`Δ¹₁`)
substitution. Specialised to subsets of `ℕ^ℕ`, his proofs apply the determinacy hypothesis to
the payoff sets of the `*`-game, of the Banach–Mazur game and of Harrington's covering game (after
transfer along a Borel isomorphism with `2^ℕ` where needed). Each of these is, or by the
complement-and-shift argument of 6A.4 reduces to, the preimage of the given set by a Borel map
`ℕ^ℕ → ℕ^ℕ` that sends the plays lost by rule-breaking to a fixed point inside or outside the set
(the cases of the empty set and of the whole space being trivial). Closure under such preimages
is therefore the hypothesis used here.

**Metatheory.** For `Γ` the family of all subsets of `ℕ^ℕ` the determinacy hypothesis is the
axiom of determinacy, which is false in Lean's ambient logic
(`MathlibExt.SetTheory.Determinacy.not_forall_determined`); the classical corollary "under AD every
set of reals is Lebesgue measurable, has the Baire property and the perfect set property" holds
in ZF + AD and cannot be stated non-vacuously here.

**Instances.** A family satisfying the closure hypothesis that contains a set `S` other than `∅`
and `ℕ^ℕ` contains every Borel set `B`: it is the preimage of `S` by the Borel map sending `B` to a
point of `S` and its complement to a point outside `S`. So every non-trivial instance of the
determinacy hypothesis includes Martin's Borel determinacy, which is a wanted theorem here
(`determined_of_measurableSet_borel`). The only instances provable in this repository today are
the trivial families `∅`, `{∅}`, `{ℕ^ℕ}` and `{∅, ℕ^ℕ}`, whose conclusions are trivial. The
intended instances, each resting on wanted theorems or further hypotheses, are the Borel sets
(Martin's theorem; their regularity is anyway a theorem of ZFC), the analytic and co-analytic sets
under a measurable cardinal (Moschovakis 6G.7 with 6A.4), and the projective sets under projective
determinacy.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.SetTheory.DeterminacyWanted

open MathlibExt.SetTheory.Determinacy

/-- **Measurability from determinacy.** Let `Γ` be a family of subsets of Baire space `ℕ^ℕ`,
closed under preimages by Borel maps `ℕ^ℕ → ℕ^ℕ`, all of whose members are determined. Then every
member of `Γ` is `μ`-measurable for every σ-finite Borel measure `μ` on `ℕ^ℕ`
(J. Mycielski and S. Świerczkowski, *On the Lebesgue measurability and the axiom of
determinateness*, Fund. Math. 54 (1964) 67–71; Moschovakis, *Descriptive Set Theory*, 2nd ed.,
AMS 2009, 6A.17–6A.18, with Harrington's covering game). -/
theorem_wanted nullMeasurableSet_of_determined {Γ : Set (Set (ℕ → ℕ))}
    (hΓ : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ)
    (hdet : ∀ B ∈ Γ, Determined B) {S : Set (ℕ → ℕ)} (hS : S ∈ Γ)
    (μ : Measure (ℕ → ℕ)) [SigmaFinite μ] : NullMeasurableSet S μ

end MathlibExt.SetTheory.DeterminacyWanted
