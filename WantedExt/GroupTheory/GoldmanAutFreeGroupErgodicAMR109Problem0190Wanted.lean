/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ergodicity of Aut(F_n) on Hom(F_n, G) for compact Lie groups (Goldman's conjecture)

B. Farb (ed.), Problems on Mapping Class Groups and Related Topics, Ch. 13 (W. Goldman), Conjecture
2.3: for `π` a free group of rank `r ≥ 3` and `G` a compact connected Lie group, the action of
`Out(π)` on `Hom(π, G)/G` is ergodic (proved there when every simple factor of `G` is locally
isomorphic to `SU(2)`).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

namespace MathlibExt.GroupTheory.GoldmanAutFreeGroupErgodicAMR109Problem0190Wanted

/-!
Source: B. Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 13 (W.
Goldman), Conjecture 2.3. UnsolvedMath record UM-11000190 (`AMR-109-0190`), dataset
ulamai/UnsolvedMath v1.8.0.

Stated, as Gelander does, for `Aut(F_n)` acting on `Hom(F_n, G) = Gⁿ` with Haar measure; Gelander
notes (after Goldman's Lemma 3.1) that this is equivalent to ergodicity of `Out(F_n)` on `Hom(F_n,
G)/G`. `φ` acts by precomposition, `(gᵢ) ↦ (ρ_g(φ(eᵢ)))ᵢ` with `ρ_g` the homomorphism sending the
basis element `eᵢ` to `gᵢ`. Ergodic: every measurable invariant set is null or conull (for the
countable group `Aut(F_n)`, almost invariant sets can be replaced by invariant ones, as in
Gelander's proof). A compact connected Lie group is a `C^∞` Lie group modelled on a
finite-dimensional real normed space, compact and connected, with any Haar measure `μ`; `Gⁿ` carries
the product measure.
-/

open scoped ContDiff Manifold

/-- The action of `φ ∈ Aut(F_n)` on `Hom(F_n, G) = Gⁿ` by precomposition: the homomorphism sending
the basis element `eᵢ` to `gᵢ` is sent to the one sending `eᵢ` to its value at `φ(eᵢ)`. -/
def autAction {n : ℕ} {G : Type*} [Group G] (φ : MulAut (FreeGroup (Fin n))) (g : Fin n → G) :
    Fin n → G :=
  fun i => FreeGroup.lift g (φ (FreeGroup.of i))

/-- Goldman's conjecture (Farb (ed.), Problems on Mapping Class Groups, Ch. 13, Conjecture 2.3),
in the form proved by Gelander: for `n ≥ 3` and every compact connected Lie group `G`, the action
of `Aut(F_n)` on `Hom(F_n, G) = Gⁿ` is ergodic for Haar measure: an invariant measurable set is
null or conull. -/
def goldmanErgodicity : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [CompactSpace G] [ConnectedSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (A : Set (Fin n → G)), MeasurableSet A →
    (∀ φ : MulAut (FreeGroup (Fin n)), autAction φ ⁻¹' A = A) →
    MeasureTheory.Measure.pi (fun _ => μ) A = 0 ∨ MeasureTheory.Measure.pi (fun _ => μ) Aᶜ = 0

/--
Resolved true: Gelander proved Goldman's conjecture: for `n ≥ 3` and every compact connected Lie
group `G`, `Aut(F_n)` acts ergodically on `Hom(F_n, G) = Gⁿ` with Haar measure (Theorems 1.6–1.7 for
semisimple `G`, and the general case by Goldman's reduction, as Gelander states). Source: B. Farb
(ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 13 (W. Goldman), Conjecture
2.3; resolution: T. Gelander, On deformations of F_n in compact Lie groups, Israel J. Math. 167
(2008), arXiv:math/0611830, Theorems 1.6 and 1.7: for n ≥ 3 and G compact connected semisimple,
Aut(F_n) acts ergodically on Gⁿ and Out(F_n) on Hom(F_n, G)/G ("conjectured by W.M. Goldman"); the
paragraph after Theorem 1.7: "the general case follows from the semisimple one, i.e. one can omit
the assumption that the connected compact Lie group G is semisimple",
https://arxiv.org/abs/math/0611830.
-/
public theorem_wanted goldmanErgodicity_holds : goldmanErgodicity

end MathlibExt.GroupTheory.GoldmanAutFreeGroupErgodicAMR109Problem0190Wanted
