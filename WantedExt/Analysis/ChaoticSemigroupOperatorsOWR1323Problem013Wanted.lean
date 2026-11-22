/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chaotic operators in chaotic C0-semigroups (Oberwolfach Reports 37/2006)

Mini-Workshop: Hypercyclicity and Linear Chaos (2006), open problem 5 (A. Peris and J. A. Conejero):
let `T = {T_t}_{t ≥ 0}` be a `C₀`-semigroup on a separable complex Banach space that is chaotic in
the sense of Devaney (hypercyclic, with a dense set of periodic points `{x | ∃ t > 0, T_t x = x}`).
Is every single operator `T_t` (`t > 0`) chaotic? Does there exist at least one `t₀ > 0` such that
`T_{t₀}` is chaotic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Analysis.ChaoticSemigroupOperatorsOWR1323Problem013Wanted

/-!
Source: A. Peris and J. A. Conejero, Chaotic operators in C0-semigroups, open problem 5, in
Mini-Workshop: Hypercyclicity and Linear Chaos, Oberwolfach Reports 3 (2006), Report 37/2006, p.
2272, DOI 10.4171/OWR/2006/37. UnsolvedMath record UM-30000576 (`OWR-1323-013`), dataset
ulamai/UnsolvedMath v1.8.0.

A `C₀`-semigroup is a family `T : ℝ≥0 → (X →L[ℂ] X)` with `T 0 = id`, `T (s + t) = T s ∘ T t` and `t
↦ T t x` continuous (the report's `lim_{t → s} T_t x = T_s x`). Chaos follows the report:
hypercyclic plus dense periodic points, for the semigroup with periods `t > 0` and for an operator
`S` with periods `n ≥ 1` (Devaney chaos of a linear operator). Banach spaces range over `Type`,
which contains the counterexample.
-/

/-- A `C₀`-semigroup of bounded operators on `X`: `T 0 = id`, `T (s + t) = T s ∘ T t`, and
`t ↦ T t x` is continuous on `[0, ∞)` for every `x`. -/
structure IsCZeroSemigroup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : NNReal → X →L[ℂ] X) : Prop where
  map_zero : T 0 = ContinuousLinearMap.id ℂ X
  map_add : ∀ s t, T (s + t) = (T s).comp (T t)
  continuous_apply : ∀ x, Continuous fun t => T t x

/-- A `C₀`-semigroup is chaotic (in the sense of Devaney) if it is hypercyclic (some orbit
`{T t x | t ≥ 0}` is dense) and its set of periodic points `{x | ∃ t > 0, T t x = x}` is dense. -/
def IsChaoticSemigroup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : NNReal → X →L[ℂ] X) : Prop :=
  (∃ x, Dense (Set.range fun t => T t x)) ∧ Dense {x | ∃ t > 0, T t x = x}

/-- An operator is chaotic (in the sense of Devaney) if it is hypercyclic (some orbit
`{Sⁿ x | n ∈ ℕ}` is dense) and its set of periodic points `{x | ∃ n ≥ 1, Sⁿ x = x}` is dense. -/
def IsChaoticOperator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (S : X →L[ℂ] X) :
    Prop :=
  (∃ x, Dense (Set.range fun n : ℕ => (S ^ n) x)) ∧ Dense {x | ∃ n ≥ 1, (S ^ n) x = x}

/-- Question 1 (Peris-Conejero): in a chaotic `C₀`-semigroup on a separable complex Banach space,
every operator `T t`, `t > 0`, is chaotic. -/
def chaoticSemigroupEveryOperatorChaotic : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (T : NNReal → X →L[ℂ] X),
    IsCZeroSemigroup T → IsChaoticSemigroup T → ∀ t > 0, IsChaoticOperator (T t)

/-- Question 2 (Peris-Conejero): every chaotic `C₀`-semigroup on a separable complex Banach space
contains a chaotic operator `T t₀`, `t₀ > 0`. -/
def chaoticSemigroupSomeOperatorChaotic : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (T : NNReal → X →L[ℂ] X),
    IsCZeroSemigroup T → IsChaoticSemigroup T → ∃ t > 0, IsChaoticOperator (T t)

/--
Resolved false: Bayart and Bermúdez constructed chaotic `C₀`-semigroups that contain no chaotic
operator, and chaotic `C₀`-semigroups with `T_{t₀}` not chaotic and `T_{t₁}` chaotic; either kind
has an operator `T_t`, `t > 0`, that is not chaotic. Source: A. Peris and J. A. Conejero, Chaotic
operators in C0-semigroups, open problem 5, in Mini-Workshop: Hypercyclicity and Linear Chaos,
Oberwolfach Reports 3 (2006), Report 37/2006, p. 2272, DOI 10.4171/OWR/2006/37; resolution: F.
Bayart and T. Bermúdez, Semigroups of chaotic operators, Bull. Lond. Math. Soc. 41 (2009), no. 5,
823-830, DOI 10.1112/blms/bdp055, Zbl 1182.47007; E. M. Mangino and A. Peris, Frequently hypercyclic
semigroups, Studia Math. 202 (2011), no. 3, 227-242, DOI 10.4064/sm202-3-2, Bayart-Bermúdez,
abstract: 'We prove the existence of chaotic semigroups of operators that do not contain any chaotic
operator. In particular, we obtain a chaotic operator T such that λT is not chaotic for some
unimodular complex number λ'; Mangino-Peris, p. 235 (before Proposition 2.6), with chaos defined on
p. 227 as hypercyclicity plus density of {x | ∃ t > 0, T_t x = x} on a separable Banach space: 'by
recent results of Bayart and Bermúdez [4], there are chaotic C0-semigroups (T_t)_{t≥0} such that no
single operator T_t is chaotic, and chaotic C0-semigroups (T_t)_{t≥0} containing non-chaotic
operators T_t0, t0 > 0, and at the same time chaotic T_t1 for some t1 > 0',
https://doi.org/10.1112/blms/bdp055.
-/
public theorem_wanted chaoticSemigroupEveryOperatorChaotic_refuted :
    ¬ chaoticSemigroupEveryOperatorChaotic

/--
Resolved false: Bayart and Bermúdez constructed a chaotic `C₀`-semigroup on a separable complex
Banach space that contains no chaotic operator `T_t`, `t > 0`. Source: A. Peris and J. A. Conejero,
Chaotic operators in C0-semigroups, open problem 5, in Mini-Workshop: Hypercyclicity and Linear
Chaos, Oberwolfach Reports 3 (2006), Report 37/2006, p. 2272, DOI 10.4171/OWR/2006/37; resolution:
F. Bayart and T. Bermúdez, Semigroups of chaotic operators, Bull. Lond. Math. Soc. 41 (2009), no. 5,
823-830, DOI 10.1112/blms/bdp055, Zbl 1182.47007; E. M. Mangino and A. Peris, Frequently hypercyclic
semigroups, Studia Math. 202 (2011), no. 3, 227-242, DOI 10.4064/sm202-3-2, Bayart-Bermúdez,
abstract: 'We prove the existence of chaotic semigroups of operators that do not contain any chaotic
operator. In particular, we obtain a chaotic operator T such that λT is not chaotic for some
unimodular complex number λ'; Mangino-Peris, p. 235 (before Proposition 2.6), with chaos defined on
p. 227 as hypercyclicity plus density of {x | ∃ t > 0, T_t x = x} on a separable Banach space: 'by
recent results of Bayart and Bermúdez [4], there are chaotic C0-semigroups (T_t)_{t≥0} such that no
single operator T_t is chaotic, and chaotic C0-semigroups (T_t)_{t≥0} containing non-chaotic
operators T_t0, t0 > 0, and at the same time chaotic T_t1 for some t1 > 0',
https://doi.org/10.1112/blms/bdp055.
-/
public theorem_wanted chaoticSemigroupSomeOperatorChaotic_refuted :
    ¬ chaoticSemigroupSomeOperatorChaotic

end MathlibExt.Analysis.ChaoticSemigroupOperatorsOWR1323Problem013Wanted
