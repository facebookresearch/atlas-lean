/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Meromorphic functions with deficiency sum two (Hayman–Lingham Problem 1.3)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 1.3: if `f(z)` is
meromorphic of finite order `ρ` and `∑ δ(a, f) = 2`, it is conjectured that `ρ = n/2` with `n` an
integer, `n ≥ 2`, and that all the deficiencies are rational (F. Nevanlinna).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

@[expose] public section

namespace MathlibExt.Analysis.DeficiencySumTwoNevanlinnaAMR22Problem1003Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 1.3 (conjecture of F. Nevanlinna). UnsolvedMath record
UM-02301003 (`AMR-022-1003`), dataset ulamai/UnsolvedMath v1.8.0.

Nevanlinna theory uses Mathlib's `ValueDistribution`: `T(r, f) = characteristic f ⊤ r = m(r, ∞) +
N(r, ∞)` and `m(r, a) = proximity f a r` for `a ∈ ℂ ∪ {∞}` (`WithTop ℂ`). The deficiency is `δ(a, f)
= liminf_{r → ∞} m(r, a)/T(r, f)` and the order `ρ = limsup log T(r, f) / log r` (in `EReal`). `f`
is meromorphic on `ℂ` and not constant (off a codiscrete set), and the deficiency sum over `ℂ ∪ {∞}`
is taken in `ℝ≥0∞`. Both conclusions are stated in one target.
-/

/-- The Nevanlinna characteristic `T(r, f) = m(r, ∞) + N(r, ∞)`. -/
noncomputable def nevanlinnaT (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ValueDistribution.characteristic f ⊤ r

/-- The Nevanlinna deficiency `δ(a, f) = liminf_{r → ∞} m(r, a) / T(r, f)` of `a ∈ ℂ ∪ {∞}`. -/
noncomputable def deficiency (f : ℂ → ℂ) (a : WithTop ℂ) : ℝ :=
  Filter.liminf (fun r : ℝ => ValueDistribution.proximity f a r / nevanlinnaT f r) Filter.atTop

/-- The order `ρ = limsup_{r → ∞} log T(r, f) / log r` of `f`, in `EReal`. -/
noncomputable def order (f : ℂ → ℂ) : EReal :=
  Filter.limsup (fun r : ℝ => ((Real.log (nevanlinnaT f r) / Real.log r : ℝ) : EReal)) Filter.atTop

/-- F. Nevanlinna's conjecture (Hayman–Lingham Problem 1.3): if `f` is a non-constant meromorphic
function of finite order `ρ` with `∑_a δ(a, f) = 2`, then `ρ = n / 2` for an integer `n ≥ 2` and
every deficiency is rational. -/
def deficiencySumTwoConjecture : Prop :=
  ∀ f : ℂ → ℂ, Meromorphic f → (¬ ∃ c : ℂ, ∀ᶠ z in Filter.codiscrete ℂ, f z = c) →
    order f < ⊤ → ∑' a : WithTop ℂ, ENNReal.ofReal (deficiency f a) = 2 →
      (∃ n : ℕ, 2 ≤ n ∧ order f = (n : EReal) / 2) ∧ ∀ a : WithTop ℂ, ∃ q : ℚ, deficiency f a = q

/--
Resolved true: Drasin proved F. Nevanlinna's conjecture: a meromorphic function of finite order `ρ`
with deficiency sum `2` has `2ρ` an integer `≥ 2`, and each of its deficiencies is a positive
integer multiple of `1/ρ` or `0`, hence rational (Hayman–Lingham Update 1.3). Source: W. K. Hayman
and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary Edition (2019),
arXiv:1809.07200, Problem 1.3 (conjecture of F. Nevanlinna); resolution: D. Drasin, Proof of a
conjecture of F. Nevanlinna concerning functions which have deficiency sum two, Acta Math. 158
(1987), 1-94; recorded in Hayman–Lingham, Update 1.3, Section 1.1, THEOREM: "F. Nevanlinna's
conjecture is correct": if f is meromorphic in the plane of finite order λ = limsup log T(r)/log r
and ∑ δ(a) = 2, then 2λ is an integer ≥ 2 (1.4) and every deficient value has δ(a) = λ⁻¹ p(a) with
p(a) a positive integer (1.5); Hayman–Lingham Update 1.3: "The conjecture was completely proved by
Drasin", https://doi.org/10.1007/BF02392256.
-/
public theorem_wanted deficiencySumTwoConjecture_holds : deficiencySumTwoConjecture

end MathlibExt.Analysis.DeficiencySumTwoNevanlinnaAMR22Problem1003Wanted
