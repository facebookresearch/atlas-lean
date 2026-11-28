/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Bishop–Cannings theorem and Haigh's condition for matrix-game ESSs

For a finite symmetric matrix game with payoff matrix `A` and mixed strategies `p` in the
simplex, payoff `E(p, q) = pᵀ A q`, a strategy `p` is an evolutionarily stable strategy (ESS) if
for every mixed `q ≠ p` either `qᵀ A p < pᵀ A p`, or `qᵀ A p = pᵀ A p` and `qᵀ A q < pᵀ A q`.
(a) Equal payoffs on the support (Haigh 1974; Bishop and Cannings): if `p` is an ESS, then every
pure strategy `i` in the support of `p` earns `(A p)ᵢ = pᵀ A p`, and no pure strategy earns more.
(b) Support property (Bishop and Cannings): if `p` is an ESS and `q ≠ p` is a mixed strategy with
support contained in the support of `p`, then `q` is not an ESS; so the supports of the ESSs form
a Sperner family. (c) Haigh's condition: if `p` is an ESS then `xᵀ A x < 0` for every `x ≠ 0`
with `∑ xᵢ = 0` and support in the support of `p`; conversely a regular Nash equilibrium (equal
payoffs on the support, strictly lower payoffs off it) satisfying this condition is an ESS
(Taylor and Jonker 1978).

Recorded here: (b), Haigh's necessary condition and the regular-ESS converse. Part (a) is not
restated: both of its halves are proved for every ESS, boundary ESSs included, in
`Domains.Biology.Ecology.BoundaryESSStabilityReLtZero`. The primaries of Bishop and Cannings
(1976) and Haigh (1975) are paywalled and were not read; the statements follow Haigh's 1974
appendix, Taylor and Jonker (1978) and the Encyclopedia of Mathematics entry by C. Cannings. The
ESS predicate is the library's
`MathlibExt.Biology.Dynamics.Replicator.IsESS` (`Domains.Biology.Dynamics.ReplicatorStability`),
for which an ESS is a Nash equilibrium (`IsESS.isNash`), and a mixed strategy is the library's
`MathlibExt.Biology.Dynamics.AsymmetricESS.IsMixed` (`Domains.Biology.Dynamics.AsymmetricESS`),
the simplex condition of `IsESS`.

Sources: D. T. Bishop and C. Cannings, "Models of animal conflict", Adv. Appl. Probab. 8 (1976)
616–621; D. T. Bishop and C. Cannings, "A generalized war of attrition", J. Theor. Biol. 70
(1978) 85–124, doi:10.1016/0022-5193(78)90304-1; J. Haigh, "Game theory and evolution", Adv.
Appl. Probab. 7 (1975) 8–11; J. Haigh, appendix to J. Maynard Smith, J. Theor. Biol. 47 (1974)
219–221; P. D. Taylor and L. B. Jonker, "Evolutionarily stable strategies and game dynamics",
Math. Biosci. 40 (1978) 145–156.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Dynamics.AsymmetricESS
public import Domains.Biology.Dynamics.ReplicatorStability
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace WantedExt.Biology.Ecology.BishopCanningsWanted

open Matrix
open MathlibExt.Biology.Dynamics.Replicator (IsESS)
open MathlibExt.Biology.Dynamics.AsymmetricESS (IsMixed)

/-- **No nested ESS supports.** Let `A` be a real square matrix indexed by a finite type and `p` an
ESS. If `q` is a mixed strategy (`IsMixed q`) with `q ≠ p` whose support is contained in the
support of `p` (`qᵢ > 0 → pᵢ > 0` for every `i`), then `q` is not an ESS.

Sources: Bishop and Cannings (1976); Bishop and Cannings (1978), Theorem 3. -/
public theorem_wanted not_isESS_of_support_subset {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (p q : ι → ℝ) (hp : IsESS A p) (hq : IsMixed q) (hne : q ≠ p)
    (hsupp : ∀ i, 0 < q i → 0 < p i) :
    ¬ IsESS A q

/-- **Haigh's condition.** Let `A` be a real square matrix indexed by a finite type and `p` an ESS.
Then `xᵀ A x < 0` for every `x ≠ 0` with `∑ xᵢ = 0` whose support is contained in the support of
`p` (`xᵢ ≠ 0 → pᵢ > 0` for every `i`).

Sources: Haigh (1975); Taylor and Jonker (1978). -/
public theorem_wanted haigh_condition {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (p : ι → ℝ)
    (hp : IsESS A p) (x : ι → ℝ) (hx : x ≠ 0) (hsum : ∑ i, x i = 0)
    (hsupp : ∀ i, x i ≠ 0 → 0 < p i) :
    x ⬝ᵥ (A *ᵥ x) < 0

/-- **Regular ESS.** Let `A` be a real square matrix indexed by a finite type and `p` a mixed
strategy (`IsMixed p`) such that (1) every pure strategy in the support earns
`(A p)ᵢ = pᵀ A p`; (2) every pure strategy outside the support earns `(A p)ⱼ < pᵀ A p`; and
(3) `xᵀ A x < 0` for every `x ≠ 0` with `∑ xᵢ = 0` and support in the support of `p`. Then `p` is
an ESS.

Source: Taylor and Jonker (1978). -/
public theorem_wanted isESS_of_regular {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (p : ι → ℝ)
    (hp : IsMixed p) (heq : ∀ i, 0 < p i → (A *ᵥ p) i = p ⬝ᵥ (A *ᵥ p))
    (hlt : ∀ j, p j = 0 → (A *ᵥ p) j < p ⬝ᵥ (A *ᵥ p))
    (hneg : ∀ x : ι → ℝ, x ≠ 0 → ∑ i, x i = 0 → (∀ i, x i ≠ 0 → 0 < p i) →
      x ⬝ᵥ (A *ᵥ x) < 0) :
    IsESS A p

end WantedExt.Biology.Ecology.BishopCanningsWanted
