/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.InformationTheory.FiniteSanov

/-!
# Gibbs' conditioning principle for finite alphabets: wishlist

`MathlibExt.InformationTheory.FiniteSanov` proves Sanov's theorem for finite alphabets by the
method of types. Its companion, the conditional limit theorem, says that conditioned on the
unlikely event `P̂ₙ ∈ Γ`, the first `k` draws are asymptotically i.i.d. with law `P*`, the
I-projection of `Q` on `Γ`. The proof combines the type-class estimates with the Pythagorean
inequality of `MathlibExt.InformationTheory.IProjection`; it is not formalized here.

## References

* I. Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), Section III, Corollary
  to Theorem III.3.
* I. Csiszár, "Sanov property, generalized I-projection and a conditional limit theorem",
  Ann. Probab. 12 (1984), 768–793 (the general-alphabet version; not consulted for the statement
  below).
-/

namespace MathlibExt.InformationTheory.GibbsConditioningWanted

@[expose] public section

open Finset Real Filter Topology MathlibExt.InformationTheory.MethodOfTypes

/-- **Gibbs' conditioning principle, finite alphabet** (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), Corollary to Theorem III.3). Let `Q > 0` be a distribution on a
finite alphabet and `Γ` a set of distributions satisfying (III.21), in the form: `r ≤ D(P ‖ Q)` on
`Γ`, and some `n`-types `s n`, in `Γ` for all large `n`, have `D(P̂_{s n} ‖ Q) → r`, so
`r = D(Γ ‖ Q)`; for nonempty `Γ` this form is equivalent to (III.21), since `D(Γ ‖ Q) < ∞` when
`Q > 0`. If a unique `P*` in the closure
of `Γ` has `D(P* ‖ Q) = r`, then for every `k` and every word `y` of length `k`, the conditional
probability that the first `k` of `n` independent draws from `Q` spell `y`, given that their
empirical distribution lies in `Γ`, tends to `∏ᵢ P*(yᵢ)`. The source allows any `Q`; this
statement assumes `Q > 0`. -/
theorem_wanted tendsto_iidProb_prefix_div_iidProb {α : Type*} [Fintype α] [DecidableEq α]
    {Q : α → ℝ} (hQ : ∀ a, 0 < Q a) (hQ1 : ∑ a, Q a = 1)
    {Γ : Set (α → ℝ)} [DecidablePred (· ∈ Γ)]
    (hΓ : ∀ P ∈ Γ, (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1)
    {r : ℝ} (hr : ∀ P ∈ Γ, r ≤ ∑ a, P a * log (P a / Q a))
    (s : ∀ n : ℕ, Sym α n) (hs : ∀ᶠ n in atTop, empirical (s n) ∈ Γ)
    (hlim : Tendsto (fun n => ∑ a, empirical (s n) a * log (empirical (s n) a / Q a))
      atTop (𝓝 r))
    {Ps : α → ℝ} (hPs : Ps ∈ closure Γ) (hPsD : ∑ a, Ps a * log (Ps a / Q a) = r)
    (huniq : ∀ P ∈ closure Γ, ∑ a, P a * log (P a / Q a) = r → P = Ps)
    (k : ℕ) (y : Fin k → α) :
    Tendsto (fun n : ℕ =>
      iidProb Q (univ.filter fun x : Fin n → α =>
          empirical (seqType x) ∈ Γ ∧ ∀ i : Fin k, ∀ h : (i : ℕ) < n, x ⟨i, h⟩ = y i) /
        iidProb Q (univ.filter fun x : Fin n → α => empirical (seqType x) ∈ Γ))
      atTop (𝓝 (∏ i, Ps (y i)))

end

end MathlibExt.InformationTheory.GibbsConditioningWanted
