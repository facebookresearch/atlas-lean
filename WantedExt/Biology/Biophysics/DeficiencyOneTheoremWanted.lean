/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Feinberg's deficiency-one theorem

A chemical reaction network on a finite set `S` of species is a finite family of reactions `r`,
each turning a source complex `src r : S → ℕ` into a product complex `prod r : S → ℕ`. Its
linkage classes are the connected components of the undirected reaction graph on the complexes.
For a linkage class `θ` with `n_θ` complexes, let `𝒮_θ` be the span of the reaction vectors
`prod r - src r` of the reactions whose source complex lies in `θ`; its deficiency is
`δ_θ = n_θ - 1 - dim 𝒮_θ`. The deficiency of the network is `δ = n - ℓ - s`. A strong linkage
class is a class of complexes that are mutually reachable along directed paths of reactions; it
is terminal if no reaction leads out of it. A complex `c` lies in a terminal strong linkage class
exactly when every complex reachable from `c` can reach `c` back, and two such complexes lie in
the same terminal strong linkage class exactly when one reaches the other.

**Deficiency-one theorem** (Feinberg 1987, Theorem 6.2.1, as stated in Johnston 2016, Theorem
2.2). Consider a mass-action system whose network has `ℓ` linkage classes, each containing just
one terminal strong linkage class, and suppose that (i) `δ_θ ≤ 1` for every linkage class `θ` and
(ii) `∑_θ δ_θ = δ`. If, for some choice of positive rate constants, the system has a positive
steady state, then each positive stoichiometric compatibility class contains exactly one positive
steady state. If the network is moreover weakly reversible, the system has a positive steady
state for every choice of positive rate constants.

The two statements below are consequences of this theorem: for every choice of positive rate
constants, each positive stoichiometric compatibility class contains at most one positive steady
state, and for a weakly reversible network exactly one. The step from one positive steady state to
one in every class is not stated here.

The linear-algebra part of the proof (hypothesis (ii) holds exactly when the subspaces `𝒮_θ` are
independent, and the mass-action equations then decouple across linkage classes) is proved in
`Domains.Biology.Dynamics.DeficiencyOne` (`sum_linkageClassDeficiency_eq_iff`). The
linkage-class subspaces and deficiencies used here are the shared definitions of
`MathlibExt.Dynamics.PolynomialNetworks.LinkageClass`, on which that file is built, and the
network, its stoichiometric subspace, linkage graph, deficiency, weak reversibility and
mass-action field are those of `MathlibExt.Dynamics.PolynomialNetworks.Deficiency`. Complexes
are encoded with natural-number stoichiometric coefficients, as for the chemical networks of the
source; Johnston's networks allow nonnegative real coefficients, and the statements here are its
case of natural-number coefficients. The existence half for
weakly reversible networks is also a consequence of Boros's theorem (every weakly reversible
mass-action system has a positive steady state in every positive stoichiometric class).

Sources: M. Feinberg, "Chemical reaction network structure and the stability of complex
isothermal reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42
(1987) 2229–2268, Section 6.2, Theorem 6.2.1; proof in M. Feinberg, "The existence and
uniqueness of steady states for a class of chemical reaction networks", Arch. Rational Mech.
Anal. 132 (1995) 311–370; M. D. Johnston, "A linear programming approach to dynamical
equivalence, linear conjugacy, and the Deficiency One Theorem", J. Math. Chem. 54 (2016)
1612–1631, Section 2.4, Theorem 2.2 (arXiv:1602.08396v2).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.LinkageClass
public import Mathlib.Logic.Relation

@[expose] public section

namespace WantedExt.Biology.Biophysics.DeficiencyOneTheoremWanted

open MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*} (N : ReactionNetwork S ρ)

/-- A complex lies in a terminal strong linkage class: every complex reachable from it along a
directed path of reactions reaches it back. -/
def IsTerminalComplex (c : S → ℕ) : Prop :=
  ∀ c', Relation.ReflTransGen N.Reacts c c' → Relation.ReflTransGen N.Reacts c' c

/-- Each linkage class contains exactly one terminal strong linkage class: it contains a complex
of a terminal strong linkage class, and any two such complexes in it are linked by a directed path
of reactions (so they lie in the same strong linkage class). -/
def OneTerminalClassPerLinkageClass : Prop :=
  ∀ θ : N.linkageGraph.ConnectedComponent,
    (∃ c ∈ θ.supp, IsTerminalComplex N c.1) ∧
      ∀ c ∈ θ.supp, ∀ c' ∈ θ.supp,
        IsTerminalComplex N c.1 → IsTerminalComplex N c'.1 →
          Relation.ReflTransGen N.Reacts c.1 c'.1

/-- **Deficiency-one theorem, uniqueness** (Feinberg 1987, Theorem 6.2.1). Let the network have
finitely many species (`[Fintype S]`), reactions (`[Fintype ρ]`) and linkage classes. Suppose
each linkage class contains just one terminal strong linkage class, every linkage-class
deficiency is at most one, and the linkage-class deficiencies sum to the deficiency of the
network. Then for all positive rate constants `k`, two positive steady states `x` and `y` of the
mass-action system whose difference lies in the stoichiometric subspace (the same positive
stoichiometric compatibility class) are equal.

Source: M. Feinberg, Chem. Eng. Sci. 42 (1987) 2229–2268, Theorem 6.2.1.

Source: M. D. Johnston, J. Math. Chem. 54 (2016) 1612–1631, Theorem 2.2 (arXiv:1602.08396v2), the
case of natural-number coefficients. -/
theorem_wanted eq_of_pos_steadyState [Fintype S] [Fintype ρ]
    (hT : OneTerminalClassPerLinkageClass N)
    [Fintype N.linkageGraph.ConnectedComponent] (hδ : ∀ θ, N.linkageClassDeficiency θ ≤ 1)
    (hsum : ∑ θ, N.linkageClassDeficiency θ = N.deficiency)
    {k : ρ → ℝ} (hk : ∀ r, 0 < k r) {x y : S → ℝ} (hx : ∀ s, 0 < x s) (hy : ∀ s, 0 < y s)
    (hxy : x - y ∈ N.stoichiometricSubspace) (hxe : N.massActionField k x = 0)
    (hye : N.massActionField k y = 0) :
    x = y

/-- **Deficiency-one theorem, weakly reversible case** (Feinberg 1987, Theorem 6.2.1). Let the
network have finitely many species (`[Fintype S]`), reactions (`[Fintype ρ]`) and linkage
classes. Suppose each linkage class contains just one terminal strong linkage class, every
linkage-class deficiency is at most one, the linkage-class deficiencies sum to the deficiency of
the network, and the network is weakly reversible. Then for all positive rate constants `k` and
every positive state `x₀` there is exactly one positive steady state `x` of the mass-action
system with `x - x₀` in the stoichiometric subspace.

Source: M. Feinberg, Chem. Eng. Sci. 42 (1987) 2229–2268, Theorem 6.2.1.

Source: M. D. Johnston, J. Math. Chem. 54 (2016) 1612–1631, Theorem 2.2 (arXiv:1602.08396v2), the
case of natural-number coefficients. -/
theorem_wanted existsUnique_pos_steadyState_of_isWeaklyReversible [Fintype S] [Fintype ρ]
    (hT : OneTerminalClassPerLinkageClass N)
    [Fintype N.linkageGraph.ConnectedComponent] (hδ : ∀ θ, N.linkageClassDeficiency θ ≤ 1)
    (hsum : ∑ θ, N.linkageClassDeficiency θ = N.deficiency)
    (hwr : N.IsWeaklyReversible) {k : ρ → ℝ} (hk : ∀ r, 0 < k r) {x₀ : S → ℝ}
    (hx₀ : ∀ s, 0 < x₀ s) :
    ∃! x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0

end WantedExt.Biology.Biophysics.DeficiencyOneTheoremWanted
