# Deficiency one theorem

Consider a mass action system whose reaction network has $\ell$ linkage classes, each containing just one terminal strong linkage class. Let $\delta$ be the [deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) of the network and $\delta_1, \dots, \delta_\ell$ the [deficiencies of the individual linkage classes](../../../Chemistry/chemical-kinetics/deficiency-one-theory-of-reaction-networks/linkage-class-deficiency.md), and suppose that (i) $\delta_\theta \le 1$ for $\theta = 1, \dots, \ell$ and (ii) $\sum_{\theta=1}^{\ell} \delta_\theta = \delta$. Feinberg's Deficiency One Theorem (Feinberg 1987, Theorem 6.2.1) states: no matter what positive values the rate constants take, the differential equations admit no more than one steady state within a positive [stoichiometric compatibility class](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md); and if the network is weakly reversible, they admit precisely one steady state in each positive stoichiometric compatibility class. For a network with one linkage class condition (ii) holds trivially, so multiple positive steady states in a compatibility class require the deficiency or the number of terminal strong linkage classes to exceed one (Corollary 6.2.2). The source states that the proof appears in a separate article of Feinberg.

## Depends on

- [Deficiency of a chemical reaction network](../../../Dynamics/smooth-dynamics/deficiency.md)
- [Stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md)
- [Deficiency of a linkage class](../../../Chemistry/chemical-kinetics/deficiency-one-theory-of-reaction-networks/linkage-class-deficiency.md)
- [Mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md)
- [Weakly reversible reaction network](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Proof depends on

- [∑ δ_θ = δ iff the linkage-class subspaces are independent](../../../Chemistry/chemical-kinetics/deficiency-one-theory-of-reaction-networks/sum-linkage-class-deficiency-eq-iff.md)

## Expansion

1. Definitions: complexes, strong and terminal strong linkage classes, and stoichiometric compatibility classes (Sections 2.4–2.9 of the source); the linkage-class deficiencies are already the [deficiency of a linkage class](../../../Chemistry/chemical-kinetics/deficiency-one-theory-of-reaction-networks/linkage-class-deficiency.md), and the reformulation of condition (ii) as a direct sum of the linkage-class stoichiometric subspaces (condition (5.45) of the source) is already [∑ δ_θ = δ iff the linkage-class subspaces are independent](../../../Chemistry/chemical-kinetics/deficiency-one-theory-of-reaction-networks/sum-linkage-class-deficiency-eq-iff.md).
2. Uniqueness of a positive steady state in each compatibility class under (i) and (ii).
3. Existence for weakly reversible networks, compared with the [deficiency-zero theorem, weakly reversible case](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium.md).
4. Corollary 6.2.2 and the worked examples of Section 6.2 of the source, including networks of deficiency two to which the theorem applies.

## Sources

- M. Feinberg, Chemical reaction network structure and the stability of complex isothermal reactors I. The deficiency zero and deficiency one theorems, Chem. Eng. Sci. 42 (1987), 2229–2268, Theorem 6.2.1 and Corollary 6.2.2. <https://doi.org/10.1016/0009-2509(87)80099-4>
