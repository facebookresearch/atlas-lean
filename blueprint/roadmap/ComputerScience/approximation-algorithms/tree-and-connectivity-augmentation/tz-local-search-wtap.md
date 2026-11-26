# Traub-Zenklusen local search: weighted tree augmentation is (1.5 + eps)-approximable

For every fixed $\varepsilon > 0$ there is a polynomial-time $(1.5+\varepsilon)$-approximation algorithm for WTAP, obtained by a non-oblivious local search over the components of the relative greedy framework. The same technique gives a purely combinatorial $(\ln 4+\varepsilon)$-approximation for the Steiner tree problem in graphs, with cost bounded by $(\ln 4+\varepsilon)$ times the value of the hypergraphic LP, and hence an alternative proof that the hypergraphic LP has integrality gap at most $\ln 4$.

## Proof sketch

Maintain a solution consisting of chosen components together with the up-links they have not dropped, and measure progress by a potential that weights each up-link according to how many components cover it, rather than by the solution weight itself. A local move adds one component of $\mathcal{K}_\varepsilon$ and removes the links it makes redundant; when no move improves the potential by a $1+\varepsilon/\mathrm{poly}(n)$ factor, applying the decomposition lemma to an optimum shows the potential, and hence the weight, is at most $(1.5+\varepsilon)\mathrm{OPT}$. For Steiner tree, full components play the role of link sets and the potential is compared against the hypergraphic LP.

## Depends on

- [Traub-Zenklusen: weighted tree augmentation is (1 + ln 2 + eps)-approximable](tz-one-plus-ln-two.md)
- [Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)](wtap-component-decomposition.md)
- [Steiner tree instances](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)
- [STEINER TREE is NP-complete](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-np-complete.md)

## Proof depends on

- [Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)](wtap-component-decomposition.md)
- [Traub-Zenklusen: weighted tree augmentation is (1 + ln 2 + eps)-approximable](tz-one-plus-ln-two.md)

## Sources

- Vera Traub, Rico Zenklusen, "Local Search for Weighted Tree Augmentation and Steiner Tree", SODA (2022), arXiv:2107.07403.
- Jaroslaw Byrka, Fabrizio Grandoni, Thomas Rothvoss, Laura Sanita, "Steiner Tree Approximation via Iterative Randomized Rounding", Journal of the ACM (2013).
