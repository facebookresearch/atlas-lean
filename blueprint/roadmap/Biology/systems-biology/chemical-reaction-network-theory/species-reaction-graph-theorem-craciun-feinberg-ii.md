# Species–reaction graph criterion for unique equilibria (Craciun–Feinberg)

The SR graph of a reaction network is a signed, labelled bipartite multigraph with one vertex for each species and one for each reaction; edges join a species to the reactions in which it participates and carry as label its stoichiometric coefficient (Banaji 2010, Section 3). In Banaji's formulation (Section 4), a cycle is an e-cycle if its parity $(-1)^{|C|/2}\operatorname{sign}(C)$ equals $1$ and an o-cycle otherwise; it is an s-cycle if the alternating product of its edge labels, $\prod_i \mathrm{lbl}(e_{2i-1}) - \prod_i \mathrm{lbl}(e_{2i})$, vanishes; and two cycles have S-to-R intersection if each component of their intersection is a path between a species vertex and a reaction vertex. Condition $(*)$ requires that all e-cycles be s-cycles and that no two e-cycles have S-to-R intersection. For reaction systems with outflow of every species, $\dot x = x_{\mathrm{in}} + \Gamma v(x) - Q(x)$, whose kinetics are N1C (a class that includes mass action and Michaelis–Menten kinetics), an SR graph satisfying $(*)$ makes the vector field injective (Banaji 2010, Proposition 1). An injective vector field has at most one zero, so injectivity excludes multiple equilibria, as in the result that [injectivity precludes multiple equilibria (Craciun–Feinberg)](../../../Biology/systems-biology/chemical-reaction-network-theory/injectivity-criterion-precludes-multistationarity-craciun-feinberg-i.md); Condition $(*)$ is therefore a graph-theoretic sufficient condition for injectivity, and hence for at most one equilibrium. For mass action kinetics in the continuous-flow stirred-tank reactor, this is the species–reaction graph theorem of Craciun and Feinberg, which Lipson (2007, Theorem 3) restates as: if no two cycles with even potential strongly intersect (and those cycles satisfy a value condition), the network cannot have multiple equilibria, regardless of the rate constants.

## Depends on

- [Injectivity precludes multiple equilibria (Craciun–Feinberg)](../../../Biology/systems-biology/chemical-reaction-network-theory/injectivity-criterion-precludes-multistationarity-craciun-feinberg-i.md)

## Expansion

1. Definitions: the SR graph, edge signs and labels, parity, e-cycles, o-cycles, s-cycles and S-to-R intersection, as in the source.
2. The expansion of the Jacobian determinant into terms indexed by cycle structures (Lipson 2007, Section 6.2), and the argument that the cycle condition makes the determinant nonzero for all concentrations and all positive rate constants.
3. Condition $(*)$ implies injectivity of the reaction vector field, and an injective vector field has at most one equilibrium, as in the [Craciun–Feinberg injectivity result](../../../Biology/systems-biology/chemical-reaction-network-theory/injectivity-criterion-precludes-multistationarity-craciun-feinberg-i.md).
4. The original mass-action statement of Craciun and Feinberg in its own terminology (odd-cycles, stoichiometric cycles, even-cycles), fixed from their paper.
5. Systems without outflow: at most one nondegenerate positive equilibrium in each stoichiometry class (Banaji 2010, Section 5.1), as a separate statement.

## Sources

- M. Banaji, Cycle structure in SR and DSR graphs: implications for multiple equilibria and stable oscillation in chemical reaction networks, arXiv preprint, 2010, Sections 3–5 and Proposition 1. <https://arxiv.org/abs/1005.5472>
- M. Lipson, Differential and graphical approaches to multistability theory for chemical reaction networks, arXiv preprint, 2007, Theorem 3. <https://arxiv.org/abs/0709.0125>
- Original result: G. Craciun and M. Feinberg, Multiple equilibria in complex chemical reaction networks: II. The species–reaction graph, SIAM J. Appl. Math. 66 (2006), 1321–1338. <https://doi.org/10.1137/050634177> The SR-graph criterion follows Banaji (2010, Proposition 1) and the restatement in Lipson (2007, Theorem 3).
