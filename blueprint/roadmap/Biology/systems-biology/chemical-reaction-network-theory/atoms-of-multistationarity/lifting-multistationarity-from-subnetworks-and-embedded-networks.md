# Lifting multistationarity from subnetworks and embedded networks

**Definitions.** A reaction network $G$ has species $\mathscr{S}$, complexes and reactions $\mathscr{R}$; its stoichiometric subspace $\bar S_G$ is spanned by the reaction vectors. A *subnetwork* uses a subset of the reactions. An *embedded network* of $G$ is defined by a subset $S \subseteq \mathscr{S}$ of species and a subset $R \subseteq \mathscr{R}$ of reactions involving all species of $S$: it consists of the reactions of $R$ with every species outside $S$ deleted from the complexes (discarding trivial reactions). A network *admits multiple nondegenerate positive steady states* if, for some rate constants, it has at least two positive steady states in one stoichiometric compatibility class at which the Jacobian is nonsingular on the stoichiometric subspace. A *mass-action flow-type subnetwork* for a species $X_i$ is a nonempty subnetwork whose reactions involve only $X_i$ and which, for some rate constants, has $x_i = 1$ as a nondegenerate steady state (e.g. $X_i \rightleftarrows 0$).

**Theorem (subnetworks).** Let $N$ be a subnetwork of $G$ with the same stoichiometric subspace, $\bar S_N = \bar S_G$, and fix a parametrized family of kinetics (e.g. mass action). If $N$ admits multiple nondegenerate positive steady states, so does $G$, and at least as many when $N$ has finitely many; the same holds for multiple exponentially stable positive steady states. In particular multistationarity lifts when irreversible reactions are made reversible, and from a sub-CFSTR to a fully open CFSTR.

**Theorem (embedded networks).** Let $N$ be an embedded network of $G$ such that
1. $\bar S_N = \mathbb{R}^{|\mathscr{S}_N|}$ (full-dimensional), and
2. every species of $G$ not in $N$ has a mass-action flow-type subnetwork in $G$.

If $N$ admits multiple nondegenerate positive mass-action steady states (resp. multiple exponentially stable ones), so does $G$, and at least as many when finitely many. In particular, if $N$ is an embedded CFSTR of a fully open CFSTR $G$ (a network containing all inflow and outflow reactions $0 \rightleftarrows X_i$), multistationarity of $N$ lifts to $G$.

## Expansion

Both results are perturbation arguments. Adding reactions with small rate constants $\varepsilon\kappa$ to $N$ perturbs the steady-state equations restricted to the common stoichiometric class; nondegenerate steady states persist by the implicit function theorem, and exponential stability is an open condition. For an embedded network, the deleted species are held near $1$ by their flow-type subnetworks run with large rate constants, so their concentrations act as nearly constant factors that can be absorbed into the rate constants of $N$; again nondegenerate solutions persist. The hypotheses on stoichiometric subspaces ensure that the compatibility classes of the two networks match.

## Sources

- Badal Joshi and Anne Shiu, "Atoms of multistationarity in chemical reaction networks", Journal of Mathematical Chemistry (2012), <https://doi.org/10.1007/s10910-012-0072-0>; numbering as in arXiv:1108.5238: Definitions 2.4 and 4.1, Theorem 3.1, Corollaries 3.5–3.6, Theorem 4.2 and Corollary 4.6.
