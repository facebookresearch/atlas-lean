# Classification of degenerate two-dimensional zero-one networks

**Setting.** As in the companion article, a consistent mass-action network is *degenerate* if every positive steady state has a Jacobian whose restriction to the stoichiometric subspace is not surjective. Given a network $G$ on species $X_1, \dots, X_s$ and a map $\phi$ sending each species to a sum of new species, the network $\phi(G)$ with reactions $\sum_i \alpha_{ij}\phi(X_i) \to \sum_i \beta_{ij}\phi(X_i)$ is a *species refinement* of $G$ if it has the same dimension as $G$ (and $G$ is a *lumping network* of $\phi(G)$). A *consistent subnetwork* is a subset of reactions that is itself consistent.

**Theorem.** A two-dimensional zero-one network without trivial species is degenerate if and only if it is a consistent subnetwork of a species refinement of one of two prototype networks: the *complete paired-exchange network* or the *catalytic-pair conversion network*. Equivalently, writing $\mathcal N$ for the stoichiometric matrix and $\mathcal X$ for the reactant matrix, degeneracy holds if and only if every species row $(\mathcal N_i, \mathcal X_i)$ belongs to one of two explicit finite lists of row patterns, built from two basis stoichiometric rows and a reactant pattern together with its $0/1$ complement.

## Depends on

- [Algebraic criterion for degenerate reaction networks](algebraic-criterion-for-degenerate-reaction-networks.md)

## Expansion

Species refinement splits a species into several that always move together, which preserves the steady-state structure and the dimension, so degeneracy passes from a lumping network to its refinements and to consistent subnetworks. The converse uses the algebraic criterion and the binomial structure found for up to three species: in dimension two, degeneracy forces each species row to repeat one of a few stoichiometric directions with a matching or complementary reactant pattern, and every such configuration lumps onto one of the two prototypes. The complete paired-exchange prototype has five consistent subnetworks while the catalytic-pair conversion prototype has none, which yields a finite catalogue of degenerate networks up to refinement.

## Sources

- Y. Chen, X. Tang, "Characterization of Minimal Degenerate Zero-One Reaction Networks", arXiv:2608.18509 (2026), Main Theorem and its matrix version (Section 3), <https://doi.org/10.48550/arXiv.2608.18509>.
