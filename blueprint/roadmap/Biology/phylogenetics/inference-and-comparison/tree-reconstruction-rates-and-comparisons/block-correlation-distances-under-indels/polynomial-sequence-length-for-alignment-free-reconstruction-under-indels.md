# Polynomial sequence length for alignment-free phylogeny reconstruction under indels

**Setting.** Sequences evolve on an $n$-leaf rooted binary tree under the two-state substitution–insertion–deletion process of [the state-deviation correlation model](expected-state-deviation-correlation-under-an-indel-process.md): along each edge every site flips at rate $\nu_e$ and is deleted at rate $\mu_e$, and new uniform sites are inserted at rate $\lambda_e$; $k_r$ denotes the root sequence length. The reconstruction problem asks for the tree topology from the leaf sequences alone, without a given alignment.

**Theorem (consistency, finite tree).** If $0<t_e,\nu_e,\lambda_e,\mu_e<\infty$ for every edge, then some procedure returns the correct tree from the leaf sequences with failure probability tending to $0$ as $k_r\to\infty$. No ultrametric or clock assumption is needed.

**Theorem (two-state model, molecular clock).** Assume the molecular clock (all leaves contemporaneous and $\nu_e=\nu$, $\lambda_e=\lambda$, $\mu_e=\mu$ for all $e$), branch lengths $f<t_e<g$ for constants $0<f<g<\infty$ independent of $n$, and $0<\underline{\nu}<\nu<\overline{\nu}$, $0\le\lambda<\overline{\lambda}$, $0\le\mu<\overline{\mu}$ for constants independent of $n$. Then for every $\beta'>0$ there is $\beta''>0$ and a polynomial-time algorithm that returns the correct tree with failure probability at most $n^{-\beta'}$ whenever

$$k_r \ge n^{\beta''}.$$

**Theorem (GTR substitutions, bounded rates).** The same conclusion holds when substitutions follow a reversible rate matrix $\nu_e Q$ on four states, the leaves are contemporaneous (ultrametric, without requiring a molecular clock), $f<t_e<g$ and $\underline{\nu}<\nu_e<\overline{\nu}$ for all $e$, and the insertion and deletion rates are common to all edges and bounded by constants independent of $n$.

In particular, constant (not vanishing) indel rates are allowed, at the cost of a polynomial rather than polylogarithmic sequence length.

## Expansion

The proof has four steps. First, the expected block statistic is computed exactly through the branching-process moments of the [state-deviation correlation](expected-state-deviation-correlation-under-an-indel-process.md), which defines an additive metric. Second, moment-generating-function bounds on the length process show that, under the stated assumptions, every site is displaced by at most $O(\sqrt{k\log k})$ positions. Third, each sequence is cut into consecutive blocks of length about $k^{\zeta}$ with $\zeta>1/2$; because displacements are much smaller than blocks, matching blocks across leaves share most of their homologous sites, and the block correlations have approximately the right expectation. Fourth, conditional on the high-probability length and displacement events, the block estimates are independent enough to concentrate. With all pairwise distances estimated to small additive error, a standard distance-based reconstruction applies. The polynomial requirement comes from needing many blocks, each long enough to dominate the displacement.

## Depends on

- [Expected state-deviation correlation under an indel process](expected-state-deviation-correlation-under-an-indel-process.md)

## Sources

- Constantinos Daskalakis and Sebastien Roch, "Alignment-free phylogenetic reconstruction: sample complexity via a branching process analysis", arXiv:1109.5002 (2011), Section 1.2 (Theorems 1–3 and the proof sketch), Sections 3–5 (block partitioning, concentration, extensions), <https://doi.org/10.48550/arXiv.1109.5002>. Published version: The Annals of Applied Probability 23(2) (2013), 693–721, <https://doi.org/10.1214/12-aap852>; locators above refer to the arXiv version.
