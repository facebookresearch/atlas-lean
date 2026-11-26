# Logarithmic sequence length suffices for distance-based phylogeny reconstruction under GTR

**Setting.** A phylogeny on $n$ leaves is a binary tree with edge weights (branch lengths) $w_e$. Sequences of length $k$ evolve along it, sites i.i.d., under a general time-reversible (GTR) substitution model with rate matrix $Q$ on $r \ge 2$ states. For $0 < \Delta \le f \le g$, let $\mathcal Y^{f,g}_\Delta$ be the phylogenies with all $w_e \in [f, g]$ and all $w_e$ integer multiples of $\Delta$ (the $\Delta$-branch model). The reconstruction problem asks to recover the topology from the leaf sequences with probability tending to $1$. A **distance-based** method uses only estimates of pairwise evolutionary distances computed from pairs of sequences, or, here, from averages over groups of leaves of such distances. Let

$$g^* = \ln\sqrt 2,$$

the Kesten–Stigum reconstruction threshold under the paper's scaling of edge weights.

**Theorem.** For every $r \ge 2$, every GTR rate matrix $Q$, and all $0 < \Delta \le f \le g < g^*$, there is a distance-based method that solves the phylogenetic reconstruction problem on $\mathcal Y^{f,g}_\Delta \otimes \{Q\}$ with sequence length

$$k = O(\log n),$$

with dependence $\Delta^{-2}$ on the discretization. This matches, up to constants, the optimal $O(\log n)$ sample complexity previously known only for the two-state (CFN) model via likelihood-type ancestral reconstruction, and improves the polynomial sequence length of general distance methods valid for all $0 < f \le g$ (Erdős–Steel–Székely–Warnow). The homogeneous case (all leaves at the same graph depth) is proved first and then extended to general trees.

## Expansion

The key is to compute accurate "deep" distances between internal vertices without reconstructing ancestral states. For a unit flow $\Psi$ from a vertex $\rho$ to the leaves below it, the weighted-majority statistic $S = \sum_x \Psi(x)\,\sigma_x/\Theta_{\rho,x}$ built from an eigenvector $\sigma$ of $Q$ satisfies $\mathbb E[S \mid \xi_\rho] = \sigma_\rho$ and $\mathrm{Var}[S] = 1 + K_\Psi$, with $K_\Psi = \sum_e R_\rho(e)\Psi(e)^2$ an effective resistance that stays bounded when $g < g^*$ (the tree branches faster than the signal decays); an exponential-moment bound gives concentration with $O(\log n)$ sites. Averaging pairwise products of such statistics estimates distances between internal vertices to within $\varepsilon$ when they are close, and a diameter test discards long, unreliable distances; with the $\Delta$-discretization the distorted metric is recovered exactly, and the tree is built level by level from triplets of nearby subtrees.

## Sources

- Sebastien Roch, "Phase Transition in Distance-Based Phylogeny Reconstruction", arXiv (2011). Section 1 (Theorems 1–3), Section 2 (Propositions 1–4), Section 3 (Theorem 4, Propositions 5–6), Section 4 (extension to general trees). <https://doi.org/10.48550/arXiv.1108.5781>
