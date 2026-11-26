# Automorphism-corrected Metropolis–Hastings for leaf-labelled networks

**Quotient chains.** Let $M$ be an irreducible aperiodic Markov chain on a finite state space $X$ with stationary law $\pi$, and let $\sim$ be an equivalence relation on states and transitions such that equivalent transitions join the same pair of classes. The quotient chain on $X/\!\sim$ with transition probabilities

$$P'_{\tilde m}=\frac1{\pi(U)}\sum_{(m:u\to v)\in\tilde m}\pi(u)P_m$$

is irreducible and its stationary law $\tilde\pi$ satisfies $\tilde\pi(V)=\pi(V)$ for every class $V$. When the classes are orbits of a group $\Gamma$ acting on a proposal graph with proposal probabilities $g$, a Metropolis–Hastings chain on $V/\Gamma$ with target $\pi$ is obtained with acceptance

$$A(\tilde m:U\to V)=\min\!\Big(1,\frac{\pi(V)}{\pi(U)}\,\frac{|U|}{|V|}\,\frac{g(m^{-1})}{g(m)}\Big),$$

for arbitrary representatives $m$, $m^{-1}$ of the move and its reverse.

**Theorem (leaf-labelled networks).** Let $\pi$ be a positive target on leaf-labelled phylogenetic networks, and propose moves by choosing uniformly among the moves of a fully labelled representative (all internal nodes named). If the quotient proposal chain is irreducible and aperiodic, then for rSPR, tail and head moves the acceptance probability

$$A(N\to N')=\min\!\Big(1,\frac{\pi(N')}{\pi(N)}\,\frac{|\mathrm{Aut}(N')|}{|\mathrm{Aut}(N)|}\Big)$$

yields stationary law $\pi$, where $\mathrm{Aut}(N)$ is the group of automorphisms of $N$ fixing every leaf. For a network with $n$ leaves and $k$ reticulations, moves that add or remove a reticulation carry the additional proposal factors $\frac{(2n+3k-1)^2}{2n+3k+2}$ and $\frac{2n+3k-1}{(2n+3k-4)^2}$ respectively.

## Expansion

A leaf-labelled network $N$ has $c/|\mathrm{Aut}(N)|$ fully labelled representatives, with $c$ depending only on the numbers of internal nodes, so orbit sizes are inversely proportional to automorphism counts. Without the factor $|\mathrm{Aut}(N')|/|\mathrm{Aut}(N)|$ the chain targets $\pi$ on fully labelled networks and therefore undersamples leaf-labelled networks with internal symmetry. Counting automorphisms reduces to isomorphism tests (Mathon's reduction): fixing vertices one at a time multiplies $|\mathrm{Aut}|$ by orbit sizes, giving an $O(n^2f(n))$ algorithm with $f$ the cost of binary network isomorphism, and grouping vertices by their $\mu$-vectors (counts of root-to-leaf paths through each vertex) reduces this to $O(knf(n))$, $k$ the largest group of equal $\mu$-vectors.

## Sources

- Leo van Iersel, Remie Janssen, Mark Jones, Yukihiro Murakami, "Metropolis-Hastings Sampling of Phylogenetic Networks: Correcting for Symmetries", arXiv:2608.12430: Theorem 1 (quotient Markov chains), Lemma 1, Theorem 2 (quotient Metropolis–Hastings), Theorem 3 (acceptance functions for rSPR, tail, head, and reticulation-adding and -removing moves), Lemmas 3, 4 and 6 (automorphism counting). <https://doi.org/10.48550/arXiv.2608.12430>
