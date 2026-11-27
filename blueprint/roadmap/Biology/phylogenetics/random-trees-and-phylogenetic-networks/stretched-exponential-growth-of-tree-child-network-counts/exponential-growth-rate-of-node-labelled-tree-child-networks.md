# Exponential growth rate of node-labelled tree-child networks

**Setting.** A tree-child network is a rooted binary phylogenetic network (root of out-degree $1$, tree nodes of in-/out-degree $1/2$, reticulation nodes of in-/out-degree $2/1$, leaves of in-degree $1$) in which every non-leaf node has at least one child that is not a reticulation node. Let $\mathrm{TC}_{n,k}$ be the number of tree-child networks with $n$ labelled leaves and $k$ reticulation nodes, and let $\widehat{\mathrm{TC}}_N$ be the number of tree-child networks with $N$ non-root nodes that are all bijectively labelled. Such networks exist only for odd $N$, since $n+k=(N+1)/2$.

**Reduction to leaf-labelled counts.** For odd $N$,

$$
\widehat{\mathrm{TC}}_N=\sum_{n=\lceil (N+3)/4\rceil}^{(N+1)/2}\frac{N!}{n!}\,\mathrm{TC}_{n,(N+1)/2-n}.
$$

**Theorem.** As $N\to\infty$ through odd integers,

$$
\widehat{\mathrm{TC}}_N=\left(\frac{3}{e^5}+o(1)\right)^{N/4}N^{5N/4}.
$$

More precisely, with $a_1\approx-2.3381$ the largest zero of the Airy function $\mathrm{Ai}$,

$$
\widehat{\mathrm{TC}}_N=\Omega\!\left(N^{1/12}e^{a_1(3N/4)^{1/3}}\left(\frac{3}{e^5}\right)^{N/4}N^{5N/4}\right),\qquad \widehat{\mathrm{TC}}_N=O\!\left(N^{2}e^{\sqrt{3N}/2}\left(\frac{3}{e^5}\right)^{N/4}N^{5N/4}\right).
$$

So $(3/e^5)^{1/4}$ is the base of the exponential growth beyond the dominant factor $N^{5N/4}$; the bounds still differ by a stretched-exponential factor.

## Expansion

Two structural facts give the reduction: in a tree-child network, $n+k=(N+1)/2$, and distinct non-root nodes have distinct sets of descendant leaves. Hence a fully labelled network is the same as a leaf-labelled network together with a choice of which $n$ of the $N$ labels go to the leaves (assigned order-preservingly) and an arbitrary assignment of the other $N-n$ labels to internal non-root nodes, which gives the factor $\binom{N}{n}(N-n)!=N!/n!$.

For the lower bound, keep only the term $\tilde n=\lceil (N+3)/4\rceil$, where the network is maximally or next-to-maximally reticulated ($\mathrm{TC}_{n,n-2}=\mathrm{TC}_{n,n-1}/2$). Maximally reticulated tree-child networks with leaf labels removed are in bijection with words in which each of $n-1$ letters occurs three times subject to a prefix-dominance condition, and the Airy-type asymptotics of these words give the stated $\Omega$-bound after Stirling's formula. For the upper bound, the inequality $2(n-k-1)\mathrm{TC}_{n,k}\le\mathrm{TC}_{n,k+1}$ bounds every $\mathrm{TC}_{n,k}$ by the maximally reticulated count, and the cruder bound $a_n=O(n^{-1}(12/e)^n n^n)$ on the word counts, maximized over $n$, gives the $O$-bound.

## Sources

- Michael Fuchs, Guan-Ru Yu, Louxin Zhang, "On the asymptotic growth of the number of tree-child networks", European Journal of Combinatorics 93 (2021), 103278, <https://doi.org/10.1016/j.ejc.2020.103278>. Published version of arXiv:2003.08049, cited next; locators there refer to the arXiv version.
- Michael Fuchs, Guan-Ru Yu and Louxin Zhang, "On the Asymptotic Growth of the Number of Tree-Child Networks", arXiv (2020): Corollary 1 (exponential growth rate), Lemma 6 (reduction formula), Proposition 6 (lower bound), Proposition 7 (upper bound), with Lemma 2, Proposition 2 (bijection with words) and Lemma 5 (crude bound on the word counts). <https://doi.org/10.48550/arXiv.2003.08049>
