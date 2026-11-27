# Sequence length sufficient to reconstruct level-1 networks under the CFN model

**CFN model on a network.** Let $N$ be a binary rooted phylogenetic level-1 network on $n$ taxa. Each site evolves on a displayed tree chosen by picking, independently at every reticulation, an incoming edge $e$ with inheritance probability $\gamma(e) \in (0,1)$; along the chosen tree the binary state flips across each non-reticulation edge $e$ with probability $p(e) \in (0, \tfrac12)$, with a uniform root state (Cavender-Farris-Neyman model). Write $\theta(e) = 1 - 2p(e)$. On a tree path with edges $e_1,\dots,e_m$ the endpoints differ with probability $\tfrac12\big(1 - \prod_i \theta(e_i)\big)$.

**Network parameters.** $\mathrm{depth}(N)$ is the largest, over displayed trees $T$ and edges $e = (v_1,v_2)$ of $T$, of the shortest topological distance from $v_i$ to a leaf after deleting $e$; $lc(N)$ is the maximum cycle length. Let $\gamma_{\min}$, $\gamma_{\max}$ be the extreme inheritance probabilities. For each reticulation edge $e$ put $g(e)=\frac{\gamma(e)}{1-\gamma(e)}\cdot\frac{\log\min_{e'}\theta(e')}{\log\max_{e'}\theta(e')}>0$ and define $s(e)>\tfrac12$ by

$$g(e)+\epsilon=\begin{cases}\dfrac{2s(e)^2-7s(e)}{2s(e)^2+s(e)-1}&\text{if }g(e)<1,\\[2ex]\dfrac{4s(e)^3+4s(e)^2-s(e)-1}{12s(e)^2+4s(e)+1}&\text{otherwise,}\end{cases}$$

for a fixed sufficiently small $\epsilon>0$; $s_{\max}$ is the largest value of $s$ over the reticulation edges. It grows as the inheritance probabilities approach $0$ or $1$.

**Dyadic closure method.** From $k$ aligned sites compute pairwise Hamming dissimilarities $h^{ij}$ and transform them to $d_{ij}=-\tfrac12\log(1-2h^{ij})$; for a width threshold $w$, run the *L1QPC* rule on every four-taxon set $\{x_i,x_j,x_k,x_l\}$ whose pairwise dissimilarities are all at most $w$, labelled so that $d_{ij}+d_{kl}\le d_{il}+d_{jk}\le d_{ik}+d_{jl}$: with $\Delta_1=(d_{il}+d_{jk})-(d_{ij}+d_{kl})$ and $\Delta_2=(d_{ik}+d_{jl})-(d_{il}+d_{jk})$, output all three trivial quartet profiles if $\Delta_1=\Delta_2$, the quartet tree $x_ix_j|x_kx_l$ if $\Delta_1>\Delta_2$, and the 4-cycle profile $(x_ix_jx_kx_l)$ if $\Delta_1<\Delta_2$; apply the dyadic closure; and, over thresholds $w$ ranging through the observed dissimilarities, return the network built from a closure that is complete and consistent, which is $\overline N$ (the network with 2-cycles, 3-cycles and the reticulation vertices of 4-cycles suppressed, which is all quartet profiles can determine).

**Theorem (Section 5).** If $k$ sites evolve under the CFN model on $N$, the dyadic closure method returns $\overline N$ with probability $1 - o(1)$ provided

$$k > \frac{c \log n}{\Big(1 - \max_{e} \theta(e)^{\min\{\gamma_{\min},\, 1-\gamma_{\max}\}/s_{\max}}\Big)^2 \Big(\min_{e} \theta(e)\Big)^{2(\mathrm{depth}(N) + lc(N))}}$$

for a fixed constant $c$.

**Corollary (Section 5).** With fixed inheritance probabilities, mutation probabilities bounded away from $0$ and $\tfrac12$ by constants, bounded cycle length and $\mathrm{depth}(N) = O(\log\log n)$, a polylogarithmic sequence length $k = \mathrm{polylog}(n)$ suffices. If $\mathrm{depth}(N)$ and $lc(N)$ are bounded, $k = O(\log n)$ suffices; if they grow logarithmically, a polynomial length suffices.

## Expansion

The proof follows the short-quartet strategy for trees: by the dyadic closure theorem, it suffices that some width $w$ yields a quartet set containing all representative quartet profiles and only correct profiles. Every representative profile spans leaves at topological distance at most $\mathrm{depth}(N) + lc(N)$, so its true pairwise dissimilarities are bounded away from $\tfrac12$ by $\tfrac12 \min_e \theta(e)^{\mathrm{depth}(N)+lc(N)}$. Azuma-Hoeffding concentration of the empirical dissimilarities, applied with $k$ of the stated order, makes all $O(n^4)$ relevant estimates accurate simultaneously with probability $1-o(1)$. For a 4-cycle quartet the expected distance matrix is the mixture $\gamma D(T_1) + (1-\gamma) D(T_2)$ of the two displayed trees' matrices, and Lemma 5.1 shows the profile $(abcd)$ is recovered when $\gamma$ is far enough from $0$ and $1$ relative to the edge parameters, which produces the inheritance-probability factor in the bound. For trees ($lc = 0$, no reticulations) the bound reduces to the classical $c \log n / \big((1-\max\theta)^2 (\min\theta)^{\mathrm{depth}(T)}\big)$ order of the short-quartet method.

## Depends on

- [Dyadic closure of level-1 quartet profiles](dyadic-closure-of-level-1-quartet-profiles.md)

## Sources

- M. Frohn, N. Holtgrefe, L. van Iersel, M. Jones, "Bounds on the sequence length sufficient to reconstruct binary level-1 phylogenetic networks under the CFN model", *Annals of Combinatorics* (2026), Section 2 (CFN model, path lemma, depth and cycle length), Section 4 (dyadic closure network construction and width of a quartet), Section 5 (Lemma 5.1, main sequence-length theorem and polylogarithmic corollary), Tables 1 and 2, <https://doi.org/10.1007/s00026-026-00830-0> (preprint arXiv:2511.22736).
