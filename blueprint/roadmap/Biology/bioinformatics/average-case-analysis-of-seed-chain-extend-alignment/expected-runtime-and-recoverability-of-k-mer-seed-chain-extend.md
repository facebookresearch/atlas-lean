# Expected runtime and recoverability of k-mer seed-chain-extend

**Model.** Let $S = x_1 \cdots x_{n+k-1}$ be a uniformly random string of i.i.d. letters over a DNA alphabet, and let $S'$ be its substring of length $m + k - 1$ starting at a fixed position, with each character independently substituted by a different letter with probability $\theta$ (no indels); $S$ and $S'$ contain $n$ and $m$ $k$-mers. Seed-chain-extend takes the $k$-mers as seeds, forms *anchors* (exact $k$-mer matches between $S'$ and $S$), computes an optimal *chain* (a maximum-score colinear set of anchors), and fills gaps between consecutive chained anchors by quadratic-time dynamic-programming *extension*. The *recoverability* of a chain is the fraction of homologous base pairs lying in regions the chain can align.

**Theorem.** Assume $\theta < 0.206$, set $\alpha = -\log_4(1 - \theta)$, choose $C > \frac{2}{1 - 2\alpha}$, and assume $m = \Omega(n^{2C\alpha + \epsilon})$ for some $\epsilon > 0$, with the longer string already seeded. Taking $k = C\log n$ and the chaining gap parameter as specified in the source,

- the expected extension time is $O(m\, n^{C\alpha}\log n)$;
- the expected optimal chaining time is $O(m\, n^{-C\alpha}\log m)$;
- the expected recoverability of any optimal chain is at least $1 - O(1/\sqrt m)$.

Since $C\alpha$ can be taken arbitrarily close to $\frac{2\alpha}{1 - 2\alpha} < 2.43\,\theta$, the total expected time is $O(m\, n^{2.43\theta}\log n)$: nearly $O(m \log n)$ for modest divergence, far below the $\Theta(mn)$ of full dynamic programming, while still recovering almost all homologous bases.

## Expansion

A homologous $k$-mer survives mutation with probability $(1-\theta)^k = n^{-C\alpha}$, so long anchor-free gaps are rare and extension of a gap of length $\ell$ costs $O(\ell^2)$; summing over the geometric-like gap distribution gives the $n^{C\alpha}$ factor. Spurious anchors arise from random $k$-mer matches with probability about $4^{-k} = n^{-C}$ per pair, which is negligible for $C$ large; second-moment bounds on the dependent sums of homologous and spurious anchor counts control both the chaining work and the chance that an optimal chain uses spurious anchors. The constraint $\theta < 0.206$ is equivalent to $\alpha < 1/6$, needed to make the conditions on $C$ compatible.

## Sources

- J. Shaw and Y. W. Yu, "Proving sequence aligners can guarantee accuracy in almost O(m log n) time through an average-case analysis of the seed-chain-extend heuristic", *Genome Research* (2023), Results (mutation model, modeling seed-chain-extend), Theorem 1 and its proof (Theorem 6, Corollary 3, Lemmas 7–9). <https://doi.org/10.1101/gr.277637.122> (PMC10538486)
