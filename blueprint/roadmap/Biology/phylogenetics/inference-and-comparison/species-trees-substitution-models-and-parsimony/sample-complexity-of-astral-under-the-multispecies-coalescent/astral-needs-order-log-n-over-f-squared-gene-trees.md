# ASTRAL needs order log n over f squared gene trees

Let a rooted species tree on $n$ leaves have shortest internal branch length $f$ (in coalescent units), and let $m$ unrooted gene trees be drawn independently under the multispecies coalescent and observed without error. **ASTRAL\*** is the exact version of ASTRAL: it returns an unrooted species tree maximizing the total number of gene-tree quartets it displays (the sum, over all $\binom{n}{4}$ four-taxon subsets, of the number of gene trees whose induced quartet agrees with it).

**Theorem.**

1. (Upper bound) If $f < \log\sqrt2$, then for every $\epsilon > 0$ ASTRAL\* returns the true species tree with probability at least $1 - \epsilon$ whenever

$$m > \frac{9}{2}\,\log\!\Big(\frac{4\binom{n}{4}}{\epsilon}\Big)\,\frac{1}{(1 - e^{-f})^2}.$$

2. (Lower bound, four taxa) For $n = 4$ and internal branch length $f$: for every $\epsilon \in [0, 1/2)$ there are $f_0 > 0$ and $d_\epsilon$ such that for all $f \le f_0$ and $m \le d_\epsilon/f^2$, ASTRAL\* outputs the wrong quartet with probability at least $\epsilon$.
3. (Lower bound, many taxa) For every $\rho, a \in (0,1)$ there are $f_0, n_0$ such that for all $n \ge n_0$ and $f \le f_0$ there is a species tree with $n$ leaves and shortest branch $f$ for which ASTRAL\* with $m \le \frac{a}{5}\,\frac{\log n}{f^2}$ gene trees reconstructs the wrong tree with probability at least $1 - \rho$.

Since $1 - e^{-f} \approx f$ for small $f$, the number of genes needed is $\Theta(f^{-2}\log n)$.

## Expansion

Under the multispecies coalescent the gene quartet matching the species quartet has probability $1 - \tfrac23 e^{-f_q}$ and each of the two alternatives $\tfrac13 e^{-f_q}$, where $f_q$ is the length of the quartet's internal path, so the gap between the true and each wrong quartet is $1 - e^{-f_q} \ge 1 - e^{-f}$. Hoeffding's inequality and a union bound over the $\binom{n}{4}$ quartets give the upper bound: with that many genes every quartet's empirical frequencies are within the needed margin, and a combinatorial argument over the bipartitions near each short branch shows the quartet-score maximizer is then the true tree. The four-taxon lower bound is the anti-concentration of a binomial whose mean gap $\Theta(f)$ is smaller than its standard deviation $\Theta(m^{-1/2})$. For many taxa, a caterpillar-like tree contains $\Theta(n)$ nearly independent short-branch quartets, and the maximum of that many weakly correlated fluctuations forces $m = \Omega(f^{-2}\log n)$.

## Sources

- Shubhanshu Shekhar, Sebastien Roch, Siavash Mirarab, "Species Tree Estimation Using ASTRAL: How Many Genes Are Enough?", IEEE/ACM Transactions on Computational Biology and Bioinformatics 15 (2018), 1738–1747, <https://doi.org/10.1109/tcbb.2017.2757930>. Published version of arXiv:1704.06831, cited next; locators there refer to the arXiv version.
- Shubhanshu Shekhar, Sebastien Roch, Siavash Mirarab, "Species tree estimation using ASTRAL: how many genes are enough?", arXiv (2017). Theorem 2.1, Theorem 2.2, Theorem 2.3, Lemmas A.1–A.2. <https://doi.org/10.48550/arXiv.1704.06831>
