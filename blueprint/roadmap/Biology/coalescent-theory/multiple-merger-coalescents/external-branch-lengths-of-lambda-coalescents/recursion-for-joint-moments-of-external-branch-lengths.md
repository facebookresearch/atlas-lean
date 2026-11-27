# Recursion for joint moments of external branch lengths

**Setting.** Let $\Lambda$ be a finite measure on $[0,1]$ and $\Pi^{(n)}$ the $\Lambda$-coalescent started from $n$ singletons. Its block-counting process jumps from $n$ to $m < n$ blocks at rate

$$ g_{nm} = \binom{n}{m-1}\int_{[0,1]} x^{n-m-1}(1-x)^{m-1}\,\Lambda(dx), $$

with total rate

$$ g_n = \sum_{m=1}^{n-1} g_{nm} = \int_{[0,1]} \frac{1-(1-x)^n - nx(1-x)^{n-1}}{x^2}\,\Lambda(dx), $$

and $p_{nm} = g_{nm}/g_n$. For $i = 1, \dots, n$, let $\tau_{n,i}$ be the length of the external branch ending in leaf $i$, i.e. the time at which $\{i\}$ first merges with another block. For $j \in \{1,\dots,n\}$ and $k = (k_1,\dots,k_j) \in \mathbb N^j$ write $\mu_n(k) = \mathbb E\big[\tau_{n,1}^{k_1}\cdots\tau_{n,j}^{k_j}\big]$ and $(x)_j = x(x-1)\cdots(x-j+1)$.

**Theorem.** For all $n \ge 2$, $j \in \{1, \dots, n\}$ and $k \in \mathbb N^j$,

$$ \mu_n(k) = \frac{1}{g_n}\sum_{i=1}^{j} k_i\,\mu_n(k - e_i) + \sum_{m=j+1}^{n-1} p_{nm}\,\frac{(m-1)_j}{(n)_j}\,\mu_m(k), $$

where $e_i$ is the $i$-th unit vector (a coordinate of $k - e_i$ equal to $0$ means that branch is omitted). Together with $\mu_n(0) = 1$ this determines all joint moments recursively in $n$ and $|k|$.

## Expansion

Condition on the first jump, which occurs after an exponential time $T$ with rate $g_n$ and takes the process to $m$ blocks with probability $p_{nm}$. All $j$ tagged external branches survive the first merger exactly when the merging set of $n-m+1$ blocks avoids the $j$ tagged leaves; by exchangeability this has probability $\binom{n-j}{n-m+1}/\binom{n}{n-m+1} = (m-1)_j/(n)_j$, in which case the surviving tagged branches continue as external branches of an $m$-block coalescent and $\tau_{n,i} = T + \tau'_{m,i}$; if any tagged leaf is involved, its branch ends at $T$. Expanding $\prod_i (T + \tau'_{m,i})^{k_i}$ and using the memorylessness of $T$ (via integration by parts, $\mathbb E[T^{\ell}] = \ell\,\mathbb E[T^{\ell-1}]/g_n$) collapses the binomial expansions into the displayed first-order recursion. The case $j = 1$, $k = 1$ recovers the known recursion for the expected external branch length.

## Sources

- Jean-Stéphane Dhersin, Martin Möhle, "On the external branches of coalescents with multiple collisions", *Electronic Journal of Probability* 18 (2013), <https://doi.org/10.1214/EJP.v18-2286>; preprint arXiv:1209.3380, <https://doi.org/10.48550/arXiv.1209.3380>. Numbering of the arXiv version: Section 1 (rates (1)–(2), Theorem 1.1), Section 2 (proof of Theorem 1.1).
