# Counting one-component d-combining tree-child networks

**Setting.** A rooted phylogenetic network with $n$ labeled leaves is *$d$-combining* ($d \ge 2$) if every internal vertex is either a tree vertex (indegree $1$, outdegree $2$) or a reticulation (indegree $d$, outdegree $1$); $d = 2$ is the usual bicombining case. It is *tree-child* if every non-leaf vertex has a child that is not a reticulation, and *one-component* if every reticulation is immediately followed by a leaf. By the handshake lemma a network with $k$ reticulations has $n + (d-1)k - 1$ tree vertices and $2n + dk$ vertices in total.

**Theorem (exact count).** The number of one-component $d$-combining tree-child networks with $n$ leaves and $k$ reticulations, $0 \le k \le n-1$, is

$$\mathrm{OTC}^{(d)}_{n,k} = \binom{n}{k}\,\frac{(2n + (d-2)k - 2)!}{(d!)^k\,2^{\,n-k-1}\,(n-k-1)!}.$$

**Theorem (asymptotics of $\mathrm{OTC}^{(d)}_n = \sum_k \mathrm{OTC}^{(d)}_{n,k}$).**

1. $d = 2$: $\displaystyle \mathrm{OTC}^{(2)}_n \sim \frac{1}{4\pi\sqrt{e}}\,(n!)^2\,2^n\,e^{2\sqrt n}\,n^{-9/4}$ (a stretched exponential).
2. $d = 3$: $\displaystyle \mathrm{OTC}^{(3)}_n \sim I_1(2)\,\mathrm{OTC}^{(3)}_{n,n-1} \sim \frac{I_1(2)\sqrt3}{9\pi}\,(n!)^3\Big(\frac92\Big)^n n^{-3}$, with $I_1$ the modified Bessel function of the first kind.
3. $d \ge 4$: $\displaystyle \mathrm{OTC}^{(d)}_n \sim \mathrm{OTC}^{(d)}_{n,n-1} \sim \frac{d!}{d^{\,d-1/2}(2\pi)^{(d-1)/2}}\,(n!)^d\Big(\frac{d^d}{d!}\Big)^n n^{3(1-d)/2}$.

**Theorem (number of reticulations).** Let $R^{(d)}_n$ be the number of reticulations of a uniformly random one-component $d$-combining tree-child network with $n$ leaves. Then

- $d = 2$: $\big(R^{(2)}_n - n + \sqrt n\big)/(n/4)^{1/4} \to N(0,1)$ in distribution;
- $d = 3$: $n - 1 - R^{(3)}_n \to \mathrm{Bessel}(1,2)$, i.e. $\mathbb{P}(\,\cdot = k) = \dfrac{1}{I_1(2)\,k!\,(k+1)!}$;
- $d \ge 4$: $n - 1 - R^{(d)}_n \to 0$ in distribution.

**Sackin index.** With $S$ the Sackin index (sum over leaves of the longest root-to-leaf path length), a uniformly random one-component network has $\mathbb{E}(S^{(2)}_n) = \Theta(n^{7/4})$ and $\mathbb{E}(S^{(d)}_n) = \Theta(n^2)$ for $d \ge 3$.

## Expansion

Combinatorially, a one-component network is a phylogenetic tree with $n-k$ leaves in which $k$ of the leaf-attaching positions are replaced by reticulations with a pendant leaf, whose $d$ incoming arcs are inserted into edges of the tree; counting the ways to choose the reticulated leaves ($\binom nk$), the underlying tree, and ordered insertions of the $dk$ reticulation arcs (divided by $d!$ for each reticulation) gives the closed form. Asymptotically, comparing $\mathrm{OTC}^{(d)}_{n,n-1-j}$ with $\mathrm{OTC}^{(d)}_{n,n-1}$ via the closed form: for $d \ge 4$ only $j = 0$ survives, for $d = 3$ the ratios converge to $1/(j!(j+1)!)$, whose sum is $I_1(2)$, and for $d = 2$ the dominant $j$ is of order $\sqrt n$, producing the factor $e^{2\sqrt n}$ and the Gaussian fluctuations.

## Sources

- Yu-Sheng Chang, Michael Fuchs, Hexuan Liu, Michael Wallner and Guan-Ru Yu, "Enumerative and distributional results for d-combining tree-child networks", arXiv:2209.03850 (2022), Definitions 1.1–1.4, Theorems 1.5–1.6 and Section 2 (Theorem 2.1, Lemma 2.4, Proposition 2.5, Proposition 2.8, Theorem 2.10), <https://doi.org/10.48550/arXiv.2209.03850>. Published version: Advances in Applied Mathematics 157 (2024) 102704, <https://doi.org/10.1016/j.aam.2024.102704>.
