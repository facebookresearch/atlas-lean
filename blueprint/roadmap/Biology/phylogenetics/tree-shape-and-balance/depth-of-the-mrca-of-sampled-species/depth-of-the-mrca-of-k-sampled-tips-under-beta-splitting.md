# Depth of the MRCA of $k$ sampled tips under Aldous's $\beta$-splitting model

**Setting.** In Aldous's $\beta$-splitting model ($\beta > -2$) a rooted binary tree with $n$ labeled leaves is built recursively: a clade of $m$ leaves splits into subclades of sizes $i$ and $m - i$ with probability $\pi_{m,i} = \frac{1}{c_m(\beta)}\frac{\Gamma(i + \beta + 1)\Gamma(m - i + \beta + 1)}{i!\,(m-i)!}$, $1 \le i \le m-1$, where $c_m(\beta)$ normalizes. The value $\beta = 0$ is the Yule–Harding model, $\beta = -1$ is critical, and $\beta = -3/2$ is the uniform (PDA) model. Sample $k$ of the $n$ leaves uniformly without replacement and let $D_{n,k}$ be the number of edges between the root and the most recent common ancestor (MRCA) of the sample. Write $H_m = \sum_{i=1}^m 1/i$.

**Theorem (exact probability that the MRCA is the root).** For $2 \le k \le n$:
- if $\beta = -1$: $\mathbb{P}(D_{n,k} = 0) = H_{k-1}/H_{n-1}$, which tends to $0$ for fixed $k$ but to $\alpha$ when $k \sim n^\alpha$, $0 < \alpha \le 1$;
- if $\beta \ne -1$:

$$\mathbb{P}(D_{n,k} = 0) = 1 - \frac{2(\beta+1)\cdots(\beta+k)}{k!\binom nk}\cdot\frac{\binom{n+2\beta+1}{n-k} - \binom{n+\beta}{n-k}}{\binom{n+2\beta+1}{n} - 2\binom{n+\beta}{n}}.$$

**Theorem (limit laws for fixed $k \ge 2$).** As $n \to \infty$:
1. for $\beta > -1$, $D_{n,k}$ converges in distribution to a geometric variable, $\mathbb{P}(G_k = r) = (1-q)q^r$, $r \ge 0$, with

$$q = q(\beta,k) = \frac{(\beta+2)\cdots(\beta+k)}{(2\beta+3)\cdots(2\beta+k+1)} = \frac{2\Gamma(2\beta+2)\Gamma(\beta+k+1)}{\Gamma(\beta+1)\Gamma(2\beta+k+2)};$$

2. for $\beta = -1$, $H_{k-1}D_{n,k}/\log n \to \operatorname{Exp}(1)$;
3. for $\beta = -3/2$, $D_{n,k}/\sqrt{n} \to D_k$, the law determined by the moments $\mathbb{E}D_k^m = \dfrac{m!\,C_{k-1}4^{1-k}k!\sqrt{\pi}}{\Gamma(k + (m-1)/2)}$, with $C_{k-1}$ the Catalan number.

So for balanced trees ($\beta > -1$) the sample MRCA stays within $O(1)$ edges of the root, while for the more caterpillar-like shapes typical of real phylogenies it drifts down like $\log n$ or $\sqrt n$.

## Expansion

The MRCA is strictly below the root iff all $k$ sampled leaves fall in the same root subclade, so $\mathbb{P}(D_{n,k} \ge 1) = \sum_i p_n(i)\big[\binom ik + \binom{n-i}{k}\big]/\binom nk$ over the root split law $p_n$, which sums in closed form; iterating the split gives a recursion for the full law. For $\beta > -1$, the root split fraction converges to a Beta$(\beta+1,\beta+1)$ variable, and each step down has asymptotically the same chance $q(\beta,k) = 2\,\mathbb{E}[U^k]$, $U \sim$ Beta$(\beta+1,\beta+1)$, to keep all $k$ leaves together, giving a geometric limit. For $\beta = -1$ and $\beta = -3/2$ the splits are typically very unbalanced, and singularity analysis of the generating functions of factorial moments (a $\log$ singularity, respectively a square-root singularity at $z = 1/4$) gives the exponential and moment-determined limits.

## Sources

- M. Fuchs and M. Steel, "Predicting the depth of the most recent common ancestor of a random sample of $k$ species: the impact of phylogenetic tree shape", *Journal of Mathematical Biology* 92(2) (2026), 24, Theorems 1, 2, 9, 12, Corollaries 5, 6 and Proposition 14, <https://doi.org/10.1007/s00285-025-02337-3> (preprint arXiv:2501.09270).
- D. Aldous, "Probability distributions on cladograms", in Random Discrete Structures, IMA Volumes in Mathematics and its Applications 76 (1996).
