# Exact p-value of the minimum hypergeometric score

**Setting.** Fix integers $N \ge 1$ and $0 \le B \le N$, and let $\Lambda = \{\lambda \in \{0,1\}^N : \sum_i \lambda_i = B\}$ be the set of binary label vectors over a ranked list of $N$ elements with exactly $B$ ones (for example, promoters ranked by a binding signal, labelled $1$ when they contain a motif). For $1 \le n \le N$ let $b_n(\lambda) = \sum_{i \le n} \lambda_i$ be the number of ones among the top $n$ elements, and let

$$\mathrm{HGT}(b; N, B, n) = \sum_{i = b}^{\min(n, B)} \frac{\binom{n}{i}\binom{N - n}{B - i}}{\binom{N}{B}}$$

be the hypergeometric upper tail. The **minimum hypergeometric (mHG) score** of $\lambda$ is

$$\mathrm{mHG}(\lambda) = \min_{1 \le n < N} \mathrm{HGT}\big(b_n(\lambda); N, B, n\big),$$

the enrichment at the most favourable cutoff of the ranked list.

**Proposition (lattice-path p-value).** Let $\lambda$ be uniform on $\Lambda$ and fix $p \in [0,1]$. Call a grid point $(n, b)$ with $1 \le n < N$ *rejecting* if $\mathrm{HGT}(b; N, B, n) \le p$, and let $R = R(p)$ be the set of rejecting points. Let $\Pi_R(n, b)$ be the number of monotone lattice paths from $(0,0)$ to $(n,b)$, with steps $(1,0)$ and $(1,1)$, that visit no point of $R$. Then

$$\Pr\big(\mathrm{mHG}(\lambda) \le p\big) = 1 - \frac{\Pi_R(N, B)}{\binom{N}{B}},$$

and $\Pi_R$ satisfies the recursion $\Pi_R(0,0) = 1$, $\Pi_R(n, b) = 0$ if $b < 0$, $b > n$ or $(n,b) \in R$, and otherwise

$$\Pi_R(n, b) = \Pi_R(n - 1, b) + \Pi_R(n - 1, b - 1).$$

Hence the exact p-value is computed with $O(NB)$ additions, with no simulation and no multiple-testing correction over cutoffs.

## Expansion

Map $\lambda$ to the path whose $i$-th step is $(1, \lambda_i)$; this is a bijection between $\Lambda$ and the $\binom{N}{B}$ paths from $(0,0)$ to $(N,B)$, and the path visits $(n, b_n(\lambda))$ after $n$ steps. By definition $\mathrm{mHG}(\lambda) \le p$ exactly when some visited point with $n < N$ is rejecting, so the complementary event is that the path avoids $R$. Counting avoiding paths by the last step gives the recursion, since a path reaching a non-rejecting $(n,b)$ arrives from $(n-1,b)$ or $(n-1,b-1)$ and every prefix of an avoiding path is avoiding. Because the cutoff is chosen to maximize enrichment, $\mathrm{mHG}(\lambda)$ itself is not a p-value; the recursion calibrates it exactly under the null that all label configurations with $B$ ones are equally likely. The source extends the score to occurrence counts (several motif copies per sequence) with a multidimensional hypergeometric model and uses the exact p-value to filter motif seeds.

## Sources

- E. Eden, D. Lipson, S. Yogev and Z. Yakhini, *Discovering motifs in ranked lists of DNA sequences*, PLoS Computational Biology (2007). <https://doi.org/10.1371/journal.pcbi.0030039> (PMCID: PMC1829477). Materials and Methods: "The minimum hypergeometric score", "Calculating the p-value of the mHG score" (Equation 4, Figure 8).
