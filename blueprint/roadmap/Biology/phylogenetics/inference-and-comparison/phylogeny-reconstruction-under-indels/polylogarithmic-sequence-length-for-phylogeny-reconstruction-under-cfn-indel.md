# Polylogarithmic sequence length for phylogeny reconstruction under the CFN-indel model

**Model (CFN-Indel).** A rooted binary model tree $T$ with $n$ leaves carries a uniformly random bitstring of length $k$ at the root. Along each edge $e$, independently for every bit and simultaneously:

- the bit is flipped with probability $p_S(e)$ (substitution);
- the bit is deleted with probability $p_D(e)$;
- a uniformly random new bit is inserted to its right with probability $p_I(e)$.

The data are the (unaligned) bitstrings at the leaves. Define the edge length

$$\lambda(e) = -\Big[\ln\big(1 - 2p_S(e)\big) + \ln\big(1 - p_D(e)\big) - \tfrac12\ln\big(1 + p_I(e) - p_D(e)\big)\Big] \ge 0,$$

and assume the $\Delta$-branch model: $\lambda(e)$ is an integer multiple of $\lambda_{\min}$, with $\lambda_{\min} \le \lambda(e) < \lambda_{\max}$.

**Theorem (symmetric case).** Suppose $T$ is balanced, $p_I(e) = p_D(e)$ for all $e$, $\lambda_{\max} \le \ln\sqrt2$ (below the Kesten–Stigum threshold) and $\lambda_{\min} = \Omega(1/\mathrm{polylog}\,n)$. Then for a sufficiently large constant $\kappa$, root sequence length $k = O(\log^\kappa n)$ suffices for an algorithm (TreeReconstruct) to recover $T$ with high probability. In particular the substitution and indel probabilities may all be constants.

**Theorem (asymmetric case).** Let $h$ be the maximum depth of $T$. If $h \le \log^\alpha n$ and $|p_I(e) - p_D(e)| \le \beta\log\log n/h$ for constants $\alpha, \beta$, with the same bounds on $\lambda$, then root length $O(\log^\kappa n)$ suffices for a sufficiently large $\kappa = \kappa(\alpha,\beta)$. This drift allowance is optimal up to constants: if deletions exceed insertions by $\kappa\log\log n/h$ on every edge, leaf strings are nearly empty with high probability.

Previous indel-tolerant reconstructions needed either polynomial sequence length or vanishing indel rates; here both the sequence length matches the substitution-only Kesten–Stigum regime up to the polylog exponent and indel rates are constant.

## Expansion

Indels destroy alignment, so instead of site-wise comparisons each sequence is summarized by a **signature**: split it into $L \approx k^{1/2-\zeta}$ consecutive blocks of length $l \approx k^{1/2+\zeta}$ and record each block's centered bit sum, $s_{a,i} = \Delta_{a,i}/\sqrt l$. A single indel shifts block boundaries by one site, perturbing every block slightly but none much, so signatures of nodes at distance $d$ have correlation about $\frac14 e^{-d}$ up to $\mathrm{polylog}$ corrections. Ancestral signatures are reconstructed recursively by averaging children's signatures; below the Kesten–Stigum threshold ($2e^{-2\lambda_{\max}} \ge 1$) the number of descendants grows faster than correlations decay, keeping the estimator's variance bounded, and indel-induced shift noise is controlled by concentration of sequence lengths along each path. Distances estimated as $-\ln(4\langle s_u, s_v\rangle)$ concentrate for nearby nodes, which feeds a standard short-quartet distance-based tree builder.

## Sources

- Arun Ganesh and Qiuyi Zhang, "Optimal sequence length requirements for phylogenetic tree reconstruction with indels", Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing (2019), 721–732, <https://doi.org/10.1145/3313276.3316345>; numbering as in arXiv:1811.01121: Preliminaries (CFN-Indel model, edge length, signatures, and the main theorems for the symmetric and asymmetric cases) and the section "Asymmetric Probabilities".
