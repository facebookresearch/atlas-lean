# Diploid sweepstakes coalescent in a random environment

**Model.** A diploid panmictic population of $N$ individuals forms monogamous parent pairs (no selfing) each generation. Each pair independently produces $X$ potential diploid offspring; each offspring inherits one uniformly chosen chromosome from each parent, and $2N$ chromosome copies (that is, $N$ individuals) are drawn without replacement from the potential offspring. Write $X \rhd \mathbb L(a, \zeta(N))$ if for $k \in \{2, \dots, \zeta(N)\}$
$$g_a(k)\bigl(k^{-a} - (k+1)^{-a}\bigr) \le \mathbb P(X = k) \le f_a(k)\bigl(k^{-a} - (k+1)^{-a}\bigr)$$
with the remaining mass on $\{0,1\}$, and assume $\mathbb E[X] \to m_\infty > 2$. In each generation, independently, all pairs use $\mathbb L(\alpha, \zeta(N))$ with probability $\varepsilon_N$ (a sweepstakes generation, $0 < \alpha < 2$) and $\mathbb L(\kappa, \zeta(N))$ with $\kappa \ge 2$ otherwise. Let $\xi^{n,N}$ be the ancestral process of $n$ sampled diploid individuals ($2n$ gene copies) and $c_N$ the pairwise coalescence probability per generation.

**Theorem.** As $N \to \infty$, $\{\xi^{n,N}(\lfloor t/c_N \rfloor)\}_{t \ge 0}$ converges in finite-dimensional distributions (and, after completing dispersed lineages, weakly in Skorokhod space) to a coalescent $\xi^n$, where for $1 \le \alpha < 2$ one takes $\varepsilon_N = c\,N^{\alpha - 2}(\mathbf 1_{\kappa > 2} + \mathbf 1_{\kappa = 2} \log N)$:
1. $\xi^n$ is the Kingman coalescent if either $0 < \alpha < 1$, $\zeta(N)^{3-\alpha}/N^2 \to 0$ and $\limsup \varepsilon_N / c_N < \infty$; or $1 \le \alpha < 2$ and $\zeta(N)/N \to 0$.
2. If $1 \le \alpha < 2$ and $\zeta(N)/N \to K \in (0, \infty]$, then $\xi^n$ is an $\Omega$-$\delta_0$-Beta$(\gamma, 2 - \alpha, \alpha)$ $\Xi$-coalescent with $\gamma = K/(K + m_\infty)$ (and $\gamma = 1$ if $K = \infty$): from $n$ blocks, $r \in \{1,2,3,4\}$ simultaneous mergers of sizes $k_1, \dots, k_r$ ($k = \sum k_i$, $s = n - k$) occur at rate
$$\lambda_{n;\mathbf k;s} = \mathbf 1_{\{r = 1, k_1 = 2\}} \frac{C_\kappa}{C_{\alpha,\gamma}} + \frac{\alpha c f^{(\infty)}_\alpha}{C_{\alpha,\gamma}\, m_\infty^{\alpha}} \sum_{\ell = 0}^{s \wedge (4 - r)} \binom{s}{\ell} \frac{(4)_{r+\ell}}{4^{k+\ell}} \int_0^\gamma x^{k + \ell - \alpha - 1}(1 - x)^{n - k - \ell + \alpha - 1}\, dx,$$
with explicit normalising constants $C_\kappa$, $C_{\alpha,\gamma} = C_\kappa + \frac{\alpha c f^{(\infty)}_\alpha}{4 m_\infty^\alpha} B(\gamma, 2-\alpha, \alpha)$, where $B(\gamma, a, b)$ is the incomplete beta integral.

Moreover, for any positive function $v$ on $[0, \infty)$ there are deterministically varying population sizes for which the limit is the corresponding time-changed $\Xi$-coalescent.

## Depends on

- [Cannings model of a haploid population](../multiple-merger-coalescents/cannings-models/cannings-model.md)

## Expansion

In a sweepstakes generation a single parent pair may produce a fraction $x$ of the next generation, with $x$ asymptotically distributed as Beta$(2 - \alpha, \alpha)$ truncated at $\gamma$, the truncation coming from the cap $\zeta(N)$ on litter size relative to the mean output $m_\infty N$. Lineages descending from that pair are distributed uniformly among the pair's four chromosomes, which is why up to four groups merge simultaneously and the factor $(4)_{r+\ell}/4^{k+\ell}$ appears. Ordinary generations contribute Kingman pair mergers through $C_\kappa$. Kingman behaviour survives when the cap or the sweepstakes frequency is too small for large litters to register on the coalescent time scale $1/c_N$.

## Sources

- B. Eldon, "Gene genealogies in diploid populations evolving according to sweepstakes reproduction", arXiv:2601.10364 (2026), Definitions of the diploid population and the random environment, Theorems 1 and 3, Corollary 3.13, <https://doi.org/10.48550/arXiv.2601.10364>.
