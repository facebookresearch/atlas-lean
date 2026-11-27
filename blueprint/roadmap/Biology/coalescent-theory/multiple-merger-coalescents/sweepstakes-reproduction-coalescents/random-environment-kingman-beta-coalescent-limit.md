# Kingman–Beta coalescent limit of sweepstakes reproduction in a random environment

**Model.** A haploid population of size $N$ evolves by supercritical sampling: each of the $N$ individuals independently produces $X_i$ potential offspring and $N$ of them are sampled uniformly without replacement to form the next generation. For $a > 0$ and a cutoff $\zeta(N) \in \mathbb{N}$, write $X \rhd \mathbb{L}(a, \zeta(N))$ if $\mathbb{P}(X \le \zeta(N)) = 1$ and, for $k \in [\zeta(N)]$,

$$g_a(k)\left(k^{-a} - (k+1)^{-a}\right) \le \mathbb{P}(X = k) \le f_a(k)\left(k^{-a} - (k+1)^{-a}\right)$$

for positive functions $f_a, g_a$ on $\mathbb{N}$, so the offspring law is a truncated power law with index $a$. Assume $m_N = \mathbb{E}X_1 > 1$ for all $N$ with $m_N \to m_\infty$.

**Type A random environment.** Fix $0 < \alpha < 2 \le \kappa$ and $\varepsilon_N \in (0,1)$. Independently in each generation, with probability $\varepsilon_N$ all $X_i \rhd \mathbb{L}(\alpha, \zeta(N))$ (a *sweepstakes* generation), and otherwise all $X_i \rhd \mathbb{L}(\kappa, \zeta(N))$. Let $c_N$ be the pair-coalescence probability per generation and $\xi^{n,N}$ the ancestral partition process of $n$ sampled gene copies.

**Theorem.** Assume $\lim_k g_\alpha(k) = \lim_k f_\alpha(k) =: f_\alpha^{(\infty)}$ and $\inf_{i \ge 2} g_\kappa(i) = \sup_{i \ge 2} f_\kappa(i) =: \overline{f_\kappa}(2)$. Then $\{\xi^{n,N}(\lfloor t/c_N \rfloor)\}$ converges in finite-dimensional distributions as follows.
1. If $\zeta(N)/N \to 0$ and $1 \le \alpha < 2$, the limit is the Kingman coalescent.
2. If $1 \le \alpha < 2$, $\zeta(N)/N$ is bounded away from $0$ (with $\zeta(N)/N \to K \in (0,\infty)$ or $\to \infty$), and $\varepsilon_N = c N^{\alpha - 2}\left(\mathbf{1}\{\kappa > 2\} + \mathbf{1}\{\kappa = 2\}\log N\right)$ for a fixed $c > 0$, the limit is the $\Lambda$-coalescent with $\Lambda = C_\kappa\,\delta_0 + \frac{\alpha c f_\alpha^{(\infty)}}{m_\infty^{\alpha}}\,x^{1-\alpha}(1-x)^{\alpha-1}\mathbf{1}\{0 < x \le \gamma\}\,dx$, normalized to total mass $1$: a given group of $k \in \{2, \dots, n\}$ of $n$ blocks merges at rate

$$\lambda_{n,k} = \frac{\mathbf{1}\{k = 2\}\, C_\kappa + m_\infty^{-\alpha}\, \alpha c f_\alpha^{(\infty)}\, B(\gamma; k - \alpha, n - k + \alpha)}{C_\kappa + m_\infty^{-\alpha}\, \alpha c f_\alpha^{(\infty)}\, B(\gamma; 2 - \alpha, \alpha)},$$

where $B(p; a, b) = \int_0^p t^{a-1}(1-t)^{b-1}\,dt$ is the incomplete beta function,

$$\gamma = \frac{K}{m_\infty + K}\ \text{ if } \zeta(N)/N \to K, \qquad \gamma = 1\ \text{ if } \zeta(N)/N \to \infty,$$

$$C_\kappa = \frac{2\overline{f_\kappa}(2)}{m_\infty^2}\left(\mathbf{1}\{\kappa = 2\} + \mathbf{1}\{\kappa > 2\}\frac{c_\kappa}{2^\kappa(\kappa-2)(\kappa-1)}\right)$$

for a constant $c_\kappa > 0$ depending only on $\kappa$.

## Depends on

- [Coalescent limits of supercritical sampling with heavy-tailed potential offspring](supercritical-sampling-coalescent-limits.md)

## Proof idea

In an ordinary generation ($\kappa \ge 2$) families are small and only pairwise mergers occur, with probability of order $N^{-1}$ (or $N^{-1}\log N$ when $\kappa = 2$). In a sweepstakes generation one family can grab a fraction $X/(X + N m_\infty)$ of the next generation; the cutoff $\zeta(N) \approx K N$ caps that fraction at $\gamma = K/(m_\infty + K)$, which truncates the Beta density at $\gamma$. Choosing $\varepsilon_N$ so that sweepstakes generations contribute merger probability of the same order as ordinary ones balances the two, so both the Kingman atom $\delta_0$ and the truncated Beta part survive the time rescaling by $c_N$. If $\zeta(N) = o(N)$ no family is macroscopic and only the Kingman part remains.

## Sources

- B. Eldon, "Gene genealogies in haploid populations evolving according to sweepstakes reproduction", Bulletin of Mathematical Biology 88 (2026), article 166, <https://doi.org/10.1007/s11538-026-01736-x>. Numbering as in the preprint arXiv:2601.09537v2, <https://arxiv.org/abs/2601.09537v2>: Definition 3.3, Theorem 3.5 (Cases 1 and 2) and Eqs. (25)–(26).
