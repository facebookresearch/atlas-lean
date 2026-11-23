# The $p$-equivalence class sum

Let $\sigma$ be a finite set of variables, let $p$ be a
natural number and let $\lambda$ be a multiset of natural numbers whose elements sum to $n$. In
$\mathbb{Q}[x_i : i \in \sigma]$ let $p_k = \sum_{i \in \sigma} x_i^k$ be the $k$-th power sum. For
a partition $\mu$ of $n$ with parts $\mu_1, \dots, \mu_\ell$, write
$p_\mu = p_{\mu_1} \cdots p_{\mu_\ell}$, $\varepsilon_\mu = (-1)^{n - \ell}$ and
$z_\mu = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts of $\mu$ equal to $a$ and the
product runs over the distinct parts $a$ of $\mu$. The $p$-equivalence class sum of $\lambda$ is

$$g_\lambda = \sum_{\mu \in C_\lambda} \frac{\varepsilon_\mu}{z_\mu} \, p_\mu,$$

where $C_\lambda$ is the $p$-equivalence class of $\lambda$: the set of partitions of $n$ that are
$p$-equivalent to $\lambda$.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Section 5.2, display (8).
