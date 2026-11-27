# Tree height of multinomial-resampling particle genealogies

Consider sequential Monte Carlo with $N$ particles and multinomial resampling whose potentials satisfy $a^{-1} \le g_t \le a$ and whose mutation kernels satisfy $\varepsilon h(x') \le q_t(x,x') \le \varepsilon^{-1}h(x')$ for constants $0 < \varepsilon \le 1 \le a$, so that genealogies of $n$ sampled particles converge to Kingman's $n$-coalescent under the time change $\tau_N$. Let $T_n$ be the time to the most recent common ancestor of Kingman's $n$-coalescent, so that $\tau_N(T_n)$ is the number of generations back to the common ancestor of the $n$ particles.

**Theorem.** For every $1 \le n \le N$ and any coupling of $(\tau_N, T_n)$,

$$\frac{2\varepsilon^4 N}{a^4}\Big(1 - \frac1n\Big) \le \mathbb{E}[\tau_N(T_n)] \le \frac{2a^4 N}{\varepsilon^4}\Big(1 - \frac1n\Big) + \frac{a^8}{\varepsilon^4},$$

$$\frac{N^2\varepsilon^8}{a^8}\Big(\frac{4\pi^2}{3} - 12 + O(n^{-1})\Big) \le \operatorname{Var}(\tau_N(T_n)) \le \frac{N^2 a^8}{\varepsilon^8}\Big(\frac{4\pi^2}{3} - 12 + O(n^{-1})\Big) + O(N).$$

So the genealogy of an SMC run has height of order $N$ generations, with constants controlled by how far the weights and kernels are from uniform.

## Depends on

- [Kingman limit of genealogies of weighted resampling particle systems](kingman-limit-of-genealogies-of-weighted-resampling-particle-systems.md)
- [Variance of the time to the most recent common ancestor](../../kingman-s-coalescent-and-watterson-s-estimator/variance-tmrca.md)

## Expansion

Kingman's $n$-coalescent has $\mathbb{E}[T_n] = 2(1 - 1/n)$ and $\operatorname{Var}(T_n) = \sum_{k=2}^n \binom{k}{2}^{-2} \to \frac{4\pi^2}{3} - 12$. Under the bounded-weight and mixing conditions the conditional pair-merger probability satisfies $\varepsilon^4/(a^4 N) \lesssim \mathbb{E}[c_N(t)\mid\mathcal{F}_{t-1}] \lesssim a^4/(\varepsilon^4 N)$, so the time change $\tau_N$ converts one unit of coalescent time into between $\varepsilon^4 N/a^4$ and $a^4 N/\varepsilon^4$ generations, which transfers the moments of $T_n$ to $\tau_N(T_n)$ up to these factors.

## Sources

- Jere Koskela, Paul A. Jenkins, Adam M. Johansen and Dario Spanò, *Asymptotic genealogies of interacting particle systems with an application to sequential Monte Carlo*, Ann. Statist. 48(1) (2020), 560–583. <https://doi.org/10.1214/19-AOS1823> Lemma 3, Corollary 1, Corollary 2. Erratum: Ann. Statist. 50(4) (2022), 2467–2468. <https://doi.org/10.1214/21-AOS2135> Locators use the numbering of the preprint arXiv:1804.01811. Its latest version includes the corrected argument.
