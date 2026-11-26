# Excursion decomposition of allelic replacement in the Moran model

**Setting.** Let $X^N$ be the continuous-time two-allele Moran model with recurrent mutation on $\{0,\dots,N\}$: a birth–death chain with up-rates $\lambda_i$, down-rates $\mu_i$, reversible stationary law $\pi=\mathrm{BetaBin}(N,a_N,b_N)$ and scale function

$$s^{(N)}_0=0,\qquad s^{(N)}_n=\sum_{k=0}^{n-1}\frac1{\pi_k\lambda_k}\quad(1\le n\le N).$$

From a boundary state $b\in\{0,N\}$ (one allele fixed), the path splits into *excursions* away from $b$, indexed by local time at $b$. An excursion from $0$ is *returning* if it comes back to $0$ before reaching $N$ (an unsuccessful invasion of allele $A$) and *switching* if it reaches $N$ first (a population-wide replacement).

**Theorem (excursion point process).** Started at $b$, the excursions form a Poisson point process on $\mathbb R_+\times\mathcal U^b_N$ with intensity $d\ell\otimes n^b_N$, where the excursion measure $n^b_N$ has finite-dimensional distributions given by an entrance law $(\nu^b_{N,t})$ of the chain killed at $\{0,N\}$, $\nu^b_{N,t}P^{N,\circ}_s=\nu^b_{N,t+s}$.

**Corollary (switching intensity).** The two switching intensities coincide:

$$n^0_N\big(\mathcal U^0_{N,\mathrm{switch}}\big)=n^N_N\big(\mathcal U^N_{N,\mathrm{switch}}\big)=\Big(\sum_{k=0}^{N-1}\frac1{\lambda_k\pi_k}\Big)^{-1}=\frac1{s^{(N)}_N}.$$

**Proposition (failed invasions before replacement).** Let $\mu^0_N$ be the law of one excursion from $0$, let $K_N$ be the number of returning excursions before the first switching one, and $\xi_1,\dots,\xi_{K_N+1}$ the successive excursions. For bounded functionals $g,h$ with $|\mathcal F_N[g]|<1$, where $\mathcal F_N[g]=\int_{\text{return}}g\,d\mu^0_N$ and $\mathcal S_N[h]=\int_{\text{switch}}h\,d\mu^0_N$,

$$\mathbb E_0\Big[h(\xi_{K_N+1})\prod_{r=1}^{K_N}g(\xi_r)\Big]=\frac{\mathcal S_N[h]}{1-\mathcal F_N[g]}.$$

In particular ($g\equiv z$, $h\equiv1$) $K_N$ is geometric with success probability $\mathcal S_N[1]=\mathbb P_1(\tau_N<\tau_0)=s^{(N)}_1/s^{(N)}_N$, and joint Laplace transforms of the number, heights and durations of failed invasions follow by choosing $g(\xi)=z^{\max\xi}e^{-\psi\zeta(\xi)}$.

## Depends on

- [Pure-death duality and spectral transition probabilities of the Moran model with mutation](pure-death-duality-and-spectral-transition-probabilities-of-the-moran-model-with-mutation.md)

## Expansion

Because $X^N$ is a birth–death chain, every excursion from $0$ starts with a mutation $0\to1$ and its fate is decided by the gambler's-ruin probabilities $(s_i-s_0)/(s_N-s_0)$ of the scale function. Itô's excursion theory turns the strong Markov property at returns to the boundary into independence of successive invasion attempts, giving the renewal identity above. The equality of the two switching intensities expresses reversibility: in stationarity the flux of replacements $a\to A$ equals that of $A\to a$, and $1/s^{(N)}_N$ is the inverse of the total "resistance" of the chain between the two boundaries. Killed Green functions $G^{N,(a,b)}_0(i,j)=(s_{i\wedge j}-s_a)(s_b-s_{i\vee j})/(s_b-s_a)$ give expected occupation times during an excursion, and under Doob $h$-transforms the excursion measures restricted to excursions above a fixed height converge, after rescaling, to their Wright–Fisher diffusion counterparts.

## Sources

- J. Sant, I. Valentić, "From invasion to replacement: excursions of the Moran model", arXiv:2611.31663 (2026), Corollary 1, Theorem 3, Proposition 5, Corollary 2 and Proposition 6 (Sections 3–5), <https://doi.org/10.48550/arXiv.2611.31663>.
