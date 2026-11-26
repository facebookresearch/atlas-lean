# Central limit theorem for the final size of a household epidemic with general contact numbers

**Model $\mathcal{E}_{n,h}(X_G,X_L)$.** A population of $N = nh$ individuals is split into $n$ households of size $h \ge 2$. Each individual, when infected, draws an independent copy of a random vector $(X_G, X_L)$ on $\mathbb{Z}_+^2$: it makes $X_G$ *global* contacts with individuals chosen uniformly from the whole population and $X_L$ *local* contacts with members chosen uniformly from the other $h-1$ members of its household; contacted susceptibles become infected (SIR, no reinfection). The classical household model with infectious period $I$ and contact rates $\beta_G, \beta_L$ is the case $(X_G,X_L) = (\mathrm{MixPo}(\beta_G I), \mathrm{MixPo}(\beta_L I))$.

For one household with a single initial case, let $C$ be the number of global contacts made by the within-household epidemic, with pgf $f_C$, and let $S$ be the size of the susceptibility set of a typical member (the household members whose infection would lead to its infection), with pgf $f_S$. Then

$$R_* = \mathbb{E}[C] = \mu_G\,\mathbb{E}[S], \qquad \mu_G = \mathbb{E}[X_G].$$

If $R_* > 1$, let $z \in (0,1]$ be the unique solution of $z = 1 - f_S(e^{-\mu_G z})$ and $\rho \in [0,1)$ the smallest solution of $\rho = f_C(\rho)$. A *major epidemic* is the event $\mathcal{G}^{n,h}$ that at least $\lfloor \log n\rfloor$ households are infected.

**Theorem.** Suppose $R_* > 1$, the epidemic starts with $m$ uniformly chosen infectives for all large $n$, and $\mathbb{E}[X_G^{2+a}] < \infty$ for some $a > 0$. Let $\bar Z_{n,h}$ be the final fraction infected. Then, as $n \to \infty$ with $h$ fixed,
1. $\bar Z_{n,h} \to Z$ in distribution, where $\mathbb{P}(Z = 0) = 1 - \mathbb{P}(Z = z) = \rho^m$;
2. there is an explicit $0 < \sigma^2 < \infty$ (depending on the within-household epidemic exposed to external infection) such that

$$\sqrt{nh}\,\big(\bar Z_{n,h} - z\big)\ \big|\ \mathcal{G}^{n,h} \xrightarrow{d} \mathrm{N}(0,\sigma^2).$$

## Expansion

Early on, infected households form a branching process whose offspring are the global contacts $C$ of a household epidemic, so a major outbreak occurs with probability $1-\rho^m$ and needs $R_* > 1$. In a major outbreak each individual escapes global infection with probability $e^{-\mu_G z}$ for every member of its susceptibility set, giving the final-size equation $z = 1 - f_S(e^{-\mu_G z})$. The CLT is proved by an embedding: households are exposed to global infection pressure in a random time-change, the number infected is a sum of i.i.d. household contributions evaluated at a random stopping level, and a delta-method argument around the stopping level gives the Gaussian fluctuations; the enhanced embedding handles general, possibly dependent, $(X_G, X_L)$ rather than Poisson contacts driven by an infectious period.

## Sources

- F. Ball, T. Britton, P. Neal, "Household epidemic models revisited", arXiv:2505.17890 (2025), Section 2 (model, Equations for $R_*$, $z$ and $\sigma^2$), Theorem 2.1, Corollary 4.1 and Theorem 4.1, <https://doi.org/10.48550/arXiv.2505.17890>.
