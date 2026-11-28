# Site frequency spectrum of an exponentially growing population

**Setting.** Type-0 cells form a linear birth–death branching process $Z_0(t)$ with birth rate $a_0$ and death rate $b_0 < a_0$; put $\lambda_0 = a_0 - b_0$ and $\gamma = \lambda_0 / a_0$. Time is measured so that $a_0 = 1$, hence $\gamma = \lambda_0$. Conditioned on non-extinction, the number $Y_0(t)$ of cells whose families survive forever is a Yule process with birth rate $\lambda_0$ ($= \gamma$ under this normalization), and $Y_0(t)/Z_0(t) \to \gamma$ in probability. Neutral (passenger) mutations arise at rate $\nu$ per cell per unit time, each at a new site (infinite sites). Let $F_t(x)$ be the expected number of passenger mutations carried by more than a fraction $x$ of the cells at time $t$ and $F(x) = \lim_{t\to\infty} F_t(x)$.

**Theorem 1 (population spectrum).** For $0 < x < 1$,

$$ F(x) = \frac{\nu}{\gamma x}. $$

Without the normalization $a_0 = 1$ the result reads $F(x) = \nu/(\lambda_0 x)$: each period with $k$ surviving lineages carries $\nu/\lambda_0$ expected mutations, each above frequency $x$ with probability $(1-x)^{k-1}$. (The source writes $\nu/(\gamma x)$ and a Yule rate $\gamma$ without fixing $a_0 = 1$, which is correct only when $a_0 = 1$.)

**Theorem 2 (sample spectrum).** Consider a Moran model whose population size $t$ units before the present is $N(t) = N e^{-\gamma t}$, with neutral mutation rate $\nu$, and let $\eta_{n,m}$ be the number of segregating sites at which exactly $m$ of $n$ sampled individuals carry the mutant base. As $N \to \infty$,

$$ \mathbb E\,\eta_{n,m} \to \frac{n\nu}{\gamma}\cdot\frac{1}{m(m-1)} \quad (2 \le m < n), \qquad \mathbb E\,\eta_{n,1} \sim \frac{n\nu}{\gamma}\,\log(N\gamma). $$

**Theorem 3 (finite-size singletons).** The number of singletons is better approximated, for finite $N$, by

$$ \mathbb E\,\eta_{n,1} \approx \frac{\nu}{\gamma}\sum_{k=1}^{N\gamma} \frac{n}{n+k}\cdot\frac{k}{n+k-1}. $$

In contrast with the constant-size neutral spectrum $\mathbb E\,\eta_{n,m} = 2N\nu/m$, the non-singleton classes stay bounded as the final population grows, the sample size $n$ takes the place of the population size, and the spectrum decays like $1/m^2$.

## Expansion

Since each cell alive at time $t$ independently founds a surviving family with probability $\gamma$, it suffices to study mutations inside the Yule process $Y_0$. A mutation arising when the Yule process has $k$ individuals is inherited by a fraction of the eventual population that is asymptotically $\mathrm{Beta}(1, k-1)$-distributed, so it exceeds frequency $x$ with probability $(1-x)^{k-1}$; summing these geometric terms over the successive Yule population sizes, weighted by the mutation input per size, gives the $1/x$ law. Sampling $n$ individuals binomially from the population spectrum and using $\int_0^1 x^a(1-x)^b\,dx = a!\,b!/(a+b+1)!$ gives $\binom{n}{m}\int_0^1 x^{m}(1-x)^{n-m}\,\frac{\nu}{\gamma x^2}\,dx = \frac{n\nu}{\gamma m(m-1)}$ for $m \ge 2$. For $m = 1$ the integral diverges at $x = 0$, reflecting the nearly star-shaped genealogy: the time for the process to reach size $N$ is about $\gamma^{-1}\log(N\gamma)$, and each of the $n$ external branches has this length, giving $n\nu\gamma^{-1}\log(N\gamma)$ singletons; truncating the Yule sum at $N\gamma$ individuals yields Theorem 3. Running time at rate $1/N(s)$ maps the sample genealogy to Kingman's coalescent, which links these results to the general Griffiths–Tavaré formula for variable population size.

## Sources

- Rick Durrett, "Population genetics of neutral mutations in exponentially growing cancer cell populations", Annals of Applied Probability 23(1) (2013); arXiv:1302.2742, Section 1.1 (Theorems 1–3), Section 2 (proofs, Lemma 2.1), Section 3 (Theorem 8, time change to the coalescent). <https://doi.org/10.48550/arXiv.1302.2742>. Published version: The Annals of Applied Probability 23(1) (2013), 230–250, <https://doi.org/10.1214/11-aap824>; locators above refer to the arXiv version.
