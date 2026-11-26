# Integral representation of sample coalescence times in a Galton–Watson process

**Setting.** Let $(N_t(n_0))_{t\ge0}$ be a Bienaymé–Galton–Watson process started from $n_0$ founders, with offspring probability generating function $\phi$ and $t$-fold iterate $\phi_t=\phi\circ\dots\circ\phi$, so $\mathbb E\,u^{N_t(n_0)}=\phi_t(u)^{n_0}$; $f^{(i)}$ denotes the $i$-th derivative. Sample $i$ individuals without replacement from generation $t$ (on $\{N_t(n_0)\ge i\}$) and let $\tau^{(t)}_{i,1}(n_0)$ be the number of generations back to their most recent common ancestor, with $\tau=\infty$ if they descend from different founders.

**Lemma (size-biased sampling identity).** For i.i.d. nonnegative integer variables $M_1,\dots,M_n$ with pgf $\phi$ and falling factorials $(m)_i$,

$$\mathbb E\!\left[\frac{(M_1)_i}{\big(\sum_{l=1}^nM_l\big)_i}\right]=\frac1{\Gamma(i)}\int_0^1(1-z)^{i-1}\phi(z)^{n-1}\phi^{(i)}(z)\,dz ,$$

and more generally $\mathbb E\big[\prod_{l=1}^j(M_l)_{i_l}/(\sum M)_{i_l}\big]=\frac1{\Gamma(i)}\int_0^1(1-z)^{i-1}\phi(z)^{n-j}\prod_{l=1}^j\phi^{(i_l)}(z)\,dz$ for $i_1+\dots+i_j=i$.

**Theorem (TMRCA of a sample).** For $0\le k\le t-1$,

$$\mathbb P\big(\infty>\tau^{(t)}_{i,1}(n_0)\ge k\big)=\frac1{\Gamma(i)}\int_0^1(1-z)^{i-1}\big[\phi_t^{n_0}\big]^{(1)}(z)\,\frac{\phi_{t-k}^{(i)}(z)}{\phi_{t-k}^{(1)}(z)}\,dz ,$$

and $\mathbb P(\tau^{(t)}_{i,1}(n_0)<\infty)$ is the case $k=0$. For two individuals, the probability that they descend from different founders is $n_0(n_0-1)\int_0^1(1-z)\,\phi_t^{(1)}(z)^2\phi_t(z)^{n_0-2}\,dz$.

**Theorem (whole-population TMRCA).** For a single founder, conditionally on survival to generation $t$,

$$\mathbb P\big(\tau^{(t)}_{N_t(1),1}(1)\ge k\mid N_t(1)>0\big)=\frac{\mathbb P(N_{t-k}(1)>0)}{\mathbb P(N_t(1)>0)}\;\phi_k^{(1)}\big(\mathbb P(N_{t-k}(1)=0)\big).$$

The backward ancestral count process $\widehat N_s$ (number of distinct ancestors in generation $s$ of the sample) is a time-inhomogeneous Markov chain with explicit transition probabilities of the same integral form.

## Expansion

Conditionally on generation $t-1$, the offspring numbers of the $N_{t-1}$ parents are i.i.d. with pgf $\phi$, and sampling $i$ children without replacement picks children of one given parent with probability $(M_1)_i/(\sum M)_i$; the identity follows by writing $(M_1)_i/(\sum M)_i$ via the Beta integral $\frac{\Gamma(a)\Gamma(b)}{\Gamma(a+b)}=\int_0^1z^{a-1}(1-z)^{b-1}dz$ and exchanging expectation and integral, which turns ratios of falling factorials into derivatives of the pgf. Iterating over generations and using the branching property ($\phi_{t}=\phi_k\circ\phi_{t-k}$) gives the TMRCA law. For the whole population, all survivors coalesce before generation $t-k$ iff exactly one individual at generation $k$ has surviving descendants at $t$, which produces $\phi_k^{(1)}$ evaluated at the extinction probability. Closed forms follow for $b$-ary, linear-fractional and Sibuya (infinite-mean) offspring laws, whose iterates are explicit.

## Sources

- Nicolas Grosjean, Thierry Huillet, "On the genealogy and coalescence times of Bienaymé-Galton-Watson branching processes", arXiv:1709.07630: Proposition 1 and Corollary 2 (ancestral count transition matrix), Theorem 3 and Corollary 4 (coalescence and TMRCA laws), Proposition 5 and Corollaries 6–7 (finiteness and conditional laws), Theorem 8 (whole-population TMRCA), Lemma 9 and Corollary 10 (sampling identity), Section 4 (examples). <https://doi.org/10.48550/arXiv.1709.07630>
