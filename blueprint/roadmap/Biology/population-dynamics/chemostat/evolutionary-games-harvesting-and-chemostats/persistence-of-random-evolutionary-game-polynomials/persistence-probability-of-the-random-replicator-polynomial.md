# Persistence probability of the random replicator polynomial

**Setting.** In a $d$-player two-strategy evolutionary game with random payoffs, the internal equilibria of the replicator dynamics correspond, after the change of variables $y=x/(1-x)$ for the frequency $x\in(0,1)$, to the positive roots of the random polynomial

$$f_n(y)=\sum_{i=0}^{n}\binom ni a_i\,y^i ,\qquad n=d-1,$$

where $a_i$ is the payoff difference between the two strategies when $i$ of the $n$ co-players use the first one. Assume the $a_i$ are i.i.d. standard normal. The *persistence probability* is $\mathbb P\bigl(f_n(y)>0\ \forall y\in(0,\infty)\bigr)$; by symmetry of the coefficients, the probability that the game has no internal equilibrium is twice this.

**Theorem.** With $b$ the persistence exponent of the centered stationary Gaussian process $Z$ with correlation $\mathbb E[Z_0Z_t]=e^{-t^2/4}$,

$$b=-\lim_{T\to\infty}\frac1T\log\mathbb P\Bigl(\inf_{0\le t\le T}Z(t)>0\Bigr),$$

one has

$$\lim_{n\to\infty}\frac{\log\mathbb P\bigl(f_n(y)>0\ \forall y>0\bigr)}{\pi\sqrt n}=-b .$$

So the probability that a random $d$-player two-strategy game has no internal equilibrium decays like $\exp(-(b+o(1))\pi\sqrt{d})$: subexponentially in the number of players, with the same exponent that governs persistence of random Kac-type polynomials.

## Expansion

The variance of $f_n(y)$ is $M_n(y)=\sum_i\binom ni^2y^{2i}$, which near the bulk behaves like $(1+y)^{2n+1}/(2\sqrt{\pi ny})$ (equivalently, via Legendre polynomials, $M_n(y)=(1-y^2)^nL_n\bigl(\frac{1+y^2}{1-y^2}\bigr)$). Splitting $(0,\infty)$ into $(0,n^{-1/6})$, $(n^{-1/6},n^{1/6})$ and $(n^{1/6},\infty)$, the two outer ranges contribute only $e^{o(\sqrt n)}$ to the persistence probability. On the middle range, after the logarithmic time change $y=e^{2t/\sqrt n}$-type reparametrization, the normalized process $f_n/\sqrt{M_n}$ converges, with uniformly controlled correlations, to the stationary Gaussian process with correlation $e^{-t^2/4}$ on an interval of length of order $\pi\sqrt n$. A comparison lemma for Gaussian processes with nonnegative correlations transfers the persistence exponent from the limit process, and a small-ball bound (a differentiable Gaussian process stays positive on short intervals with probability bounded below) glues the pieces together.

## Sources

- Van Hao Can, Manh Hong Duong, Viet Viet Hung Pham, "Persistence probability of a random polynomial arising from evolutionary game theory", Journal of Applied Probability 56 (2019), 870–890, <https://doi.org/10.1017/jpr.2019.50>. Published version of arXiv:1804.05908, cited next; locators there refer to the arXiv version.
- V. H. Can, M. H. Duong, V. H. Pham, "Persistence probability of a random polynomial arising from evolutionary game theory", arXiv:1804.05908 (2018), Theorem 1.1, Lemmas 2.1, 2.3 and 2.4, Remark 2.2 and Propositions 3.1–3.2. <https://doi.org/10.48550/arXiv.1804.05908>
