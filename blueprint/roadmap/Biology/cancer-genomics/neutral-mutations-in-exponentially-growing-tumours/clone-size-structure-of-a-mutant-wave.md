# Clone-size structure of a mutant wave in a growing tumour

**Setting.** Type-$k$ cells form linear birth–death processes with birth rate $a_k$, death rate $b_k$ and growth rate $\lambda_k = a_k - b_k > 0$, with $\lambda_0 < \lambda_1$, and a type-0 cell produces a type-1 mutant at rate $u_1$. Following the convention that the type-0 population is $Z_0^*(t) = V_0 e^{\lambda_0 t}$ for all $t \in (-\infty, \infty)$, let $Z_1^*(t)$ be the number of type-1 cells and set $\alpha = \lambda_0/\lambda_1 \in (0,1)$.

**Poisson limit.** Regarding $V_0$ as fixed, $e^{-\lambda_1 t} Z_1^*(t) \to V_1$ as $t \to \infty$, where $V_1$ is the sum of the points of a Poisson process on $(0,\infty)$ with mean measure

$$ \mu(x, \infty) = c_{\mu,1}\, u_1 V_0\, x^{-\alpha}, \qquad c_{\mu,1} = \frac{1}{a_1}\Big(\frac{a_1}{\lambda_1}\Big)^{\alpha}\Gamma(\alpha); $$

each point is the (rescaled) size of one surviving type-1 clone. Conditionally on $V_0$, $V_1$ is one-sided $\alpha$-stable: $\mathbb E[e^{-\theta V_1} \mid V_0] = \exp(-c_{\mu,1}\Gamma(1-\alpha)\, u_1 V_0\, \theta^\alpha)$.

**Theorem (clonal diversity).** Let $X_1 > X_2 > \cdots$ be the points of this Poisson process and $V_1 = \sum_i X_i$. Then

1. the expected Simpson index, i.e. the probability that two type-1 cells chosen at random descend from the same type-1 mutation,

$$ \mathbb E\Big[\sum_{i \ge 1} \frac{X_i^2}{V_1^2}\Big] = 1 - \alpha; $$

2. the reciprocal of the fraction of the wave held by the largest clone has mean

$$ \mathbb E\Big[\frac{V_1}{X_1}\Big] = \frac{1}{1-\alpha}. $$

Both quantities depend on the growth rates only through $\alpha = \lambda_0/\lambda_1$, not on the mutation rate $u_1$ or the size $V_0$. The same structure recurs in every later wave: conditionally on the earlier waves, the type-$k$ limit $V_k$ is a Poisson sum with intensity proportional to $u_k V_{k-1} x^{-\lambda_{k-1}/\lambda_k}$.

## Expansion

A type-1 mutation born at time $s$ founds a clone of size about $e^{\lambda_1(t-s)}W_1$ by time $t$, where $W_1$ is $0$ with probability $b_1/a_1$ and otherwise exponential with mean $a_1/\lambda_1$. Mutations arrive at rate $u_1 V_0 e^{\lambda_0 s}$, so the rescaled clone sizes $e^{-\lambda_1 s}W_1$ form a Poisson process; changing variables from birth time to rescaled size turns the exponential arrival rate into the power-law tail $x^{-\lambda_0/\lambda_1}$, which is the Lévy measure of an $\alpha$-stable law. For the ratios, a Poisson process with intensity proportional to $x^{-\alpha-1}dx$ has ranked normalized points $X_i/V_1$ following the Poisson–Dirichlet distribution $\mathrm{PD}(\alpha, 0)$, whose Simpson index has mean $1 - \alpha$; the mean of $V_1/X_1$ follows from Darling's analysis of the ratio of a stable sum to its largest term. Small $\alpha$ (a mutant growing much faster than its parent wave) concentrates the wave in a few early clones, while $\alpha$ near $1$ spreads it over many.

## Sources

- Rick Durrett, "Population genetics of neutral mutations in exponentially growing cancer cell populations", Annals of Applied Probability 23(1) (2013); arXiv:1302.2742, Section 1.2 (Theorem 4, quoted from Durrett and Moseley, and Theorems 5–6), Section 1.3 (Theorem 7 for wave $k$). <https://doi.org/10.48550/arXiv.1302.2742>. Published version: The Annals of Applied Probability 23(1) (2013), 230–250, <https://doi.org/10.1214/11-aap824>; locators above refer to the arXiv version.
