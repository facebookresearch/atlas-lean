# Normal limit of the stationary infected size in the SIS birth-death chain

**Model.** In a population of constant size $M$, the number of infected individuals $I$ is a birth-death chain on $\{0,\dots,M\}$. Lifetimes are exponential with rate $\alpha$ and each death is replaced by a susceptible newborn, so $I \to I-1$ at rate $\mu_i = \alpha i$ for $1 \le i \le M$. Infection occurs at the logistic rate $\beta i(M-i)/M$, which vanishes at $i = 0$, so $0$ would be absorbing. An external infection rate $\epsilon > 0$ is added at state $0$ only: the upward rates are $\lambda_0 = \epsilon$, $\lambda_i = \beta i(M-i)/M$ for $1 \le i \le M-1$, and there is no upward transition from $M$. The chain is then irreducible with stationary distribution $\pi^{[\epsilon]}_M(i) = \theta_i/\sum_{j=0}^{M}\theta_j$, where $\theta_0 = 1$ and $\theta_i = \frac{\lambda_0\lambda_1\cdots\lambda_{i-1}}{\mu_1\cdots\mu_i}$ for $1 \le i \le M$. Let $R = \beta/\alpha$ be the reproduction number. (Adding $\epsilon$ to the infection rate at every state, as in the source's numerical illustration, gives a different chain with different stationary weights; the theorem below is about the chain just defined.)

**Theorem.** Assume $R > 1$ and $\epsilon > 0$ fixed.

*(1)* As $M \to \infty$, $\pi^{[\epsilon]}_M(k) \sim \pi(k)$ for $k = 1,\dots,M$, where

$$\pi(k) = \frac{R-1}{R}\,\frac{M}{(M-k)!\,k}\Big(\frac{M}{R}\Big)^{M-k}e^{-M/R}.$$

Equivalently, $\pi(k) \propto \frac{M}{k}\,\mathbb{P}(X = M-k)$ with $X \sim \mathrm{Poisson}(M/R)$, and the normalization uses $\mathbb{E}[M/(M-X)\mid X<M] \to R/(R-1)$.

*(2)* The stationary infected size is asymptotically normal with mean $(1 - \tfrac{1}{R})M$ and variance $\tfrac{M}{R}$.

## Expansion

For $k \ge 1$ the products telescope: $\theta_k \approx \frac{\epsilon}{\alpha}\big(\frac{R}{M}\big)^{k-1}\frac{(M-1)!}{(M-k)!\,k}$, which grows exponentially in $M$ near $k \approx (1-1/R)M$ when $R > 1$, so the mass at $0$ (weight $\theta_0 = 1$) becomes negligible and $\epsilon$ drops out after normalization. Rewriting in terms of the number of susceptibles $M - k$ gives a Poisson$(M/R)$ law tilted by the slowly varying factor $M/k$, which near the bulk is essentially the constant $R/(R-1)$. The Poisson law with mean $M/R$ is asymptotically normal with variance $M/R$, giving the stated limit for $k = M - X$. This matches the deterministic endemic level $I^* = (1-1/R)M$ of the logistic SIS equation $\dot I = \beta I(1 - I/M) - \alpha I$.

## Sources

- A. H. Nzokem, "SIS Epidemic Model: Birth-and-Death Markov Chain Approach", arXiv:2102.08992 (2021), Section 3, Corollary 3.3 and Theorems 3.9 and 3.10, <https://doi.org/10.48550/arXiv.2102.08992>.
