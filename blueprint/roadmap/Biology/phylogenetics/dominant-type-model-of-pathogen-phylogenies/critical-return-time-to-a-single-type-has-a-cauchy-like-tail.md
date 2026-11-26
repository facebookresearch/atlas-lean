# The critical return time to a single type has a Cauchy-like tail

**Model (Liggett–Schinazi).** The number of pathogen types alive is a birth–death chain $N(t)$ with birth rate $\lambda N$ and death rate $N$. Each new type receives an independent fitness value, a death removes the type with the lowest fitness, and the type with the highest fitness is **dominating**. When only one type is alive it cannot die, so state $1$ reflects. Only fitness ranks matter, so the fitness distribution is irrelevant.

**Dominance turnover.** For $\delta\in(0,1)$, as $t\to\infty$,

$$\Pr(\text{the dominating types at times } \delta t \text{ and } t \text{ coincide}) \to \begin{cases}\delta, & \lambda \le 1,\\ 0, & \lambda > 1.\end{cases}$$

In the subcritical and critical regime one type can dominate for long periods, the influenza-like pattern. In the supercritical regime the dominating type keeps changing, the HIV-like pattern.

**Lemma (critical case $\lambda = 1$).** Let $H$ be the hitting time of state $1$ starting from state $2$. It is a positive random variable with

$$\lim_{t\to\infty} t\,\Pr(H > t) = 1,$$

so $H$ has a power-law tail with exponent $\gamma = 1$ and constant $C = 1$. In particular $\mathbb{E}H = \infty$, and every moment $\mathbb{E}H^m$ with $m \ge 1$ is infinite. The return time from $1$ to $1$ is $X + H$ with $X\sim\operatorname{Exp}(\lambda)$, so it also has infinite mean.

An earlier claim that $\Pr(H\le t) = t/(t+1)$ exactly is false. Only the tail asymptotics hold.

## Expansion

The tail limit comes from the exact analysis of the critical chain by Bartoszek and Krzemiński. Since $\Pr(H > y)\sim 1/y$, the integral $\mathbb{E}H^m = \int_0^\infty\Pr(H^m > y)\,dy$ diverges for every $m\ge1$. Heavy-tailed excursions away from a single type are what keep the probability of unchanged dominance strictly positive at $\lambda = 1$. Because the excursions have infinite mean length, a direct Gillespie simulation undersamples the right tail of $H$. The source therefore uses a hybrid scheme. It fixes a tail proportion $p$ and sets $T_{\min} = 1/p$, so that $\Pr(H > T_{\min})\approx p$. It then simulates the embedded chain (holding rate $2N$, up and down steps equally likely) until it hits $1$ or exceeds $T_{\min}$, and in the second case draws the value from the asymptotic law $\Pr(H > y) \approx 1/y$ on $[T_{\min},\infty)$.

## Sources

- K. Bartoszek, "Simulating an infinite mean waiting time", arXiv:1907.10117 (2019), Section 1 (Theorem 1.1, Definition 1.1, Lemma 1.2) and Section 2 (simulation algorithm), <https://doi.org/10.48550/arXiv.1907.10117>.
- T. M. Liggett and R. B. Schinazi, "A stochastic model for phylogenetic trees", J. Appl. Probab. (2009).
