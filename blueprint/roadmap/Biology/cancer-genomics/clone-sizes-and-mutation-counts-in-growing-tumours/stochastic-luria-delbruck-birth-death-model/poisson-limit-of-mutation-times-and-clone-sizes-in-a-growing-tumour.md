# Poisson limit of mutation times and clone sizes in a growing tumour

**Setting.** The two-type birth–death model of [the growth-rate trichotomy](growth-rate-trichotomy-for-mutants-in-the-two-type-birth-death-model.md): supercritical wildtype growth with fitness $\lambda_A > 0$, mutation intensity $\nu A(t)$, and independent mutant clones $Y_i$ with birth and death rates $\alpha_B, \beta_B$, $\lambda_B = \alpha_B - \beta_B$ and $q_B = \beta_B/\alpha_B$. Consider the **large population–small mutation limit**: mutation rates $\nu_n$ with $n\nu_n \to \theta \in (0,\infty)$, observed at $\rho_n$, the first time the wildtype (or, equivalently in the limit, the total) population reaches $n$.

**Theorem (mutation times).** Conditioned on $\rho_n < \infty$, the mutation counting process recentered at $\rho_n$ converges in finite-dimensional distributions,

$$K^{(n)}(\rho_n + t) \to K^*(t),$$

where $K^*$ is a Poisson process on $\mathbb{R}$ with intensity $\theta e^{\lambda_A t}$. In particular the first mutation time satisfies $P(T_1^* \ge t) = \exp\!\big(-\tfrac{\theta}{\lambda_A}e^{\lambda_A t}\big)$, a Gumbel law.

**Proposition (number of mutants).** $B^{(n)}(\rho_n) \to B^* \overset{d}{=} \sum_{i=1}^{K^*}Y_i(\xi_i)$, with $K^* \sim \mathrm{Poisson}(\theta/\lambda_A)$ and i.i.d. clone ages $\xi_i \sim \mathrm{Exp}(\lambda_A)$. Its generating function is

$$\mathbb{E}\big[z^{B^*}\big] = \exp\!\Big(\frac{\theta}{\lambda_A}\big(r(z) - 1\big)\Big), \qquad r(z) = 1 - (1-q_B)\,{}_2F_1\!\Big(1, \frac{\lambda_A}{\lambda_B}; 1 + \frac{\lambda_A}{\lambda_B}; \frac{q_B - z}{1-z}\Big).$$

For $\alpha_B = \lambda_A$, $\beta_B = 0$ this reduces to the Luria–Delbrück law $\mathbb{E}[z^{B^*}] = (1-z)^{\frac{\theta}{\lambda_A}(z^{-1}-1)}$. For $\lambda_B > 0$ the tails are power laws:

$$\lim_{k\to\infty} k^{1+\lambda_A/\lambda_B}\,\mathbb{P}[B^* = k] = \frac{\theta}{\lambda_B}(1-q_B)^{1-\lambda_A/\lambda_B}\,\Gamma\Big(1 + \frac{\lambda_A}{\lambda_B}\Big).$$

**Proposition (clone statistics).** The number of clones with size in a set $I$ converges to a $\mathrm{Poisson}\big(\frac{\theta}{\lambda_A}\mathbb{P}[Y_i(\xi_i) \in I]\big)$ variable, and the largest clone $M^*$ satisfies $\mathbb{P}[M^* \le k] = \exp\!\big(-\frac{\theta}{\lambda_A}\mathbb{P}[Y_i(\xi_i) > k]\big)$.

**Site frequency spectrum.** In a neutral multi-site model where cells divide at rate $a$, die at rate $b$, and each division mutates an unmutated site in one daughter with probability $\mu_n$, the mutant count at each site is a two-type model with $\alpha_B = a$, $\beta_A = \beta_B = b$. If $n\mu_n a \to \theta$, the expected number of the $S$ sites carried by exactly $k$ cells at size $n$ converges to $S\,\mathbb{P}[B^* = k]$.

## Depends on

- [Growth-rate trichotomy for mutants in the two-type birth–death model](growth-rate-trichotomy-for-mutants-in-the-two-type-birth-death-model.md)

## Expansion

On survival, $A(\rho_n + t) \approx n e^{\lambda_A t}$, so the mutation intensity $\nu_n A(\rho_n + t)$ tends to $\theta e^{\lambda_A t}$ uniformly on half-lines with an integrable bound; dominated convergence yields the Poisson limit. A Poisson point with intensity $\theta e^{\lambda_A t}$ on $(-\infty, 0]$ has total mass $\theta/\lambda_A$ and ages distributed as $\mathrm{Exp}(\lambda_A)$, hence the compound Poisson form. Averaging the birth–death generating function over an exponential age and substituting $s = e^{-\lambda_B t}$ gives the hypergeometric $r(z)$, and its singularity at $z = 1$ produces the power-law exponent $1 + \lambda_A/\lambda_B$. Clone counts and the maximum follow from Poisson thinning.

## Sources

- David Cheek and Tibor Antal, "Mutation frequencies in a birth–death branching process", arXiv:1710.09783 (2017), Section 4 (Proposition 4.1, Theorem 4.2, Proposition 4.3, Remark 4.4, Propositions 4.5–4.6) and Section 7 (Proposition 7.3), <https://doi.org/10.48550/arXiv.1710.09783>. Published version: The Annals of Applied Probability 28 (2018) 3922–3947, <https://doi.org/10.1214/18-aap1413>.
