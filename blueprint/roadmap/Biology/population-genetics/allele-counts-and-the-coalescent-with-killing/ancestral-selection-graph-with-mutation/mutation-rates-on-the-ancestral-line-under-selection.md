# Mutation rates on the ancestral line under selection

**Model.** In the two-type Moran model with $N$ individuals, type $0$ (fit) reproduces at rate $1 + s^N$ and type $1$ at rate $1$; each individual mutates at rate $u^N$, to type $0$ with probability $\nu_0$ and to type $1$ with probability $\nu_1 = 1 - \nu_0$. In the *deterministic limit* ($s^N \to s > 0$, $u^N \to u > 0$, time unscaled) the type-1 frequency converges to the solution of an ODE with stationary value $y_\infty$; in the *diffusion limit* ($Ns^N \to \sigma$, $Nu^N \to \theta$, time scaled by $N$) it converges to the Wright–Fisher diffusion $d\mathcal Y = (-\sigma\mathcal Y(1 - \mathcal Y) - \theta\nu_0\mathcal Y + \theta\nu_1(1 - \mathcal Y))dt + \sqrt{2\mathcal Y(1 - \mathcal Y)}\,dW$. The *ancestral line* of an individual sampled at stationarity is traced back with the pruned lookdown ancestral selection graph (pLD-ASG), whose line-counting process has, in the deterministic limit, a geometric stationary law $\mathbb P(L_\infty = n) = p^{n-1}(1 - p)$ with

$$p = \frac12\left(\frac{u + s}{u\nu_1} - \sqrt{\Bigl(\frac{u + s}{u\nu_1}\Bigr)^2 - \frac{4s}{u\nu_1}}\right) \ (\nu_1 > 0), \qquad p = \frac{s}{u + s} \ (\nu_1 = 0).$$

**Theorem.**
1. *(Deterministic limit.)* The type process on the ancestral line at stationarity is a two-state Markov chain with beneficial ($1 \to 0$) and deleterious ($0 \to 1$) mutation rates

$$q_A(1, 0) = \frac{u\nu_0}{1 - p}, \qquad q_A(0, 1) = u\nu_1(1 - p),$$

so, compared with the neutral rates $u\nu_0, u\nu_1$, beneficial mutations are over-represented and deleterious ones under-represented on the ancestral line.
2. *(Diffusion limit.)* The stationary mutation fluxes on the ancestral line are $f(1, 0) = \theta\nu_0\sum_{n > 0}\alpha_{n-1}\beta_n$ and $f(0, 1) = \theta\nu_1\sum_{n > 0}\omega_n(\beta_{n-1} - \beta_n)$, where $\alpha_n$ are tail probabilities of the pLD-ASG line count, $\omega_n$ its stationary weights, and $\beta_n$ absorption probabilities of the killed ASG. Exact finite-$N$ analogues hold, and fluxes satisfy level-wise balance identities.
3. *(Monotonicity.)* The tail probabilities of the line count increase strictly with the selection strength ($s^N$, $\sigma$ or $s$), and the stationary probability that the ancestor is unfit, $\mathbb P(A_\infty = 1)$, decreases strictly with it, in all three regimes.

## Depends on

- [Absorption probabilities with killing versus stationary tails with catastrophes](absorption-probabilities-with-killing-versus-stationary-tails-with-catastrophes.md)
- [Stationary law of the pruned lookdown ancestral selection graph line count](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/stationary-law-of-the-pruned-lookdown-asg-line-c.md)

## Expansion

The ancestral line is biased towards fit individuals because fit individuals leave more long-term offspring; the stationary ratio $\mathbb P(A_\infty = 1)/y_\infty = (1 - p)\,\mathbb P(A_\infty = 0)/(1 - y_\infty)$ shows that a type-1 individual has relative long-term offspring $1 - p$. Mutation rates on the ancestral line follow from stationary probability fluxes: the rate of a $1 \to 0$ mutation seen from the ancestor is the forward rate times the ratio of reproductive values, which yields the factors $1/(1 - p)$ and $1 - p$. This connects population-genetic dynamics with the substitution process seen in molecular phylogenies, which samples exactly such ancestral lines.

## Sources

- Ellen Baake, Fernando Cordero and Enrico Di Gaspero, "The mutation process on the ancestral line under selection", Theor. Popul. Biol. 158 (2024), 60–75, <https://doi.org/10.1016/j.tpb.2024.04.004>. Numbering follows the arXiv version, arXiv:2306.03512 (2023): Theorem 5.1, Corollaries 5.3–5.4, Proposition 6.1, Propositions 7.1 and 7.3, <https://doi.org/10.48550/arXiv.2306.03512>.
