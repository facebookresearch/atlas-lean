# Growth-rate trichotomy for mutants in the two-type birth–death model

**Model.** Wildtype cells form a linear birth–death process $A(t)$ with birth rate $\alpha_A$, death rate $\beta_A$ and fitness $\lambda_A = \alpha_A - \beta_A > 0$, started from a fixed $A(0) \in \mathbb{N}$. Mutations occur as a Cox process $K(t)$ with intensity $\nu A(t)$, $\nu > 0$, at times $T_i$; each mutation founds an independent clone $Y_i(t)$, a linear birth–death process with rates $\alpha_B, \beta_B$, fitness $\lambda_B = \alpha_B - \beta_B$ and $Y_i(0) = 1$. The mutant population is

$$B(t) = \sum_{i=1}^{K(t)} Y_i(t - T_i).$$

Let $\tau_n = \inf\{t : A(t) \ge n\}$ and $\sigma_n = \inf\{t : A(t) + B(t) \ge n\}$. Classically $e^{-\lambda_A t}A(t) \to W$ a.s., where $W \overset{d}{=} \sum_{i=1}^{A(0)}\chi_i\psi_i$ with independent $\chi_i \sim \mathrm{Bernoulli}(\lambda_A/\alpha_A)$ and $\psi_i \sim \mathrm{Exp}(\lambda_A/\alpha_A)$, and $\{W = 0\}$ is the wildtype extinction event.

**Theorem (large time).** Almost surely:

1. if $\lambda_A > \lambda_B$, $\displaystyle\lim_{t\to\infty} e^{-\lambda_A t}B(t) = \frac{\nu}{\lambda_A - \lambda_B}\,W$;
2. if $\lambda_A = \lambda_B$, $\displaystyle\lim_{t\to\infty} t^{-1}e^{-\lambda_A t}B(t) = \nu W$;
3. if $\lambda_A < \lambda_B$, $\displaystyle\lim_{t\to\infty} e^{-\lambda_B t}B(t) = V$ for a random variable $V$.

**Corollary (fixed wildtype size).** Conditioned on $W > 0$, almost surely: $n^{-1}B(\tau_n) \to \nu/(\lambda_A - \lambda_B)$ if $\lambda_A > \lambda_B$; $(n\log n)^{-1}B(\tau_n) \to \nu/\lambda_A$ if $\lambda_A = \lambda_B$; and $n^{-\lambda_B/\lambda_A}B(\tau_n) \to V W^{-\lambda_B/\lambda_A}$ if $\lambda_A < \lambda_B$.

**Corollary (fixed total size).** Conditioned on $W > 0$, almost surely:

1. if $\lambda_A > \lambda_B$, $n^{-1}B(\sigma_n) \to \nu/(\lambda_A - \lambda_B + \nu)$;
2. if $\lambda_A = \lambda_B$, $n^{-1}\log(n)\,(n - B(\sigma_n)) \to \lambda_A/\nu$;
3. if $\lambda_A < \lambda_B$, $n^{-\lambda_A/\lambda_B}(n - B(\sigma_n)) \to V^{-\lambda_A/\lambda_B}W$.

So with a fixed mutation rate, less fit mutants settle at a constant fraction of the tumour, neutral mutants take over at a logarithmically slow rate, and fitter mutants take over polynomially fast.

## Expansion

Conditionally on the wildtype path, the mean mutant count is $\int_0^t \nu A(s)\,e^{\lambda_B(t-s)}\,ds$. Substituting $A(s) \approx W e^{\lambda_A s}$ gives $\nu W e^{\lambda_A t}/(\lambda_A - \lambda_B)$, $\nu W t e^{\lambda_A t}$ or $O(e^{\lambda_B t})$ in the three regimes; martingale arguments upgrade these to almost-sure limits, and in the fitter-mutant regime the early clones dominate, leaving a nondegenerate random limit $V$. Part 1 is a special case of Janson's limit theorems for generalized Pólya urns, and part 3 is due to Durrett and Moseley. The corollaries follow by evaluating at the hitting times, where $e^{\lambda_A\tau_n} \sim n/W$.

## Sources

- David Cheek and Tibor Antal, "Mutation frequencies in a birth–death branching process", arXiv:1710.09783 (2017), Section 2 (model), Section 3 (Eq. for $W$, Theorem 3.2, Corollaries 3.3 and 3.4), <https://doi.org/10.48550/arXiv.1710.09783>. Published version: The Annals of Applied Probability 28 (2018) 3922–3947, <https://doi.org/10.1214/18-aap1413>.
