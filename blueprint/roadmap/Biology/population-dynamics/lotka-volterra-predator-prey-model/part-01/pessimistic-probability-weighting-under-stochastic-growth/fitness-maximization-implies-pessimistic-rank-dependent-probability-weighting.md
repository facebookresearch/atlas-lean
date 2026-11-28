# Fitness maximization implies pessimistic rank-dependent probability weighting

**Rank-dependent expected utility.** A lottery pays outcomes $x_1 \ge x_2 \ge \dots \ge x_m$ (sorted from best to worst) with probabilities $p_1, \dots, p_m$. Let $\theta_i = \sum_{j \le i} p_j$ be the rank of outcome $i$ ($\theta_0 = 0$), and let $w : [0,1] \to [0,1]$ be increasing with $w(0) = 0$, $w(1) = 1$. With decision weights $\rho_i = w(\theta_i) - w(\theta_{i-1})$ and utility $u$, the rank-dependent value and the expected-utility value are

$$V^{\mathrm{RDEUT}} = \sum_{i=1}^{m} \rho_i\, u(x_i), \qquad V^{\mathrm{EUT}} = \sum_{i=1}^{m} p_i\, u(x_i).$$

The weighting is (regularly) pessimistic if $w(\theta) \le \theta$ for all $\theta \in [0,1]$.

**Theorem (Quiggin).** If $u$ is increasing and concave, then the decision maker is pessimistic, $w(\theta) \le \theta$ for all $\theta$, if and only if $V^{\mathrm{RDEUT}} \le V^{\mathrm{EUT}}$ for every lottery.

**Evolutionary consequence.** Let a strategy $s$ induce a lottery over the achieved value $f_k$ of one vital rate (say an age-specific fertility) with probabilities $p^{(s)}_k$, mean $f^{(s)} = \sum_k p^{(s)}_k f_k$ and standard deviation $\sigma^{(s)}$, all other Leslie-matrix entries fixed. An expected-value decision maker values the strategy at the fitness $a^{(s,\mathrm{EUT})}$ of the deterministic matrix carrying the mean $f^{(s)}$, whereas its true fitness $a^{(s)}$ is the stochastic growth rate. By the small-noise approximation,

$$\sigma^{(s)} > 0 \iff a^{(s,\mathrm{EUT})} > a^{(s)}, \qquad\text{while}\qquad \text{pessimism} \iff V^{(s,\mathrm{RDEUT})} \le V^{(s,\mathrm{EUT})}.$$

Thus expected-value evaluation of vital rates is systematically optimistic about risky strategies, and the probability reweighting that aligns the decision maker's valuation with fitness lowers the value of risky lotteries relative to their mean: selection favors pessimistic weighting, whatever the specific environment.

## Expansion

Summation by parts writes both values in rank form: $V^{\mathrm{RDEUT}} - V^{\mathrm{EUT}} = \sum_{i=1}^{m-1} \big(w(\theta_i) - \theta_i\big)\big(u(x_i) - u(x_{i+1})\big)$, using $w(\theta_m) = \theta_m = 1$. With $u$ increasing, each $u(x_i) - u(x_{i+1}) \ge 0$, so $w \le \theta$ gives $V^{\mathrm{RDEUT}} \le V^{\mathrm{EUT}}$. Conversely, a two-outcome lottery with strictly ordered utilities and probability $\theta$ on the better outcome has $V^{\mathrm{RDEUT}} - V^{\mathrm{EUT}} = (w(\theta) - \theta)(u(x_1) - u(x_2))$, which forces $w(\theta) \le \theta$. The source applies the theorem with concave maps from consumption to vital rates. Pessimism underweights the best-ranked outcomes and overweights low-probability extreme bad outcomes, the same feature that rank-dependent utility and cumulative prospect theory use to explain the Allais paradox. Here it arises from the intolerance of multiplicative growth to near-zero outcomes. The source's motivating case: East African pastoralists keep mixed goat and camel herds although goat-only herds grow faster on average, because mixed herds have a far higher probability of long-term persistence.

## Depends on

- [Small-noise stochastic growth rate and the variance penalty on vital rates](small-noise-stochastic-growth-rate-and-the-variance-penalty-on-vital-rates.md)

## Sources

- M. H. Price, J. H. Jones, "Fitness-maximizers employ pessimistic probability weighting for decisions under risk", Evolutionary Human Sciences 2 (2020) e28, Section 2, Eqs (3)–(5) and Theorem 1, and Section 6, Eqs (14)–(16), <https://doi.org/10.1017/ehs.2020.28>, PMCID PMC10427448.
- J. Quiggin, Generalized Expected Utility Theory: The Rank-Dependent Model, Kluwer (1993), chapter 6, <https://doi.org/10.1007/978-94-011-2182-8>.
