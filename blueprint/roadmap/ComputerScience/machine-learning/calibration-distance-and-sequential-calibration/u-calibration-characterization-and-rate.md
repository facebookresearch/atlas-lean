# Sublinear U-calibration characterizes forecasts that are good for every agent and is achievable at square-root rate

Sublinear U-calibration error is necessary and sufficient for every agent with a bounded utility who best responds to the forecasts to have sublinear (external) regret. Optimizing the forecasts for a single scoring rule, such as the Brier score, does not guarantee sublinear regret for all agents, whereas calibrated forecasts do, but calibration is not necessary and calibrated forecasting has provably worse convergence rates. Calibration does imply U-calibration, with $\mathrm{UCal}_T \le 4\,\mathrm{Cal}_T$ for utilities in $[-1,1]$. There is a randomized online algorithm whose expected U-calibration error is $O(\sqrt{T})$ for every outcome sequence fixed in advance (an oblivious adversary), bypassing the super-$\sqrt{T}$ lower bounds for $\ell_1$ calibration error, and the U-calibration error of a given sequence is computable in polynomial time.

## Proof sketch

Every bounded proper scoring rule is a mixture of V-shaped elementary scoring rules $S_\theta(p, y)$, one per threshold $\theta$, so the U-calibration error is at most twice the supremum over thresholds of the regret under $S_\theta$. The algorithm ForecastHedge forecasts $p_1 = \tfrac12$ and then draws $p_t$ with $\Pr[p_t \le v] = \sigma\big(2\eta(t-1)(v - \hat{x}_{t-1})\big)$, where $\sigma$ is the logistic function, $\eta = 1/\sqrt{T}$ and $\hat{x}_{t-1}$ is the mean of the past outcomes. For every threshold $\theta$ the induced action of the threshold agent is distributed as the Hedge algorithm on its two actions, so each $S_\theta$ has expected regret $O(\sqrt{T})$, and a uniform bound over $\theta$ gives the claim. The sufficiency of calibration uses that the regret of each best-responding agent is controlled by the $\ell_1$ calibration error.

## Depends on

- [U-calibration error](u-calibration-error.md)
- [External regret](../../../GameTheory/not-yet-classified/part-02/regret/external-regret.md)

## Proof depends on

- [Best responding to calibrated forecasts gives no swap regret](calibrated-forecasts-best-response-swap-regret.md)
- [Bounded proper scoring rules are mixtures of V-shaped elementary scoring rules](v-shaped-elementary-scoring-rules.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168, Theorems 4–6, 8 and 10, Section 5.2.
