# Bounded proper scoring rules are mixtures of V-shaped elementary scoring rules

For a threshold $\theta \in [0,1]$ let the **V-shaped** (elementary) scoring rule be $S_\theta(p, y) = (\theta - y)\,\mathrm{sign}(p - \theta)$ with $\mathrm{sign}(0) = 0$, the loss of an agent who takes action $1$ when the forecast exceeds $\theta$ and whose utility difference between the two actions is $y - \theta$. Its univariate form $S_\theta(p) = \mathbb{E}_{y \sim \mathrm{Ber}(p)} S_\theta(p,y)$ is $-|p - \theta|$, and $S_\theta$ is a proper scoring rule with values in $[-1,1]$. Every proper scoring rule $S(p, y)$ for binary outcomes with values in $[-1,1]$ can be written, up to an additive term depending only on $y$, as $S(p,y) = \int_0^1 S_\theta(p, y)\,d\nu(\theta)$ for a nonnegative measure $\nu$ of total mass at most $2$. Consequently, writing $\mathrm{VCal}_T = \sup_{\theta \in [0,1]} \mathrm{Reg}_{S_\theta}$ for the largest regret of the forecasts under a V-shaped rule,

$$
\tfrac12\,\mathrm{UCal}_T \le \mathrm{VCal}_T \le \mathrm{UCal}_T .
$$

## Proof sketch

The univariate form $G(p) = \mathbb{E}_{y \sim \mathrm{Ber}(p)} S(p,y)$ of a proper loss is concave and $S(p,y) = G(p) + G'(p)(y - p)$. Up to an affine function of $p$, which changes $S$ only by a term depending on $y$ and so does not change regret, $G$ is the integral of the functions $-|p-\theta|$ against the measure $\nu = -G''/2$. Since $G'(p) = S(p,1) - S(p,0) \in [-2,2]$, the total mass of $\nu$ is $(G'(0) - G'(1))/2 \le 2$. Regret is linear in the scoring rule, so $\mathrm{Reg}_S \le 2 \sup_\theta \mathrm{Reg}_{S_\theta}$; the other inequality holds because each $S_\theta$ is one of the rules in the supremum defining $\mathrm{UCal}_T$.

## Depends on

- [U-calibration error](u-calibration-error.md)
- [Scoring rules and properness for finite outcomes](../../../GameTheory/mechanism-design/remaining-clauses-of-scoring-rules-and-properness.md)

## Proof depends on

- [Characterization of proper scoring rules](../../../GameTheory/mechanism-design/characterization-of-proper-scoring-rules.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168, Lemma 1, Corollary 2 and Theorem 8.
