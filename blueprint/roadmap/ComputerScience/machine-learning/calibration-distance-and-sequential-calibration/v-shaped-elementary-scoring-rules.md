# Bounded proper scoring rules are mixtures of V-shaped elementary scoring rules

For a threshold $\theta \in [0,1]$ let the **V-shaped** (elementary) scoring rule be $S_\theta(p, y) = (\theta - y)\,\mathrm{sign}(p - \theta)$ with $\mathrm{sign}(0) = 0$, the loss of an agent with utility $u_\theta(a, y) = (-1)^a(\theta - y)$ for actions $a \in \{0,1\}$ who takes action $1$ when the forecast exceeds $\theta$ and action $0$ when it is below $\theta$: the loss is $-u_\theta(1, y) = \theta - y$ for $p > \theta$ and $-u_\theta(0, y) = y - \theta$ for $p < \theta$, so the agent's utility difference between the two actions is $u_\theta(1, y) - u_\theta(0, y) = 2(y - \theta)$ (the agent used in the proof of Theorem 10 of the source). Its univariate form $S_\theta(p) = \mathbb{E}_{y \sim \mathrm{Ber}(p)} S_\theta(p,y)$ is $-|p - \theta|$, and $S_\theta$ is a proper scoring rule with values in $[-1,1]$. Every proper scoring rule $S(p, y)$ for binary outcomes with values in $[-1,1]$ has a univariate form $G(p) = \mathbb{E}_{y \sim \mathrm{Ber}(p)} S(p,y)$, its Bayes risk, equal up to an affine function of $p$ to $\int_0^1 S_\theta(p)\,d\nu(\theta) = -\int_0^1 |p - \theta|\,d\nu(\theta)$ for a nonnegative measure $\nu$ of total mass at most $2$. Accordingly $S(p,y)$ equals $\int_0^1 S_\theta(p, y)\,d\nu(\theta)$, up to an additive term depending only on $y$, at every $p$ that is not an atom of $\nu$. At an atom $\theta_0$ the bivariate form is not determined by $G$: $S(\theta_0, \cdot)$ may use any supergradient of $G$ at $\theta_0$, which amounts to replacing $\mathrm{sign}(0) = 0$ in $S_{\theta_0}(\theta_0, \cdot)$ by a tie value in $[-1, 1]$. Consequently, writing $\mathrm{VCal}_T = \sup_{\theta \in [0,1]} \mathrm{Reg}_{S_\theta}$ for the largest regret of the forecasts under a V-shaped rule,

$$
\tfrac12\,\mathrm{UCal}_T \le \mathrm{VCal}_T \le \mathrm{UCal}_T .
$$

## Proof sketch

The univariate form $G$ of a proper scoring rule is concave and $S(p,y) = G(p) + G'(p)(y - p)$ for a supergradient $G'(p)$ of $G$ at $p$, unique except at the kinks of $G$, which are the atoms of $\nu$. Up to an affine function of $p$, which changes $S$ only by a term depending on $y$ and so does not change regret, $G$ is the integral of the functions $-|p-\theta|$ against the measure $\nu = -G''/2$. Since $G'(p) = S(p,1) - S(p,0) \in [-2,2]$, the total mass of $\nu$ is $(G'(0) - G'(1))/2 \le 2$. Regret is linear in the scoring rule, so $\mathrm{Reg}_S \le 2 \sup_\theta \mathrm{Reg}_{S_\theta}$, and the choice of tie values at the finitely many forecast values does not change $\mathrm{VCal}_T$ (Remark 3 of the source); the other inequality holds because each $S_\theta$ is one of the rules in the supremum defining $\mathrm{UCal}_T$.

## Depends on

- [U-calibration error](u-calibration-error.md)
- [Scoring rules and properness for finite outcomes](../../../GameTheory/mechanism-design/remaining-clauses-of-scoring-rules-and-properness.md)

## Proof depends on

- [Characterization of proper scoring rules](../../../GameTheory/mechanism-design/characterization-of-proper-scoring-rules.md)

## Sources

- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168, Lemma 1, Corollary 2, Theorem 8, Remark 3 and the proof of Theorem 10.
