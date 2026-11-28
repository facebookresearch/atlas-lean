# Best responding to calibrated forecasts gives no swap regret

Consider $T$ rounds with outcomes $y_t \in \{0,1\}$, forecasts $p_t$ taking finitely many values, and an agent with finite action set $\mathcal{A}$ and utilities $u(a, y) \in [0,1]$ who plays $a_t = a^*(p_t) \in \arg\max_a \big(p_t u(a,1) + (1-p_t) u(a,0)\big)$. Let $n_v = \#\{t : p_t = v\}$ and $m_v = \#\{t : p_t = v, y_t = 1\}$. Then the agent's swap regret satisfies

$$
\max_{\phi : \mathcal{A} \to \mathcal{A}} \sum_{t=1}^T \big(u(\phi(a_t), y_t) - u(a_t, y_t)\big) \le 2 \sum_v |m_v - v\, n_v|,
$$

the right side being twice the $\ell_1$ calibration error of the forecasts. This is Theorem 12 of Kleinberg–Paes Leme–Schneider–Teng, which takes utilities in $[-1,1]$ and obtains the constant $4$; rescaling such utilities to $[0,1]$ halves the regret and gives the constant $2$ above.

## Proof sketch

Group the rounds by forecast value $v$. On those rounds the agent plays $a^*(v)$, and for any deviation $b$ the gain is $(m_v - v n_v)(u(b,1) - u(b,0) - u(a^*(v),1) + u(a^*(v),0)) + n_v\big(\bar u_v(b) - \bar u_v(a^*(v))\big)$, where $\bar u_v(a) = v u(a,1) + (1-v)u(a,0)$. The second term is nonpositive by the choice of $a^*(v)$ and the first is at most $2|m_v - v n_v|$; a swap function $\phi$ deviates on the rounds with forecast $v$ to $b = \phi(a^*(v))$, so the swap regret is at most the sum over $v$ of the best single deviation on those rounds, and summing the bound over $v$ gives the claim.

## Depends on

- [Swap regret](../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)

## Sources

- D. P. Foster, R. V. Vohra, "Calibrated Learning and Correlated Equilibrium", Games and Economic Behavior 21 (1997).
- R. Kleinberg, R. Paes Leme, J. Schneider, Y. Teng, "U-Calibration: Forecasting for an Unknown Agent", COLT (2023), arXiv:2307.00168, Theorem 12.
