# Block learner: running a full-information algorithm on block-averaged losses

Let $X$ be a finite set of actions, $m \ge 1$ a block length and $K$ a number of blocks. For losses $\ell_t \in [0,1]^X$ define the block averages $c_\tau(i) = \frac1m \sum_{t = \tau m}^{\tau m + m - 1} \ell_t(i)$. Let $H$ be a full-information online algorithm with external regret at most $R$ over $K$ rounds on the losses $c_0, \ldots, c_{K-1}$. Playing $H(c_0, \ldots, c_{\tau-1})$ throughout block $\tau$ yields

$$
\sum_{t < Km} \langle p_t, \ell_t \rangle \le L_{\min}^{Km} + m R .
$$

## Proof sketch

The loss over block $\tau$ equals $m\langle H_\tau, c_\tau\rangle$ and the best fixed action's loss over all blocks equals $m \min_i \sum_\tau c_\tau(i)$. Multiplying the block regret bound by $m$ gives the claim.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
