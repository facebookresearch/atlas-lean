# Exp3 with uniform mixing: weak regret $(e-1)\gamma G_{\max} + K \ln K/\gamma$

Consider a $K$-armed bandit with rewards $g_t \in [0,1]^K$ fixed in advance by an oblivious adversary, and let $G_{\max} = \max_a \sum_{t<T} g_t(a)$. Exp3 with mixing parameter $\gamma \in (0,1]$ keeps weights $w_t(a)$, plays $p_t(a) = (1-\gamma)\, w_t(a)/\sum_b w_t(b) + \gamma/K$, observes the reward of the drawn arm $I_t$, forms the importance-weighted estimate $\hat g_t(a) = g_t(I_t)\mathbf{1}[a = I_t]/p_t(I_t)$, and updates $w_{t+1}(a) = w_t(a) \exp(\gamma \hat g_t(a)/K)$. Then

$$
G_{\max} - \mathbb{E}\Big[\sum_{t<T} g_t(I_t)\Big] \le (e-1)\gamma G_{\max} + \frac{K \ln K}{\gamma},
$$

and a tuned $\gamma$ (depending on $K$ and $T$) gives weak regret at most $2\sqrt{(e-1) T K \ln K}$ for every horizon $T$.

## Proof sketch

The estimate is conditionally unbiased and its weighted second moment is at most the sum of rewards over arms divided by the mixing floor. A second-order exponential-weights potential bound on the estimated rewards, using $e^x \le 1 + x + (e-2)x^2$ for $x \le 1$ (guaranteed by $\gamma \hat g / K \le 1$), and taking expectations, gives the bound. Bounding $G_{\max} \le T$ and optimizing $\gamma$ gives the tuned form.

## Depends on

- [Oblivious adversarial bandits](../../reinforcement-learning/multi-armed-bandits/oblivious-adversarial-bandits.md)

## Proof depends on

- [The second-order Hedge bound](../hedge-algorithm/alg-loss-le-sq.md)

## Sources

- Peter Auer, Nicolò Cesa-Bianchi, Yoav Freund and Robert E. Schapire, "The Nonstochastic Multiarmed Bandit Problem", SIAM Journal on Computing, 2002.
- Sébastien Bubeck and Nicolò Cesa-Bianchi, "Regret Analysis of Stochastic and Nonstochastic Multi-Armed Bandit Problems", Foundations and Trends in Machine Learning, 2012.
