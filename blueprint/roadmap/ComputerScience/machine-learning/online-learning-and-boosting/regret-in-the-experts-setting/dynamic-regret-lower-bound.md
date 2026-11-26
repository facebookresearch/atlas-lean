# No online algorithm competes with the best action sequence

Let $X$ have $N \ge 1$ actions and let $H$ be any causal (possibly randomized) online algorithm in the experts setting. For every horizon $T$ there are a binary loss sequence $\ell_t \in \{0,1\}^X$ and an action sequence $g_0, g_1, \ldots$ with $\sum_{t<T} \ell_t(g_t) = 0$ such that

$$
L_H^T \ge T\left(1 - \frac{1}{N}\right).
$$

So regret against the class of all action sequences is linear in $T$.

## Proof sketch

In each round the adversary computes $p_t$ (determined by the past), picks an action $g_t$ of minimum probability, so $p_t(g_t) \le 1/N$, and gives loss $0$ to $g_t$ and $1$ to all other actions. The algorithm then loses $1 - p_t(g_t) \ge 1 - 1/N$ per round, while the sequence $g$ loses nothing.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
